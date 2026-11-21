-- Prove2me | solution 1 for StableMSR.Recovery.BallCoverCatalog.selector_expression
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:30:27.997525+00:00
-- url     : https://prove2.me/submissions/5eac03c4-5f49-435b-9f78-6cdc473169c0

import Definitions.Def_StableMSR_BallCoverCatalog
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open StableMSR.Recovery.BallCoverCatalog
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private abbrev ZF (f : World→Env→ℤ) := Form (fun x e=>iv (f x e))
private abbrev NF (f : World→Env→ℕ) := ZF (fun x e=>(f x e:ℤ))
private abbrev RF (f : World→Env→ℝ) := Form (fun x e=>rv (f x e))
private noncomputable def BF (p : World→Env→Prop) := Form (fun x e=>if p x e then iv 1 else iv 0)
private def tail (e : Env) := fun j=>e (j+1)
private lemma upZ {f : World→Env→ℤ} (hf : ZF f) : ZF (fun x e=>f x (tail e)) := hf.rename Nat.succ
private lemma upN {f : World→Env→ℕ} (hf : NF f) : NF (fun x e=>f x (tail e)) := hf.rename Nat.succ
private lemma addZ {f g : World→Env→ℤ} (hf : ZF f) (hg : ZF g) : ZF (fun x e=>f x e+g x e) := by
  have eq := Form.bin .add hf hg
  convert eq using 1
  funext x e;apply Prod.ext <;> simp [Prim.val,iv]
private lemma leZ {f g : World→Env→ℤ} (hf : ZF f) (hg : ZF g) : BF (fun x e=>f x e ≤ g x e) := by
  unfold BF
  convert Form.bin .ile hf hg using 1
  funext x e;by_cases h : f x e ≤ g x e <;> simp [Prim.val,iv,flag,h]
private lemma leR {f g : World→Env→ℝ} (hf : RF f) (hg : RF g) : BF (fun x e=>f x e ≤ g x e) := by
  unfold BF
  convert Form.bin .rle hf hg using 1
  funext x e;by_cases h : f x e ≤ g x e <;> simp [Prim.val,rv,flag,h]
private lemma iteF {p : World→Env→Prop} {f g : Term} [∀x e,Decidable (p x e)]
    (hp : BF p) (hf : Form f) (hg : Form g) : Form (fun x e=>if p x e then f x e else g x e) := by
  unfold BF at hp
  convert Form.branch hp hf hg using 1
  funext x e;by_cases h : p x e <;> simp [iv,h]
private lemma noF {p : World→Env→Prop} (hp : BF p) : BF (fun x e=>¬p x e) := by
  unfold BF
  convert iteF hp (.const 0) (.const 1) using 1
  funext x e;by_cases h : p x e <;> simp [h]
private lemma andF {p q : World→Env→Prop} (hp : BF p) (hq : BF q) : BF (fun x e=>p x e ∧ q x e) := by
  unfold BF at hq ⊢
  convert iteF hp hq (.const 0) using 1
  funext x e;by_cases h : p x e <;> simp [h]
private lemma orF {p q : World→Env→Prop} (hp : BF p) (hq : BF q) : BF (fun x e=>p x e ∨ q x e) := by
  simpa only [not_and_or,not_not] using noF (andF (noF hp) (noF hq))
private lemma impF {p q : World→Env→Prop} (hp : BF p) (hq : BF q) : BF (fun x e=>p x e → q x e) := by
  simpa only [not_and,not_not] using noF (andF hp (noF hq))
private lemma eqZ {f g : World→Env→ℤ} (hf : ZF f) (hg : ZF g) : BF (fun x e=>f x e=g x e) := by
  simpa only [le_antisymm_iff] using andF (leZ hf hg) (leZ hg hf)
private lemma eqN {f g : World→Env→ℕ} (hf : NF f) (hg : NF g) : BF (fun x e=>f x e=g x e) := by
  simpa only [Int.natCast_inj] using eqZ hf hg
private lemma ltN {f g : World→Env→ℕ} (hf : NF f) (hg : NF g) : BF (fun x e=>f x e < g x e) := by
  simpa only [not_le,Int.ofNat_lt] using noF (leZ hg hf)
private lemma leN {f g : World→Env→ℕ} (hf : NF f) (hg : NF g) : BF (fun x e=>f x e ≤ g x e) := by
  simpa only [Int.ofNat_le] using leZ hf hg
private lemma eqR {f g : World→Env→ℝ} (hf : RF f) (hg : RF g) : BF (fun x e=>f x e=g x e) := by
  simpa only [le_antisymm_iff] using andF (leR hf hg) (leR hg hf)
private lemma ltR {f g : World→Env→ℝ} (hf : RF f) (hg : RF g) : BF (fun x e=>f x e < g x e) := by
  simpa only [not_le] using noF (leR hg hf)
private lemma ifZ {p : World→Env→Prop} {f g : World→Env→ℤ} [∀x e,Decidable (p x e)]
    (hp : BF p) (hf : ZF f) (hg : ZF g) : ZF (fun x e=>if p x e then f x e else g x e) := by
  convert iteF hp hf hg using 1
  funext x e;by_cases h : p x e <;> simp [h]
private lemma sumIV (s : Finset ℕ) (f : ℕ→ℤ) : (∑i ∈ s,iv (f i))=iv (∑i ∈ s,f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty];rfl
  | insert a s h ih => simp only [Finset.sum_insert h,ih];apply Prod.ext <;> simp [iv]
private lemma sumRV (s : Finset ℕ) (f : ℕ→ℝ) : (∑i ∈ s,rv (f i))=rv (∑i ∈ s,f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty];rfl
  | insert a s h ih => simp only [Finset.sum_insert h,ih];apply Prod.ext <;> simp [rv]
private lemma sumZ (a : Axis) {f : World→Env→ℕ→ℤ} (hf : ZF (fun x e=>f x (tail e) (e 0))) :
    ZF (fun x e=>∑i ∈ Finset.range (x.size a),f x e i) := by
  convert Form.total a hf using 1
  funext x e;exact (sumIV _ _).symm
private lemma sumR (a : Axis) {f : World→Env→ℕ→ℝ} (hf : RF (fun x e=>f x (tail e) (e 0))) :
    RF (fun x e=>∑i ∈ Finset.range (x.size a),f x e i) := by
  convert Form.total a hf using 1
  funext x e;exact (sumRV _ _).symm
private lemma allF (a : Axis) {p : World→Env→ℕ→Prop} (hp : BF (fun x e=>p x (tail e) (e 0))) :
    BF (fun x e=>∀i < x.size a,p x e i) := by
  have count := sumZ a (f:=fun x e i=>if p x e i then 0 else 1) (ifZ hp (.const 0) (.const 1))
  have test := eqZ count (.const 0)
  unfold BF at *
  convert test using 1
  funext x e
  have eq : (∑i ∈ Finset.range (x.size a),if p x e i then (0:ℤ) else 1)=0 ↔ ∀i < x.size a,p x e i := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i hi=>by split <;> decide)]
    simp
  by_cases h : ∀i < x.size a,p x e i <;> simp [eq,h]
private lemma exF (a : Axis) {p : World→Env→ℕ→Prop} (hp : BF (fun x e=>p x (tail e) (e 0))) :
    BF (fun x e=>∃i < x.size a,p x e i) := by
  simpa only [not_forall,Classical.not_imp,not_not,exists_prop] using noF (allF a (p:=fun x e i=>¬p x e i) (noF hp))
private lemma readZ {f : World→Env→ℕ} (hf : NF f) : ZF (fun x e=>x.mem (f x e)) := by
  simpa [Prim.val,iv,ZF] using Form.bin .read hf (.const 0)
private lemma qry {f g : World→Env→ℤ} (hf : ZF f) (hg : ZF g) :
    RF (fun x e=>MinSumFPT.oracleAnswer x.dist (f x e) (g x e)) := Form.bin .query hf hg
private lemma addrF {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) : NF (fun x e=>addr x.k (r x e) (j x e)) := by
  have mul := sumZ .blocks (f:=fun x e _=>(r x e:ℤ)) (upN hr)
  have s := addZ mul hj
  have total := addZ (.const 3) (addZ s s)
  convert total using 1
  funext x e
  congr 1
  simp [addr,World.size];ring
private lemma centerF {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) : ZF (fun x e=>center x (r x e) (j x e)) := readZ (addrF hr hj)
private lemma witF {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) : ZF (fun x e=>witness x (r x e) (j x e)) := by
  apply readZ
  simpa only [NF,Nat.cast_add,Nat.cast_one] using addZ (addrF hr hj) (.const 1)
private lemma chargeF {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) : RF (fun x e=>charge x (r x e) (j x e)) :=
  qry (centerF hr hj) (witF hr hj)
private lemma hitsF {r i j : World→Env→ℕ} (hr : NF r) (hi : NF i) (hj : NF j) : BF (fun x e=>hits x (r x e) (i x e) (j x e)) :=
  leR (qry (centerF hr hj) hi) (chargeF hr hj)
private lemma goodF {r : World→Env→ℕ} (hr : NF r) : BF (fun x e=>good x (r x e)) := by
  apply andF
  · apply allF .blocks (p:=fun x e j=>∀l < x.k, center x (r x e) j=center x (r x e) l → j=l)
    apply allF .blocks (p:=fun x e l=>center x (r x (tail e)) (e 0)=center x (r x (tail e)) l → e 0=l)
    exact impF (eqZ (centerF (upN (upN hr)) (.var 1)) (centerF (upN (upN hr)) (.var 0))) (eqN (.var 1) (.var 0))
  · apply allF .points (p:=fun x e i=>∃j < x.k,hits x (r x e) i j)
    apply exF .blocks (p:=fun x e j=>hits x (r x (tail e)) (e 0) j)
    exact hitsF (upN (upN hr)) (.var 1) (.var 0)
private lemma scoreF {r : World→Env→ℕ} (hr : NF r) : RF (fun x e=>score x (r x e)) :=
  sumR .blocks (f:=fun x e j=>charge x (r x e) j) (chargeF (upN hr) (.var 0))
private lemma winsF {r : World→Env→ℕ} (hr : NF r) : BF (fun x e=>wins x (r x e)) := by
  apply andF (goodF hr)
  apply allF .rows (p:=fun x e u=>good x u →
    score x (r x e)<score x u ∨ score x (r x e)=score x u ∧ r x e ≤ u)
  exact impF (goodF (.var 0)) (orF (ltR (scoreF (upN hr)) (scoreF (.var 0)))
    (andF (eqR (scoreF (upN hr)) (scoreF (.var 0))) (leN (upN hr) (.var 0))))
private lemma firstF {p : World→Env→ℕ→Prop} (hp : BF (fun x e=>p x (tail e) (e 0))) :
    ZF (fun x e=>BallCoverCatalog.first x.k (p x e)) := by
  apply sumZ .blocks (f:=fun x e j=>if p x e j ∧ ∀l < x.k,l < j → ¬p x e l then (j:ℤ) else 0)
  apply ifZ _ (.var 0) (.const 0)
  apply andF hp
  apply allF .blocks (p:=fun x e l=>l < e 0 → ¬p x (tail e) l)
  apply impF (ltN (.var 0) (.var 1))
  apply noF
  exact Form.rename hp (fun i=>Nat.casesOn i 0 (fun j=>j+2))
private lemma assignF {r i : World→Env→ℕ} (hr : NF r) (hi : NF i) : ZF (fun x e=>assigned x (r x e) (i x e)) := by
  let pred := fun (x : World) (e : Env) (j : ℕ)=>center x (r x e) j=(i x e:ℤ)
  have pp : BF (fun x e=>pred x (tail e) (e 0)) := eqZ (centerF (upN hr) (.var 0)) (upN hi)
  exact ifZ (exF .blocks (p:=pred) pp) (firstF (p:=pred) pp)
    (firstF (p:=fun x e j=>hits x (r x e) (i x e) j) (hitsF (upN hr) (upN hi) (.var 0)))

theorem solution : Form (fun x ρ=>iv (output x (ρ 0))) := by
  apply ifZ (exF .rows (p:=fun x _ r=>good x r) (goodF (.var 0)))
  · apply sumZ .rows (f:=fun x e r=>if wins x r then assigned x r (e 0) else 0)
    exact ifZ (winsF (.var 0)) (assignF (.var 0) (.var 1)) (.const 0)
  · have lt : BF (fun x e=>(e 0:ℤ) < (x.k:ℤ)) := by
      simpa only [not_le,World.size] using noF (leZ (Form.size .blocks) (Form.var 0))
    apply ifZ lt (.var 0)
    exact addZ (.size .blocks) (.const (-1))
