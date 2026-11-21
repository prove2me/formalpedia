-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.row_decoder_expression
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:35:02.92436+00:00
-- url     : https://prove2.me/submissions/b1f764ea-deee-48af-99b0-189ea680c646

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
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
private lemma firstF {p : World→Env→ℕ→Prop} (hp : BF (fun x e=>p x (tail e) (e 0))) :
    ZF (fun x e=>BallCoverCatalog.first x.n (p x e)) := by
  apply sumZ .points (f:=fun x e j=>if p x e j ∧ ∀l < x.n,l < j → ¬p x e l then (j:ℤ) else 0)
  apply ifZ _ (.var 0) (.const 0)
  apply andF hp
  apply allF .points (p:=fun x e l=>l < e 0 → ¬p x (tail e) l)
  apply impF (ltN (.var 0) (.var 1))
  apply noF
  exact Form.rename hp (fun i=>Nat.casesOn i 0 (fun j=>j+2))
private lemma natZ {f : World→Env→ℤ} (hf : ZF f) : NF (fun x e=>(f x e).toNat) := by
  have h := ifZ (leZ (.const 0) hf) hf (.const 0)
  convert h using 1
  funext x e;by_cases pos : 0≤f x e
  · simp [pos,Int.toNat_of_nonneg pos]
  · simp [pos,Int.toNat_of_nonpos (le_of_lt (lt_of_not_ge pos))]
private lemma zd (n : ℕ) : NF (fun _ _=>n) := Form.const (n:ℤ)
private lemma distF {a b : World→Env→ℕ} (ha : NF a) (hb : NF b) : RF (fun x e=>distAt x (a x e) (b x e)) := qry ha hb
private lemma relF {r i j : World→Env→ℕ} (hr : NF r) (hi : NF i) (hj : NF j) :
    BF (fun x e=>storedRel x (r x e) (i x e) (j x e)) := by
  let active (x : World) (v : ℕ) := 0<v ∧ v≤(x.mem 1).toNat
  have af {v : World→Env→ℕ} (hv : NF v) : BF (fun x e=>active x (v x e)) :=
    andF (ltN (zd 0) hv) (leN hv (natZ (readZ (zd 1))))
  have one {p : World→Env→ℕ} (hp : NF p) : BF (fun x e=>∃v < x.k,active x v ∧ hits x (r x e) (p x e) v) :=
    exF .blocks (p:=fun x e v=>active x v ∧ hits x (r x e) (p x e) v)
      (andF (af (.var 0)) (hitsF (upN hr) (upN hp) (.var 0)))
  apply orF
  · apply exF .blocks (p:=fun x e v=>active x v ∧ hits x (r x e) (i x e) v ∧ hits x (r x e) (j x e) v)
    exact andF (af (.var 0)) (andF (hitsF (upN hr) (upN hi) (.var 0)) (hitsF (upN hr) (upN hj) (.var 0)))
  · exact andF (noF (one hi)) (andF (noF (one hj)) (leR (distF hi hj) (chargeF hr (zd 0))))
private lemma rootF {r i : World→Env→ℕ} (hr : NF r) (hi : NF i) :
    BF (fun x e=>root x.n (storedRel x (r x e)) (i x e)) := by
  apply allF .points (p:=fun x e q=>storedRel x (r x e) (i x e) q → i x e ≤ q)
  exact impF (relF (upN hr) (upN hi) (.var 0)) (leN (upN hi) (.var 0))
private lemma rankF {r i : World→Env→ℕ} (hr : NF r) (hi : NF i) :
    NF (fun x e=>rank x.n (storedRel x (r x e)) (i x e)) := by
  have hh := sumZ .points (f:=fun x e q=>if q < i x e ∧ root x.n (storedRel x (r x e)) q then 1 else 0)
    (ifZ (andF (ltN (.var 0) (upN hi)) (rootF (upN hr) (.var 0))) (.const 1) (.const 0))
  convert hh using 1
  funext x e;congr 1;simp [rank,World.size,Finset.sum_boole]
private lemma slotF {r j i : World→Env→ℕ} (hr : NF r) (hj : NF j) (hi : NF i) :
    BF (fun x e=>slot x.n (storedRel x (r x e)) (j x e) (i x e)) := by
  apply exF .points (p:=fun x e p=>root x.n (storedRel x (r x e)) p ∧
    rank x.n (storedRel x (r x e)) p=j x e ∧ storedRel x (r x e) p (i x e))
  exact andF (rootF (upN hr) (.var 0)) (andF (eqN (rankF (upN hr) (.var 0)) (upN hj))
    (relF (upN hr) (.var 0) (upN hi)))
private lemma encF {r j c w : World→Env→ℕ} (hr : NF r) (hj : NF j) (hc : NF c) (hw : NF w) :
    BF (fun x e=>encloses x (storedRel x (r x e)) (j x e) (c x e) (w x e)) := by
  apply andF (slotF hr hj hc);apply andF (slotF hr hj hw)
  apply allF .points (p:=fun x e i=>slot x.n (storedRel x (r x e)) (j x e) i →
    distAt x (c x e) i ≤ distAt x (c x e) (w x e))
  exact impF (slotF (upN hr) (upN hj) (.var 0)) (leR (distF (upN hc) (.var 0)) (distF (upN hc) (upN hw)))
private lemma bestF {r j c w : World→Env→ℕ} (hr : NF r) (hj : NF j) (hc : NF c) (hw : NF w) :
    BF (fun x e=>best x (storedRel x (r x e)) (j x e) (c x e) (w x e)) := by
  apply andF (encF hr hj hc hw)
  apply allF .points (p:=fun x e a=>∀b < x.n,encloses x (storedRel x (r x e)) (j x e) a b →
    distAt x (c x e) (w x e) ≤ distAt x a b)
  apply allF .points (p:=fun x e b=>encloses x (storedRel x (r x (tail e))) (j x (tail e)) (e 0) b →
    distAt x (c x (tail e)) (w x (tail e)) ≤ distAt x (e 0) b)
  exact impF (encF (upN (upN hr)) (upN (upN hj)) (.var 1) (.var 0))
    (leR (distF (upN (upN hc)) (upN (upN hw))) (distF (.var 1) (.var 0)))
private lemma pickF {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) :
    ZF (fun x e=>pickedCenter x (storedRel x (r x e)) (j x e)) := by
  apply firstF (p:=fun x e c=>∃w < x.n,best x (storedRel x (r x e)) (j x e) c w)
  apply exF .points (p:=fun x e w=>best x (storedRel x (r x (tail e))) (j x (tail e)) (e 0) w)
  exact bestF (upN (upN hr)) (upN (upN hj)) (.var 1) (.var 0)
private lemma farF {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) :
    ZF (fun x e=>pickedWitness x (storedRel x (r x e)) (j x e)) := by
  apply firstF (p:=fun x e w=>best x (storedRel x (r x e)) (j x e)
    (pickedCenter x (storedRel x (r x e)) (j x e)).toNat w)
  exact bestF (upN hr) (upN hj) (natZ (pickF (upN hr) (upN hj))) (.var 0)
theorem solution (w : Bool) : Form (fun x ρ=>iv (transformed x (ρ 0) (ρ 1) w)) := by
  cases w
  · exact ifZ (ltN (.var 0) (natZ (readZ (zd 2)))) (centerF (.var 0) (.var 1)) (pickF (.var 0) (.var 1))
  · exact ifZ (ltN (.var 0) (natZ (readZ (zd 2)))) (witF (.var 0) (.var 1)) (farF (.var 0) (.var 1))
