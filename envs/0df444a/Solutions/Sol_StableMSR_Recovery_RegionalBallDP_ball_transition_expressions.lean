-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.ball_transition_expressions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:13:57.746127+00:00
-- url     : https://prove2.me/submissions/eafb8aee-68c5-43fb-9404-ff1e2fffc148

import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
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
private lemma natF {f : World→Env→ℤ} (hf : ZF f) : NF (fun x e=>(f x e).toNat) := by
  have h := ifZ (leZ (.const 0) hf) hf (.const 0)
  convert h using 1
  funext x e;by_cases hz : 0≤f x e
  · simp [hz,Int.toNat_of_nonneg]
  · simp [hz,Int.toNat_of_nonpos (by omega : f x e≤0)]
private lemma plus {f g : World→Env→ℕ} (hf : NF f) (hg : NF g) : NF (fun x e=>f x e+g x e) := by
  simpa only [NF,Nat.cast_add] using addZ hf hg
private lemma ifN {p : World→Env→Prop} {f g : World→Env→ℕ} [∀x e,Decidable (p x e)] (hp : BF p) (hf : NF f) (hg : NF g) :
    NF (fun x e=>if p x e then f x e else g x e) := by simpa only [NF,apply_ite] using ifZ hp hf hg
private lemma ifR {p : World→Env→Prop} {f g : World→Env→ℝ} [∀x e,Decidable (p x e)] (hp : BF p) (hf : RF f) (hg : RF g) :
    RF (fun x e=>if p x e then f x e else g x e) := by
  convert iteF hp hf hg using 1
  funext x e;by_cases h : p x e <;> simp [h]
private lemma fld {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) (w : Bool) :
    ZF (fun x e=>field x (r x e) (j x e) w) := by cases w
                                                  · exact centerF hr hj
                                                  · exact witF hr hj
private lemma legal {z : World→Env→ℤ} (hz : ZF z) : ZF (fun x e=>legalize x.n (z x e)) := by
  have h : BF (fun x e=>z x e < (x.n:ℤ)) := by
    simpa only [not_le,World.size] using noF (leZ (.size .points) hz)
  exact ifZ (andF (leZ (.const 0) hz) h) hz (.const 0)
private lemma nslots : NF (fun x _=>slots x) := natF (centerF (.const 0) (.const 0))
private lemma wide {v : World→Env→ℕ} (hv : NF v) : NF (fun x e=>width x (v x e)) := by
  let z := fun (x : World) (e : Env)=>(center x (slots x+slots x+v x e) 0).toNat
  have hz : NF z := natF (centerF (plus (plus nslots nslots) hv) (.const 0))
  have h := ifN (leN (.size .blocks) hz) (.size .blocks) hz
  have hmin : NF (fun x e=>min x.k (z x e)) := by
    convert h using 1
    funext x e;by_cases le : x.k≤z x e <;> simp [World.size,min_def,le]
  exact ifN (eqN hv (.const 1)) (.const 0) hmin
private lemma parF {q : World→Env→ℕ} (hq : NF q) : NF (fun x e=>parent x (q x e)) :=
  natF (centerF (plus (plus (plus nslots nslots) nslots) hq) (.const 0))
private lemma destF {q : World→Env→ℕ} (hq : NF q) : ZF (fun x e=>destination x (q x e)) :=
  witF (plus (plus (plus nslots nslots) nslots) hq) (.const 0)
private lemma vertF {q : World→Env→ℕ} (hq : NF q) : BF (fun x e=>vertex x (q x e)) :=
  andF (ltN (.const 0) hq) (leN hq nslots)
private lemma eligF {v q : World→Env→ℕ} (hv : NF v) (hq : NF q) : BF (fun x e=>eligible x (v x e) (q x e)) :=
  andF (andF (vertF hq) (andF (vertF (parF hq)) (andF (ltN (parF hq) hv)
    (andF (eqZ (destF hq) hv) (leN (wide (parF hq)) (wide hv)))))) (leZ (.const 0) (centerF (parF hq) (.const 0)))
private lemma candF {v q j : World→Env→ℕ} (hv : NF v) (hq : NF q) (hj : NF j) (w : Bool) :
    ZF (fun x e=>candidate x (v x e) (q x e) (j x e) w) :=
  ifZ (ltN hj (wide (parF hq))) (ifZ (ltN hj (.size .blocks)) (fld (parF hq) hj w) (.const 0))
    (ifZ (ltN hj (wide hv)) (legal (fld (plus nslots hq) hj w)) (.const 0))
private lemma priceF {v q : World→Env→ℕ} (hv : NF v) (hq : NF q) : RF (fun x e=>price x (v x e) (q x e)) := by
  apply sumR .blocks (f:=fun x e j=>if j<width x (v x e) then
    MinSumFPT.oracleAnswer x.dist (candidate x (v x e) (q x e) j false) (candidate x (v x e) (q x e) j true) else 0)
  exact ifR (ltN (.var 0) (wide (upN hv))) (qry (candF (upN hv) (upN hq) (.var 0) false)
    (candF (upN hv) (upN hq) (.var 0) true)) (show RF (fun _ _=>0) from .const 0)
private lemma winF {v q : World→Env→ℕ} (hv : NF v) (hq : NF q) : BF (fun x e=>winner x (v x e) (q x e)) := by
  apply andF (eligF hv hq)
  apply allF .rows (p:=fun x e z=>eligible x (v x e) z →
    price x (v x e) (q x e)<price x (v x e) z ∨ price x (v x e) (q x e)=price x (v x e) z ∧ q x e≤z)
  have a:=priceF (upN hv) (upN hq)
  have b:=priceF (upN hv) (show NF (fun _ e=>e 0) from .var 0)
  exact impF (eligF (upN hv) (.var 0)) (orF (ltR a b) (andF (eqR a b) (leN (upN hq) (.var 0))))
private lemma headerF (w : Bool) {j : World→Env→ℕ} (hj : NF j) : BF (fun x e=>j x e=0 ∧ w=true) := by
  cases w
  · unfold BF;simp;exact .const 0
  · simpa only [and_true] using eqN hj (.const 0)
theorem solution :
    (∀w : Bool,Form (fun x ρ=>iv (seedTable x (ρ 0) (ρ 1) w))) ∧
    (∀w : Bool,Form (fun x ρ=>iv (tick x (ρ 0) (ρ 1) w))) ∧
    (∀w : Bool,Form (fun x ρ=>iv (clean x (ρ 0) (ρ 1) w))) := by
  have v : NF (fun _ e=>e 0) := .var 0
  have j : NF (fun _ e=>e 1) := .var 1
  refine ⟨?_,?_,?_⟩
  · intro w
    exact ifZ (eqN v (.const 0)) (ifZ (headerF w j) (.const 0) (fld v j w))
      (ifZ (leN v nslots) (ifZ (eqN v (.const 1)) (.const 0) (.const (-1))) (fld v j w))
  · intro w
    apply ifZ (eqN v (.const 0)) (ifZ (headerF w j) (addZ (witF (.const 0) (.const 0)) (.const 1)) (fld v j w))
    apply ifZ (leN v nslots) _ (fld v j w)
    apply ifZ (eqN v (.const 1)) (.const 0)
    apply ifZ (exF .rows (p:=fun x e q=>eligible x (e 0) q) (eligF (upN v) (.var 0))) _ (.const (-1))
    apply sumZ .rows (f:=fun x e q=>if winner x (e 0) q then candidate x (e 0) q (e 1) w else 0)
    exact ifZ (winF (upN v) (.var 0)) (candF (upN v) (.var 0) (upN j) w) (.const 0)
  · intro w;exact legal (fld v j w)

