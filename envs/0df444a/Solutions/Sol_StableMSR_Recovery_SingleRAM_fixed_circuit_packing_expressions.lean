-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.fixed_circuit_packing_expressions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:36.179806+00:00
-- url     : https://prove2.me/submissions/dda00ac6-def2-44fd-af02-bae7cee325c5

import Definitions.Def_StableMSR_SingleCircuitRAM
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
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
  funext x e;by_cases hz : 0≤ f x e
  · simp [hz,Int.toNat_of_nonneg]
  · simp [hz,Int.toNat_of_nonpos (by omega : f x e≤0)]
private lemma plus {f g : World→Env→ℕ} (hf : NF f) (hg : NF g) : NF (fun x e=>f x e+g x e) := by
  simpa only [NF,Nat.cast_add] using addZ hf hg
private lemma ifN {p : World→Env→Prop} {f g : World→Env→ℕ} [∀x e,Decidable (p x e)] (hp : BF p) (hf : NF f) (hg : NF g) :
    NF (fun x e=>if p x e then f x e else g x e) := by simpa only [NF,apply_ite] using ifZ hp hf hg

private lemma iffF {p q : World→Env→Prop} (hp : BF p) (hq : BF q) : BF (fun x ρ=>p x ρ ↔ q x ρ) := by
  simpa only [iff_iff_implies_and_implies] using andF (impF hp hq) (impF hq hp)
private lemma sumN (a : Axis) {f : World→Env→ℕ→ℕ} (hf : NF (fun x ρ=>f x (tail ρ) (ρ 0))) :
    NF (fun x ρ=>∑i∈Finset.range (x.size a),f x ρ i) := by
  simpa only [NF,Nat.cast_sum] using sumZ a (f:=fun x ρ i=>(f x ρ i:ℤ)) hf
private lemma predF {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>f x ρ-1) := by
  have g:=natF (addZ hf (.const (-1)))
  convert g using 1
  funext x ρ;congr 2;omega
private lemma timesAxis (a : Axis) {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>f x ρ*x.size a) := by
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using
    sumN a (f:=fun x ρ _=>f x ρ) (upN hf)
private lemma twiceF {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>2*f x ρ) := by
  simpa only [two_mul] using plus hf hf

private lemma fieldF (s : Bool) {r j : World→Env→ℕ} (hr : NF r) (hj : NF j) :
    ZF (fun x ρ=>RegionalBallDP.field x (r x ρ) (j x ρ) s) :=by
  cases s
  · exact centerF hr hj
  · exact witF hr hj
private lemma subF {a b : World→Env→ℕ} (ha : NF a) (hb : NF b) :
    NF (fun x ρ=>subR x (a x ρ) (b x ρ)) :=
  sumN .rows (f:=fun x ρ t=>if b x ρ+t=a x ρ then t else 0)
    (ifN (eqN (plus (upN hb) (.var 0)) (upN ha)) (.var 0) (.const 0))
private lemma divF {a : World→Env→ℕ} (ha : NF a) : NF (fun x ρ=>divN x (a x ρ)) :=
  sumN .rows (f:=fun x ρ t=>if t*x.n≤ a x ρ ∧ a x ρ<(t+1)*x.n then t else 0)
    (ifN (andF (leN (timesAxis .points (.var 0)) (upN ha))
      (ltN (upN ha) (timesAxis .points (plus (.var 0) (.const 1))))) (.var 0) (.const 0))
private lemma remF {a : World→Env→ℕ} (ha : NF a) : NF (fun x ρ=>remN x (a x ρ)) :=
  subF ha (timesAxis .points (divF ha))
private lemma mulC (a : ℕ) {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>a*f x ρ) :=by
  induction a with
  | zero => simpa only [Nat.zero_mul] using (show NF (fun _ _=>0) from .const 0)
  | succ a ih => simpa only [Nat.succ_mul] using plus ih hf
private lemma sizeF : NF (fun x _=>rawSize x):=natF (readZ (.const 0))
private lemma qF {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>quotient x (f x ρ)):=by
  apply sumN .rows (f:=fun x ρ i=>if 3*i≤ f x ρ ∧ f x ρ<3*(i+1) then i else 0)
  exact ifN (andF (leN (mulC 3 (.var 0)) (upN hf)) (ltN (upN hf) (mulC 3 (plus (.var 0) (.const 1))))) (.var 0) (.const 0)
private lemma slF {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>slot x (f x ρ)):=subF hf (mulC 3 (qF hf))
private lemma opF {f : World→Env→ℕ} (hf : NF f) : ZF (fun x ρ=>inputTag x (f x ρ)):=centerF (plus (.const 1) hf) (.const 0)
private lemma lF {f : World→Env→ℕ} (hf : NF f) : ZF (fun x ρ=>inputLeft x (f x ρ)):=witF (plus (.const 1) hf) (.const 0)
private lemma rF {f : World→Env→ℕ} (hf : NF f) : ZF (fun x ρ=>inputRight x (f x ρ)):=centerF (plus (plus (.const 1) sizeF) hf) (.const 0)
private lemma rtF {f : World→Env→ℕ} (hf : NF f) : ZF (fun x ρ=>inputRoot x (f x ρ)):=centerF (plus (plus (.const 1) (mulC 2 sizeF)) hf) (.const 0)
private lemma bitF {f i : World→Env→ℕ} (hf : NF f) (hi : NF i) : ZF (fun x ρ=>inputBit x (f x ρ) (i x ρ)):=readZ (plus (plus (addrF (plus (.const 1) (mulC 5 sizeF)) (.const 0)) (timesAxis .points hf)) hi)
private lemma kindF {t : World→Env→ℤ} {j : World→Env→ℕ} (ht : ZF t) (hj : NF j) : ZF (fun x ρ=>tagFor (t x ρ) (j x ρ)):=by
  let z:=eqN hj (.const 0);let o:=eqN hj (.const 1);let two:=eqN hj (.const 2)
  exact ifZ (eqZ ht (.const 0)) (ifZ z (.const 0) (.const (-1)))
    (ifZ (eqZ ht (.const 1)) (ifZ z (.const 1) (ifZ o (.const 2) (.const (-1))))
      (ifZ (eqZ ht (.const 2)) (ifZ (orF z o) (.const 1) (ifZ two (.const 2) (.const (-1)))) (.const (-1))))
private lemma ptrF {t l r : World→Env→ℤ} {j : World→Env→ℕ} (ht : ZF t) (hl : ZF l) (hr : ZF r) (hj : NF j) :
    ZF (fun x ρ=>childFor (t x ρ) (l x ρ) (r x ρ) (j x ρ)):=
  ifZ (orF (eqZ ht (.const 1)) (eqZ ht (.const 2))) (ifZ (eqN hj (.const 0)) hl (ifZ (eqN hj (.const 1)) hr (.const 0))) (.const 0)
theorem solution : ∀s : Bool,Form (fun x ρ=>iv (packCell x (ρ 0) (ρ 1) s)) := by
  intro s
  have r : NF (fun _ ρ=>ρ 0):=.var 0
  have j : NF (fun _ ρ=>ρ 1):=.var 1
  let m:=mulC 3 sizeF
  let b1:=plus (.const 1) m;let b2:=plus (.const 1) (mulC 2 m)
  let b3:=plus (.const 1) (mulC 3 m);let b4:=plus (.const 1) (mulC 4 m)
  let a:=subF r (.const 1);let q:=subF r b1;let p:=qF q
  let step:=timesAxis .blocks (subF r b4)
  let d:=plus (mulC 2 (plus step j)) (show NF (fun _ _=>if s then 1 else 0) from by cases s <;> exact .const _)
  let last:=bitF (qF (divF d)) (remF d)
  let ptr:=ptrF (opF p) (lF p) (rF p) (slF q)
  let rest:=ifZ (ltN r b2) ptr (ifZ (ltN r b3) (.const 0) (ifZ (ltN r b4) (rtF (subF r b3)) last))
  cases s
  · exact ifZ (eqN r (.const 0)) m (ifZ (ltN r b1) (kindF (opF (qF a)) (slF a)) rest)
  · exact ifZ (eqN r (.const 0)) (readZ (.const 1)) (ifZ (ltN r b1) (qF a) rest)
