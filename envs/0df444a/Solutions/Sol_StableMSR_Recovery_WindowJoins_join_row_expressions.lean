-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.join_row_expressions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:52:54.906174+00:00
-- url     : https://prove2.me/submissions/ef9e4cde-055d-4ef3-82fc-11173a58c56e

import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
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
private lemma sumN (a : Axis) {f : World→Env→ℕ→ℕ} (hf : NF (fun x ρ=>f x (tail ρ) (ρ 0))) :
    NF (fun x ρ=>∑i∈Finset.range (x.size a),f x ρ i) := by
  simpa only [NF,Nat.cast_sum] using sumZ a (f:=fun x ρ i=>(f x ρ i:ℤ)) hf
private lemma predF {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>f x ρ-1) := by
  have g:=natF (addZ hf (.const (-1)))
  convert g using 1
  funext x ρ;congr 2;omega
private lemma mulC (a : ℕ) {f : World→Env→ℕ} (hf : NF f) : NF (fun x ρ=>a*f x ρ) :=by
  induction a with
  | zero => simpa only [Nat.zero_mul] using (show NF (fun _ _=>0) from .const 0)
  | succ a ih => simpa only [Nat.succ_mul] using plus ih hf
private lemma ns : NF (fun x _=>slots x) :=natF (centerF (.const 0) (.const 0))
private lemma bandF (b : ℕ) (s : Bool) {q j : World→Env→ℕ} (hq : NF q) (hj : NF j) :
    ZF (fun x ρ=>band x b (q x ρ) (j x ρ) s) :=
  ifZ (andF (ltN hq ns) (ltN hj (.size .blocks))) (fld (plus (plus (.const 1) (mulC b ns)) hq) hj s) (.const 0)
private lemma countF {v : World→Env→ℕ} (hv : NF v) : NF (fun x ρ=>(decode x).len (v x ρ)) :=by
  let z:=fun (x : World) (ρ : Env)=>(band x 2 (v x ρ) 0 false).toNat
  have p : NF z:=natF (bandF 2 false hv (.const 0))
  have a:=ifN (leN (.size .blocks) p) (.size .blocks) p
  change NF (fun x ρ=>min x.k (z x ρ))
  convert a using 1
  funext x ρ;by_cases h : x.k≤ z x ρ <;> simp [World.size,min_def,h]
private lemma forkF {q : World→Env→ℕ} (hq : NF q) : BF (fun x ρ=>(decode x).fork (q x ρ)) :=by
  simpa only [decode,not_le] using noF (leZ (bandF 3 true hq (.const 0)) (.const 0))
private lemma leftF {q : World→Env→ℕ} (hq : NF q) : NF (fun x ρ=>(decode x).lhs (q x ρ)) :=natF (bandF 4 false hq (.const 0))
private lemma rightF {q : World→Env→ℕ} (hq : NF q) : NF (fun x ρ=>(decode x).rhs (q x ρ)) :=natF (bandF 4 true hq (.const 0))
private lemma actF {q : World→Env→ℕ} (hq : NF q) : BF (fun x ρ=>liveRow x (q x ρ)) :=leZ (.const 0) (centerF (plus (.const 1) hq) (.const 0))
private lemma rowF (s : Bool) {v j : World→Env→ℕ} (hv : NF v) (hj : NF j) :
    ZF (fun x ρ=>rowWord x (v x ρ) (j x ρ) s) :=ifZ (ltN hj (.size .blocks)) (fld (plus (.const 1) hv) hj s) (.const 0)
private lemma eligF {v q : World→Env→ℕ} (hv : NF v) (hq : NF q) :
    BF (fun x ρ=>eligible (decode x) (liveRow x) (v x ρ) (q x ρ)) :=by
  have l:=leftF hq;have r:=rightF hq
  exact andF (andF (ltN hq ns) (eqZ (bandF 3 false hq (.const 0)) hv))
    (impF (forkF hq) (andF (andF (ltN l hv) (andF (ltN r hv) (eqN (plus (countF l) (countF r)) (countF hv)))) (andF (actF l) (actF r))))
private lemma shiftF {j a : World→Env→ℕ} (hj : NF j) (ha : NF a) : NF (fun x ρ=>shift x.k (j x ρ) (a x ρ)) :=
  sumN .blocks (f:=fun x ρ t=>if a x ρ+t=j x ρ then t else 0)
    (ifN (eqN (plus (upN ha) (.var 0)) (upN hj)) (.var 0) (.const 0))
private lemma candF (s : Bool) {v q j : World→Env→ℕ} (hv : NF v) (hq : NF q) (hj : NF j) :
    ZF (fun x ρ=>candidate x.k (decode x) (rowWord x) (v x ρ) (q x ρ) (j x ρ) s) :=by
  have l:=leftF hq;have r:=rightF hq;have a:=countF l;have c:=countF hv
  simp only [candidate,ite_apply,appendWords,atomWord]
  exact ifZ (forkF hq) (ifZ (ltN hj a) (rowF s l hj) (ifZ (ltN hj c) (rowF s r (shiftF hj a)) (.const 0)))
    (ifZ (ltN hj c) (legal (bandF 1 s hq hj)) (.const 0))
private lemma priceF {v q : World→Env→ℕ} (hv : NF v) (hq : NF q) :
    RF (fun x ρ=>weight x ((decode x).len (v x ρ)) (candidate x.k (decode x) (rowWord x) (v x ρ) (q x ρ))) :=by
  apply sumR .blocks (f:=fun x ρ j=>if j<(decode x).len (v x ρ) then
    MinSumFPT.oracleAnswer x.dist (candidate x.k (decode x) (rowWord x) (v x ρ) (q x ρ) j false)
      (candidate x.k (decode x) (rowWord x) (v x ρ) (q x ρ) j true) else 0)
  exact ifR (ltN (.var 0) (countF (upN hv))) (qry (candF false (upN hv) (upN hq) (.var 0))
    (candF true (upN hv) (upN hq) (.var 0))) (show RF (fun _ _=>0) from .const 0)
private lemma winF {v q : World→Env→ℕ} (hv : NF v) (hq : NF q) :
    BF (fun x ρ=>winner x (decode x) (liveRow x) (rowWord x) (v x ρ) (q x ρ)) :=by
  let cost:=fun (x : World) (v r : ℕ)=>weight x ((decode x).len v) (candidate x.k (decode x) (rowWord x) v r)
  apply andF (eligF hv hq)
  apply allF .rows (p:=fun x ρ r=>eligible (decode x) (liveRow x) (v x ρ) r → cost x (v x ρ) (q x ρ)< cost x (v x ρ) r ∨
    cost x (v x ρ) (q x ρ)=cost x (v x ρ) r ∧ q x ρ≤ r)
  have a:=priceF (upN hv) (upN hq);have b:=priceF (upN hv) (show NF (fun _ ρ=>ρ 0) from .var 0)
  exact impF (eligF (upN hv) (.var 0)) (orF (ltR a b) (andF (eqR a b) (leN (upN hq) (.var 0))))
private lemma bestF (s : Bool) {v j : World→Env→ℕ} (hv : NF v) (hj : NF j) :
    ZF (fun x ρ=>bestWord x (decode x) (liveRow x) (rowWord x) (v x ρ) (j x ρ) s) :=by
  apply ifZ (exF .rows (p:=fun x ρ q=>eligible (decode x) (liveRow x) (v x ρ) q) (eligF (upN hv) (.var 0))) _ (.const (-1))
  apply sumZ .rows (f:=fun x ρ q=>if winner x (decode x) (liveRow x) (rowWord x) (v x ρ) q then candidate x.k (decode x) (rowWord x) (v x ρ) q (j x ρ) s else 0)
  exact ifZ (winF (upN hv) (.var 0)) (candF s (upN hv) (.var 0) (upN hj)) (.const 0)
private lemma header (s : Bool) : BF (fun _ ρ=>ρ 0=0 ∧ ρ 1=0 ∧ s=true) :=by
  cases s
  · unfold BF;simp;exact .const 0
  · simpa only [and_true] using andF (eqN (.var 0) (.const 0)) (eqN (.var 1) (.const 0))
theorem solution : (∀w : Bool,Form (fun x ρ=>iv (seed x (ρ 0) (ρ 1) w))) ∧
    (∀w : Bool,Form (fun x ρ=>iv (advance x (ρ 0) (ρ 1) w))) ∧
    (∀w : Bool,Form (fun x ρ=>iv (project x (ρ 0) (ρ 1) w))) ∧ Form (fun x _=>iv (storedScenes x)) := by
  have r : NF (fun _ ρ=>ρ 0):=.var 0;have j : NF (fun _ ρ=>ρ 1):=.var 1
  have clk:=witF (.const 0) (.const 0);have v:=natF clk
  refine ⟨fun w=>ifZ (header w) (.const 0) (fld r j w),?_,?_,?_⟩
  · intro w;exact ifZ (header w) (addZ clk (.const 1)) (ifZ (andF (ltN v ns) (eqN r (plus (.const 1) v))) (bestF w v j) (fld r j w))
  · intro w;exact ifZ (ltN r ns) (fld (plus (.const 1) (natF (bandF 2 true r (.const 0)))) j w) (fld r j w)
  · exact centerF (predF (.size .rows)) (.const 0)
