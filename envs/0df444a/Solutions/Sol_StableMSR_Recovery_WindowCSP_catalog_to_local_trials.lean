-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.catalog_to_local_trials
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:11:19.44383+00:00
-- url     : https://prove2.me/submissions/39fdaf2e-bc43-4cc7-8a85-29410fc23fb6

import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
open StableMSR.Recovery.RegionalBallDP
open Polynomial
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
private lemma unaryForm (b : Bool) : Form (fun x ρ=>iv (unaryField x (ρ 0) (ρ 1) b)) := by
  have r : NF (fun _ e=>e 0):=.var 0
  have j : NF (fun _ e=>e 1):=.var 1
  have n : NF (fun x _=>originalRows x):=natF (readZ (.const 0))
  have m : NF (fun x _=>tableSlots x):=plus n (.const 1)
  have tw:=plus m m
  have th:=plus tw m
  have g := sumZ .rows (f:=fun x e i=>if i< originalRows x ∧ tableSlots x+(i+2)=e 0
    then field x i (e 1) b else 0)
    (ifZ (andF (ltN (.var 0) (upN n)) (eqN (plus (upN m) (plus (.var 0) (.const 2))) (upN r)))
      (fld (.var 0) (upN j) b) (.const 0))
  have q := sumZ .rows (f:=fun x e i=>if tableSlots x+tableSlots x+tableSlots x+i=e 0 then (i:ℤ) else 0)
    (ifZ (eqN (plus (upN th) (.var 0)) (upN r)) (.var 0) (.const 0))
  apply ifZ (eqN r (.const 0)) m
  apply ifZ (leN r tw) g
  apply ifZ (leN r th) (.size .blocks)
  cases b
  · exact .const 1
  · exact q
private def seqOps : List Op→Cmd
  | []=>.skip
  | o::os=>.seq (.atom o) (seqOps os)
private noncomputable def runOps {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op→Store
  | []=>s
  | o::os=>runOps d (o.eval d s) os
private lemma runs {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (os : List Op) :
    Executes d (seqOps os) s (runOps d s os) os.length := by
  induction os generalizing s with
  | nil => exact .skip _
  | cons o os ih => simpa [seqOps,runOps,Nat.add_comm] using Executes.seq (.atom o s) (ih (o.eval d s))
private def resize : List Op := [.pointerConst 3 0,.integerStore 3 2,.pointerInc 2,
  .pointerAdd 2 2 2,.pointerAdd 2 2 2,.pointerInc 2]
private lemma capacity (p : Polynomial ℕ) {i j : ℕ} (le : i≤ j) : p.eval i≤ p.eval j := by
  rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun k _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le k))
theorem solution :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0< x.k → Ready x s → endpoints x →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ p.eval x.cap ∧
      let y:=worldOf x.k (1+4*(x.rows+1)) x.dist t
      Ready y t ∧ RegionalBallDP.shape y ∧ ∀r< x.rows, good x r → ∀B : ℝ,score x r≤ B →
        Nonempty (RegionalBallDP.LocalTrial y (r+2) B) := by
  obtain ⟨p,tab,compile⟩:=tabulate_ball_row_expressions unaryField unaryForm
  refine ⟨C 6+p.comp (C 4*X+C 5),.seq (seqOps resize) tab,?_⟩
  intro x s hk ready ends
  let M:=x.rows+1
  let H:=1+4*M
  let u:=runOps x.dist s resize
  let mid:=worldOf x.k H x.dist u
  have p2 : s.ptrs 2=(x.rows:ℤ):=ready.1 .rows
  have rd : Ready mid u := by
    refine ⟨?_,fun _=>rfl⟩
    intro axis
    cases axis with
    | points => exact ready.1 .points
    | blocks => exact ready.1 .blocks
    | rows => change u.ptrs 2=(H:ℤ);simp [u,runOps,resize,Op.eval,Function.update,p2,H,M];ring
  have saved : originalRows mid=x.rows := by simp [originalRows,mid,worldOf,u,runOps,resize,Op.eval,Function.update,p2]
  have ms : tableSlots mid=M := congrArg (·+1) saved
  have old (r j : ℕ) (b : Bool) : field mid r j b=field x r j b := by
    have ne : ((addr x.k r j:ℕ):ℤ)≠0 := by dsimp [addr];omega
    have ne' : ((addr x.k r j+1:ℕ):ℤ)≠0 := by omega
    have atC:=ready.2 (addr x.k r j)
    have atW:=ready.2 (addr x.k r j+1)
    cases b
    · change u.imem ((addr x.k r j:ℕ):ℤ)=x.mem (addr x.k r j)
      have nz : addr x.k r j≠0:=by dsimp [addr];omega
      simpa [u,runOps,resize,Op.eval,Function.update,nz] using atC
    · change u.imem ((addr x.k r j+1:ℕ):ℤ)=x.mem (addr x.k r j+1)
      have nz : (addr x.k r j:ℤ)+1≠0:=by omega
      simpa [u,runOps,resize,Op.eval,Function.update,nz] using atW
  obtain ⟨t,z,ez,tz,rt,out⟩:=compile mid u rd
  let y:=worldOf x.k H x.dist t
  have outF (a : ℕ) (ha : a< H) (j : ℕ) (hj : j< x.k) (b : Bool) :
      field y a j b=unaryField mid a j b := by cases b
                                               · exact (out a ha j hj).1
                                               · exact (out a ha j hj).2
  have sm : slots y=M := by
    have e:=outF 0 (by dsimp [H];omega) 0 hk false
    unfold slots;change (field y 0 0 false).toNat=M;rw [e];simp [unaryField,ms]
  have pM : 0< M := by dsimp [M];omega
  have wh (v : ℕ) (vl : 1< v) (vh : v≤ M) : width y v=x.k := by
    have e:=outF (M+M+v) (by dsimp [H];omega) 0 hk false
    have eq : center y (M+M+v) 0=(x.k:ℤ) := by
      change field y (M+M+v) 0 false=(mid.k:ℤ)
      simpa only [unaryField,ms,show M+M+v≠0 by omega,if_false,
        show ¬ M+M+v≤ M+M by omega,show M+M+v≤ M+M+M by omega,if_true] using e
    simp only [width,show v≠1 by omega,if_false,sm,eq,Int.toNat_natCast];exact Nat.min_self _
  have endpointsQ (q : ℕ) (ql : 0< q) (qh : q≤ M) : parent y q=1 ∧ destination y q=(q:ℤ) := by
    let a:=M+M+M+q
    have ha : a< H := by dsimp [a,H];omega
    have far : ¬a≤ M+M+M := by dsimp [a];omega
    have farther : ¬a≤ M+M := by omega
    have zero : a≠0:=by omega
    have value (b : Bool) := outF a ha 0 hk b
    have eqP : center y a 0=1 := by
      change field y a 0 false=1
      simpa only [unaryField,ms,zero,if_false,far,farther,Bool.false_eq_true] using value false
    have eqD : witness y a 0=(q:ℤ) := by
      change field y a 0 true=_
      rw [value true]
      simp only [unaryField,ms,zero,if_false,far,farther,if_true]
      rw [Finset.sum_eq_single q]
      · simp [a]
      · intro u _ ne;exact if_neg (by dsimp [a];omega)
      · intro bad;exact False.elim (bad (Finset.mem_range.mpr (by change q< H;dsimp [H];omega)))
    constructor
    · unfold parent;rw [sm];change (center y a 0).toNat=1;rw [eqP];rfl
    · unfold destination;rw [sm];exact eqD
  have token (r : ℕ) (hr : r< x.rows) (j : ℕ) (hj : j< x.k) (b : Bool) :
      payload y (r+2) j b=field x r j b := by
    let a:=M+(r+2)
    have cap : r+2≤ M:=by dsimp [M];omega
    have e:=outF a (by dsimp [a,H];omega) j hj b
    have val : field y a j b=field x r j b := by
      rw [e];simp only [unaryField,ms,saved,show a≠0 by dsimp [a];omega,if_false,
        show a≤ M+M by dsimp [a];omega,if_true]
      rw [Finset.sum_eq_single r]
      · rw [if_pos ⟨hr,rfl⟩,old]
      · intro u _ une;exact if_neg (by dsimp [a];omega)
      · intro bad;exact False.elim (bad (Finset.mem_range.mpr (by change r< H;dsimp [H,M];omega)))
    obtain ⟨c,w,c0,w0⟩:=ends r hr j hj
    have range : 0≤ field x r j b ∧ field x r j b<(x.n:ℤ) := by
      cases b
      · change 0≤ center x r j ∧ center x r j<(x.n:ℤ);rw [c0];exact ⟨by omega,by exact_mod_cast c.isLt⟩
      · change 0≤ witness x r j ∧ witness x r j<(x.n:ℤ);rw [w0];exact ⟨by omega,by exact_mod_cast w.isLt⟩
    unfold payload;rw [sm];change legalize x.n (field y a j b)=_;rw [val];exact if_pos range
  refine ⟨t,_,.seq (runs _ _ _) ez,?_,rt,⟨sm ▸ pM,by change 4*slots y< H;rw [sm];dsimp [H];omega⟩,?_⟩
  · change 6+z≤_
    simp only [eval_add,eval_C,eval_comp,eval_mul,eval_X]
    apply Nat.add_le_add_left (tz.trans (capacity p _)) 6
    dsimp [mid,worldOf,World.cap,H,M];omega
  · intro r hr good' B le
    let v:=r+2
    have vt : vertex y v:=⟨by dsimp [v];omega,by rw [sm];dsimp [v,M];omega⟩
    have v1 : v≠1:=by dsimp [v];omega
    have vl : 1< v:=by omega
    have wd : width y v=x.k:=wh _ vl (sm ▸ vt.2)
    have rootW : width y 1=0:=if_pos rfl
    have desc (q : ℕ) (l : link y v q) : parent y q=1 ∧ q=v := by
      obtain ⟨qp,qd⟩:=endpointsQ q l.1.1 (sm ▸ l.1.2)
      exact ⟨qp,Int.ofNat_inj.mp (qd.symm.trans l.2.2.2.1)⟩
    have ep:=endpointsQ v vt.1 (sm ▸ vt.2)
    have linkV : link y v v :=
      ⟨vt,by rw [ep.1];exact ⟨by decide,by rw [sm];omega⟩,by rw [ep.1];exact vl,ep.2,by rw [ep.1,rootW];omega⟩
    have cost' : edgeCost y v v=score x r := by
      unfold edgeCost score;apply Finset.sum_congr rfl;intro j jh
      have jlt : j< x.k:=Finset.mem_range.mp jh
      rw [ep.1,rootW,wd,if_pos ⟨by omega,jlt⟩,token r hr j jlt false,token r hr j jlt true];rfl
    refine ⟨{
      region := fun t _=>t=v
      tracked := fun t=>t=1 ∨ t=v
      viable := fun t=>t=1 ∨ t=v
      budget := fun t=>if t=v then score x r else 0
      terminal := vt
      fullWidth := wd
      trackedEnd := Or.inr rfl
      viableEnd := Or.inr rfl
      fullRegion := fun _ _=>rfl
      emptyRoot := fun _ _=>Ne.symm v1
      rootBudget := by simp [Ne.symm v1]
      terminalBudget := by simpa [v] using le
      owned := ?_
      extendBudget := ?_ }⟩
    · intro t ht tracking q lk
      rcases tracking with rfl|rfl
      · have pos:=lk.2.1.1;have lt:=lk.2.2.1;omega
      · obtain ⟨par,rfl⟩:=desc q lk
        rw [par,rootW,wd]
        refine ⟨Or.inl rfl,fun _ _=>rfl,fun _ _ _=>⟨rfl,Ne.symm v1⟩,?_,?_⟩
        · intro j _ hj l _ hl eq;rw [token r hr j hj false,token r hr l hl false] at eq
          exact good'.1 j hj l hl eq
        · intro i hi _ _
          obtain ⟨j,hj,hit⟩:=good'.2 i hi
          refine ⟨j,by omega,hj,?_⟩
          unfold containsPoint;rw [token r hr j hj false,token r hr j hj true];exact hit
    · intro t _ via ne
      rcases via with eq|rfl
      · contradiction
      · exact ⟨v,linkV,Or.inl ep.1,by change (if parent y v=v then score x r else 0)+edgeCost y v v≤(if v=v then score x r else 0);simp [ep.1,Ne.symm v1,cost']⟩

