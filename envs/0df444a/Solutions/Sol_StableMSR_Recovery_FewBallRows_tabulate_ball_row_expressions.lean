-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.tabulate_ball_row_expressions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:35:15.49399+00:00
-- url     : https://prove2.me/submissions/c147c5d8-922e-4990-9d2c-d41cd708efb4

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Theorems.Thm_StableMSR_Recovery_OracleQueries_bounded_oracle_expression_compiler
import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open Polynomial
private def ops : List Op → Cmd
  | [] => .skip
  | a::l => .seq (.atom a) (ops l)
private noncomputable def afterOps {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op → Store
  | [] => s
  | a::l => afterOps d (a.eval d s) l
private lemma steps {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (l : List Op) :
    Executes d (ops l) s (afterOps d s l) l.length := by
  induction l generalizing s with
  | nil => exact .skip _
  | cons a l ih => simpa only [ops,afterOps,List.length_cons,Nat.add_comm 1] using
      (Executes.seq (.atom a s) (ih (a.eval d s)))
private def Frame (x : World) (s : Store) := Ready x s ∧ s.ptrs 6=(x.rows:ℤ)-1 ∧
  s.ptrs 7=(x.k:ℤ)-1 ∧ s.ptrs 8=0
private def prefixOK (v : ℕ→ℤ) (a : ℕ) (s : Store) := ∀u,3≤u → u<a → s.imem (-(u:ℤ))=v u
private def emitOps : List Op := [.pointerSub 9 8 5,.integerStore 9 10,.pointerInc 5]
private lemma outputOne (g : World→ℕ→ℕ→ℤ)
    (h : Form (fun x e=>iv (g x (e 0) (e 1)))) :
    ∃p : Polynomial ℕ,∃emit : Cmd,∀(x : World) (s : Store) (r j a : ℕ) (v : ℕ→ℤ),
      Frame x s → s.ptrs 3=(r:ℤ) → s.ptrs 4=(j:ℤ) → s.ptrs 5=(a:ℤ) → 3≤a →
      prefixOK v a s → g x r j=v a →
      ∃t z,Executes x.dist emit s t z ∧ z≤p.eval x.cap+3 ∧
        Frame x t ∧ t.ptrs 3=(r:ℤ) ∧ t.ptrs 4=(j:ℤ) ∧ t.ptrs 5=((a+1:ℕ):ℤ) ∧ prefixOK v (a+1) t := by
  obtain ⟨p,engine⟩ := bounded_oracle_expression_compiler _ h
  let src (i : ℕ) := if i=0 then 3 else 4
  obtain ⟨eval,run⟩ := engine 10 src (by decide) (fun i=>by dsimp [src];split <;> decide)
  refine ⟨p,.seq eval (ops emitOps),?_⟩
  intro x s r j a v fr pr pj pa ha pre correct
  let env (i : ℕ) := if i=0 then r else j
  obtain ⟨u,z,ez,keep,hv,tz⟩ := run x s env fr.1
    (fun i=>by by_cases eq : i=0 <;> simp [src,env,eq,pr,pj])
  have F : u.ptrs 10=v a := (congrArg Prod.fst hv).trans (by simpa [env,iv] using correct)
  have P (i : ℕ) (hi : i<10) := (keep.1 i hi).1
  have u3 := (P 3 (by decide)).trans pr
  have u4 := (P 4 (by decide)).trans pj
  have u5 := (P 5 (by decide)).trans pa
  have u8 := (P 8 (by decide)).trans fr.2.2.2
  let t := afterOps x.dist u emitOps
  have mem (b : ℤ) : t.imem b=if b= -(a:ℤ) then v a else s.imem b := by
    simp [t,emitOps,afterOps,Op.eval,Function.update,u5,u8,F,keep.2,eq_comm]
  refine ⟨t,_,Executes.seq ez (steps _ _ _),by change z+3≤_;omega,⟨⟨?_,?_⟩,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro ax; have k := (P ax.reg (by cases ax <;> decide)).trans (fr.1.1 ax)
    cases ax <;> simpa [t,emitOps,afterOps,Op.eval,Function.update,Axis.reg] using k
  · intro i;rw [mem,if_neg (by omega)];exact fr.1.2 i
  · exact (P 6 (by decide)).trans fr.2.1
  · exact (P 7 (by decide)).trans fr.2.2.1
  · exact u8
  · exact u3
  · exact u4
  · simp [t,emitOps,afterOps,Op.eval,Function.update,u5]
  · intro i lo hi;rw [mem]
    by_cases eq : i=a
    · simp [eq]
    · rw [if_neg (by omega)];exact pre i lo (by omega)
private def setup : List Op := [.pointerConst 3 0,.pointerConst 5 3,.pointerCopy 6 2,.pointerDec 6,
  .pointerCopy 7 1,.pointerDec 7,.pointerConst 8 0]
private def copyInit : List Op := [.pointerCopy 6 5,.pointerDec 6,.pointerConst 3 3,.pointerConst 8 0]
private def copyOps : List Op := [.pointerSub 9 8 3,.integerLoad 10 9,.integerStore 3 10,.pointerInc 3]
private def copyTable := Cmd.seq (ops copyInit) (.whileDo (.pointerLE 3 6) (ops copyOps))
private lemma copyAll (x : World) (s : Store) (N : ℕ) (v : ℕ→ℤ)
    (dims : ∀a : Axis,s.ptrs a.reg=(x.size a:ℤ)) (pa : s.ptrs 5=((3+N:ℕ):ℤ)) (pre : prefixOK v (3+N) s) :
    ∃t z,Executes x.dist copyTable s t z ∧ z ≤ 6*N+6 ∧
      (∀a : Axis,t.ptrs a.reg=(x.size a:ℤ)) ∧ ∀u,3≤u → u<3+N → t.imem (u:ℤ)=v u := by
  let t₀ := afterOps x.dist s copyInit
  let A (i : ℕ) (t : Store) := (∀a : Axis,t.ptrs a.reg=(x.size a:ℤ)) ∧
    t.ptrs 3=((3+i:ℕ):ℤ) ∧ t.ptrs 6=((3+N:ℕ):ℤ)-1 ∧ t.ptrs 8=0 ∧ prefixOK v (3+N) t ∧
    ∀u,3≤u → u<3+i → t.imem (u:ℤ)=v u
  have start : A 0 t₀ := by
    refine ⟨?_,?_,?_,?_,pre,by omega⟩
    · intro ax;have h := dims ax;cases ax <;> simpa [t₀,afterOps,copyInit,Op.eval,Function.update,Axis.reg] using h
    all_goals simp [t₀,afterOps,copyInit,Op.eval,Function.update,pa]
  have loop : BoundedSum.LoopBound x.dist (ops copyOps) (.pointerLE 3 6) A N 4 := by
    constructor
    · intro i t at';change t.ptrs 3≤t.ptrs 6 ↔ _;rw [at'.2.1,at'.2.2.1];omega
    · intro i hi t at'
      obtain ⟨dim,p3,p6,p8,old,prev⟩ := at'
      let u := afterOps x.dist t copyOps
      have vl := old (3+i) (by omega) (by omega)
      have mem (b : ℤ) : u.imem b=if b=((3+i:ℕ):ℤ) then v (3+i) else t.imem b := by
        have vl' : t.imem (-(i:ℤ)+ -3)=v (3+i) := by convert vl using 2 <;> push_cast <;> ring
        simp [u,afterOps,copyOps,Op.eval,Function.update,p3,p8,eq_comm,vl']
      refine ⟨u,4,steps _ _ _,by decide,?_,?_,p6,p8,?_,?_⟩
      · intro ax;have h := dim ax;cases ax <;> simpa [u,afterOps,copyOps,Op.eval,Function.update,Axis.reg] using h
      · simp [u,afterOps,copyOps,Op.eval,Function.update,p3];ring
      · intro a ha lt;rw [mem,if_neg (by omega)];exact old a ha lt
      · intro a ha lt;rw [mem];by_cases eq : a=3+i
        · simp [eq]
        · rw [if_neg (by omega)];exact prev a ha (by omega)
  obtain ⟨u,z,ez,tz,av⟩ := BoundedSum.bounded_while_execution _ _ _ A N _ loop 0 (by omega) t₀ start
  exact ⟨u,_,Executes.seq (steps _ _ _) ez,by change 4+z≤_;simp at tz;omega,av.1,av.2.2.2.2.2⟩
theorem solution (f : World→ℕ→ℕ→Bool→ℤ)
    (hf : ∀w : Bool,Form (fun x ρ=>iv (f x (ρ 0) (ρ 1) w))) :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store), Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval x.cap ∧
      let y := worldOf x.k x.rows x.dist t
      Ready y t ∧ ∀r < x.rows,∀j < x.k,center y r j=f x r j false ∧ witness y r j=f x r j true := by
  obtain ⟨p,ce,hc⟩ := outputOne (fun x r j=>f x r j false) (hf false)
  obtain ⟨q,we,hw⟩ := outputOne (fun x r j=>f x r j true) (hf true)
  let cols := Cmd.seq ce (.seq we (.atom (.pointerInc 4)))
  let row := Cmd.seq (.atom (.pointerConst 4 0)) (.seq (.whileDo (.pointerLE 4 7) cols) (.atom (.pointerInc 3)))
  refine ⟨(X+1)^2*(p+q+C 50)+C 60,.seq (ops setup) (.seq (.whileDo (.pointerLE 3 6) row) copyTable),?_⟩
  intro x s ready
  let v (a : ℕ) := f x ((a-3)/2/x.k) ((a-3)/2%x.k) (decide ((a-3)%2=1))
  have field (r j : ℕ) (hj : j<x.k) :
      v (addr x.k r j)=f x r j false ∧ v (addr x.k r j+1)=f x r j true := by
    have c1 : addr x.k r j-3=2*(r*x.k+j) := by unfold addr;omega
    have c2 : addr x.k r j+1-3=2*(r*x.k+j)+1 := by unfold addr;omega
    have div : (r*x.k+j)/x.k=r := by
      rw [Nat.mul_comm r x.k,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hj,Nat.add_zero]
    have mod : (r*x.k+j)%x.k=j := Nat.mul_add_mod_of_lt hj
    have evenDiv : (2*(r*x.k+j))/2=r*x.k+j := by omega
    have oddDiv : (2*(r*x.k+j)+1)/2=r*x.k+j := by omega
    have evenMod : (2*(r*x.k+j))%2=0 := by omega
    have oddMod : (2*(r*x.k+j)+1)%2=1 := by omega
    simp [v,c1,c2,evenDiv,oddDiv,evenMod,oddMod,div,mod]
  let t₀ := afterOps x.dist s setup
  let A (r : ℕ) (t : Store) := Frame x t ∧ t.ptrs 3=(r:ℤ) ∧ t.ptrs 5=((addr x.k r 0:ℕ):ℤ) ∧
    prefixOK v (addr x.k r 0) t
  have st : A 0 t₀ := by
    refine ⟨⟨⟨?_,ready.2⟩,?_,?_,?_⟩,?_,?_,?_⟩
    · intro ax;have h:=ready.1 ax;cases ax <;> simpa [t₀,setup,afterOps,Op.eval,Function.update,Axis.reg] using h
    · have h := ready.1 Axis.rows;simpa [t₀,setup,afterOps,Op.eval,Function.update,Axis.reg,World.size] using congrArg (fun a : ℤ=>a-1) h
    · have h := ready.1 Axis.blocks;simpa [t₀,setup,afterOps,Op.eval,Function.update,Axis.reg,World.size] using congrArg (fun a : ℤ=>a-1) h
    · simp [t₀,setup,afterOps,Op.eval]
    · simp [t₀,setup,afterOps,Op.eval,Function.update]
    · simp [t₀,setup,afterOps,Op.eval,Function.update,addr]
    · intro a ha lt;simp [addr] at lt;omega
  let Cst := p.eval x.cap+q.eval x.cap+9
  have outer : BoundedSum.LoopBound x.dist row (.pointerLE 3 6) A x.rows (x.k*Cst+4) := by
    constructor
    · intro r t av;change t.ptrs 3≤t.ptrs 6 ↔ _;rw [av.2.1,av.1.2.1];omega
    · intro r hr u au
      obtain ⟨fr,pr,pa,pre⟩ := au
      let B (j : ℕ) (t : Store) := Frame x t ∧ t.ptrs 3=(r:ℤ) ∧ t.ptrs 4=(j:ℤ) ∧
        t.ptrs 5=((addr x.k r j:ℕ):ℤ) ∧ prefixOK v (addr x.k r j) t
      let s₁ := (Op.pointerConst 4 0).eval x.dist u
      have frameUpdate (t : Store) (ff : Frame x t) (i : ℕ) (op : Op)
          (pres : ∀j < 3,(op.eval x.dist t).ptrs j=t.ptrs j)
          (p6 : (op.eval x.dist t).ptrs 6=t.ptrs 6) (p7 : (op.eval x.dist t).ptrs 7=t.ptrs 7)
          (p8 : (op.eval x.dist t).ptrs 8=t.ptrs 8) (mem : (op.eval x.dist t).imem=t.imem) :
          Frame x (op.eval x.dist t) :=
        ⟨⟨fun a=>(pres a.reg (by cases a <;> decide)).trans (ff.1.1 a),fun j=>by rw [mem];exact ff.1.2 j⟩,
          p6.trans ff.2.1,p7.trans ff.2.2.1,p8.trans ff.2.2.2⟩
      have frame4 (t : Store) (ff : Frame x t) : Frame x ((Op.pointerInc 4).eval x.dist t) := by
        apply frameUpdate t ff 4 <;> try rfl
        intro j hj;simp [Op.eval,Function.update_of_ne (by omega : j≠4)]
      have frame3 (t : Store) (ff : Frame x t) : Frame x ((Op.pointerInc 3).eval x.dist t) := by
        apply frameUpdate t ff 3 <;> try rfl
        intro j hj;simp [Op.eval,Function.update_of_ne (by omega : j≠3)]
      have stB : B 0 s₁ := by
        refine ⟨?_,pr,?_,pa,pre⟩
        · apply frameUpdate u fr 4 <;> try rfl
          intro j hj;simp [Op.eval,Function.update_of_ne (by omega : j≠4)]
        · simp [s₁,Op.eval]
      have inner : BoundedSum.LoopBound x.dist cols (.pointerLE 4 7) B x.k (p.eval x.cap+q.eval x.cap+7) := by
        constructor
        · intro j t bt;change t.ptrs 4≤t.ptrs 7 ↔ _;rw [bt.2.2.1,bt.1.2.2.1];omega
        · intro j hj t bt
          obtain ⟨ff,p3,p4,p5,safe⟩ := bt
          obtain ⟨t₁,z₁,e₁,tz₁,ff₁,r₁,j₁,a₁,save₁⟩ := hc x t r j _ v ff p3 p4 p5
            (by simp [addr]) safe (field r j hj).1.symm
          obtain ⟨t₂,z₂,e₂,tz₂,ff₂,r₂,j₂,a₂,save₂⟩ := hw x t₁ r j _ v ff₁ r₁ j₁ a₁
            (by dsimp [addr];omega) save₁ (field r j hj).2.symm
          let s₂ := (Op.pointerInc 4).eval x.dist t₂
          have nxt : addr x.k r (j+1)=addr x.k r j+1+1 := by dsimp [addr];ring
          refine ⟨s₂,_,Executes.seq e₁ (.seq e₂ (.atom _ _)),by omega,frame4 t₂ ff₂,r₂,?_,?_,?_⟩
          · simp [s₂,Op.eval,j₂]
          · rw [nxt];exact a₂
          · rw [nxt];exact save₂
      obtain ⟨s₂,z,ez,tz,last⟩ := BoundedSum.bounded_while_execution _ _ _ B x.k _ inner 0 (by omega) s₁ stB
      let s₃ := (Op.pointerInc 3).eval x.dist s₂
      have nxt : addr x.k (r+1) 0=addr x.k r x.k := by unfold addr;ring
      refine ⟨s₃,_,Executes.seq (.atom _ _) (.seq ez (.atom _ _)),?_,frame3 s₂ last.1,?_,?_,?_⟩
      · change 1+(z+1)≤_;change z≤(x.k-0)*(p.eval x.cap+q.eval x.cap+7+2)+2 at tz
        simp only [Nat.sub_zero] at tz
        simpa [Cst,Nat.add_assoc] using (by omega : 1+(z+1)≤x.k*(p.eval x.cap+q.eval x.cap+7+2)+4)
      · simp [s₃,Op.eval,last.2.1]
      · rw [nxt];exact last.2.2.2.1
      · rw [nxt];exact last.2.2.2.2
  obtain ⟨u,z,ez,tz,last⟩ := BoundedSum.bounded_while_execution _ _ _ A x.rows _ outer 0 (by omega) t₀ st
  have lim : addr x.k x.rows 0=3+2*(x.rows*x.k) := by simp [addr]
  obtain ⟨t,z',ez',tz',rd,data⟩ := copyAll x u (2*(x.rows*x.k)) v last.1.1.1 (lim ▸ last.2.2.1) (lim ▸ last.2.2.2)
  refine ⟨t,_,Executes.seq (steps _ _ _) (.seq ez ez'),?_,⟨rd,fun _=>rfl⟩,?_⟩
  · change 7+(z+z')≤_
    simp only [Nat.sub_zero] at tz
    simp only [eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_C]
    have hn : x.k ≤ x.cap+1 := by unfold World.cap;omega
    have hm : x.rows ≤ x.cap+1 := by unfold World.cap;omega
    have hprod := Nat.mul_le_mul hm hn
    have first := Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.mul_le_mul_right Cst hn) 6)
    have tzN : z≤x.rows*(x.k*Cst+6)+2 := by simpa only [Nat.add_assoc] using tz
    have zz := tzN.trans (Nat.add_le_add_right first 2)
    dsimp [Cst] at zz
    nlinarith [Nat.zero_le (x.cap^2)]
  · intro r hr j hj
    have hmul := Nat.mul_le_mul_right x.k (show r+1≤x.rows by omega)
    rw [Nat.succ_mul] at hmul
    have low : 3≤addr x.k r j := by simp [addr]
    have hi : addr x.k r j+1<3+2*(x.rows*x.k) := by dsimp [addr];omega
    exact ⟨(data _ low (by omega)).trans (field r j hj).1,(data _ (by omega) hi).trans (field r j hj).2⟩
