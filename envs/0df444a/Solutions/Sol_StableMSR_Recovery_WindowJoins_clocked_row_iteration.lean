-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.clocked_row_iteration
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:48:54.186555+00:00
-- url     : https://prove2.me/submissions/7df17b5c-a1f5-4ee9-8115-8a649cdfe04a

import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
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
open StableMSR.Recovery.FewBallRows (tabulate_ball_row_expressions)
open Polynomial
private def setupClock := Cmd.seq (.atom (.pointerConst 3 4)) (.seq (.atom (.integerLoad 3 3))
  (.seq (.atom (.pointerCopy 4 2)) (.atom (.pointerDec 4))))
private lemma clock (x : World) (s : Store) (rd : Ready x s) :
    ∃t,Executes x.dist setupClock s t 4 ∧ Ready x t ∧
      t.ptrs 3=witness x 0 0 ∧ t.ptrs 4=(x.rows:ℤ)-1 := by
  let t := (Op.pointerDec 4).eval x.dist ((Op.pointerCopy 4 2).eval x.dist
    ((Op.integerLoad 3 3).eval x.dist ((Op.pointerConst 3 4).eval x.dist s)))
  refine ⟨t,.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),⟨?_,rd.2⟩,?_,?_⟩
  · intro ax;have h:=rd.1 ax;cases ax <;> simpa [t,Op.eval,Function.update,Axis.reg] using h
  · have h:=rd.2 4;simpa [t,Op.eval,Function.update,witness,addr] using h
  · have h:=rd.1 Axis.rows;simpa [t,Op.eval,Function.update,Axis.reg,World.size] using congrArg (fun a : ℤ=>a-1) h
private lemma written {x y : World} {f : World→ℕ→ℕ→Bool→ℤ}
    (h : ∀r< x.rows,∀j< x.k,center y r j=f x r j false ∧ witness y r j=f x r j true) :
    Writes x y f := by
  intro r hr j hj w;cases w
  · exact (h r hr j hj).1
  · exact (h r hr j hj).2
theorem solution (f g h : World→ℕ→ℕ→Bool→ℤ)
    (F : ∀w : Bool,Form (fun x ρ=>iv (f x (ρ 0) (ρ 1) w)))
    (G : ∀w : Bool,Form (fun x ρ=>iv (g x (ρ 0) (ρ 1) w)))
    (J : ∀w : Bool,Form (fun x ρ=>iv (h x (ρ 0) (ρ 1) w)))
    (start : ∀x,f x 0 0 true=0) (next : ∀x,g x 0 0 true=witness x 0 0+1) :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0< x.k → 0< x.rows → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ p.eval x.cap ∧
      let y:=worldOf x.k x.rows x.dist t
      Ready y t ∧ ∃a : ℕ→Mem,Writes x (replace x (a 0)) f ∧
        (∀i< x.rows,Writes (replace x (a i)) (replace x (a (i+1))) g) ∧
        Writes (replace x (a x.rows)) y h := by
  obtain ⟨p,init,runInit⟩ := tabulate_ball_row_expressions f F
  obtain ⟨q,step,runStep⟩ := tabulate_ball_row_expressions g G
  obtain ⟨u,post,runPost⟩ := tabulate_ball_row_expressions h J
  let body:=Cmd.seq step setupClock
  refine ⟨p+X*(q+C 6)+u+C 6,.seq init (.seq setupClock (.seq (.whileDo (.pointerLE 3 4) body) post)),?_⟩
  intro x s hk hH rd
  obtain ⟨s₀,z₀,e₀,t₀,rd₀,write₀⟩ := runInit x s rd
  let mem (t : Store) := fun j : ℕ=>t.imem (j:ℤ)
  let V (m : ℕ→ℤ) := replace x m
  have w₀ : Writes x (V (mem s₀)) f := written write₀
  have zer : witness (V (mem s₀)) 0 0=0 := by simpa [field,start] using w₀ 0 hH 0 hk true
  obtain ⟨s₁,e₁,rd₁,cc₁,lim₁⟩ := clock (V (mem s₀)) s₀ rd₀
  let A (i : ℕ) (s : Store) := s.ptrs 3=(i:ℤ) ∧ s.ptrs 4=(x.rows:ℤ)-1 ∧
    ∃hist : ℕ→ℕ→ℤ,Writes x (V (hist 0)) f ∧
      (∀j < i,Writes (V (hist j)) (V (hist (j+1))) g) ∧
      Ready (V (hist i)) s ∧ witness (V (hist i)) 0 0=(i:ℤ)
  have start : A 0 s₁ := ⟨cc₁.trans zer,lim₁,fun _=>mem s₀,w₀,by omega,rd₁,zer⟩
  have loop : BoundedSum.LoopBound x.dist body (.pointerLE 3 4) A x.rows (q.eval x.cap+4) := by
    constructor
    · intro i t a;change t.ptrs 3≤ t.ptrs 4 ↔ _;rw [a.1,a.2.1];omega
    · intro i hi t a
      obtain ⟨_,_,h,initOK,prev,ready,ck⟩:=a
      obtain ⟨s₂,z,ez,tz,rd₂,out₂⟩ := runStep (V (h i)) t ready
      have upd : Writes (V (h i)) (V (mem s₂)) g := written out₂
      have next : witness (V (mem s₂)) 0 0=((i+1:ℕ):ℤ) := by
        have he:=upd 0 hH 0 hk true
        simpa [field,next,ck] using he
      obtain ⟨s₃,e₃,rd₃,cc₃,lim₃⟩ := clock (V (mem s₂)) s₂ rd₂
      let h' := Function.update h (i+1) (mem s₂)
      have before (j : ℕ) (hj : j ≤ i) : h' j=h j := Function.update_of_ne (by omega) _ _ 
      have now : h' (i+1)=mem s₂ := Function.update_self ..
      refine ⟨s₃,_,.seq ez e₃,Nat.add_le_add_right tz 4,cc₃.trans next,lim₃,h',?_,?_,?_,?_⟩
      · rwa [before 0 (by omega)]
      · intro j hj
        by_cases eq : j=i
        · subst j;rwa [before i (by omega),now]
        · rw [before j (by omega),before (j+1) (by omega)];exact prev j (by omega)
      · rwa [now]
      · rwa [now]
  obtain ⟨s₂,z₂,e₂,t₂,last⟩:=BoundedSum.bounded_while_execution _ _ _ A x.rows _ loop 0 (by omega) s₁ start
  obtain ⟨_,_,h,h₀,hp,rd₂,_⟩:=last
  obtain ⟨t,z,ez,tz,rdt,out⟩:=runPost (V (h x.rows)) s₂ rd₂
  refine ⟨t,_,.seq e₀ (.seq e₁ (.seq e₂ ez)),?_,rdt,h,h₀,hp,written out⟩
  · simp only [eval_add,eval_mul,eval_X,eval_C]
    change z≤ u.eval x.cap at tz
    simp only [Nat.sub_zero] at t₂
    change z₂≤ x.rows*(q.eval x.cap+6)+2 at t₂
    have hx : x.rows≤ x.cap := by unfold World.cap;omega
    have hq:=Nat.mul_le_mul_right (q.eval x.cap+6) hx
    omega

