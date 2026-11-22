-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.regional_table_machine
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:14:41.713353+00:00
-- url     : https://prove2.me/submissions/05bbb785-f014-4e1a-b26a-b3f5fb62f8ae

import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_ball_transition_expressions
import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
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
    (h : ∀r<x.rows,∀j<x.k,center y r j=f x r j false ∧ witness y r j=f x r j true) :
    Writes x y f := by
  intro r hr j hj w;cases w
  · exact (h r hr j hj).1
  · exact (h r hr j hj).2
theorem solution :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0<x.k → 0<x.rows → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤p.eval x.cap ∧
      let y:=worldOf x.k x.rows x.dist t
      Ready y t ∧ ∃h : ℕ→ℕ→ℤ,
        Writes x (withMem x (h 0)) seedTable ∧
        (∀i<x.rows,Writes (withMem x (h i)) (withMem x (h (i+1))) tick) ∧
        Writes (withMem x (h x.rows)) y clean := by
  obtain ⟨hi,ht,hc⟩ := ball_transition_expressions
  obtain ⟨p,init,runInit⟩ := tabulate_ball_row_expressions seedTable hi
  obtain ⟨q,step,runStep⟩ := tabulate_ball_row_expressions tick ht
  obtain ⟨u,post,runPost⟩ := tabulate_ball_row_expressions clean hc
  let body:=Cmd.seq step setupClock
  refine ⟨p+X*(q+C 6)+u+C 6,.seq init (.seq setupClock (.seq (.whileDo (.pointerLE 3 4) body) post)),?_⟩
  intro x s hk hH rd
  obtain ⟨s₀,z₀,e₀,t₀,rd₀,write₀⟩ := runInit x s rd
  let mem (t : Store) := fun j : ℕ=>t.imem (j:ℤ)
  let V (m : ℕ→ℤ) := withMem x m
  have w₀ : Writes x (V (mem s₀)) seedTable := written write₀
  have zer : witness (V (mem s₀)) 0 0=0 := by simpa [field,seedTable] using w₀ 0 hH 0 hk true
  obtain ⟨s₁,e₁,rd₁,cc₁,lim₁⟩ := clock (V (mem s₀)) s₀ rd₀
  let A (i : ℕ) (s : Store) := s.ptrs 3=(i:ℤ) ∧ s.ptrs 4=(x.rows:ℤ)-1 ∧
    ∃h : ℕ→ℕ→ℤ,Writes x (V (h 0)) seedTable ∧
      (∀j < i,Writes (V (h j)) (V (h (j+1))) tick) ∧
      Ready (V (h i)) s ∧ witness (V (h i)) 0 0=(i:ℤ)
  have start : A 0 s₁ := ⟨cc₁.trans zer,lim₁,fun _=>mem s₀,w₀,by omega,rd₁,zer⟩
  have loop : BoundedSum.LoopBound x.dist body (.pointerLE 3 4) A x.rows (q.eval x.cap+4) := by
    constructor
    · intro i t a;change t.ptrs 3≤t.ptrs 4 ↔ _;rw [a.1,a.2.1];omega
    · intro i hi t a
      obtain ⟨_,_,h,initOK,prev,ready,ck⟩:=a
      obtain ⟨s₂,z,ez,tz,rd₂,out₂⟩ := runStep (V (h i)) t ready
      have upd : Writes (V (h i)) (V (mem s₂)) tick := written out₂
      have next : witness (V (mem s₂)) 0 0=((i+1:ℕ):ℤ) := by
        have he:=upd 0 hH 0 hk true
        simpa [field,tick,ck] using he
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
    change z≤u.eval x.cap at tz
    simp only [Nat.sub_zero] at t₂
    change z₂≤x.rows*(q.eval x.cap+6)+2 at t₂
    have hx : x.rows≤x.cap := by unfold World.cap;omega
    have hq:=Nat.mul_le_mul_right (q.eval x.cap+6) hx
    omega

