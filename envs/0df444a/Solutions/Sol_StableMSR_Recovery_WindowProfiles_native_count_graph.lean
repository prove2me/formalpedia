-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.native_count_graph
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:13:43.6338+00:00
-- url     : https://prove2.me/submissions/fcd09612-e507-4803-a323-b5d659711847

import Theorems.Thm_StableMSR_Recovery_WindowProfiles_rectangular_transition_expressions
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_rectangular_count_graph
import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
import Theorems.Thm_StableMSR_Recovery_OracleQueries_bounded_oracle_expression_compiler
import Definitions.Def_StableMSR_WindowProfilePacking
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

open Polynomial
private noncomputable def boundPoly : Polynomial ℕ := X+C 4*(1+X^4)+1
private lemma capUp (x : World) (m : Mem) : (arena x m).cap≤ boundPoly.eval x.cap:=by
  have ns : x.n≤ x.cap:=by dsimp [World.cap];omega
  have rs : x.rows≤ x.cap:=by dsimp [World.cap];omega
  have prod:=Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul rs ns) ns) ns
  have plus : x.n+x.k+1≤ x.cap:=by dsimp [World.cap];omega
  change x.n+x.k+height x+1≤_
  simp only [boundPoly,eval_add,eval_mul,eval_one,eval_X,eval_C,eval_pow]
  rw [show x.cap^4=x.cap*x.cap*x.cap*x.cap by ring]
  unfold height capacity;omega
private lemma monoEval (p : Polynomial ℕ) {i j : ℕ} (h : i≤ j) : p.eval i≤ p.eval j:=by
  rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun k _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k))
theorem solution : ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),1≤ x.k → x.k< x.n → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ p.eval x.cap ∧ Ready (arena x (fun j=>t.imem (j:ℤ))) t ∧
      Grid x (fun j=>t.imem (j:ℤ)) := by
  obtain ⟨h,F⟩:=rectangular_transition_expressions
  obtain ⟨A,engine⟩:=bounded_oracle_expression_compiler _ h
  obtain ⟨init,run⟩:=engine 3 (fun _=>0) (by decide) (fun _=>by decide)
  obtain ⟨B,tab,fill⟩:=FewBallRows.tabulate_ball_row_expressions packed F
  let midCmd:=Cmd.seq (.atom (.pointerConst 4 0)) (.seq (.atom (.integerStore 4 2)) (.atom (.pointerCopy 2 3)))
  refine ⟨A+C 3+B.comp boundPoly,init.seq (midCmd.seq tab),?_⟩
  intro x s hk kn ready
  obtain ⟨a,l,ea,keep,value,bound⟩:=run x s (fun _=>x.n) ready (fun _=>ready.1 .points)
  let H:=height x
  let y : World:={x with rows:=H,mem:=Function.update x.mem 0 (x.rows:ℤ)}
  let v:=(Op.pointerCopy 2 3).eval x.dist ((Op.integerStore 4 2).eval x.dist ((Op.pointerConst 4 0).eval x.dist a))
  have ex : Executes x.dist midCmd a v 3:=.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))
  have old (i : ℕ) : a.imem (i:ℤ)=x.mem i:=(congrFun keep.2 _).trans (ready.2 i)
  have p0 : a.ptrs 0=(x.n:ℤ):=(keep.1 _ (by decide)).1.trans (ready.1 .points)
  have p1 : a.ptrs 1=(x.k:ℤ):=(keep.1 _ (by decide)).1.trans (ready.1 .blocks)
  have p2 : a.ptrs 2=(x.rows:ℤ):=(keep.1 _ (by decide)).1.trans (ready.1 .rows)
  have p3 : a.ptrs 3=(H:ℤ):=congrArg Prod.fst value
  have rd : Ready y v:=by
    constructor
    · intro ax;cases ax <;> simp [v,Op.eval,Function.update,y,World.size,Axis.reg,p0,p1,p2,p3,H]
    · intro j;by_cases jz : j=0
      · subst j;simp [v,Op.eval,y,p2]
      · have nz : (j:ℤ)≠0:=by exact_mod_cast jz
        simpa [v,Op.eval,Function.update_of_ne jz,Function.update_of_ne nz,y] using old j
  obtain ⟨t,z,ez,zt,rt,out⟩:=fill y v rd
  let g : Mem:=fun j=>t.imem (j:ℤ)
  refine ⟨t,_,.seq ea (.seq ex ez),?_,rt,rectangular_count_graph x hk kn g ?_⟩
  · simp only [eval_add,eval_C,eval_comp]
    have up:=monoEval B (capUp x x.mem)
    change z≤ B.eval ((arena x x.mem).cap) at zt;omega
  · intro r hr j hj w;cases w
    · exact (out r hr j hj).1
    · exact (out r hr j hj).2

