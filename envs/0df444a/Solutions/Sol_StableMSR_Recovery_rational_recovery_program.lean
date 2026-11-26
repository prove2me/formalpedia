-- Prove2me | solution 1 for StableMSR.Recovery.rational_recovery_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:29:39.452753+00:00
-- url     : https://prove2.me/submissions/eabd27a5-d2f7-407b-8bc8-0847e076c8d9

import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_uniform_ball_cover_catalog
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_selector_expression
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_cheapest_cover_recovers
import Theorems.Thm_StableMSR_Recovery_OracleQueries_point_output_loop
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
private lemma capPoly (p : Polynomial ℕ) :
    ∃c D : ℕ,∀m : ℕ,1 ≤ m → p.eval m ≤ c*m^D := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s,e,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
private lemma combineTime (a b c D n k H E z l : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hb : 1 ≤ b) (he : 1 ≤ E) (hz : z ≤ a*n^(b*E)) (hh : H ≤ a*n^(b*E))
    (hl : l ≤ c*(n+k+H+1)^D) :
    z+l+1 ≤ (a+c*(a+3)^D+1)*n^((b*(D+1))*E) := by
  let B := n^(b*E)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hn
  have bn : n ≤ B := by
    change n ≤ n^(b*E)
    have t := Nat.pow_le_pow_right hn (show 1 ≤ b*E by exact Nat.mul_pos hb he)
    simpa using t
  change H ≤ a*B at hh
  change z ≤ a*B at hz
  have cap : n+k+H+1 ≤ (a+3)*B := by rw [Nat.add_mul];omega
  have bound := hl.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
  rw [Nat.mul_pow] at bound
  have bd : B^D ≤ B^(D+1) := Nat.pow_le_pow_right hB (by omega)
  have bb : B ≤ B^(D+1) := by
    simpa using Nat.pow_le_pow_right hB (show 1 ≤ D+1 by omega)
  have one : 1 ≤ B^(D+1) := Nat.one_le_pow _ _ hB
  rw [show (b*(D+1))*E=(b*E)*(D+1) by ring,Nat.pow_mul]
  change z+l+1 ≤ (a+c*(a+3)^D+1)*B^(D+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add _ one
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a bb))
  rw [← Nat.mul_assoc] at bound
  exact bound.trans (Nat.mul_le_mul_left _ bd)

theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∀ ε₀ : ℚ, 0 < ε₀ → ε₀ < 1 →
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            ∃ t ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)),
              let s := execute P n k d t
              s.halted = true ∧
                s.work ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)) ∧
                ValidLabels n k s ∧
                ∀ O, Stable d k (1 + (ε₀ : ℝ)) O → outputPartition n k s = O := by
  obtain ⟨a,b,ha,hb,hgen⟩ := uniform_ball_cover_catalog
  obtain ⟨p,w,writer⟩ := point_output_loop output selector_expression
  obtain ⟨c,D,bound⟩ := capPoly p
  refine ⟨a+c*(a+3)^D+1,b*(D+1),by omega,Nat.mul_pos hb (by omega),?_⟩
  intro e he he'
  obtain ⟨gen,hg⟩ := hgen e he he'
  let cmd := Cmd.seq gen w
  obtain ⟨safe,corr⟩ := compiler_execution_exact cmd 0
  refine ⟨compile cmd 0,safe,?_⟩
  intro n k d hk hn hm
  obtain ⟨s,z,H,ez,tz,hH,rd,ends,wit⟩ := hg n k d hk hn hm
  let x := worldOf k H d s
  obtain ⟨v,l,el,tl,labels⟩ := writer x s rd
  have exe : Executes d cmd (initialStore n k) v (z+l) := .seq ez el
  have init : MinSumFPT.initState n k 0 0=(initialStore n k).state 0 0 := by simp [initialStore,Store.state,MinSumFPT.initState]
  have final : execute (compile cmd 0) n k d (z+l+1)=v.haltedState cmd.size (0+(z+l)+1) 0 := by
    unfold execute MinSumFPT.run
    rw [init]
    exact corr n d _ v _ exe (fun _=>0) 0
  have hbnd := tl.trans (bound x.cap (by unfold World.cap;omega))
  have et : 1 ≤ parameterEnvelope (e:ℝ) := by unfold parameterEnvelope;omega
  have total := combineTime a b c D n k H _ z l (by omega) hn hb et tz hH hbnd
  have lab : ∀i < x.n,(v.haltedState cmd.size (0+(z+l)+1) 0).imem (-1-(i:ℤ))=output x i := labels
  obtain ⟨valid,recov⟩ := cheapest_cover_recovers x _ hk hn hm ends lab
  refine ⟨z+l+1,total,?_⟩
  dsimp only
  rw [final]
  refine ⟨rfl,by simpa [Store.haltedState,Store.state] using total,valid,?_⟩
  intro O ho
  have ep : (0:ℝ) < (e:ℝ) := by exact_mod_cast he
  exact recov (1+(e:ℝ)) (by linarith) O ho (wit O ho)
