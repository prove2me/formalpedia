-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.rational_single_run_program
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:09:29.640156+00:00
-- url     : https://prove2.me/submissions/d4cb6354-f9a4-46d4-888d-b9f5c1069863
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_rational_recovery_program
import Theorems.Thm_StableMSR_Recovery_validLabels_feasible
import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution

set_option autoImplicit false
open scoped Classical ENNReal
open StableMSR.Recovery StableMSR.Recovery.Supplement
set_option maxHeartbeats 1600000
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Supplement
private lemma tapeStep {P : MinSumFPT.Program} (hp : DeterministicProgram P)
    {n : ℕ} (d : Point n→Point n→ℝ) (ω η : Tape) (s : MinSumFPT.State) :
    MinSumFPT.step P d ω s=MinSumFPT.step P d η s := by
  unfold MinSumFPT.step
  by_cases h : s.halted=true
  · simp [h]
  · simp only [h,if_false]
    cases E : P[s.cfg.pc]? with
    | none => rfl
    | some a =>
      have mem : a∈P := List.mem_of_getElem? E
      have safe := hp.2 a mem
      cases a <;> first | rfl | contradiction
private lemma tapeRun {P : MinSumFPT.Program} (hp : DeterministicProgram P)
    {n k : ℕ} (d : Point n→Point n→ℝ) (ω : Tape) (t : ℕ) :
    randomState P n k d ω t=execute P n k d t := by
  unfold randomState execute MinSumFPT.run
  rw [show (MinSumFPT.step P d ω)=(MinSumFPT.step P d (fun _=>0)) from funext (tapeStep hp d _ _)]
private lemma parked (P : MinSumFPT.Program) {n k : ℕ} (d : Point n→Point n→ℝ)
    {t T : ℕ} (ht : t ≤ T) (halt : (execute P n k d t).halted=true) :
    execute P n k d T=execute P n k d t := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction u with
  | zero => rfl
  | succ u ih =>
    change MinSumFPT.run P n k 0 0 d (fun _=>0) (t+u+1)=_
    simp only [MinSumFPT.run,Function.iterate_succ_apply'] at *
    change MinSumFPT.step P d (fun _=>0) (execute P n k d (t+u))=_
    rw [ih]
    simp [MinSumFPT.step,halt]

theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ e : ℚ, 0 < e → e < 1 →
      ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧
        ∀ (n k : ℕ) (d : Point n → Point n → ℝ), 1 ≤ k → k ≤ n → IsMetricArray d →
          let T := a*n^(b*parameterEnvelope (e:ℝ))
          AlwaysFeasible P n k d T ∧ ∀ O : Partition n,
            Stable d k (1+(e:ℝ)) O →
            MinSumFPT.tapeLaw {ω | randomOutput P n k d T ω ≠ O} ≤ (2/3 : ENNReal) := by
  obtain ⟨a,b,ha,hb,prog⟩ := StableMSR.Recovery.rational_recovery_program
  refine ⟨a,b,ha,hb,?_⟩
  intro e he he'
  obtain ⟨P,hp,good⟩ := prog e he he'
  refine ⟨P,hp.1,?_⟩
  intro n k d hk hn hm
  obtain ⟨t,ht,halt,work,valid,recov⟩ := good n k d hk hn hm
  constructor
  · intro ω
    exact ⟨t,ht,by rw [tapeRun hp];exact ⟨halt,work,valid,validLabels_feasible _ valid⟩⟩
  · intro O ho
    have empty : {ω | randomOutput P n k d (a*n^(b*parameterEnvelope (e:ℝ))) ω≠O}=∅ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_not]
      unfold randomOutput
      rw [tapeRun hp,parked P d ht halt]
      exact recov O ho
    rw [empty];simp
