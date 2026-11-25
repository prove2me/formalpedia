-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.top_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:57.798382+00:00
-- url     : https://prove2.me/submissions/149e3a7f-4ed3-48cb-95f7-c9645f21e2a8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_ml_expand
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_sum_eq_top
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_infinite_circle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by
  set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ
  have heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2) := by
    intro z
    simp only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ml_expand]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ infinite_circle
    rintro _ ⟨θ, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]
  have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0
  simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.sum_eq_single (fun _ => 2)]
  · simp only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [if_pos (by ring), mul_one]
  · intro f _ hf
    rw [if_neg, mul_zero]
    intro h2
    exact hf (funext (sum_eq_top f h2.symm))
  · simp
end PositivityTheory.Rg.Sw.LVs.TC
