-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_proof_0c4b4118822f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:43.834244+00:00
-- url     : https://prove2.me/submissions/1d72a469-ee47-4070-bde8-a565f07109fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_prod_pow_jet_9f846f708c0d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}
namespace GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
theorem _root_.solution : Statement := by
  intro n p u h z₀ a hu hu0 hh
  have hP : ∀ α ∈ Finset.Nat.antidiagonalTuple p a,
      AnalyticAt ℂ (fun z => ∏ i, u i z ^ α i) z₀ ∧
      (∀ k < a, iteratedFDeriv ℂ k (fun z => ∏ i, u i z ^ α i) z₀ = 0) ∧
      ∀ w, iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ (fun _ => w) =
        a.factorial * ∏ i, fderiv ℂ (u i) z₀ w ^ α i := by
    intro α hα
    rw [Finset.Nat.mem_antidiagonalTuple] at hα
    obtain ⟨h1, h2, -⟩ := prod_pow_jet u hu hu0 α 0 Finset.univ
    refine ⟨h1, hα ▸ h2, fun w => ?_⟩
    have := (prod_pow_jet u hu hu0 α w Finset.univ).2.2
    rwa [hα] at this
  have h2 : iteratedFDeriv ℂ a
      (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ := by
    rw [iteratedFDeriv_fun_sum_apply (fun α hα => ((hP α hα).1.fun_mul (hh α)).contDiffAt)]
    exact Finset.sum_congr rfl fun α hα => top_mul (hP α hα).1 (hh α) (hP α hα).2.1
  refine ⟨fun k hk => ?_, h2, fun w => ?_⟩
  · rw [iteratedFDeriv_fun_sum_apply (fun α hα => ((hP α hα).1.fun_mul (hh α)).contDiffAt)]
    exact Finset.sum_eq_zero fun α hα =>
      vanish_mul (hP α hα).1 (hh α) (hP α hα).2.1 (b := 0)
        (fun k hk => absurd hk (Nat.not_lt_zero k)) k (by omega)
  · rw [h2, sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [smul_apply, (hP α hα).2.2 w, smul_eq_mul]
    ring
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
