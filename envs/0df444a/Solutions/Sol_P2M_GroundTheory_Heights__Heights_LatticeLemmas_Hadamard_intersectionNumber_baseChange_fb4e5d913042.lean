-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_Hadamard_intersectionNumber_baseChange_fb4e5d913042
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:35.477024+00:00
-- url     : https://prove2.me/submissions/7cff5ecc-6295-4340-af36-592894dfc8b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_log_gramDet_le_e183ddd6b300

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace Hadamard
theorem _root_.solution : Hadamard.Statement.{u, v, w} := by
  intro K _ _ M ι _ x La hli hcard hnorm
  classical
  set r := Module.finrank (𝓞 K) M.carrier
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : 0 ≤ Real.log (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x))) :=
    Real.log_natCast_nonneg _
  have hσ : ∀ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤ 2 * (r * Real.log La) := by
    intro σ
    refine (log_gramDet_le M.metric σ hli).trans ?_
    have hle : ∑ i, Real.log ‖fibreVec M.metric σ (x i)‖ ≤ ∑ _i : ι, Real.log La :=
      Finset.sum_le_sum fun i _ ↦ Real.log_le_log
        (norm_pos_iff.mpr ((linearIndependent_fibreVec M.metric σ hli).ne_zero i)) (hnorm i σ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hle
    linarith
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      Module.finrank ℚ K * (2 * (r * Real.log La)) := by
    calc _ ≤ ∑ _σ : K →+* ℂ, 2 * (r * Real.log La) := Finset.sum_le_sum fun σ _ ↦ hσ σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hli hcard, degreeWith,
    le_div_iff₀ hd]
  nlinarith
end Hadamard
end GroundTheory.Heights₂.Heights.LatticeLemmas
