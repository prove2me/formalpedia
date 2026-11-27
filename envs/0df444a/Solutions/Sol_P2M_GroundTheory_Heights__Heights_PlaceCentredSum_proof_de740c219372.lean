-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_proof_de740c219372
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:44.66766+00:00
-- url     : https://prove2.me/submissions/7c192beb-5a40-4e9e-958c-101d1927c5b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_centred_iff_dd0781008482
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_neg_log_apply_dfa8e9f4105e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_sum_fibre_6093e33d2f1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_finsum_fibre_114cbf332dc8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
namespace GroundTheory.Heights₂.Heights.PlaceCentredSum
theorem _root_.solution : PlaceCentredSum.Statement := by
  intro L K _ _ _ _ _ O m t
  classical
  let g : HeightOneSpectrum (𝓞 L) → ℝ := fun Q ↦
    if AbsCentredAt O m (fun u ↦ FinitePlace.mk Q u) then -Real.log (FinitePlace.mk Q t) else 0
  have hL : ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun u ↦ w u}, -Real.log (w t) =
      ∑ᶠ Q, g Q := by
    rw [finsum_mem_def, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun Q ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, FinitePlace.equivHeightOneSpectrum,
      Equiv.coe_fn_symm_mk]
    exact if_congr Iff.rfl rfl rfl
  have hK : ∑ᶠ v ∈ {v : FinitePlace K | AbsCentredAt O m fun u ↦ v (algebraMap L K u)},
      -Real.log (v (algebraMap L K t)) = ∑ᶠ v : FinitePlace K, (deg L v : ℝ) * g (below v) := by
    rw [finsum_mem_def]
    refine finsum_congr fun v ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, centred_iff, neg_log_apply]
    split_ifs <;> simp
  have hg : g.support.Finite := by
    rcases eq_or_ne t 0 with rfl | ht
    · refine Set.finite_empty.subset fun Q hQ ↦ ?_
      simp [g] at hQ
    · refine ((FinitePlace.hasFiniteMulSupport ht).preimage
        (fun a _ b _ h ↦ FinitePlace.mk_eq_iff.mp h)).subset fun Q hQ ↦ ?_
      simp only [Function.mem_support, g] at hQ
      split_ifs at hQ
      · simp only [Set.mem_preimage, Function.mem_mulSupport]
        intro h1
        exact hQ (by simp [h1])
      · exact absurd rfl hQ
  rw [hK, hL]
  exact finsum_fibre below (deg L) _ g hg sum_fibre
end GroundTheory.Heights₂.Heights.PlaceCentredSum
