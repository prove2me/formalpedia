-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_cycEval_finsupp_62d89a5ee931
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:12.103293+00:00
-- url     : https://prove2.me/submissions/18e1eb70-1b7e-41ef-bd23-0a4d46a0ed25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution {R : Type*} [CommRing R] (n : Ideal (MRingOver R ι) → ℤ)
    (Z : Ideal (MRingOver R ι) →₀ ℤ) : NumbersDVR.cycEval n ⇑Z = Z.sum fun W c => c * n W := by
  unfold NumbersDVR.cycEval
  rw [finsum_eq_sum_of_support_subset _ (s := Z.support) ?_]
  · rfl
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hW (by rw [h0, zero_mul])
end GroundTheory.Heights₂.Heights.FlagTypings
