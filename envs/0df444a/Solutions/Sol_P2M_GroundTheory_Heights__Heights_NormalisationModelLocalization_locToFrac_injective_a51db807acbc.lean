-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:11.051271+00:00
-- url     : https://prove2.me/submissions/f33ab6d0-2735-4cc0-9afb-fceeeaa25364

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_modelToFrac_injective_32d3a043c434

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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : Function.Injective (locToFrac M hJ hq) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (normalModelSubmonoid M q) z
  rw [locToFrac, IsLocalization.lift_mk'_spec, mul_zero] at hz
  rw [modelToFrac_injective M hJ hq (hz.trans (map_zero _).symm)]
  exact IsLocalization.mk'_zero _
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
