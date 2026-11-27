-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_proof_776733c74388
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:15.698569+00:00
-- url     : https://prove2.me/submissions/c261dbf6-f35f-45a8-8409-47a10cce46f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinates
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_eq_mul_ratios_73d28504c04b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_birational_ratios_c3761376fe95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_smallSectionCount_eq_of_birational_d8b403abde42


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution : Statement := by
  intro Ω _ _ κ _ x c hc
  have hx := eq_mul_ratios x hc
  refine ⟨ratioField x c, inferInstance, inferInstance, ratios x c,
    mCoordIdeal_eq (ratioField x c).subtype hc hx, birational_ratios x hc,
    fun A τ => smallSectionCount_eq_of_birational (ratioField x c).subtype hc hx hc A τ⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
