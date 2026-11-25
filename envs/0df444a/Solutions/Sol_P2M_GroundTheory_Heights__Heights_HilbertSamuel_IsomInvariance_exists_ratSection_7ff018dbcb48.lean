-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_exists_ratSection_7ff018dbcb48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:40.410808+00:00
-- url     : https://prove2.me/submissions/6ccc8fc8-068c-4435-840b-bf1ba5540c98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIsomInvariance
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_coordProd_not_mem_ea4019939c96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : IsRelevant P) (B : HermLine ι) :
    ∃ s t : MRing ι, IsRatSectionOn P B s t := by
  classical
  let c : ∀ k, ι k := fun k => (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P := fun k => (hrel k).choose_spec
  exact ⟨_, _, fun k => (B.a k).toNat, fun k => (-B.a k).toNat, Inter.AvoidRing.isMultiHomog_coordProd c _,
    Inter.AvoidRing.isMultiHomog_coordProd c _, Inter.AvoidRing.coordProd_not_mem hP c hc _,
    Inter.AvoidRing.coordProd_not_mem hP c hc _, fun k => Int.toNat_sub_toNat_neg _⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
