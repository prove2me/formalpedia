-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_pt_mem_D_iff_4133d8fe572e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:22.975072+00:00
-- url     : https://prove2.me/submissions/8d802399-259c-44c4-8558-f18e423222f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_mem_D_of_sameOrbit_6653390d49ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_sameOrbit_symm_4cd367704a50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_compat_c1fc93db7599


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) :
    R.pt y ∈ ReciprocityTheory.AnForm.R.conePts R.D ↔ R.liftAt x y ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  have h := GroundTheory.Heights₂.Heights.Inter.res_compat R x y hy (R.mem_src_idx y)
  exact ⟨fun hp => mem_D_of_sameOrbit R h hp, fun hl => mem_D_of_sameOrbit R (sameOrbit_symm h) hl⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
