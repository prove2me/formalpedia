-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_D_null_d796392db77f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:53.984104+00:00
-- url     : https://prove2.me/submissions/07680a75-d68b-4cc7-8dfb-624f33ed298b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_isAnalyticSubset_D_e54d8c491106
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_interior_D_8a07618018ce
import Theorems.Thm_ReciprocityTheory_AnForm_M_analyticNull


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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) = 0 := by
  refine measure_mono_null ?_
    (ReciprocityTheory.AnForm.M.analyticNull R.atlas _ (isAnalyticSubset_D R) (interior_D R) j)
  rintro u ⟨hu, hD⟩
  exact ⟨(R.atlas.chart j).symm u, ⟨hD, (R.atlas.chart j).map_target hu⟩, (R.atlas.chart j).right_inv hu⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
