-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_congr_pts_b0afe8eda56e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:20:14.936918+00:00
-- url     : https://prove2.me/submissions/49b30aba-f21d-49c8-836a-65314cb98135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · rfl
  · rfl
end GroundTheory.Heights₂.Heights.Inter
