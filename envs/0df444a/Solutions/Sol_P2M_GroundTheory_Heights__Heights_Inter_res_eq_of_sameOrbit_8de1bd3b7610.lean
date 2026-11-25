-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:13.874493+00:00
-- url     : https://prove2.me/submissions/cfabe169-50b6-4a4d-99e7-1b5b96c43161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι ℂ)} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {g : MCone ι → ℝ}
    (hg : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P, g (tsmul c z) = g z) (R : Res ι P e)
    (x : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) : g (R.liftAt x y) = g (R.pt y) := by
  obtain ⟨c, hc, hcy⟩ := res_compat R x y hy (R.mem_src_idx y)
  rw [hcy]
  exact hg c hc (R.pt y) (res_mem R y (R.mem_src_idx y))
end GroundTheory.Heights₂.Heights.Inter
