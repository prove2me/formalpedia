-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_smooth_0ac6a7c275c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:43.064563+00:00
-- url     : https://prove2.me/submissions/d28b6266-195b-45a5-88d3-08ee1205fa2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_comp_dcd50d5cca1a
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
theorem _root_.solution (R : Res ι P e) {u : MCone ι → ℝ} (hu : IsSmoothFn P u) :
    R.atlas.Smooth (fun x => u (R.pt x)) := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  set x0 := (R.atlas.chart j).symm y
  refine ⟨(R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0),
    (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _), ⟨hy.1, R.mem_src_idx x0⟩, ?_⟩
  refine ((res_contDiffOn_comp R hu.2 x0 j).mono Set.inter_subset_right).congr fun y' hy' => ?_
  exact (res_eq_of_sameOrbit hu.1 R x0 hy'.2.2).symm
end GroundTheory.Heights₂.Heights.Inter
