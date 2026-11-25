-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_continuousOn_lift_e6623d19a860
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:20.862084+00:00
-- url     : https://prove2.me/submissions/e9f2c05b-dc8d-41e6-a0ae-f614c49b7947

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_holo_e570b372581a
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



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
theorem _root_.solution (R : Res ι P e) (x : R.R.M) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.liftAt x z p) (R.R.src (R.idx x)) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.atlas.cover z
  have hzt : R.atlas.chart j z ∈ (R.atlas.chart j).target := (R.atlas.chart j).map_source hj
  have hc : ContinuousAt ((fun z => R.liftAt x z p) ∘ (R.atlas.chart j).symm)
      (R.atlas.chart j z) :=
    (res_holo R x p j _ ⟨hzt, by rwa [Set.mem_preimage, (R.atlas.chart j).left_inv hj]⟩).continuousAt
  have h := ((R.atlas.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => R.liftAt x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt
end GroundTheory.Heights₂.Heights.Inter
