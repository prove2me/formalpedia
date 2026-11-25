-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_int_cons_59e2cc1bd9f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:50.72624+00:00
-- url     : https://prove2.me/submissions/84650f2a-03d0-4557-bb90-ec5bfeed12cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_locDens_cons_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mInt_congr
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
theorem _root_.solution (R : Res ι P (e + 1)) {u : MCone ι → ℝ} (hu : IsSmoothFn P u)
    (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) :
    R.int (Fin.cons u φ) g = mInt R.atlas (Fin.cons (LocPot.ofFun fun x => u (R.pt x))
      fun i => R.pot (φ i)) (fun x => g (R.pt x)) := by
  have hc : (fun j => R.pot ((Fin.cons u φ : Fin (e + 1) → MCone ι → ℝ) j)) =
      Fin.cons (R.pot u) fun i => R.pot (φ i) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  unfold Res.int
  rw [hc]
  refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr _
    (ReciprocityTheory.ChartRestriction.G.Geo.locDens_cons_congr _ _ fun j y hy => ?_) fun _ => rfl
  set x0 := (R.atlas.chart j).symm y
  filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x0))).mem_nhds
    ⟨hy, R.mem_src_idx x0⟩] with y' hy'
  exact res_eq_of_sameOrbit hu.1 R x0 hy'.2
end GroundTheory.Heights₂.Heights.Inter
