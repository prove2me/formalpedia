-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_comp_dcd50d5cca1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:32.242712+00:00
-- url     : https://prove2.me/submissions/7d1e4265-1173-4300-aecd-8eef52c64eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_lift_854fe137c8a6
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
theorem _root_.solution (R : Res ι P e) {g : MCone ι → ℝ} (hg : IsLocSmooth P g)
    (x : R.R.M) (j : Fin R.atlas.n) :
    ContDiffOn ℝ ∞ (fun y => g (R.liftAt x ((R.atlas.chart j).symm y)))
      ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) := by
  have hS : IsOpen ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :=
    (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  have hF := res_contDiffOn_lift R x j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  obtain ⟨U, hU, G, hG, hgG⟩ := hg _ (res_mem R x hy.2)
  have hpre : (fun y => R.liftAt x ((R.atlas.chart j).symm y)) ⁻¹' U ∈ 𝓝 y :=
    (hF.continuousOn.continuousAt (hS.mem_nhds hy)).preimage_mem_nhds hU
  obtain ⟨u, hus, huo, hyu⟩ := mem_nhds_iff.mp hpre
  refine ⟨u, huo, hyu, ?_⟩
  refine (hG.comp (hF.mono Set.inter_subset_left) fun y' hy' => hus hy'.2).congr fun y' hy' => ?_
  exact hgG _ ⟨hus hy'.2, res_mem R x hy'.1.2⟩
end GroundTheory.Heights₂.Heights.Inter
