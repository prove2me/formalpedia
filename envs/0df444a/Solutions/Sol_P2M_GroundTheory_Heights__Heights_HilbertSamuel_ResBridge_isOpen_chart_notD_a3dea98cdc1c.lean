-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_isOpen_chart_notD_a3dea98cdc1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:46.493821+00:00
-- url     : https://prove2.me/submissions/e48d1eca-1e4c-4319-9582-96a5bd93e908

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_pt_mem_D_iff_4133d8fe572e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_analyticAt_liftAt_pi_7b40b5bddbb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894


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
    IsOpen ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, hB1⟩
  set x1 := (R.atlas.chart j).symm u1
  have hV : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x1) ∈ 𝓝 u1 :=
    ((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)).mem_nhds
      ⟨hu1, R.mem_src_idx x1⟩
  have hnot : ¬ ∀ f ∈ R.D, eval (R.liftAt x1 x1) f = 0 := fun h =>
    hB1 ⟨(GroundTheory.Heights₂.Heights.Inter.res_mem R x1 (R.mem_src_idx x1)).1, h⟩
  push Not at hnot
  obtain ⟨f, hfD, hf0⟩ := hnot
  have hcont : ContinuousAt (fun u => eval (R.liftAt x1 ((R.atlas.chart j).symm u)) f) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (R.analyticAt_liftAt_pi x1 j ⟨hu1, R.mem_src_idx x1⟩).continuousAt
  filter_upwards [hV, hcont.eventually_ne hf0] with u hu hne
  refine ⟨hu.1, fun hB => ?_⟩
  exact hne (((pt_mem_D_iff R hu.2).mp hB).2 f hfD)
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
