-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_iteratedFDeriv_sub_eq_db13c53b8c02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:56.308181+00:00
-- url     : https://prove2.me/submissions/5e0ef4c9-71c1-4a3f-bc00-e7d7fe77c8ef

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_norm_fderiv_fderiv_eq_938ca658f52c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
theorem _root_.solution {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by
  have da : DifferentiableAt ℝ a z :=
    (ha.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  have db : DifferentiableAt ℝ b z :=
    (hb.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, fderiv_fun_sub da db]
  · rw [← norm_fderiv_fderiv_eq, fderiv2_sub_of_contDiffOn hV ha hb hz]
end GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
