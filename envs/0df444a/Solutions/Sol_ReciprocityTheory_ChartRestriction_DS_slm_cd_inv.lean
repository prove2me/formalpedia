-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cd_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:57.135973+00:00
-- url     : https://prove2.me/submissions/29d4c413-eb4b-4ffc-9747-5e20ef5e271e

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hd : ∀ x ∈ s, (f x).det ≠ 0) : ContDiffOn ℝ k (fun x => (f x)⁻¹) s := by
  have hdi : ContDiffOn ℝ k (fun x => ((f x).det)⁻¹) s := (slm_cd_det hf).inv hd
  have hadj := slm_cd_adj hf
  rw [slm_cd_iff] at hadj ⊢
  intro i j
  refine (hdi.mul (hadj i j)).congr fun x _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
end ReciprocityTheory.ChartRestriction.DS
