-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_X_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:07.351364+00:00
-- url     : https://prove2.me/submissions/f244698b-e388-45e9-8e6f-a12e2c4f1ed4

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_inv

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
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmX ε g0) (cayleyChartDomain ε g0) := by
  have h1 : ContDiffOn ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => slmJi ε g0 * g) (cayleyChartDomain ε g0) :=
    slm_cd_mul contDiffOn_const contDiffOn_id
  have hA : ContDiffOn ℝ ∞ (fun g => slmJi ε g0 * g - 1) (cayleyChartDomain ε g0) := h1.sub contDiffOn_const
  have hB : ContDiffOn ℝ ∞ (fun g => slmJi ε g0 * g + 1) (cayleyChartDomain ε g0) := h1.add contDiffOn_const
  have hY := slm_cd_mul hA (slm_cd_inv hB fun g hg => hg)
  have hJYJ := slm_cd_mul (slm_cd_mul (contDiffOn_const (c := JJ ε)) (slm_cd_conjT hY))
    (contDiffOn_const (c := JJ ε))
  exact (hY.sub hJYJ).const_smul (1 / 2 : ℂ)
end ReciprocityTheory.ChartRestriction.DS
