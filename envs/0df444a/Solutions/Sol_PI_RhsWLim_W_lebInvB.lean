-- Prove2me | solution 1 for PI.RhsWLim.W.lebInvB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:44.018149+00:00
-- url     : https://prove2.me/submissions/f77d8e58-7d58-4e5e-959d-210821a6af6a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL
import Theorems.Thm_PI_RhsWLim_W_blkLin_apply
import Theorems.Thm_PI_RhsWLim_W_det_blkLin
import Theorems.Thm_PI_RhsWLim_W_normSq_det_hb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution : LebInvB := by
  intro k μ hμ
  have h1 : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : (volume : Measure ((Fin k → ℂ) × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set f : ((Fin k → ℂ) × ℂ) →ₗ[ℝ] ((Fin k → ℂ) × ℂ) := (blkLin k μ).restrictScalars ℝ with hfdef
  have hdet : LinearMap.det f = 1 := by
    rw [hfdef, LinearMap.det_restrictScalars, det_blkLin, Algebra.norm_complex_apply, normSq_det_hb hμ]
  have hf : blkAct k μ = ⇑f := by
    funext p
    rw [hfdef, LinearMap.coe_restrictScalars, blkLin_apply]
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ((Fin k → ℂ) × ℂ)))
    (by rw [hdet]; norm_num), hdet]
  simp
end PI.RhsWLim.W
