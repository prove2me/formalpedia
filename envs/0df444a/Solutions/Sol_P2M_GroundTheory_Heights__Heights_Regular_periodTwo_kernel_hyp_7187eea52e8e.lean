-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_periodTwo_kernel_hyp_7187eea52e8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:53.952864+00:00
-- url     : https://prove2.me/submissions/f86f13c9-9775-4e4f-8439-f869b323d8d9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution :
    periodTwo.IsTau0Ext (fun _ => diagonal ![Complex.I, Complex.I]) ∧ (![0, 1] : Fin 2 → ℝ) ≠ 0 ∧
      ∀ i, (periodTwo.B i).map (Int.cast : ℤ → ℝ) *ᵥ ![0, 1] = 0 := by
  refine ⟨⟨fun p q => analyticOnNhd_const, fun w _ => ?_⟩, ?_, fun i => ?_⟩
  · ext p q
    fin_cases p <;> fin_cases q <;>
      simp [PeriodPolydisc.tau0, periodTwo, diagonal_apply, div_self two_pi_I_ne_zero]
  · intro h
    have := congrFun h 1
    simp at this
  · ext k
    fin_cases k <;> simp [periodTwo, diagonal_map, mulVec, dotProduct, Fin.sum_univ_two]
end GroundTheory.Heights₂.Heights.Regular
