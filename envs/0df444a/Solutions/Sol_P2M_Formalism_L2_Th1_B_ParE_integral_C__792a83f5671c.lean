-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_B_ParE_integral_C__792a83f5671c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:03.739163+00:00
-- url     : https://prove2.me/submissions/920a3b00-f29e-45ed-bcea-57c00386e88c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}
namespace Formalism.L2.Th1.B.ParE
theorem _root_.solution {c : K} (hc : ‖c‖ ≤ 1) : Integral (MvPowerSeries.C c : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · simp
end Formalism.L2.Th1.B.ParE
