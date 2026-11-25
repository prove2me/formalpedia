-- Prove2me | solution 1 for PI.QnCovDetW.intCast_mul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:23:49.572904+00:00
-- url     : https://prove2.me/submissions/056d86f6-e7f3-48b3-a72c-178dcd77c7f9

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnCovDetW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovDetW
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (x : A) :
    (z : A) * x = (z : ℂ) • x := by
  rw [Algebra.smul_def, map_intCast]
end PI.QnCovDetW
