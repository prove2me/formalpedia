-- Prove2me | solution 1 for P2M_PI_QnCovHatW_det_sub_eq__8094bc80bf43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:40.730546+00:00
-- url     : https://prove2.me/submissions/4be842f7-1307-49b1-afc3-7cbab050e1c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q
open PI PI.QnCovHatW
namespace PI.QnCovHatW
theorem _root_.solution {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j j' : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, Q (j.succAbove k) ((j'.succAbove ∘ σ) k) =
      (Q.submatrix j.succAbove j'.succAbove).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl
end PI.QnCovHatW
