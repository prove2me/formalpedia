-- Prove2me | solution 1 for PI.QnCovHat2W.qminor_row_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:32.233307+00:00
-- url     : https://prove2.me/submissions/a9c12317-2d60-447b-a6b7-26c7b815aa29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_QnCovHat2OfLin
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (u : ℂ)
    (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E (x ∘ π) y u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorRowSkew_holds A n m E x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
end PI.QnCovHat2W
