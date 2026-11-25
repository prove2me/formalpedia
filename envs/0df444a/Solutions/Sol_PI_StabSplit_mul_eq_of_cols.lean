-- Prove2me | solution 1 for PI.StabSplit.mul_eq_of_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:27.062187+00:00
-- url     : https://prove2.me/submissions/337fa81f-708e-4b5a-8bef-8e6afe16df0e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_MulVecColOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.StabSplit
namespace PI.StabSplit
theorem _root_.solution {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : ∀ j, A *ᵥ (fun i => C i j) = fun i => C i j) :
    A * C = C := by
  ext i j
  have := congrFun (h j) i
  simpa [mulVec, dotProduct, mul_apply] using this
end PI.StabSplit
