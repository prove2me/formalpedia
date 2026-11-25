-- Prove2me | solution 1 for PI.StabSplit.mulVec_col_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:48.890693+00:00
-- url     : https://prove2.me/submissions/fb358eb4-7486-4078-bc2e-bb996cdb56ea

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
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : A * C = C) (j : m) :
    A *ᵥ (fun i => C i j) = fun i => C i j := by
  ext i
  have := congrFun (congrFun h i) j
  simpa [mulVec, dotProduct, mul_apply] using this
end PI.StabSplit
