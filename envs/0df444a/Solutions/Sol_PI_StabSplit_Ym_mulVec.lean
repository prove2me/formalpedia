-- Prove2me | solution 1 for PI.StabSplit.Ym_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:03.4178+00:00
-- url     : https://prove2.me/submissions/a85f0c75-f636-4f41-b9af-1d4ebcbf0c51

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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c) :
    Ym k r z z' γ *ᵥ c = ∑ j, c j • gramVec k r z z' γ j := by
  ext i
  simp [Ym, mulVec, dotProduct, Finset.sum_apply, mul_comm]
end PI.StabSplit
