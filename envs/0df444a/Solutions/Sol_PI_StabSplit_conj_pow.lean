-- Prove2me | solution 1 for PI.StabSplit.conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:15.859528+00:00
-- url     : https://prove2.me/submissions/8ecc2d58-356b-40d8-b931-d9c609e2cf62

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
theorem _root_.solution {N : ℕ} (A G Gi : Matrix (Fin N) (Fin N) ℂ) (h1 : Gi * G = 1) (h2 : G * Gi = 1) :
    ∀ p : ℕ, (Gi * A * G) ^ p = Gi * A ^ p * G
  | 0 => by simp [h1]
  | p + 1 => by
    rw [pow_succ, solution A G Gi h1 h2 p, pow_succ]
    calc Gi * A ^ p * G * (Gi * A * G) = Gi * A ^ p * (G * Gi) * A * G := by noncomm_ring
      _ = Gi * (A ^ p * A) * G := by rw [h2]; noncomm_ring
end PI.StabSplit
