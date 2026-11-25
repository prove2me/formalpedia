-- Prove2me | solution 1 for PI.StabSplit.flag_nilp_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:03.307053+00:00
-- url     : https://prove2.me/submissions/ceda9875-b41d-4386-a86a-ca32099bbffa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_MulVecColOfMul
import Theorems.Thm_PI_StabSplit_flag_nilp

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
theorem _root_.solution {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ m) *ᵥ v a = 0 := by
  intro a
  have e : m = (m - (a.val + 1)) + (a.val + 1) := by omega
  rw [e, pow_add, ← mulVec_mulVec, flag_nilp g v hv a, mulVec_zero]
end PI.StabSplit
