-- Prove2me | solution 1 for PI.StabSplit.flag_nilp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:32:56.438802+00:00
-- url     : https://prove2.me/submissions/ba1b1411-435a-4699-a48f-424772c8889b

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
theorem _root_.solution {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ (a.val + 1)) *ᵥ v a = 0 := by
  intro a
  induction' ht : a.val using Nat.strong_induction_on with t ih generalizing a
  have hsp : Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1) ≤
      LinearMap.ker (Matrix.mulVecLin ((g - 1) ^ t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : b.1.val < t := by rw [← ht]; exact b.2
    have := ih b.1.val hb b.1 rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have e : t = (t - (b.1.val + 1)) + (b.1.val + 1) := by omega
    rw [e, pow_add, ← mulVec_mulVec, this, mulVec_zero]
  have h1 := hsp (hv a)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1
  rw [pow_succ, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  exact h1
end PI.StabSplit
