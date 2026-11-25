-- Prove2me | solution 1 for PI.TrDualLocW.isIntegral_of_pow_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:01.823399+00:00
-- url     : https://prove2.me/submissions/2f97e704-e2bb-4f2f-ba25-ebfd06bf051e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
variable {K ℓ}
variable (K ℓ)
variable {K ℓ}
namespace PI.TrDualLocW
theorem _root_.solution (s : K) (d : ℕ) (hd : d ≠ 0) (h : ∀ n : ℕ, IsIntegral ℤ ((d : K) * s ^ n)) :
    IsIntegral ℤ s := by
  let T : Submodule ℤ K :=
    (Submodule.span ℤ (Set.range (integralBasis K))).map (LinearMap.mulLeft ℤ ((d : K)⁻¹))
  have hT : T.FG := (Submodule.fg_span (Set.finite_range _)).map _
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {s}) ≤ T := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, Submonoid.mem_closure_singleton] at hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨(d : K) * s ^ n, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_span_integralBasis]
      exact ⟨⟨_, (mem_integralClosure_iff ℤ K).2 (h n)⟩, rfl⟩
    · show (d : K)⁻¹ * ((d : K) * s ^ n) = s ^ n
      rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hd)]
  exact IsIntegral.of_mem_of_fg _ (hT.of_le hle) s (Algebra.self_mem_adjoin_singleton ℤ s)
end PI.TrDualLocW
