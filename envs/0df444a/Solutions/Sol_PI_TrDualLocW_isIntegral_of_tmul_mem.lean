-- Prove2me | solution 1 for PI.TrDualLocW.isIntegral_of_tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:09.895533+00:00
-- url     : https://prove2.me/submissions/0c18a64b-e35b-45a1-b33d-3aad45a3bcc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
import Theorems.Thm_PI_TrDualLocW_mem_S

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
theorem _root_.solution (X : K) (E : ℕ) (hX : IsIntegral ℤ ((ℓ : K) ^ E * X))
    (hS : (1 ⊗ₜ X : ℚ_[ℓ] ⊗[ℚ] K) ∈ S K ℓ) : IsIntegral ℤ X := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hw : ∀ i, ∃ w : ℤ, (integralBasis K).repr X i = w := by
    intro i
    obtain ⟨z, hz⟩ := coord_int _ hX i
    have hz' : (integralBasis K).repr ((ℓ : K) ^ E * X) i = (ℓ : ℚ) ^ E * (integralBasis K).repr X i := by
      rw [show ((ℓ : K)) ^ E * X = ((ℓ : ℚ) ^ E) • X by
        rw [Algebra.smul_def, map_pow, map_natCast]]
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hn : ‖(((integralBasis K).repr X i : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
      have := mem_S.1 hS i
      rwa [BA_repr_tmul, PadicInt.mem_subring_iff] at this
    have hdiv : ((ℓ : ℤ) ^ E : ℤ) ∣ z := by
      rw [← Padic.norm_int_le_pow_iff_dvd]
      have hq : ((z : ℚ_[ℓ])) = (ℓ : ℚ_[ℓ]) ^ E * (((integralBasis K).repr X i : ℚ) : ℚ_[ℓ]) := by
        have h2 : ((z : ℚ) : ℚ_[ℓ]) = (((ℓ : ℚ) ^ E * (integralBasis K).repr X i : ℚ) : ℚ_[ℓ]) := by
          rw [← hz', hz]
        push_cast at h2
        exact h2
      rw [hq, norm_mul, Padic.norm_p_pow]
      calc (ℓ : ℝ) ^ (-(E : ℤ)) * ‖(((integralBasis K).repr X i : ℚ) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(E : ℤ)) * 1 :=
            mul_le_mul_of_nonneg_left hn (by positivity)
        _ = _ := mul_one _
    obtain ⟨w, hw⟩ := hdiv
    refine ⟨w, ?_⟩
    have h1 : (ℓ : ℚ) ^ E * (integralBasis K).repr X i = (ℓ : ℚ) ^ E * w := by
      rw [← hz', hz, hw]
      push_cast
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hℓ) h1
  choose w hw using hw
  have hX' : X = ∑ i, (w i : ℚ) • integralBasis K i := by
    conv_lhs => rw [← (integralBasis K).sum_repr X]
    simp only [hw]
  rw [hX']
  refine IsIntegral.sum _ fun i _ => ?_
  rw [Rat.smul_def, Rat.cast_intCast, integralBasis_apply]
  have hwi : IsIntegral ℤ ((w i : ℤ) : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := w i))
  exact hwi.mul (RingOfIntegers.isIntegral_coe _)
end PI.TrDualLocW
