-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:13:19.860354+00:00
-- url     : https://prove2.me/submissions/3afdd409-2895-4178-b69d-1305d4c7fa64

import Mathlib
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_fourier

section
set_option autoImplicit false
namespace RLCDiscrepancy
theorem chk_lemma_4_9 {F : Type*} [Field F] [Fintype F] {n : ℕ} (ψ : AddChar F ℂ)
    (f : (Fin n → F) → ℝ) (y : Fin n → F) :
    fourier ψ (selfConv f) y = ((‖fourier ψ f y‖ ^ 2 : ℝ) : ℂ) := by
  have hq : ((Fintype.card F : ℂ) ^ n) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast Fintype.card_ne_zero
  push_cast
  rw [← Complex.mul_conj']
  have hc : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := fun a => (AddChar.map_neg_eq_conj ψ a).symm
  unfold fourier selfConv
  simp only [map_div₀, map_sum, map_mul, Complex.conj_ofReal, hc, map_pow, Complex.conj_natCast]
  push_cast
  field_simp
  simp only [Finset.sum_mul, Finset.mul_sum]
  have key : ∀ S : ℂ, (Fintype.card F : ℂ) ^ n * (S / (Fintype.card F : ℂ) ^ n) = S := by
    intro S; field_simp
  simp only [key]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ ?_
  intro w
  simp only [Equiv.subLeft_apply]
  have h2 : ψ (w ⬝ᵥ y) = ψ (x ⬝ᵥ y) * ψ (-((x - w) ⬝ᵥ y)) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; rw [sub_dotProduct]; ring
  rw [h2]
  ring
end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_lemma_4_9 := @RLCDiscrepancy.chk_lemma_4_9
