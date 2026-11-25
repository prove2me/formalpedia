-- Prove2me | solution 1 for PaleyWeil.splitCharacterSum_even_reduction
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-25T06:48:00.188705+00:00
-- url     : https://prove2.me/submissions/41a880a1-f47d-4377-89ea-2505957deba3

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEvenReduction
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil

section


open Finset

namespace PaleyWeil

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]







private theorem reciprocal_injective (a : K) :
    Function.Injective (fun b : K ↦ (b - a)⁻¹) := by
  intro b c h
  exact sub_left_injective (inv_injective h)





private theorem reciprocal_linear_identity (a b t : K) (hb : b ≠ a) (ht : t ≠ 0) :
    t⁻¹ + a - b = t⁻¹ * (a - b) * (t - (b - a)⁻¹) := by
  field_simp
  ring

private theorem reciprocal_linear_at_zero (a b : K) (hb : b ≠ a) :
    (a - b) * (0 - (b - a)⁻¹) = 1 := by
  rw [show a - b = -(b - a) by ring, zero_sub, neg_mul_neg,
    mul_inv_cancel₀ (sub_ne_zero.mpr hb)]

private theorem reciprocal_value_at_zero (s : Finset K) (a : K) :
    reciprocalScale s a * (∏ r ∈ reciprocalRoots s a, (0 - r)) = 1 := by
  rw [reciprocalScale, reciprocalRoots, Finset.prod_image]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro b hb
    exact reciprocal_linear_at_zero a b (Finset.ne_of_mem_erase hb)
  · exact fun b _ c _ h ↦ reciprocal_injective a h

private theorem reciprocal_split_value (s : Finset K) (a : K) (ha : a ∈ s)
    (t : K) (ht : t ≠ 0) :
    (∏ b ∈ s, (t⁻¹ + a - b)) =
      (t⁻¹) ^ s.card * reciprocalScale s a *
        (∏ r ∈ reciprocalRoots s a, (t - r)) := by
  rw [← Finset.mul_prod_erase s _ ha]
  have hf (b : K) (hb : b ∈ s.erase a) :
      t⁻¹ + a - b = t⁻¹ * (a - b) * (t - (b - a)⁻¹) :=
    reciprocal_linear_identity a b t (Finset.ne_of_mem_erase hb) ht
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, reciprocalScale, reciprocalRoots, Finset.prod_image]
  · rw [← Finset.card_erase_add_one ha]
    simp only [pow_succ]
    ring
  · exact fun b _ c _ h ↦ reciprocal_injective a h

private theorem quadraticChar_even_power {t : K} (ht : t ≠ 0) {n : ℕ}
    (hn : Even n) : quadraticChar K (t ^ n) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, map_mul, ← pow_two, ← map_pow, quadraticChar_sq_one' (pow_ne_zero _ ht)]





end
end PaleyWeil

end

open Finset
open PaleyWeil
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem solution (s : Finset K) (a : K) (ha : a ∈ s)
    (heven : Even s.card) :
    splitCharacterSum s + 1 = quadraticChar K (reciprocalScale s a) *
      splitCharacterSum (reciprocalRoots s a) := by
  have hp (t : K) : quadraticChar K (∏ b ∈ s, (t⁻¹ + a - b)) =
      quadraticChar K (reciprocalScale s a) *
        quadraticChar K (∏ r ∈ reciprocalRoots s a, (t - r)) -
          (if t = 0 then 1 else 0) := by
    by_cases ht : t = 0
    · subst t
      have hz : (∏ b ∈ s, ((0 : K)⁻¹ + a - b)) = 0 := by
        apply Finset.prod_eq_zero ha
        simp
      rw [hz, quadraticChar_zero, ← map_mul, reciprocal_value_at_zero]
      simp
    · rw [reciprocal_split_value s a ha t ht, map_mul, map_mul,
        quadraticChar_even_power (inv_ne_zero ht) heven]
      simp [ht]
  have hsum : splitCharacterSum s =
      ∑ t : K, quadraticChar K (∏ b ∈ s, (t⁻¹ + a - b)) := by
    symm
    exact Fintype.sum_equiv ((Equiv.inv K).trans (Equiv.addRight a)) _ _ (fun _ ↦ rfl)
  rw [hsum]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [splitCharacterSum]
