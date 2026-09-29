-- Prove2me | solution 1 for Padic.exists_ternary_isotropic_iff_of_norm_eq_one_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a2bbf5b7-c2e3-560a-851b-d5aba086c8b4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two

namespace HilbertRecipDyadicUnitsPort

open Polynomial

section generic

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_primitive_zero {A B : ℚ_[p]} {z x y : ℚ_[p]} (hne : ¬ (z = 0 ∧ x = 0 ∧ y = 0))
    (h : z ^ 2 - A * x ^ 2 - B * y ^ 2 = 0) :
    ∃ Z X Y : ℤ_[p], (‖Z‖ = 1 ∨ ‖X‖ = 1 ∨ ‖Y‖ = 1) ∧
      (Z : ℚ_[p]) ^ 2 - A * (X : ℚ_[p]) ^ 2 - B * (Y : ℚ_[p]) ^ 2 = 0 := by
  set m : ℝ := max ‖z‖ (max ‖x‖ ‖y‖) with hm
  have hmpos : 0 < m := by
    by_contra hle
    push Not at hle
    have hz : z = 0 := norm_le_zero_iff.mp ((le_max_left _ _).trans hle)
    have hx : x = 0 :=
      norm_le_zero_iff.mp (((le_max_left _ _).trans (le_max_right _ _)).trans hle)
    have hy : y = 0 :=
      norm_le_zero_iff.mp (((le_max_right _ _).trans (le_max_right _ _)).trans hle)
    exact hne ⟨hz, hx, hy⟩
  obtain ⟨c, hc, hcm⟩ : ∃ c : ℚ_[p], (c = z ∨ c = x ∨ c = y) ∧ ‖c‖ = m := by
    rcases le_total ‖z‖ (max ‖x‖ ‖y‖) with h1 | h1
    · rcases le_total ‖x‖ ‖y‖ with h2 | h2
      · exact ⟨y, Or.inr (Or.inr rfl), by rw [hm, max_eq_right h1, max_eq_right h2]⟩
      · exact ⟨x, Or.inr (Or.inl rfl), by rw [hm, max_eq_right h1, max_eq_left h2]⟩
    · exact ⟨z, Or.inl rfl, by rw [hm, max_eq_left h1]⟩
  have hc0 : c ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hcm; exact lt_irrefl _ (hcm ▸ hmpos)
  have hzle : ‖z / c‖ ≤ 1 := by
    rw [norm_div, hcm, div_le_one hmpos]; exact le_max_left _ _
  have hxle : ‖x / c‖ ≤ 1 := by
    rw [norm_div, hcm, div_le_one hmpos]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hyle : ‖y / c‖ ≤ 1 := by
    rw [norm_div, hcm, div_le_one hmpos]; exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨⟨z / c, hzle⟩, ⟨x / c, hxle⟩, ⟨y / c, hyle⟩, ?_, ?_⟩
  · simp only [PadicInt.norm_def]
    rcases hc with rfl | rfl | rfl
    · exact Or.inl (by rw [div_self hc0, norm_one])
    · exact Or.inr (Or.inl (by rw [div_self hc0, norm_one]))
    · exact Or.inr (Or.inr (by rw [div_self hc0, norm_one]))
  · show (z / c) ^ 2 - A * (x / c) ^ 2 - B * (y / c) ^ 2 = 0
    field_simp
    linear_combination h

end generic

noncomputable def r : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow (p := 2) 3

theorem r_eq_zero_iff (x : ℤ_[2]) : r x = 0 ↔ ‖x‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
  have h1 : r x = 0 ↔ x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 3) := Iff.rfl
  rw [h1, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  norm_num

theorem norm_two : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  have := PadicInt.norm_p (p := 2)
  simpa using this

theorem r_two_mul_eq_zero_iff (x : ℤ_[2]) : r (2 * x) = 0 ↔ ‖x‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by
  rw [r_eq_zero_iff, norm_mul, norm_two]
  norm_num
  constructor <;> intro h <;> linarith

theorem r_mul_self_of_norm_eq_one {x : ℤ_[2]} (hx : ‖x‖ = 1) : r x * r x = 1 := by
  obtain ⟨y, hy⟩ := IsUnit.exists_right_inv (PadicInt.isUnit_iff.mpr hx)
  have hr : r x * r y = 1 := by rw [← map_mul, hy, map_one]
  revert hr
  generalize r x = s, r y = t
  decide +revert

theorem r_sq_mem (x : ℤ_[2]) : r x * r x ∈ ({0, 1, 4} : Finset (ZMod 8)) := by
  generalize r x = s
  decide +revert

theorem exists_sq_eq_of_r_eq_one {c : ℤ_[2]} (hc : r c = 1) : ∃ t : ℤ_[2], t ^ 2 = c := by
  have hc1 : ‖c - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    rw [← r_eq_zero_iff, map_sub, hc, map_one, sub_self]
  set F : ℤ_[2][X] := X ^ 2 - C c with hF
  have hFeval : aeval (1 : ℤ_[2]) F = 1 - c := by simp [hF]
  have hF'eval : aeval (1 : ℤ_[2]) (derivative F) = 2 := by
    simp [hF]; norm_num
  have hhens : ‖aeval (1 : ℤ_[2]) F‖ < ‖aeval (1 : ℤ_[2]) (derivative F)‖ ^ 2 := by
    rw [hF'eval, hFeval, norm_two, norm_sub_rev]
    refine lt_of_le_of_lt hc1 ?_
    norm_num
  obtain ⟨t, ht, -⟩ := hensels_lemma hhens
  refine ⟨t, ?_⟩
  have : aeval t F = t ^ 2 - c := by simp [hF]
  rw [this] at ht
  exact sub_eq_zero.mp ht

theorem norm_coe_sub_one (B : ℤ_[2]) : ‖B - 1‖ = ‖(B : ℚ_[2]) - 1‖ := by
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]

theorem core_units : ∀ u v : ZMod 8, u * u = 1 → v * v = 1 →
    ∀ sz ∈ ({0, 1, 4} : Finset (ZMod 8)), ∀ sx ∈ ({0, 1, 4} : Finset (ZMod 8)),
    ∀ sy ∈ ({0, 1, 4} : Finset (ZMod 8)),
    (sz = 1 ∨ sx = 1 ∨ sy = 1) → sz - u * sx - v * sy = 0 →
    (2 * (u - 1) = 0 ∨ 2 * (v - 1) = 0) := by
  decide

theorem two_mul_sub_one_eq_zero : ∀ t : ZMod 8, 2 * (t - 1) = 0 → t = 1 ∨ t = 5 := by decide

theorem five_add_four_mul : ∀ v : ZMod 8, v * v = 1 → 5 + 4 * v = 1 := by decide

theorem isotropic_of_norm_sub_one_le (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h : ‖a - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ)) :
    ∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  set A : ℤ_[2] := ⟨a, ha.le⟩ with hA
  set B : ℤ_[2] := ⟨b, hb.le⟩ with hB
  have hBn : ‖B‖ = 1 := hb
  have hA1 : ‖A - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by rw [norm_coe_sub_one]; exact h
  have h2 : 2 * (r A - 1) = 0 := by
    have := (r_two_mul_eq_zero_iff (A - 1)).mpr hA1
    rwa [map_mul, map_sub, map_one, map_ofNat] at this
  rcases two_mul_sub_one_eq_zero _ h2 with h1 | h5
  ·
    obtain ⟨w, hw⟩ := exists_sq_eq_of_r_eq_one h1
    refine ⟨w, 1, 0, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, ?_⟩
    have : (w : ℚ_[2]) ^ 2 = a := by
      have := congrArg (fun s : ℤ_[2] ↦ (s : ℚ_[2])) hw
      simpa [hA] using this
    rw [this]; ring
  ·
    have hr : r (A + 4 * B) = 1 := by
      rw [map_add, map_mul, map_ofNat, h5]
      exact five_add_four_mul _ (r_mul_self_of_norm_eq_one hBn)
    obtain ⟨w, hw⟩ := exists_sq_eq_of_r_eq_one hr
    refine ⟨w, 1, 2, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, ?_⟩
    have : (w : ℚ_[2]) ^ 2 = a + 4 * b := by
      have := congrArg (fun s : ℤ_[2] ↦ (s : ℚ_[2])) hw
      simp [hA, hB] at this
      exact this
    rw [this]; ring

theorem units_iff (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖a - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) ∨ ‖b - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by
  constructor
  · rintro ⟨z, x, y, hne, h⟩
    obtain ⟨Z, X, Y, hprim, hZ⟩ := exists_primitive_zero hne h
    set A : ℤ_[2] := ⟨a, ha.le⟩ with hA
    set B : ℤ_[2] := ⟨b, hb.le⟩ with hB
    have hBn : ‖B‖ = 1 := hb
    have hAn : ‖A‖ = 1 := ha
    have hrel : Z ^ 2 - A * X ^ 2 - B * Y ^ 2 = 0 := by
      apply Subtype.val_injective
      simp only [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_mul, PadicInt.coe_zero, hA, hB]
      linear_combination hZ
    have hred : r Z * r Z - r A * (r X * r X) - r B * (r Y * r Y) = 0 := by
      have := congrArg r hrel
      simpa [map_sub, map_mul, map_pow, sq] using this
    have hprim' : r Z * r Z = 1 ∨ r X * r X = 1 ∨ r Y * r Y = 1 := by
      rcases hprim with h1 | h1 | h1
      · exact Or.inl (r_mul_self_of_norm_eq_one h1)
      · exact Or.inr (Or.inl (r_mul_self_of_norm_eq_one h1))
      · exact Or.inr (Or.inr (r_mul_self_of_norm_eq_one h1))
    have hcore := core_units (r A) (r B) (r_mul_self_of_norm_eq_one hAn)
      (r_mul_self_of_norm_eq_one hBn) _ (r_sq_mem Z) _ (r_sq_mem X) _ (r_sq_mem Y) hprim' hred
    rcases hcore with h1 | h1
    · left
      have : r (2 * (A - 1)) = 0 := by rwa [map_mul, map_sub, map_one, map_ofNat]
      have := (r_two_mul_eq_zero_iff _).mp this
      rwa [norm_coe_sub_one] at this
    · right
      have : r (2 * (B - 1)) = 0 := by rwa [map_mul, map_sub, map_one, map_ofNat]
      have := (r_two_mul_eq_zero_iff _).mp this
      rwa [norm_coe_sub_one] at this
  · rintro (h | h)
    · exact isotropic_of_norm_sub_one_le a b ha hb h
    · obtain ⟨z, x, y, hne, hz⟩ := isotropic_of_norm_sub_one_le b a hb ha h
      refine ⟨z, y, x, fun ⟨h1, h2, h3⟩ ↦ hne ⟨h1, h3, h2⟩, ?_⟩
      linear_combination hz

end HilbertRecipDyadicUnitsPort

theorem solution (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖a - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) ∨ ‖b - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) :=
  HilbertRecipDyadicUnitsPort.units_iff a b ha hb

end S_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two
end P2MW
export P2MW.S_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two (solution)
