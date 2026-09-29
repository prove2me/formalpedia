-- Prove2me | solution 1 for Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ff12be62-a0a2-57e0-92c5-617383ae7f8b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two

namespace HilbertRecipOddPort

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_lt_one_of_toZMod_eq_zero {c : ℤ_[p]} (h : PadicInt.toZMod c = 0) : ‖c‖ < 1 := by
  have : c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at this
  exact PadicInt.mem_nonunits.mp this

theorem toZMod_eq_zero_of_norm_lt_one {c : ℤ_[p]} (h : ‖c‖ < 1) : PadicInt.toZMod c = 0 := by
  have : c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact PadicInt.mem_nonunits.mpr h
  exact this

theorem norm_eq_one_of_toZMod_ne_zero {c : ℤ_[p]} (h : PadicInt.toZMod c ≠ 0) : ‖c‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one c) (not_lt.mp fun hlt ↦ h ?_)
  exact toZMod_eq_zero_of_norm_lt_one hlt

theorem exists_sq_eq_of_toZMod_eq_sq (hp2 : p ≠ 2) {c : ℤ_[p]} {s : ZMod p} (hs : s ≠ 0)
    (hcs : PadicInt.toZMod c = s ^ 2) : ∃ t : ℤ_[p], t ^ 2 = c := by
  obtain ⟨sl, hsl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) s
  have hslnorm : ‖sl‖ = 1 := norm_eq_one_of_toZMod_ne_zero (by rw [hsl]; exact hs)
  have htwo : ‖(2 : ℤ_[p])‖ = 1 := by
    have h := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    simpa using h
  set F : ℤ_[p][X] := X ^ 2 - C c with hF
  have hFeval : aeval sl F = sl ^ 2 - c := by simp [hF]
  have hF'eval : aeval sl (derivative F) = 2 * sl := by
    simp [hF]; norm_num
  have hnormF' : ‖aeval sl (derivative F)‖ = 1 := by
    rw [hF'eval, norm_mul, htwo, hslnorm, one_mul]
  have hnormF : ‖aeval sl F‖ < 1 := by
    rw [hFeval]
    apply norm_lt_one_of_toZMod_eq_zero
    rw [map_sub, map_pow, hsl, hcs, sub_self]
  have hhens : ‖aeval sl F‖ < ‖aeval sl (derivative F)‖ ^ 2 := by
    rw [hnormF', one_pow]; exact hnormF
  obtain ⟨t, ht, -⟩ := hensels_lemma hhens
  refine ⟨t, ?_⟩
  have : aeval t F = t ^ 2 - c := by simp [hF]
  rw [this] at ht
  exact sub_eq_zero.mp ht

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

end HilbertRecipOddPort

open HilbertRecipOddPort in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (p * a) * x ^ 2 - b * y ^ 2 = 0) ↔ IsSquare b := by
  have hpr : p.Prime := Fact.out
  constructor
  · rintro ⟨z, x, y, hne, h⟩
    obtain ⟨Z, X, Y, hprim, hZ⟩ := exists_primitive_zero hne h
    set A : ℤ_[p] := ⟨a, ha.le⟩ with hA
    set B : ℤ_[p] := ⟨b, hb.le⟩ with hB
    have hBn : ‖B‖ = 1 := hb
    have hAn : ‖A‖ = 1 := ha
    have hBres : PadicInt.toZMod B ≠ 0 := fun h0 ↦ by
      have := norm_lt_one_of_toZMod_eq_zero h0; rw [hBn] at this; exact lt_irrefl _ this
    have hAres : PadicInt.toZMod A ≠ 0 := fun h0 ↦ by
      have := norm_lt_one_of_toZMod_eq_zero h0; rw [hAn] at this; exact lt_irrefl _ this

    have hrel : Z ^ 2 - (p : ℤ_[p]) * A * X ^ 2 - B * Y ^ 2 = 0 := by
      apply Subtype.val_injective
      simp only [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_mul, PadicInt.coe_natCast,
        PadicInt.coe_zero, hA, hB]
      linear_combination hZ
    have hpres : PadicInt.toZMod (p : ℤ_[p]) = 0 := by
      rw [map_natCast, ZMod.natCast_self]

    have hred : PadicInt.toZMod Z ^ 2 - PadicInt.toZMod B * PadicInt.toZMod Y ^ 2 = 0 := by
      have := congrArg PadicInt.toZMod hrel
      simpa [map_sub, map_mul, map_pow, hpres] using this
    by_cases hY : PadicInt.toZMod Y = 0
    ·
      exfalso
      have hZ0 : PadicInt.toZMod Z = 0 := by
        rw [hY] at hred; simpa using hred
      have hZlt : ‖Z‖ < 1 := norm_lt_one_of_toZMod_eq_zero hZ0
      have hYlt : ‖Y‖ < 1 := norm_lt_one_of_toZMod_eq_zero hY
      obtain ⟨Z', hZ'⟩ := (PadicInt.norm_lt_one_iff_dvd Z).mp hZlt
      obtain ⟨Y', hY'⟩ := (PadicInt.norm_lt_one_iff_dvd Y).mp hYlt
      have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hpr.ne_zero
      have hrel' : (p : ℤ_[p]) * ((p : ℤ_[p]) * Z' ^ 2 - A * X ^ 2 - (p : ℤ_[p]) * B * Y' ^ 2)
          = 0 := by
        rw [hZ', hY'] at hrel; linear_combination hrel
      have hrel'' : (p : ℤ_[p]) * Z' ^ 2 - A * X ^ 2 - (p : ℤ_[p]) * B * Y' ^ 2 = 0 :=
        (mul_eq_zero.mp hrel').resolve_left hp0
      have hX0 : PadicInt.toZMod A * PadicInt.toZMod X ^ 2 = 0 := by
        have := congrArg PadicInt.toZMod hrel''
        simpa [map_sub, map_mul, map_pow, hpres] using this
      have hX : PadicInt.toZMod X = 0 := by
        rcases mul_eq_zero.mp hX0 with h0 | h0
        · exact absurd h0 hAres
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      have hXlt : ‖X‖ < 1 := norm_lt_one_of_toZMod_eq_zero hX
      rcases hprim with h1 | h1 | h1
      · rw [h1] at hZlt; exact lt_irrefl _ hZlt
      · rw [h1] at hXlt; exact lt_irrefl _ hXlt
      · rw [h1] at hYlt; exact lt_irrefl _ hYlt
    ·
      set s : ZMod p := PadicInt.toZMod Z * (PadicInt.toZMod Y)⁻¹ with hs
      have hBs : PadicInt.toZMod B = s ^ 2 := by
        have e : PadicInt.toZMod Z ^ 2 = PadicInt.toZMod B * PadicInt.toZMod Y ^ 2 :=
          sub_eq_zero.mp hred
        rw [hs, mul_pow, e, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hY), mul_one]
      have hs0 : s ≠ 0 := fun h0 ↦ hBres (by rw [hBs, h0]; ring)
      obtain ⟨t, ht⟩ := exists_sq_eq_of_toZMod_eq_sq hp hs0 hBs
      refine ⟨(t : ℚ_[p]), ?_⟩
      have h := congrArg (fun s : ℤ_[p] ↦ (s : ℚ_[p])) ht
      simp only [PadicInt.coe_pow, hB, Subtype.coe_mk] at h
      rw [← h]; ring
  · rintro ⟨w, hw⟩
    refine ⟨w, 0, 1, fun ⟨_, _, h1⟩ ↦ one_ne_zero h1, ?_⟩
    rw [hw]; ring

end S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
end P2MW
export P2MW.S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two (solution)
