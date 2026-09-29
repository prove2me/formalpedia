-- Prove2me | solution 1 for PadicInt.exists_pow_eq_of_exists_pow_eq_toZModPow_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c28500cf-8d9e-5223-a2cf-9079c12f388b

import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three

open Polynomial

theorem solution {p : ℕ} [hp : Fact p.Prime] {u : ℤ_[p]} (hu : ‖u‖ = 1) (hres : ∃ c : ZMod (p ^ 3), c ^ p = PadicInt.toZModPow 3 u) :
    ∃ z : ℤ_[p], z ^ p = u := by
  obtain ⟨c, hc⟩ := hres
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.out.ne_zero⟩
  have hu_unit : IsUnit (PadicInt.toZModPow 3 u) := (PadicInt.isUnit_iff.mpr hu).map (PadicInt.toZModPow 3)
  have hc_unit : IsUnit c := by
    have h : IsUnit (c ^ p) := hc ▸ hu_unit
    exact (isUnit_pow_iff hp.out.ne_zero).mp h
  have hc_cop : ¬ p ∣ c.val := by
    have h1 : Nat.Coprime c.val (p ^ 3) := by
      have h := ZMod.val_coe_unit_coprime hc_unit.unit
      rwa [IsUnit.unit_spec] at h
    have h2 : Nat.Coprime c.val p := h1.coprime_dvd_right (dvd_pow_self p (by norm_num))
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp h2.symm
  set a : ℤ_[p] := (c.val : ℤ_[p]) with ha_def
  have ha_res : PadicInt.toZModPow 3 a = c := by
    rw [ha_def, map_natCast, ZMod.natCast_val, ZMod.cast_id]
  have ha_norm : ‖a‖ = 1 := by
    have hne : PadicInt.toZMod a ≠ 0 := by
      rw [ha_def, map_natCast]
      intro h
      exact hc_cop ((ZMod.natCast_eq_zero_iff c.val p).mp h)
    rcases lt_or_eq_of_le (PadicInt.norm_le_one a) with h | h
    · exfalso
      apply hne
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact h
    · exact h
  set F : Polynomial ℤ_[p] := X ^ p - C u with hF_def
  have hFa : F.aeval a = a ^ p - u := by simp [hF_def]
  have hFa_norm : ‖F.aeval a‖ ≤ (p : ℝ) ^ (-(3 : ℕ) : ℤ) := by
    rw [hFa, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
      map_pow, ha_res, hc, sub_self]
  have hF'a : F.derivative.aeval a = (p : ℤ_[p]) * a ^ (p - 1) := by
    simp [hF_def, derivative_X_pow]
  have hF'a_norm : ‖F.derivative.aeval a‖ = (p : ℝ)⁻¹ := by
    rw [hF'a, norm_mul, norm_pow, ha_norm, one_pow, mul_one, PadicInt.norm_p]
  have hp_real : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hF'a_norm]
    refine lt_of_le_of_lt hFa_norm ?_
    have hkey : ((p : ℝ)⁻¹) ^ 2 = (p : ℝ) ^ (-(2 : ℕ) : ℤ) := by
      rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    rw [hkey]
    exact zpow_lt_zpow_right₀ hp_real (by norm_num)
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have hsub : z ^ p - u = 0 := by simpa [hF_def] using hz
  exact sub_eq_zero.mp hsub

end S_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three
end P2MW
export P2MW.S_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three (solution)
