-- Prove2me | solution 1 for RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cfbe7152-093f-5724-8db7-aef5ecef9154

import Mathlib
import Theorems.Thm_PowerSeries_exists_map_algebraMap_eq_of_digits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq

set_option autoImplicit false

theorem solution
    {R R' L : Type*} [CommRing R] [CommRing R'] [CommRing L] [Algebra R L]
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (e : R' →+* PowerSeries L)
    (hι : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R L r))
    (hI : ∀ i ∈ RingHom.ker π, PowerSeries.constantCoeff (e i) = 0)
    (u : PowerSeries R) (hu : e t = u.map (algebraMap R L))
    (z : R') :
    ∃ P : PowerSeries R, e z = P.map (algebraMap R L) ∧ PowerSeries.constantCoeff P = π z := by
  classical
  set I : Ideal R' := RingHom.ker π with hIdef
  have hπι : ∀ r : R, π (ι r) = r := fun r => by
    simpa using RingHom.congr_fun hπ r
  have htI : t ∈ I := by simpa [hIdef, RingHom.mem_ker] using ht

  have hsubI : ∀ w : R', w - ι (π w) ∈ I := fun w => by
    simp [hIdef, RingHom.mem_ker, hπι]

  have hspan_le : ∀ n : ℕ, Ideal.span {t ^ n} ≤ I ^ n := fun n =>
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow htI n)

  have pow_le : ∀ n : ℕ, I ^ n ≤ Ideal.span {t ^ n} ⊔ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
      calc I ^ (n + 1) = I ^ n * I := pow_succ I n
        _ ≤ (Ideal.span {t ^ n} ⊔ I ^ (n + 1)) * (Ideal.span {t} ⊔ I ^ 2) := Ideal.mul_mono ihn hcot
        _ ≤ Ideal.span {t ^ (n + 1)} ⊔ I ^ (n + 1 + 1) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_left
          · refine le_sup_of_le_right ?_
            calc Ideal.span {t ^ n} * I ^ 2 ≤ I ^ n * I ^ 2 := Ideal.mul_mono_left (hspan_le n)
              _ = I ^ (n + 2) := (pow_add I n 2).symm
              _ ≤ I ^ (n + 1 + 1) := le_of_eq (by ring_nf)
          · refine le_sup_of_le_right ?_
            calc I ^ (n + 1) * Ideal.span {t} ≤ I ^ (n + 1) * I ^ 1 := Ideal.mul_mono_right (by simpa using hspan_le 1)
              _ = I ^ (n + 1 + 1) := (pow_add I (n + 1) 1).symm
          · refine le_sup_of_le_right ?_
            calc I ^ (n + 1) * I ^ 2 = I ^ (n + 1 + 2) := (pow_add I (n + 1) 2).symm
              _ ≤ I ^ (n + 1 + 1) := Ideal.pow_le_pow_right (by omega)

  have step : ∀ (n : ℕ) (w : R'), w ∈ I ^ n → ∃ a : R, w - ι a * t ^ n ∈ I ^ (n + 1) := by
    intro n w hw
    obtain ⟨r, b, hb, rfl⟩ := Ideal.mem_span_singleton_sup.mp (pow_le n hw)
    refine ⟨π r, ?_⟩
    have h1 : r * t ^ n + b - ι (π r) * t ^ n = (r - ι (π r)) * t ^ n + b := by ring
    rw [h1]
    refine Ideal.add_mem _ ?_ hb
    have : (r - ι (π r)) * t ^ n ∈ I * I ^ n := Ideal.mul_mem_mul (hsubI r) (Ideal.pow_mem_pow htI n)
    simpa [pow_succ'] using this

  have hdig : ∀ (z : R') (n : ℕ), ∃ a : ℕ → R, z - ∑ i ∈ Finset.range n, ι (a i) * t ^ i ∈ I ^ n := by
    intro z n
    induction n with
    | zero => exact ⟨fun _ => 0, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨c, hc⟩ := step n _ ha
      refine ⟨Function.update a n c, ?_⟩
      rw [Finset.sum_range_succ, Function.update_self]
      have hsum : ∑ i ∈ Finset.range n, ι (Function.update a n c i) * t ^ i =
          ∑ i ∈ Finset.range n, ι (a i) * t ^ i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.mem_range.mp hi).ne]
      rw [hsum]
      have h2 : z - (∑ i ∈ Finset.range n, ι (a i) * t ^ i + ι c * t ^ n) =
          z - ∑ i ∈ Finset.range n, ι (a i) * t ^ i - ι c * t ^ n := by ring
      rw [h2]
      exact hc
  obtain ⟨P, hP⟩ := PowerSeries.exists_map_algebraMap_eq_of_digits ι I t e hι hI u hu hdig z

  have hconst : PowerSeries.constantCoeff (e z) = algebraMap R L (π z) := by
    have hz : z = ι (π z) + (z - ι (π z)) := by ring
    conv_lhs => rw [hz]
    rw [map_add, map_add, hI _ (hsubI z), add_zero, hι, PowerSeries.constantCoeff_C]
  refine ⟨PowerSeries.mk fun n => if n = 0 then π z else PowerSeries.coeff n P, ?_, ?_⟩
  · ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hconst]
    · rw [hP, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_mk, if_neg hn.ne']
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]

end S_RingHom_exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq
end P2MW
export P2MW.S_RingHom_exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq (solution)
