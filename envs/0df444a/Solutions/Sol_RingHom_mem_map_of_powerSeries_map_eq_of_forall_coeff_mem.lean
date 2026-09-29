-- Prove2me | solution 1 for RingHom.mem_map_of_powerSeries_map_eq_of_forall_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e28b00b7-92ae-5bea-b973-1b38cc571061

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_mem_map_of_powerSeries_map_eq_of_forall_coeff_mem

set_option autoImplicit false

theorem solution
    {R R' L : Type*} [CommRing R] [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    [CommRing L] [Algebra R L] (hinj : Function.Injective (algebraMap R L))
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (htm : t ∈ IsLocalRing.maximalIdeal R')
    (e : R' →+* PowerSeries L) (hι : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R L r))
    (hI : ∀ i ∈ RingHom.ker π, PowerSeries.constantCoeff (e i) = 0)
    (u : PowerSeries R) (hu : e t = u.map (algebraMap R L)) (hu1 : IsUnit (PowerSeries.coeff 1 u))
    (𝔞 : Ideal R) (z : R') (P : PowerSeries R) (hP : e z = P.map (algebraMap R L))
    (hPa : ∀ n : ℕ, PowerSeries.coeff n P ∈ 𝔞) :
    z ∈ 𝔞.map ι := by
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
            calc I ^ (n + 1) * Ideal.span {t} ≤ I ^ (n + 1) * I ^ 1 :=
                Ideal.mul_mono_right (by simpa using hspan_le 1)
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

  have hIX : ∀ (n : ℕ) (w : R'), w ∈ I ^ n → ∀ m < n, PowerSeries.coeff m (e w) = 0 := by
    intro n w hw
    have hmap : Ideal.map e (I ^ n) ≤ Ideal.span {(PowerSeries.X : PowerSeries L) ^ n} := by
      rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact PowerSeries.X_dvd_iff.mpr (hI i hi)
    have hdvd : (PowerSeries.X : PowerSeries L) ^ n ∣ e w :=
      Ideal.mem_span_singleton.mp (hmap (Ideal.mem_map_of_mem e hw))
    exact PowerSeries.X_pow_dvd_iff.mp hdvd

  have hu0 : PowerSeries.constantCoeff u = 0 := by
    apply hinj
    rw [map_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_map, ← hu,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hI t htI
  obtain ⟨v, hv⟩ := PowerSeries.X_dvd_iff.mpr hu0
  have hv1 : PowerSeries.coeff 1 u = PowerSeries.constantCoeff v := by
    rw [hv]
    simp
  have hcoeff_pow : ∀ n : ℕ, PowerSeries.coeff n (u ^ n) = (PowerSeries.coeff 1 u) ^ n := by
    intro n
    rw [hv1, hv, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]

  have main : ∀ n : ℕ, ∃ j ∈ 𝔞.map ι, ∃ Q : PowerSeries R, (∀ m, PowerSeries.coeff m Q ∈ 𝔞) ∧
      e j = Q.map (algebraMap R L) ∧ z - j ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact ⟨0, zero_mem _, 0, fun m => by simp, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨j, hj, Q, hQa, hQ, hzj⟩ := ih
      obtain ⟨c, hc⟩ := step n _ hzj

      have hcn : c * PowerSeries.coeff 1 u ^ n = PowerSeries.coeff n P - PowerSeries.coeff n Q := by
        apply hinj
        have h1 : PowerSeries.coeff n (e (z - j - ι c * t ^ n)) = 0 :=
          hIX (n + 1) _ hc n (Nat.lt_succ_self n)
        simp only [map_sub, map_mul, map_pow, hP, hQ, hι, hu, PowerSeries.coeff_map,
          PowerSeries.coeff_C_mul] at h1
        rw [← map_pow, PowerSeries.coeff_map, hcoeff_pow] at h1
        rw [map_mul, map_sub]
        linear_combination -h1
      have hca : c ∈ 𝔞 := by
        have hmem : c * PowerSeries.coeff 1 u ^ n ∈ 𝔞 := hcn ▸ 𝔞.sub_mem (hPa n) (hQa n)
        exact (Ideal.mul_unit_mem_iff_mem 𝔞 (hu1.pow n)).mp hmem
      refine ⟨j + ι c * t ^ n, ?_, Q + PowerSeries.C c * u ^ n, ?_, ?_, ?_⟩
      · exact Ideal.add_mem _ hj (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ι hca))
      · intro m
        rw [map_add, PowerSeries.coeff_C_mul]
        exact 𝔞.add_mem (hQa m) (𝔞.mul_mem_right _ hca)
      · simp only [map_add, map_mul, map_pow, hQ, hι, hu, PowerSeries.map_C]
      · have h2 : z - (j + ι c * t ^ n) = z - j - ι c * t ^ n := by ring
        rw [h2]
        exact hc

  set J : Ideal R' := 𝔞.map ι with hJdef
  have hzn : ∀ n : ℕ, z ∈ J ⊔ I ^ n := fun n => by
    obtain ⟨j, hj, Q, -, -, hzj⟩ := main n
    have h3 : z = j + (z - j) := by ring
    rw [h3]
    exact Submodule.add_mem_sup hj hzj

  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R') ∈ I := h ▸ Submodule.mem_top
    have h2 : π 1 = 0 := by simpa [hIdef, RingHom.mem_ker] using h1
    rw [map_one] at h2
    have h3 : (ι 1 : R') = ι 0 := congrArg ι h2
    rw [map_one, map_zero] at h3
    exact one_ne_zero h3

  have hmk : ∀ n : ℕ, Ideal.Quotient.mk J z ∈ I ^ n • (⊤ : Submodule R' (R' ⧸ J)) := by
    intro n
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp (hzn n)
    rw [← hyw, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]
    have h4 : Ideal.Quotient.mk J w = w • (1 : R' ⧸ J) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one]
    rw [h4]
    exact Submodule.smul_mem_smul hw Submodule.mem_top
  have hkr : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R' (R' ⧸ J))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hItop
  have hz0 : Ideal.Quotient.mk J z = 0 := by
    rw [← Submodule.mem_bot R', ← hkr, Submodule.mem_iInf]
    exact hmk
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz0

end S_RingHom_mem_map_of_powerSeries_map_eq_of_forall_coeff_mem
end P2MW
export P2MW.S_RingHom_mem_map_of_powerSeries_map_eq_of_forall_coeff_mem (solution)
