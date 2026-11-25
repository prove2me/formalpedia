-- Prove2me | solution 1 for PI.KLW.Pair.half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:59.215818+00:00
-- url     : https://prove2.me/submissions/69ce5a62-d2e3-45c1-9f55-79ce5b7db8b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_Ind_hf_single_single
import Theorems.Thm_PI_KLW_Ind_hf_smul_left
import Theorems.Thm_PI_KLW_Ind_hf_smul_right
import Theorems.Thm_PI_KLW_Ind_rp_add
import Theorems.Thm_PI_KLW_Ind_rp_mul
import Theorems.Thm_PI_KLW_NO_not_rp_inv_p
import Theorems.Thm_PI_KLW_NO_one_add_p_unit
import Theorems.Thm_PI_KLW_NO_rp_add
import Theorems.Thm_PI_KLW_NO_rp_c
import Theorems.Thm_PI_KLW_NO_rp_mul
import Theorems.Thm_PI_KLW_NO_rp_natCast
import Theorems.Thm_PI_KLW_NO_rp_pow
import Theorems.Thm_PI_KLW_NO_rp_pow_div
import Theorems.Thm_PI_KLW_NO_rp_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Pair
open PI.KLW
namespace PI.KLW.Pair
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, ¬ Rp K p (ε * hf c x y / p) := by
  classical
  by_contra H
  push_neg at H
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce : c ε = 1 - ε := by linear_combination hsum
  obtain ⟨T, hT⟩ : ∃ T, T = ε / p + c ε := ⟨_, rfl⟩
  have hTL : ∀ x ∈ L, T • x ∈ L := fun x hx => (hL _).2 fun y hy => by
    rw [Ind.hf_smul_left]
    have e : T * hf c x y = ε * hf c x y / p + c ε * hf c x y := by rw [hT]; ring
    rw [e]
    exact NO.rp_add (H x hx y hy) (NO.rp_mul (NO.rp_c c hε) ((hL x).1 hx y hy))
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨N, hN0, hNL⟩ := hS (Pi.single i 1)
  have hTj : ∀ j : ℕ, T ^ j • ((N : K) • Pi.single i (1 : K)) ∈ L := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul]; exact hNL
    | succ j ihj => rw [pow_succ', mul_smul]; exact hTL _ ihj
  have hvv : hf c ((N : K) • Pi.single i (1 : K)) ((N : K) • Pi.single i (1 : K))
      = (N : K) * N := by
    rw [Ind.hf_smul_left, Ind.hf_smul_right, Ind.hf_single_single, map_natCast, mul_one]
  have hj : ∀ j : ℕ, Rp K p (T ^ j * ((N : K) * N)) := fun j => by
    have := (hL _).1 (hTj j) _ hNL
    rwa [Ind.hf_smul_left, hvv] at this
  have hcT : c T = c ε / p + ε := by rw [hT, map_add, map_div₀, map_natCast, hc]
  have hjj : ∀ j : ℕ, Rp K p ((T * c T) ^ j * ((N : K) ^ 4)) := fun j => by
    have h1 := hj j
    have h2 := NO.rp_c c (hj j)
    rw [map_mul, map_pow, map_mul, map_natCast] at h2
    have e : (T * c T) ^ j * ((N : K) ^ 4)
        = (T ^ j * ((N : K) * N)) * (c T ^ j * ((N : K) * N)) := by ring
    rw [e]
    exact NO.rp_mul h1 h2
  obtain ⟨d, hd⟩ : ∃ d, d = ε * c ε / (p : K) ^ 2 := ⟨_, rfl⟩
  have hdR : Rp K p d := hd ▸ hδ
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = d + (p : K) ^ 2 * d - p * d - p * d := ⟨_, rfl⟩
  have hρR : Rp K p ρ := by
    rw [hρ]
    have hpd : Rp K p ((p : K) * d) := NO.rp_mul (NO.rp_natCast p) hdR
    exact NO.rp_sub (NO.rp_sub (NO.rp_add hdR (NO.rp_mul (NO.rp_pow (NO.rp_natCast p) 2) hdR))
      hpd) hpd
  have hTcT : T * c T = (1 + (p : K) * ρ) / p := by
    rw [hcT, hT, hρ, hd, hce]
    field_simp
    ring
  obtain ⟨hu0, huinv⟩ := NO.one_add_p_unit c hc hK hne hp hρR
  have hQ : N ^ 4 ≠ 0 := pow_ne_zero _ hN0
  have hpow := NO.rp_pow_div (K := K) hp hQ (le_refl (N ^ 4))
  have hA := hjj (N ^ 4 + 1)
  have hB := NO.rp_pow huinv (N ^ 4 + 1)
  obtain ⟨M, hM⟩ : ∃ M, N ^ 4 = M := ⟨_, rfl⟩
  rw [hM] at hpow hA hB
  have hMK : (M : K) = (N : K) ^ 4 := by rw [← hM]; push_cast; ring
  have hN : (N : K) ≠ 0 := by exact_mod_cast hN0
  have e1 : (1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  have hpM : (p : K) ^ M ≠ 0 := pow_ne_zero _ hp0
  have hN4 : (N : K) ^ 4 ≠ 0 := pow_ne_zero _ hN
  have key : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1))
      * ((p : K) ^ M / (M : K)) = ((p : K))⁻¹ := by
    have e2 : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1))
        * ((p : K) ^ M / (M : K))
        = ((1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1))
          * ((N : K) ^ 4 / (N : K) ^ 4) * ((p : K) ^ M / ((p : K) ^ M * p)) := by
      rw [hTcT, div_pow, hMK]
      ring
    rw [e2, e1, div_self hN4, div_mul_eq_div_div, div_self hpM, one_mul, one_mul, one_div]
  apply NO.not_rp_inv_p (K := K) hp
  rw [← key]
  exact NO.rp_mul (NO.rp_mul hA hB) hpow
end PI.KLW.Pair
