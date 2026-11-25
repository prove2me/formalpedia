-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_pow_card_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:56.784879+00:00
-- url     : https://prove2.me/submissions/6571480c-e2a5-4e00-a7b5-fa9cc95d56e4

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_trace_aeval_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_idem_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] [CharZero K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) : N ^ r = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact Subsingleton.elim _ _
  have hint : IsIntegral K N := IsIntegral.of_finite K N
  set m := minpoly K N with hm
  have hmon : m.Monic := minpoly.monic hint
  have hm0 : aeval N m = 0 := minpoly.aeval K N
  have hmdeg : m.natDegree ≤ r := by
    have h2 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N)
      (Matrix.charpoly_monic N).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hrK : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hmc : m.coeff 0 = 0 := by
    have h := unip_trace_aeval_zero N hN m hmdeg
    rw [hm0, Matrix.trace_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hrK
  have hXm : X ∣ m := Polynomial.X_dvd_iff.mpr hmc
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd m hmon.ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set k := m.rootMultiplicity 0 with hkdef
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hq
    exact hXq (hq ▸ hXm)
  have hcop : IsCoprime (X ^ k) q :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr hXq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨P, hP⟩ : ∃ P : K[X], P = u * X ^ k := ⟨_, rfl⟩
  have hPP : aeval N P * aeval N P = aeval N P := by
    have hsub : P - 1 = -(v * q) := by rw [hP, ← huv]; ring
    have hfac : P * P - P = -(u * v) * m := by
      calc P * P - P = P * (P - 1) := by ring
        _ = -(u * v) * (X ^ k * q) := by rw [hsub, hP]; ring
        _ = -(u * v) * m := by rw [← hq]
    have h := congrArg (aeval N) hfac
    rw [map_sub, map_mul, map_mul, hm0, mul_zero] at h
    exact sub_eq_zero.mp h
  obtain ⟨P', hP'⟩ : ∃ P' : K[X], P' = P %ₘ m := ⟨_, rfl⟩
  have hdiv : P' + m * (P /ₘ m) = P := by
    rw [hP']
    first
      | exact Polynomial.modByMonic_add_div P hmon
      | exact Polynomial.modByMonic_add_div P m
  have hPeq : aeval N P' = aeval N P := by
    have h := congrArg (aeval N) hdiv
    rw [map_add, map_mul, hm0, zero_mul, add_zero] at h
    exact h
  have hP'deg : P'.natDegree ≤ r := by
    rw [hP']
    refine le_trans ?_ hmdeg
    first
      | exact Polynomial.natDegree_modByMonic_le P hmon
      | exact Polynomial.natDegree_modByMonic_le P m
  have hP'0 : P'.coeff 0 = 0 := by
    have h := congrArg (fun p => Polynomial.coeff p 0) hdiv
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, hmc, zero_mul, add_zero] at h
    rw [h, hP, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have htr : (aeval N P).trace = 0 := by
    rw [← hPeq, unip_trace_aeval_zero N hN P' hP'deg, hP'0, zero_mul]
  have hE : aeval N P = 0 := unip_idem_eq_zero _ hPP htr
  have hmP : m ∣ P := minpoly.dvd K N hE
  have hqu : q ∣ u := by
    rw [hq, hP, mul_comm u] at hmP
    exact (mul_dvd_mul_iff_left (pow_ne_zero k Polynomial.X_ne_zero)).mp hmP
  have hq1 : IsUnit q := by
    apply isUnit_of_dvd_one
    rw [← huv]
    exact (dvd_mul_of_dvd_left hqu _).add (dvd_mul_left q v)
  have hNk : N ^ k = 0 := by
    have h := hm0
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at h
    exact ((hq1.map (aeval N)).mul_left_eq_zero).mp h
  have hkm : k ≤ m.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hmon.ne_zero
    rwa [Polynomial.natDegree_X_pow] at h
  exact pow_eq_zero_of_le (le_trans hkm hmdeg) hNk
end ReciprocityTheory.MultiplicativeHeights
