-- Prove2me | solution 1 for WeierstrassCurve.transcendental_j_perturb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/856daa70-f743-5fcd-b696-f556043e7401

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_transcendental_j_perturb

set_option autoImplicit false

open Polynomial WeierstrassCurve

namespace JPerturb

variable {R : Type*} [CommRing R]

noncomputable def WX (W : WeierstrassCurve R) : WeierstrassCurve (Polynomial R) :=
  ⟨C W.a₁, C W.a₂, C W.a₃, C W.a₄ + X, C W.a₆ + X ^ 2⟩

theorem WX_c₄ (W : WeierstrassCurve R) : (WX W).c₄ = C (-48 : R) * X + C W.c₄ := by
  simp only [WX, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, map_add, map_sub,
    map_mul, map_pow, map_neg, map_ofNat]
  ring

theorem WX_Δ (W : WeierstrassCurve R) : (WX W).Δ =
    C (-432 : R) * X ^ 4
    + C (72*W.a₁^2 + 288*W.a₂ - 64) * X ^ 3
    + C (-W.a₁^6 - 12*W.a₁^4*W.a₂ + W.a₁^4 + 36*W.a₁^3*W.a₃ - 48*W.a₁^2*W.a₂^2 + 8*W.a₁^2*W.a₂
        + 72*W.a₁^2*W.a₄ + 144*W.a₁*W.a₂*W.a₃ - 96*W.a₁*W.a₃ - 64*W.a₂^3 + 16*W.a₂^2
        + 288*W.a₂*W.a₄ - 216*W.a₃^2 - 192*W.a₄ - 864*W.a₆) * X ^ 2
    + C (W.a₁^5*W.a₃ + 2*W.a₁^4*W.a₄ + 8*W.a₁^3*W.a₂*W.a₃ + 16*W.a₁^2*W.a₂*W.a₄ - 30*W.a₁^2*W.a₃^2
        + 72*W.a₁^2*W.a₆ + 16*W.a₁*W.a₂^2*W.a₃ - 192*W.a₁*W.a₃*W.a₄ + 32*W.a₂^2*W.a₄
        + 72*W.a₂*W.a₃^2 + 288*W.a₂*W.a₆ - 192*W.a₄^2) * X
    + C W.Δ := by
  simp only [WX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  ring

theorem natDegree_WX_c₄_le (W : WeierstrassCurve R) : (WX W).c₄.natDegree ≤ 1 := by
  rw [WX_c₄]; compute_degree

theorem natDegree_WX_Δ_le (W : WeierstrassCurve R) : (WX W).Δ.natDegree ≤ 4 := by
  rw [WX_Δ]; compute_degree

theorem coeff_WX_c₄_one (W : WeierstrassCurve R) : (WX W).c₄.coeff 1 = -48 := by
  rw [WX_c₄]; simp only [coeff_add, coeff_C_mul_X, coeff_C]; norm_num

theorem coeff_WX_Δ_four (W : WeierstrassCurve R) : (WX W).Δ.coeff 4 = -432 := by
  rw [WX_Δ]; simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]; norm_num

theorem map_WX {L : Type*} [CommRing L] (φ : R →+* L) (t : L) (W : WeierstrassCurve R) :
    (WX W).map (eval₂RingHom φ t) = ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ := by
  simp [WX, WeierstrassCurve.map]

end JPerturb

open JPerturb in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {L : Type*} [Field L] [CharZero L]
    (φ : R →+* L) (t : L) (ht : ∀ P : Polynomial R, P ≠ 0 → P.eval₂ φ t ≠ 0)
    (W : WeierstrassCurve R) :
    ∃ hΔ : (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _
        (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L)
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by

  have h432 : (-432 : R) ≠ 0 := by norm_num
  have h48 : (-48 : R) ≠ 0 := by norm_num
  have hDne : (WX W).Δ ≠ 0 := fun h => h432 (by simpa [h] using (coeff_WX_Δ_four W).symm)
  have hCne : (WX W).c₄ ≠ 0 := fun h => h48 (by simpa [h] using (coeff_WX_c₄_one W).symm)
  have hDdeg : (WX W).Δ.natDegree = 4 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_WX_Δ_le W) (by rw [coeff_WX_Δ_four]; exact h432)
  have hDlead : (WX W).Δ.leadingCoeff = -432 := by
    rw [leadingCoeff, hDdeg, coeff_WX_Δ_four]

  set δ : L := (WX W).Δ.eval₂ φ t with hδ
  set γ : L := (WX W).c₄.eval₂ φ t with hγ
  have hδne : δ ≠ 0 := ht _ hDne
  have hγne : γ ≠ 0 := ht _ hCne
  have hΔt : (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L).Δ = δ := by
    rw [← map_WX φ t W, map_Δ]; rfl
  have hc₄t : (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L).c₄ = γ := by
    rw [← map_WX φ t W, map_c₄]; rfl
  refine ⟨by rw [hΔt]; exact hδne, ?_⟩

  set Wt : WeierstrassCurve L := ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ with hWt
  letI : Wt.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by rw [hΔt]; exact hδne)⟩
  have hj : Wt.j = γ ^ 3 / δ := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', hΔt, hc₄t, div_eq_inv_mul]
  show Transcendental ℚ Wt.j

  intro halg
  obtain ⟨m, hm0, hm⟩ : IsAlgebraic ℤ Wt.j := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr halg
  rw [hj] at hm

  set d := m.natDegree with hd
  set c4 := (WX W).c₄ with hc4
  set Δx := (WX W).Δ with hΔx
  set P : Polynomial R := ∑ i ∈ Finset.range (d + 1), C ((m.coeff i : ℤ) : R) * (c4 ^ (3 * i) * Δx ^ (d - i))
    with hP

  have hPt : P.eval₂ φ t = 0 := by
    have hsum : P.eval₂ φ t = ∑ i ∈ Finset.range (d + 1), (m.coeff i : L) * (γ ^ (3 * i) * δ ^ (d - i)) := by
      rw [hP, eval₂_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eval₂_mul, eval₂_C, eval₂_mul, eval₂_pow, eval₂_pow, map_intCast]
    have hm' : ∑ i ∈ Finset.range (d + 1), (m.coeff i : L) * (γ ^ 3 / δ) ^ i = 0 := by
      rw [aeval_def, eval₂_eq_sum_range] at hm
      simpa using hm
    have hscale : ∑ i ∈ Finset.range (d + 1), (m.coeff i : L) * (γ ^ (3 * i) * δ ^ (d - i))
        = δ ^ d * ∑ i ∈ Finset.range (d + 1), (m.coeff i : L) * (γ ^ 3 / δ) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [div_pow, ← pow_mul, pow_sub₀ δ hδne hi']
      field_simp
    rw [hsum, hscale, hm', mul_zero]

  have hc4deg : c4.natDegree = 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_WX_c₄_le W) (by rw [coeff_WX_c₄_one]; exact h48)
  have hc4lead : c4.leadingCoeff = -48 := by rw [leadingCoeff, hc4deg, coeff_WX_c₄_one]
  set i₀ := m.natTrailingDegree with hi₀
  have hi₀d : i₀ ≤ d := natTrailingDegree_le_natDegree m
  have htrail : m.coeff i₀ ≠ 0 := by
    rw [hi₀, ← trailingCoeff]; exact trailingCoeff_nonzero_iff_nonzero.mpr hm0
  have hdegpow : ∀ i, (c4 ^ (3 * i) * Δx ^ (d - i)).natDegree = 3 * i + 4 * (d - i) := by
    intro i
    rw [natDegree_mul (pow_ne_zero _ hCne) (pow_ne_zero _ hDne), natDegree_pow, natDegree_pow,
      hc4deg, hDdeg]
    ring
  have hleadpow : ∀ i, (c4 ^ (3 * i) * Δx ^ (d - i)).leadingCoeff = (-48) ^ (3 * i) * (-432) ^ (d - i) := by
    intro i
    rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow, hc4lead, hDlead]
  have hcoeffP : P.coeff (3 * i₀ + 4 * (d - i₀))
      = ((m.coeff i₀ : ℤ) : R) * ((-48) ^ (3 * i₀) * (-432) ^ (d - i₀)) := by
    rw [hP, finsetSum_coeff]
    rw [Finset.sum_eq_single i₀]
    · rw [coeff_C_mul, ← hleadpow i₀, ← hdegpow i₀, coeff_natDegree]
    · intro i hi hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      ·
        have hmi : m.coeff i = 0 := coeff_eq_zero_of_lt_natTrailingDegree (by rw [← hi₀]; exact hlt)
        rw [hmi, Int.cast_zero, map_zero, zero_mul, coeff_zero]
      ·
        have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hdeg_lt : (c4 ^ (3 * i) * Δx ^ (d - i)).natDegree < 3 * i₀ + 4 * (d - i₀) := by
          rw [hdegpow i]; omega
        rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt hdeg_lt, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi₀d)) h
  have hPne : P ≠ 0 := by
    intro h
    have h0 : P.coeff (3 * i₀ + 4 * (d - i₀)) = 0 := by rw [h, coeff_zero]
    rw [hcoeffP] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact htrail (Int.cast_eq_zero.mp h1)
    · rcases mul_eq_zero.mp h2 with h3 | h4
      · exact pow_ne_zero _ h48 h3
      · exact pow_ne_zero _ h432 h4
  exact ht P hPne hPt

end S_WeierstrassCurve_transcendental_j_perturb
end P2MW
export P2MW.S_WeierstrassCurve_transcendental_j_perturb (solution)
