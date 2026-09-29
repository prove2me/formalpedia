-- Prove2me | solution 1 for WeierstrassCurve.exists_tateParameter_of_prime_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f1e5446a-2864-55da-ae3f-b0d2d178177e

import Mathlib
import Definitions.Def_TateCurve_QSeries
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr

open scoped NNReal

namespace TateLocalGlobalS17

variable (q : ℕ) [Fact q.Prime]

private lemma one_lt_q_nnreal : (1 : ℝ≥0) < (q : ℝ≥0) := by
  exact_mod_cast (Fact.out : q.Prime).one_lt

theorem nnnorm_padic_ratCast_eq_zpow {x : ℚ} (hx : x ≠ 0) :
    ‖(x : ℚ_[q])‖₊ = (q : ℝ≥0) ^ (-padicValRat q x) := by
  apply NNReal.coe_injective
  rw [coe_nnnorm, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hx,
    NNReal.coe_zpow, NNReal.coe_natCast]
  push_cast
  rfl

theorem nnnorm_padic_ratCast_eq_one {x : ℚ} (hx : x ≠ 0) (h : padicValRat q x = 0) :
    ‖(x : ℚ_[q])‖₊ = 1 := by
  rw [nnnorm_padic_ratCast_eq_zpow q hx, h, neg_zero, zpow_zero]

theorem nnnorm_padic_ratCast_lt_one {x : ℚ} (hx : x ≠ 0) (h : 0 < padicValRat q x) :
    ‖(x : ℚ_[q])‖₊ < 1 := by
  rw [nnnorm_padic_ratCast_eq_zpow q hx]
  have hlt := zpow_lt_zpow_right₀ (one_lt_q_nnreal q)
    (show -padicValRat q x < 0 by omega)
  simpa using hlt

theorem one_lt_nnnorm_padic_ratCast {x : ℚ} (hx : x ≠ 0) (h : padicValRat q x < 0) :
    1 < ‖(x : ℚ_[q])‖₊ := by
  rw [nnnorm_padic_ratCast_eq_zpow q hx]
  have hlt := zpow_lt_zpow_right₀ (one_lt_q_nnreal q)
    (show (0 : ℤ) < -padicValRat q x by omega)
  simpa using hlt

end TateLocalGlobalS17

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_c₄ map map_Δ Δ c₄"
p2m_open "WeierstrassCurve"

namespace ModelTateS17

open TateLocalGlobalS17

variable (W : WeierstrassCurve ℤ) (ℓ : ℕ) [Fact ℓ.Prime]

omit [Fact ℓ.Prime] in
theorem c₄_ne_zero_of_not_dvd (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) : W.c₄ ≠ 0 :=
  fun h => hndvd (h ▸ dvd_zero _)

omit [Fact ℓ.Prime] in
theorem padicValRat_intCast_c₄_eq_zero (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    padicValRat ℓ (W.c₄ : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hndvd, Nat.cast_zero]

theorem one_le_padicValInt_Δ (hΔ : W.Δ ≠ 0) (hdvd : (ℓ : ℤ) ∣ W.Δ) :
    1 ≤ padicValInt ℓ W.Δ := by
  rcases (padicValInt_dvd_iff (p := ℓ) 1 W.Δ).mp (by rwa [pow_one]) with h | h
  · exact absurd h hΔ
  · exact h

theorem padicValRat_intCast_Δ_pos (hΔ : W.Δ ≠ 0) (hdvd : (ℓ : ℤ) ∣ W.Δ) :
    0 < padicValRat ℓ (W.Δ : ℚ) := by
  rw [padicValRat.of_int]
  have h1 := one_le_padicValInt_Δ W ℓ hΔ hdvd
  omega

theorem padicValRat_intCast_c₄_pow_three_div_Δ (hΔ : W.Δ ≠ 0) (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    padicValRat ℓ ((W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ)) = -padicValRat ℓ (W.Δ : ℚ) := by
  have hc₄ : (W.c₄ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (c₄_ne_zero_of_not_dvd W ℓ hndvd)
  have hΔ' : (W.Δ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hΔ
  rw [padicValRat.div (pow_ne_zero 3 hc₄) hΔ', padicValRat.pow _,
    padicValRat_intCast_c₄_eq_zero W ℓ hndvd]
  ring

theorem nnnorm_padic_intCast_c₄_eq_one (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    ‖((W.c₄ : ℚ) : ℚ_[ℓ])‖₊ = 1 :=
  nnnorm_padic_ratCast_eq_one ℓ (Int.cast_ne_zero.mpr (c₄_ne_zero_of_not_dvd W ℓ hndvd))
    (padicValRat_intCast_c₄_eq_zero W ℓ hndvd)

theorem one_lt_nnnorm_padic_intCast_c₄_pow_three_div_Δ (hΔ : W.Δ ≠ 0)
    (hdvd : (ℓ : ℤ) ∣ W.Δ) (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    1 < ‖(((W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) : ℚ) : ℚ_[ℓ])‖₊ := by
  have hc₄ : (W.c₄ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (c₄_ne_zero_of_not_dvd W ℓ hndvd)
  have hΔ' : (W.Δ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hΔ
  have hval : padicValRat ℓ ((W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ)) < 0 := by
    rw [padicValRat_intCast_c₄_pow_three_div_Δ W ℓ hΔ hndvd]
    have hpos := padicValRat_intCast_Δ_pos W ℓ hΔ hdvd
    omega
  exact one_lt_nnnorm_padic_ratCast ℓ (div_ne_zero (pow_ne_zero 3 hc₄) hΔ') hval

omit [Fact ℓ.Prime] in
theorem map_ratCast_c₄ : (W.map (Int.castRingHom ℚ)).c₄ = (W.c₄ : ℚ) := by
  rw [WeierstrassCurve.map_c₄, eq_intCast]

omit [Fact ℓ.Prime] in
theorem map_ratCast_Δ : (W.map (Int.castRingHom ℚ)).Δ = (W.Δ : ℚ) := by
  rw [WeierstrassCurve.map_Δ, eq_intCast]

end ModelTateS17

end WeierstrassCurve

open WeierstrassCurve.ModelTateS17 TateLocalGlobalS17 in
theorem solution (W : WeierstrassCurve ℤ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hΔ : W.Δ ≠ 0) (hdvd : (ℓ : ℤ) ∣ W.Δ) (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    ∃ qT : ℚ_[ℓ], qT ≠ 0 ∧ ‖qT‖₊ < 1 ∧
      (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[ℓ])
            * (TateCurve.curve qT).Δ ∧
      ‖qT‖₊ = ((ℓ : ℝ≥0) ^ padicValInt ℓ W.Δ)⁻¹ := by
  have hj : 1 < ‖(((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) :
      ℚ_[ℓ])‖₊ := by
    rw [map_ratCast_c₄, map_ratCast_Δ]
    exact one_lt_nnnorm_padic_intCast_c₄_pow_three_div_Δ W ℓ hΔ hdvd hndvd
  obtain ⟨qT, hqT0, hqT1, _hqTnorm, hjeq⟩ :=
    TateCurve.exists_tateParameter
      (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[ℓ]) hj
  have hcube := TateCurve.c₄_pow_eq_of_curve_j_eq hqT0 hqT1 hjeq
  refine ⟨qT, hqT0, hqT1, hcube, ?_⟩

  have hΔ' : (W.Δ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hΔ
  have hcross : ((W.Δ : ℚ) : ℚ_[ℓ]) * (TateCurve.curve qT).c₄ ^ 3
      = ((W.c₄ : ℚ) : ℚ_[ℓ]) ^ 3 * (TateCurve.curve qT).Δ := by
    have h := hcube
    rw [map_ratCast_c₄, map_ratCast_Δ] at h
    rw [h]
    push_cast
    field_simp
  have key : ‖((W.Δ : ℚ) : ℚ_[ℓ]) * (TateCurve.curve qT).c₄ ^ 3‖₊
      = ‖((W.c₄ : ℚ) : ℚ_[ℓ]) ^ 3 * (TateCurve.curve qT).Δ‖₊ := by rw [hcross]
  rw [nnnorm_mul, nnnorm_mul, nnnorm_pow, nnnorm_pow, TateCurve.nnnorm_c₄ hqT1,
    TateCurve.nnnorm_Δ hqT0 hqT1, nnnorm_padic_intCast_c₄_eq_one W ℓ hndvd,
    one_pow, mul_one, one_mul] at key
  rw [← key, nnnorm_padic_ratCast_eq_zpow ℓ (Int.cast_ne_zero.mpr hΔ), padicValRat.of_int,
    zpow_neg, zpow_natCast]

end S_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr
end P2MW
export P2MW.S_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr (solution)
