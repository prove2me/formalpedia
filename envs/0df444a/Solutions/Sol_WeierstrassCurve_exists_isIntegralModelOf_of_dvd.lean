-- Prove2me | solution 1 for WeierstrassCurve.exists_isIntegralModelOf_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e62762e7-64c5-5cb6-bf7e-98d1892187b5

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isIntegralModelOf_of_dvd

open WeierstrassCurve

namespace LayerESol

section E3

variable {W W' : WeierstrassCurve ℤ} {n : ℤ}

private theorem b₂_modEq_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n]) :
    W'.b₂ ≡ W.b₂ [ZMOD n] :=
  (h₁.pow 2).add (h₂.mul_left 4)

private theorem b₄_modEq_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n])
    (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) : W'.b₄ ≡ W.b₄ [ZMOD n] :=
  (h₄.mul_left 2).add (h₁.mul h₃)

private theorem b₆_modEq_of_modEq (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n]) :
    W'.b₆ ≡ W.b₆ [ZMOD n] :=
  (h₃.pow 2).add (h₆.mul_left 4)

private theorem b₈_modEq_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n])
    (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n]) :
    W'.b₈ ≡ W.b₈ [ZMOD n] :=
  (((((h₁.pow 2).mul h₆).add ((h₂.mul_left 4).mul h₆)).sub ((h₁.mul h₃).mul h₄)).add
    (h₂.mul (h₃.pow 2))).sub (h₄.pow 2)

theorem c4_modEq_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n])
    (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) :
    W'.c₄ ≡ W.c₄ [ZMOD n] :=
  ((b₂_modEq_of_modEq h₁ h₂).pow 2).sub ((b₄_modEq_of_modEq h₁ h₃ h₄).mul_left 24)

theorem c6_modEq_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n])
    (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n]) :
    W'.c₆ ≡ W.c₆ [ZMOD n] :=
  ((((b₂_modEq_of_modEq h₁ h₂).pow 3).neg).add
    (((b₂_modEq_of_modEq h₁ h₂).mul_left 36).mul (b₄_modEq_of_modEq h₁ h₃ h₄))).sub
    ((b₆_modEq_of_modEq h₃ h₆).mul_left 216)

theorem Delta_modEq_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n])
    (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n]) :
    W'.Δ ≡ W.Δ [ZMOD n] :=
  have hb₂ := b₂_modEq_of_modEq h₁ h₂
  have hb₄ := b₄_modEq_of_modEq h₁ h₃ h₄
  have hb₆ := b₆_modEq_of_modEq h₃ h₆
  have hb₈ := b₈_modEq_of_modEq h₁ h₂ h₃ h₄ h₆
  ((((hb₂.pow 2).neg.mul hb₈).sub ((hb₄.pow 3).mul_left 8)).sub ((hb₆.pow 2).mul_left 27)).add
    (((hb₂.mul_left 9).mul hb₄).mul hb₆)

theorem not_dvd_c4_of_dvd_Delta_iff_of_modEq {p : ℤ} (h₁ : W'.a₁ ≡ W.a₁ [ZMOD p])
    (h₂ : W'.a₂ ≡ W.a₂ [ZMOD p]) (h₃ : W'.a₃ ≡ W.a₃ [ZMOD p]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD p])
    (h₆ : W'.a₆ ≡ W.a₆ [ZMOD p]) :
    (p ∣ W'.Δ → ¬ p ∣ W'.c₄) ↔ (p ∣ W.Δ → ¬ p ∣ W.c₄) := by
  rw [(Delta_modEq_of_modEq h₁ h₂ h₃ h₄ h₆).dvd_iff, (c4_modEq_of_modEq h₁ h₂ h₃ h₄).dvd_iff]

theorem Delta_ne_zero_of_modEq (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n])
    (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n])
    (hn : ¬ n ∣ W.Δ) : W'.Δ ≠ 0 := fun h0 =>
  hn (((Delta_modEq_of_modEq h₁ h₂ h₃ h₄ h₆).dvd_iff).mp (h0 ▸ dvd_zero n))

end E3

section E5

theorem exists_variableChange_eq_shortModel {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, C • W = ⟨0, 0, 0, -27 * W.c₄, -54 * W.c₆⟩ := by
  haveI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : K) := invertibleOfNonzero (by norm_num)
  obtain ⟨C₀, hC₀⟩ := W.exists_variableChange_isShortNF
  set S := C₀ • W with hS
  haveI := hC₀

  have h4 : S.a₄ = -((C₀.u : K)⁻¹) ^ 4 * W.c₄ / 48 := by
    have h := S.c₄_of_isShortNF
    rw [hS, variableChange_c₄, Units.val_inv_eq_inv_val] at h
    rw [hS]
    linear_combination h / 48
  have h6 : S.a₆ = -((C₀.u : K)⁻¹) ^ 6 * W.c₆ / 864 := by
    have h := S.c₆_of_isShortNF
    rw [hS, variableChange_c₆, Units.val_inv_eq_inv_val] at h
    rw [hS]
    linear_combination h / 864
  have h6u : (6 : K) ≠ 0 := by norm_num

  refine ⟨⟨(Units.mk0 (6 : K) h6u * C₀.u)⁻¹, 0, 0, 0⟩ * C₀, ?_⟩
  rw [mul_smul, ← hS]
  ext
  · simp [variableChange_a₁]
  · simp [variableChange_a₂]
  · simp [variableChange_a₃]
  · rw [variableChange_a₄, S.a₁_of_isShortNF, S.a₂_of_isShortNF, S.a₃_of_isShortNF, h4, inv_inv,
      Units.val_mul, Units.val_mk0]
    field_simp
    ring
  · rw [variableChange_a₆, S.a₁_of_isShortNF, S.a₂_of_isShortNF, S.a₃_of_isShortNF, h6, inv_inv,
      Units.val_mul, Units.val_mk0]
    field_simp
    ring

theorem exists_variableChange_of_c4_eq_of_c6_eq {K : Type*} [Field K] [CharZero K]
    {W W' : WeierstrassCurve K} (u : K) (hu : u ≠ 0) (h₄ : W.c₄ = u ^ 4 * W'.c₄)
    (h₆ : W.c₆ = u ^ 6 * W'.c₆) : ∃ C : VariableChange K, C • W = W' := by
  obtain ⟨C₁, hC₁⟩ := exists_variableChange_eq_shortModel W
  obtain ⟨C₂, hC₂⟩ := exists_variableChange_eq_shortModel W'
  refine ⟨C₂⁻¹ * ⟨Units.mk0 u hu, 0, 0, 0⟩ * C₁, ?_⟩
  rw [mul_smul, mul_smul, hC₁, inv_smul_eq_iff, hC₂, h₄, h₆]
  ext
  · simp [variableChange_a₁]
  · simp [variableChange_a₂]
  · simp [variableChange_a₃]
  · rw [variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  · rw [variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring

theorem exists_model_c4_eq_c6_eq_of_dvd (W : WeierstrassCurve ℤ) (c₄' c₆' n : ℤ)
    (h₄ : 1728 * n ∣ W.c₄ - c₄') (h₆ : 1728 * n ∣ W.c₆ - c₆') :
    ∃ W' : WeierstrassCurve ℤ, W'.a₁ = W.a₁ ∧ W'.a₂ = W.a₂ ∧ W'.a₃ = W.a₃ ∧
      W'.a₄ ≡ W.a₄ [ZMOD n] ∧ W'.a₆ ≡ W.a₆ [ZMOD n] ∧ W'.c₄ = c₄' ∧ W'.c₆ = c₆' := by
  obtain ⟨k₄, hk₄⟩ := h₄
  obtain ⟨k₆, hk₆⟩ := h₆
  refine ⟨⟨W.a₁, W.a₂, W.a₃, W.a₄ + 36 * n * k₄,
    W.a₆ + n * (3 * (W.a₁ ^ 2 + 4 * W.a₂) * k₄ + 2 * k₆)⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-(36 * k₄), by ring⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-(3 * (W.a₁ ^ 2 + 4 * W.a₂) * k₄ + 2 * k₆), by ring⟩
  · simp only [c₄, b₂, b₄] at hk₄ ⊢
    linear_combination hk₄
  · simp only [c₆, b₂, b₄, b₆] at hk₆ ⊢
    linear_combination hk₆

end E5

theorem exists_isIntegralModelOf_of_dvd (W : WeierstrassCurve ℤ) (A B n : ℤ)
    (hA : 46656 * n ∣ A + 27 * W.c₄) (hB : 93312 * n ∣ B + 54 * W.c₆) :
    ∃ W' : WeierstrassCurve ℤ, W'.IsIntegralModelOf ⟨0, 0, 0, A, B⟩ ∧
      W'.a₁ = W.a₁ ∧ W'.a₂ = W.a₂ ∧ W'.a₃ = W.a₃ ∧ W'.a₄ ≡ W.a₄ [ZMOD n] ∧ W'.a₆ ≡ W.a₆ [ZMOD n] ∧
      -27 * W'.c₄ = A ∧ -54 * W'.c₆ = B := by
  obtain ⟨k₄, hk₄⟩ := hA
  obtain ⟨k₆, hk₆⟩ := hB
  obtain ⟨W', h₁, h₂, h₃, h₄, h₆, hc₄, hc₆⟩ :=
    exists_model_c4_eq_c6_eq_of_dvd W (W.c₄ - 1728 * n * k₄) (W.c₆ - 1728 * n * k₆) n
      ⟨k₄, by ring⟩ ⟨k₆, by ring⟩
  have hA' : -27 * W'.c₄ = A := by rw [hc₄]; linear_combination -hk₄
  have hB' : -54 * W'.c₆ = B := by rw [hc₆]; linear_combination -hk₆
  refine ⟨W', ?_, h₁, h₂, h₃, h₄, h₆, hA', hB'⟩

  refine exists_variableChange_of_c4_eq_of_c6_eq (6 : ℚ) (by norm_num) ?_ ?_
  · rw [map_c₄, eq_intCast, show ((W'.c₄ : ℤ) : ℚ) = -(A : ℚ) / 27 by
      rw [← hA']; push_cast; ring]
    simp only [c₄, b₂, b₄]
    ring
  · rw [map_c₆, eq_intCast, show ((W'.c₆ : ℤ) : ℚ) = -(B : ℚ) / 54 by
      rw [← hB']; push_cast; ring]
    simp only [c₆, b₂, b₄, b₆]
    ring

theorem isSemistableModel_of_modEq {W W' : WeierstrassCurve ℤ} {n : ℤ} (hW : W.IsSemistableModel)
    (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n]) (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n])
    (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n])
    (haway : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ n → (p : ℤ) ∣ W'.c₄ → ¬ (p : ℤ) ∣ W'.c₆) :
    W'.IsSemistableModel := by
  intro p hp hpΔ hpc₄
  by_cases hpn : (p : ℤ) ∣ n
  · have key := (not_dvd_c4_of_dvd_Delta_iff_of_modEq (h₁.of_dvd hpn) (h₂.of_dvd hpn) (h₃.of_dvd hpn)
      (h₄.of_dvd hpn) (h₆.of_dvd hpn)).mpr (hW p hp)
    exact key hpΔ hpc₄
  · have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    refine haway p hp hpn hpc₄ (hpZ.dvd_of_dvd_pow (n := 2) ?_)
    have hrel := W'.c_relation
    rw [show W'.c₆ ^ 2 = W'.c₄ ^ 3 - 1728 * W'.Δ by linear_combination hrel]
    exact dvd_sub (dvd_pow hpc₄ three_ne_zero) (hpΔ.mul_left 1728)

end LayerESol

theorem solution (W : WeierstrassCurve ℤ) (A B n : ℤ) (hA : 46656 * n ∣ A + 27 * W.c₄) (hB : 93312 * n ∣ B + 54 * W.c₆) : ∃ W' : WeierstrassCurve ℤ, W'.IsIntegralModelOf ⟨0, 0, 0, A, B⟩ ∧ W'.a₁ = W.a₁ ∧ W'.a₂ = W.a₂ ∧ W'.a₃ = W.a₃ ∧ W'.a₄ ≡ W.a₄ [ZMOD n] ∧ W'.a₆ ≡ W.a₆ [ZMOD n] ∧ -27 * W'.c₄ = A ∧ -54 * W'.c₆ = B :=
  LayerESol.exists_isIntegralModelOf_of_dvd W A B n hA hB

end S_WeierstrassCurve_exists_isIntegralModelOf_of_dvd
end P2MW
export P2MW.S_WeierstrassCurve_exists_isIntegralModelOf_of_dvd (solution)
