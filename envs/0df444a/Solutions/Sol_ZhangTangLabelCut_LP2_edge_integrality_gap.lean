-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.edge_integrality_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T21:35:50.144074+00:00
-- url     : https://prove2.me/submissions/415d9d36-0947-4f0c-b928-675fda4217bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Theorems.Thm_ZhangTangLabelCut_LP2_large_integral_optimum
import Theorems.Thm_ZhangTangLabelCut_LP2_fractional_optimum_le_k

open ZhangTangLabelCut.LP2

private lemma shutterVertex_card_ge (k D : ℕ) (hk : 2 ≤ k) :
    k ^ (2 + 3 * D) ≤ Fintype.card (ShutterVertex k (32 * k ^ (2 * D)) (k ^ D)) := by
  set d := 32 * k ^ (2 * D)
  set h := k ^ D
  let inj : Fin (k / 2) × Fin (k / 2) × Fin h × Fin d → ShutterVertex k d h :=
    fun ⟨a, b, i, j⟩ =>
      Sum.inr
        ((⟨(⟨a.1, by omega⟩, ⟨b.1 + k / 2, by omega⟩), by
            change a.1 < b.1 + k / 2
            omega⟩,
          i),
         Sum.inr (j, true))
  have hinj : Function.Injective inj := by
    rintro ⟨a₁, b₁, i₁, j₁⟩ ⟨a₂, b₂, i₂, j₂⟩ h_eq
    simp only [inj, Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at h_eq
    rcases h_eq with ⟨⟨⟨ha, hb⟩, rfl⟩, rfl, -⟩
    have ha' : a₁ = a₂ := Fin.ext ha
    have hb' : b₁ = b₂ := Fin.ext (by omega)
    subst ha' hb'
    rfl
  have h_card := Fintype.card_le_of_injective inj hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at h_card
  have hk_div : k ≤ 3 * (k / 2) := by omega
  have hk_sq : k ^ 2 ≤ 32 * (k / 2) * (k / 2) := by nlinarith
  have h_pow_split : k ^ (2 + 3 * D) = k ^ 2 * (k ^ D * k ^ (2 * D)) := by
    calc k ^ (2 + 3 * D)
      _ = k ^ (2 + (D + 2 * D)) := by congr 1; omega
      _ = k ^ 2 * (k ^ D * k ^ (2 * D)) := by rw [pow_add, pow_add]
  have h_rhs_eq :
      k / 2 * (k / 2 * (h * d)) = (32 * (k / 2) * (k / 2)) * (k ^ D * k ^ (2 * D)) := by
    dsimp [h, d]
    ring
  have h_le : k ^ (2 + 3 * D) ≤ k / 2 * (k / 2 * (h * d)) := by
    rw [h_pow_split, h_rhs_eq]
    exact Nat.mul_le_mul_right (k ^ D * k ^ (2 * D)) hk_sq
  exact le_trans h_le h_card

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, 1 ≤ M₀ ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ directed : Bool, ∃ I : LabelCut,
        I.graph.directed = directed ∧ I.Admissible ∧
        1 ≤ Fintype.card I.graph.E ∧ Fintype.card I.graph.E ≤ M ∧
        C * (M : ℝ) ^ (1 / 3 - ε) ≤ I.ratio := by
  let ε' : ℝ := min ε (1 / 3)
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le_third : ε' ≤ 1 / 3 := min_le_right ε (1 / 3)
  have hε'_le_ε : ε' ≤ ε := min_le_left ε (1 / 3)
  have h_exp_nonneg : 0 ≤ 1 / 3 - ε' := by linarith
  have h_exp_le : 1 / 3 - ε ≤ 1 / 3 - ε' := by linarith
  rcases large_integral_optimum ε' hε'_pos with ⟨D, hD, C₀, hC₀, k₀, hk₀, h_large⟩
  let m : ℕ := 2 + 3 * D
  have hm_pos : 1 ≤ m := by dsimp [m]; omega
  let K : ℝ := 64 * (2 : ℝ) ^ m
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  let C : ℝ := C₀ / K ^ (1 / 3 - ε')
  have hC_pos : 0 < C := div_pos hC₀ (Real.rpow_pos_of_pos hK_pos _)
  let M₀ : ℕ := 64 * k₀ ^ m
  have hM₀_ge : 1 ≤ M₀ := by
    have hk₀_pow : 1 ≤ k₀ ^ m := Nat.one_le_pow m k₀ (by omega)
    dsimp [M₀]
    omega
  refine ⟨C, hC_pos, M₀, hM₀_ge, ?_⟩
  intro M hM directed
  classical
  have h_ex : ∃ j : ℕ, M < 64 * (j + 1) ^ m := by
    refine ⟨M, ?_⟩
    have h1 : M + 1 ≤ (M + 1) ^ m := Nat.le_self_pow (by omega) (M + 1)
    omega
  let k : ℕ := Nat.find h_ex
  have hk_upper : M < 64 * (k + 1) ^ m := Nat.find_spec h_ex
  have hk_ge_k₀ : k₀ ≤ k := by
    by_contra h_lt
    have hk1_le : k + 1 ≤ k₀ := by omega
    have h_pow_le : (k + 1) ^ m ≤ k₀ ^ m := Nat.pow_le_pow_left hk1_le m
    have : 64 * (k + 1) ^ m ≤ M := le_trans (Nat.mul_le_mul_left 64 h_pow_le) hM
    omega
  have hk_ge_two : 2 ≤ k := le_trans hk₀ hk_ge_k₀
  have hk_lower : 64 * k ^ m ≤ M := by
    have hk_pred_lt : k - 1 < k := by omega
    have h_not := Nat.find_min h_ex hk_pred_lt
    have hk_sub : k - 1 + 1 = k := by omega
    rw [hk_sub] at h_not
    omega
  rcases h_large k hk_ge_k₀ directed with ⟨σ, h_adm, h_opt, _, h_E_le⟩
  let I := shutterInstance k (32 * k ^ (2 * D)) (k ^ D) directed σ
  have hd_pos : 0 < 32 * k ^ (2 * D) := by
    have : 0 < k ^ (2 * D) := pow_pos (by omega) _
    omega
  have hh_pos : 0 < k ^ D := pow_pos (by omega) _
  refine ⟨I, rfl, h_adm, ?_, ?_, ?_⟩
  · let e₀ : I.graph.E :=
      ((⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩, ⟨0, hh_pos⟩), (⟨0, hd_pos⟩, false, false))
    exact Fintype.card_pos_iff.mpr ⟨e₀⟩
  · exact le_trans h_E_le hk_lower
  · have h_V_ge : k ^ m ≤ Fintype.card I.graph.V :=
      shutterVertex_card_ge k D hk_ge_two
    have hk1_le_2k : k + 1 ≤ 2 * k := by omega
    have h_M_le_K_V_nat : M ≤ 64 * 2 ^ m * Fintype.card I.graph.V := by
      have h1 : M ≤ 64 * (k + 1) ^ m := le_of_lt hk_upper
      have h2 : (k + 1) ^ m ≤ (2 * k) ^ m := Nat.pow_le_pow_left hk1_le_2k m
      have h3 : 64 * (2 * k) ^ m = 64 * 2 ^ m * k ^ m := by
        rw [mul_pow]
        ring
      calc M ≤ 64 * (k + 1) ^ m := h1
        _ ≤ 64 * (2 * k) ^ m := Nat.mul_le_mul_left 64 h2
        _ = 64 * 2 ^ m * k ^ m := h3
        _ ≤ 64 * 2 ^ m * Fintype.card I.graph.V := Nat.mul_le_mul_left _ h_V_ge
    have h_M_le_K_V : (M : ℝ) ≤ K * (Fintype.card I.graph.V : ℝ) := by
      dsimp [K]
      exact_mod_cast h_M_le_K_V_nat
    have h_M_div_K : (M : ℝ) / K ≤ (Fintype.card I.graph.V : ℝ) := by
      rw [div_le_iff₀ hK_pos]
      linarith
    have h_M_ge_one : (1 : ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := by omega
      exact_mod_cast this
    have h_rpow_exp : (M : ℝ) ^ (1 / 3 - ε) ≤ (M : ℝ) ^ (1 / 3 - ε') :=
      Real.rpow_le_rpow_of_exponent_le h_M_ge_one h_exp_le
    have h_rpow_base :
        ((M : ℝ) / K) ^ (1 / 3 - ε') ≤ (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') :=
      Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg M) (le_of_lt hK_pos)) h_M_div_K h_exp_nonneg
    rw [Real.div_rpow (Nat.cast_nonneg M) (le_of_lt hK_pos)] at h_rpow_base
    have h_C_M_le :
        C * (M : ℝ) ^ (1 / 3 - ε) ≤ C₀ * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') := by
      calc C * (M : ℝ) ^ (1 / 3 - ε)
        _ ≤ C * (M : ℝ) ^ (1 / 3 - ε') :=
          mul_le_mul_of_nonneg_left h_rpow_exp (le_of_lt hC_pos)
        _ = C₀ * ((M : ℝ) ^ (1 / 3 - ε') / K ^ (1 / 3 - ε')) := by
          dsimp [C]
          ring
        _ ≤ C₀ * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') :=
          mul_le_mul_of_nonneg_left h_rpow_base (le_of_lt hC₀)
    rcases h_adm.2.2 with ⟨v, hv_pos, hv_eq⟩
    have h_frac_pos : 0 < I.frac := by
      unfold LabelCut.frac
      rw [hv_eq, EReal.toReal_coe]
      exact hv_pos
    have h_frac_le_k : I.frac ≤ (k : ℝ) :=
      fractional_optimum_le_k k (32 * k ^ (2 * D)) (k ^ D) hk_ge_two hd_pos hh_pos directed σ
    have h_ratio_ge :
        C₀ * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') ≤ I.ratio := by
      unfold LabelCut.ratio
      rw [le_div_iff₀ h_frac_pos]
      have h1 :
          C₀ * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') * I.frac ≤
            C₀ * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') * (k : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_frac_le_k
        exact mul_nonneg (le_of_lt hC₀) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 :
          C₀ * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') * (k : ℝ) =
            C₀ * (k : ℝ) * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε') := by ring
      linarith
    exact le_trans h_C_M_le h_ratio_ge
