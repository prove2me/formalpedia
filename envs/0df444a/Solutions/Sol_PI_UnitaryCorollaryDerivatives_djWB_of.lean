-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.djWB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:03.679816+00:00
-- url     : https://prove2.me/submissions/59d22c43-e789-4092-a84e-907dda6acb30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_MxLeOne
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_mx_le_one
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_dw_dj
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_len_LR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (h1 : DjCurve) (h2 : PolyB) (h3 : DjPoly) (h4 : CompC) : DjWB := by
  intro k j ρ χ n hχ
  obtain ⟨hcD, hB⟩ := h2 k (j + ρ) j (DjU k j ρ) (h3 k j ρ)
  obtain ⟨CP, hCP⟩ := hB n
  refine ⟨hχ.1.comp hcD, ?_⟩
  obtain ⟨R, hR⟩ := (hχ.2.1 : IsCompact (tsupport χ)).isBounded.exists_norm_le
  refine h4 k (j + ρ) (DjU k j ρ) χ (costP k j ρ) n (|CP| + (max 1 (j : ℝ)) ^ n * |R|) hcD hχ.1 hχ.2.1 ?_
  intro u v hu hv hl hne g hg hgs
  have hg1 := gN_ge_one hg
  have hS0 : (0 : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ |CP| := abs_nonneg _
  have hBn : 0 ≤ (max 1 (j : ℝ)) ^ n * |R| := by positivity
  by_cases hall : ∀ X ∈ u ++ v, inLieP k j ρ X
  ·
    have hw : ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1 := by
      intro x hx
      simp only [wL, wR, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact ⟨hall X (List.mem_append_left _ hX), mx_le_one (hu X hX)⟩
      · exact ⟨hall X (List.mem_append_right _ hX), mx_le_one (hv X hX)⟩
    obtain ⟨K, hK, hD⟩ := dw_dj h1 k j ρ _ hw
    rw [dLR_eq, hD g, norm_mul]
    have hlen : (wL u ++ wR v).length ≤ n := by rw [len_LR]; exact hl
    have hK' : ‖K‖ ≤ (max 1 (j : ℝ)) ^ n :=
      hK.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hlen))
    have hDR : ‖DjU k j ρ g‖ ≤ |R| := (hR _ hgs).trans (le_abs_self _)
    have h1' : 1 ≤ B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Real.one_le_rpow hg1 hS0
    calc ‖K‖ * ‖DjU k j ρ g‖ ≤ (max 1 (j : ℝ)) ^ n * |R| :=
          mul_le_mul hK' hDR (norm_nonneg _) (by positivity)
      _ ≤ (|CP| + (max 1 (j : ℝ)) ^ n * |R|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1' (by positivity)
  · obtain ⟨X, hX, hXP⟩ : ∃ X ∈ u ++ v, ¬ inLieP k j ρ X := by
      by_contra hc; exact hall (fun X hX => by by_contra h; exact hc ⟨X, hX, h⟩)
    have hcX : costP k j ρ X = j := by simp [costP, hXP]
    have hjS : (j : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := costP k j ρ) hX)
      rw [hcX] at this; exact_mod_cast this
    have hb := hCP u v hu hv hl g hg
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero, add_zero] at hb
    calc ‖B.dLR u v (DjU k j ρ) g‖ ≤ CP * B.gN g ^ (j : ℝ) := hb
      _ ≤ |CP| * B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) :=
          mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hg1 hjS) (by positivity) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end PI.UnitaryCorollaryDerivatives
