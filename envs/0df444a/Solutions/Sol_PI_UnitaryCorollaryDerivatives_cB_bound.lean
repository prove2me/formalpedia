-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cB_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:54.924945+00:00
-- url     : https://prove2.me/submissions/1e2e8cb3-a86c-4223-aec6-0071f3efef30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_curve
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_mx_le
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_unitLie
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_wP
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_len_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sub_LR
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dw_expmul
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_bound


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
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (hP : PolyB) (hC : DjCurve) {k j ρ κ : ℕ} {P : B.Mat k (j + ρ) → ℂ} (hPd : IsPolyDeg κ P)
    (a b n : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u →
      unitP k j ρ v → u.length + v.length ≤ n → ∀ g ∈ B.GV k (j + ρ), δ ≤ ‖DjU k j ρ g‖ →
        ‖Dw (wL u ++ wR v) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) g‖ ≤
          C * B.gN g ^ (κ : ℝ) := by
  obtain ⟨hPs, hWB⟩ := hP k (j + ρ) κ P hPd
  obtain ⟨CP, hCP⟩ := hWB n
  obtain ⟨lam, hlam⟩ := cB_curve hC k j ρ a b
  set Λ : ℝ := ((a + b : ℕ) : ℝ) * j with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨(1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|), by positivity, ?_⟩
  intro u v hu hv hl g hg hDg
  have hw := cB_wP hu hv
  have e : (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) =
      fun g => hhF k j ρ a b g • P g := by
    funext g; simp only [hhF, smul_eq_mul]; ring
  rw [e, cA_Dw_expmul lam (hhF k j ρ a b) _ P hPs (fun x hx g t => (hlam x (hw x hx).1).2 g t), norm_smul]
  have hp := gN_pos hg
  have hD0 : 0 < ‖DjU k j ρ g‖ := lt_of_lt_of_le hδ hDg
  have hh : ‖hhF k j ρ a b g‖ ≤ δ⁻¹ ^ (a + b) := by
    unfold hhF
    rw [norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_star, pow_add]
    have : ‖DjU k j ρ g‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hDg
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) this a) (pow_le_pow_left₀ (by positivity) this b)
      (by positivity) (by positivity)
  have hb := cA_Dwl_bound lam hΛ0 g (|CP| * B.gN g ^ (κ : ℝ)) (wL u ++ wR v) P hPs
    (fun x hx => (hlam x (hw x hx).1).1.trans (by
      have := cB_mx_le (hw x hx).2
      calc ((a + b : ℕ) : ℝ) * j * mx x.2 ≤ ((a + b : ℕ) : ℝ) * j * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Λ := by rw [mul_one]))
    (by
      intro s hs
      obtain ⟨u', v', hu', hv', rfl⟩ := sub_LR hs
      rw [← dLR_eq]
      have := hCP u' v' (fun X hX => cB_unitLie hu X (hu'.subset hX)) (fun X hX => cB_unitLie hv X (hv'.subset hX))
        (by have := hu'.length_le; have := hv'.length_le; omega) g hg
      simp only [List.map_append, List.map_const', List.sum_append, Nat.cast_add] at this
      refine this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) |>.trans_eq ?_
      congr 2
      simp)
  have hpow : (1 + Λ) ^ (wL u ++ wR v).length ≤ (1 + Λ) ^ n := by
    rw [len_LR]; exact pow_le_pow_right₀ (by linarith) hl
  calc ‖hhF k j ρ a b g‖ * ‖Dwl lam (wL u ++ wR v) P g‖
      ≤ δ⁻¹ ^ (a + b) * ((1 + Λ) ^ n * (|CP| * B.gN g ^ (κ : ℝ))) :=
        mul_le_mul hh (hb.trans (mul_le_mul_of_nonneg_right hpow (by positivity))) (norm_nonneg _) (by positivity)
    _ = (1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|) * B.gN g ^ (κ : ℝ) := by ring
end PI.UnitaryCorollaryDerivatives
