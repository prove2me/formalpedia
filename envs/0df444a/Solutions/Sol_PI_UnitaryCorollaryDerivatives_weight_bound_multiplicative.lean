-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.weight_bound_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:28.47114+00:00
-- url     : https://prove2.me/submissions/d8dceeb7-a558-46cd-9563-6d5fdd91d3e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_Dw_clm
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_ckOn_of_contDiff
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_sum_cost_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_leib_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_len_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sub_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_unit_lie


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
theorem _root_.solution : WBmul := by
  intro k r φ₁ φ₂ c₁ c₂ n C₁ C₂ e₁ e₂ h₁ h₂ hw₁ hw₂
  refine ⟨2 ^ n * (|C₁| * |C₂|), fun u v hu hv hl g hg => ?_⟩
  set a : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun h => ContinuousLinearMap.mul ℂ ℂ (φ₁ h) with ha
  have hfun : (fun h => φ₁ h * φ₂ h) = ap a φ₂ := by funext h; simp [ap, ha]
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hca : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a :=
    ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).contDiff.comp h₁
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) ((wL u ++ wR v).length : ℕ) a φ₂ :=
    ⟨ckOn_of_contDiff hca, ckOn_of_contDiff h₂, fun _ _ h => absurd h (Set.notMem_empty _)⟩
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  set S : ℝ := (((u ++ v).map c₁).sum : ℝ) with hS
  set T : ℝ := (((u ++ v).map c₂).sum : ℝ) with hT
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg
    (|C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T))) (wL u ++ wR v) a φ₂ hlie hP (by
      intro w₁ w₂ hs₁ hs₂ _
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
      have hl₁ : u₁.length + v₁.length ≤ n := by
        have := hu₁.length_le; have := hv₁.length_le; omega
      have hl₂ : u₂.length + v₂.length ≤ n := by
        have := hu₂.length_le; have := hv₂.length_le; omega
      have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
      have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
      have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
      have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
      have ea : Dw (wL u₁ ++ wR v₁) a g = ContinuousLinearMap.mul ℂ ℂ (Dw (wL u₁ ++ wR v₁) φ₁ g) :=
        Dw_clm (ContinuousLinearMap.mul ℂ ℂ) _ (lie_LR (unit_lie hu₁') (unit_lie hv₁'))
          (ckOn_of_contDiff h₁) g hg
      have b1 : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ |C₁| * B.gN g ^ (e₁ + S) := by
        rw [ea]
        refine (ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans ?_
        rw [← dLR_eq]
        refine (hw₁ u₁ v₁ hu₁' hv₁' hl₁ g hg).trans ?_
        refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith [sum_cost_le c₁ hu₁ hv₁])
      have b2 : ‖Dw (wL u₂ ++ wR v₂) φ₂ g‖ ≤ |C₂| * B.gN g ^ (e₂ + T) := by
        rw [← dLR_eq]
        refine (hw₂ u₂ v₂ hu₂' hv₂' hl₂ g hg).trans ?_
        refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith [sum_cost_le c₂ hu₂ hv₂])
      calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) φ₂ g‖
          ≤ (|C₁| * B.gN g ^ (e₁ + S)) * (|C₂| * B.gN g ^ (e₂ + T)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
        _ = |C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T)) := by
            rw [show e₁ + e₂ + (S + T) = (e₁ + S) + (e₂ + T) by ring, Real.rpow_add hp (e₁ + S) (e₂ + T)]; ring)
  have hST : ((((u ++ v).map (c₁ + c₂)).sum : ℕ) : ℝ) = S + T := by
    rw [hS, hT, ← Nat.cast_add, ← List.sum_map_add]; rfl
  rw [hfun, dLR_eq, hST]
  have hpow : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := by
    rw [len_LR]; exact pow_le_pow_right₀ (by norm_num) hl
  calc ‖Dw (wL u ++ wR v) (ap a φ₂) g‖ ≤ 2 ^ (wL u ++ wR v).length * (|C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T))) := hb
    _ ≤ 2 ^ n * (|C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 ^ n * (|C₁| * |C₂|) * B.gN g ^ (e₁ + e₂ + (S + T)) := by ring
end PI.UnitaryCorollaryDerivatives
