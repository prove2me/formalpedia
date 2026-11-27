-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeSlabBound_proof_1984d2802da4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:37.668803+00:00
-- url     : https://prove2.me/submissions/6c495df9-b9ca-4e41-a129-9ad2d9a4a43f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietySlabMeasure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSlabBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_proof_5269562464a9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeSlabBound
theorem _root_.solution (hV : VarietySlabMeasure.Statement) : ConeSlabBound.Statement := by
  intro n e h W f u hW hf hu
  have hWp : W.IsPrime := hW.isPrime
  have hdim := ChowFormDimLe.proof ℂ n (e + 1) W f hW hf

  let E := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let F : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ h.matᵀ.mulVecLin ∘ₗ E.toLinearMap)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ (h.matᵀ)⁻¹.mulVecLin ∘ₗ E.toLinearMap)
  have hF : ∀ y i, F y i = h.pointOf y i := fun _ _ => rfl
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hLF : ∀ y, L (F y) = y := by
    intro y
    ext i
    change ((h.matᵀ)⁻¹ *ᵥ (h.matᵀ *ᵥ fun j => y j)) i = y i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  obtain ⟨C, α, hC, hα, hb⟩ := hV n (e + 1) W u hWp hdim hu ‖F‖
  set s : ℝ := ((2 * (e + 1) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  let K : ℝ≥0 := ‖L‖₊
  refine ⟨(K : ℝ) ^ s * C, α, hα, fun ε hε hε1 => ?_⟩

  have hsub : coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖} ⊆
      L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    rintro y ⟨⟨hy1, hyW⟩, hyu⟩
    refine ⟨F y, ⟨fun q hq => ?_, ?_, ?_⟩, hLF y⟩
    · have : (fun i => F y i) = h.pointOf y := funext (hF y)
      rw [this]
      exact hyW q hq
    · calc ‖F y‖ ≤ ‖F‖ * ‖y‖ := F.le_opNorm y
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hy1.le (norm_nonneg _)
        _ = ‖F‖ := mul_one _
    · simp only [hF]
      calc ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ := hyu
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hy1.le hε.le
        _ = ε := mul_one _
  calc μH[s] (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖})
      ≤ μH[s] (L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε}) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ s * μH[s] {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} :=
        L.lipschitz.hausdorffMeasure_image_le hs0 _
    _ ≤ (K : ℝ≥0∞) ^ s * ENNReal.ofReal (C * ε ^ α) := by
        gcongr
        exact hb ε hε hε1
    _ = ENNReal.ofReal ((K : ℝ) ^ s * C * ε ^ α) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg K.coe_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg K.coe_nonneg hs0, ENNReal.ofReal_coe_nnreal]
end ConeSlabBound
end GroundTheory.Heights₂.Heights
