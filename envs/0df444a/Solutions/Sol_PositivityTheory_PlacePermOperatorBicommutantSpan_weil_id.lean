-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.weil_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:40.109639+00:00
-- url     : https://prove2.me/submissions/e8d5bb30-8adf-41e3-a460-e6f6888e39d8

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_mul
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_U
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_D
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_fou_chiB
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_uniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (b : Rˣ) {m : ℝ} (hm : 0 < m) (hμ : ∀ s : Set (ι → R), MeasurableSet s →
      μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) =
      γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R)
        (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) := by
  have h1 := impl_mul (impl_U H b) (impl_fou_chiB H)
  have h2 := impl_mul (impl_fou_chiB H) (impl_mul (impl_U H (-((b⁻¹ : Rˣ) : R))) (impl_mul (impl_D H b⁻¹ hm hμ)
    (impl_mul (impl_fou_chiB H) (impl_U H (-((b⁻¹ : Rˣ) : R))))))
  have e : wMat * (nMat (-((b⁻¹ : Rˣ) : R)) * (mMat b⁻¹ * (wMat * nMat (-((b⁻¹ : Rˣ) : R))))) =
      nMat (b : R) * wMat := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [wMat, nMat, mMat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at h2
  exact impl_uniq H h2 h1
end PositivityTheory.PlacePermOperatorBicommutantSpan
