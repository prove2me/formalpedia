-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.impl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:15.090206+00:00
-- url     : https://prove2.me/submissions/8efcf3e2-d79d-4442-ac4d-2942a3ec06a8

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe

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
omit H
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {g g' : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g' T') : Impl ψ h B μ (g * g') (T ∘ T') := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hT
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hT'
  refine ⟨fun φ hφ => a1 _ (b1 φ hφ), fun φ hφ => ?_, fun φ φ' hφ hφ' => ?_, fun c φ hφ => ?_, fun φ hφ => ?_,
    fun x y φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, rfl⟩ := a2 φ hφ
    obtain ⟨φ₂, h2, rfl⟩ := b2 φ₁ h1
    exact ⟨φ₂, h2, rfl⟩
  · simp only [Function.comp, b3 φ φ' hφ hφ', a3 _ _ (b1 φ hφ) (b1 φ' hφ')]
  · simp only [Function.comp, b4 c φ hφ, a4 c _ (b1 φ hφ)]
  · exact (a5 _ (b1 φ hφ)).trans (b5 φ hφ)
  · simp only [Function.comp, a6 x y _ (b1 φ hφ), b6 _ _ φ hφ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    congr 3 <;> module
end PositivityTheory.PlacePermOperatorBicommutantSpan
