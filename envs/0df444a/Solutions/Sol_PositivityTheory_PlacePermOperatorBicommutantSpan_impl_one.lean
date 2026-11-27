-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.impl_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:08.976426+00:00
-- url     : https://prove2.me/submissions/2838a4f8-873e-4611-bb08-8ba2e99b3849

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
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : Impl ψ h B μ 1 id :=
  ⟨fun _ hφ => hφ, fun φ hφ => ⟨φ, hφ, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun x y φ _ => by simp⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan
