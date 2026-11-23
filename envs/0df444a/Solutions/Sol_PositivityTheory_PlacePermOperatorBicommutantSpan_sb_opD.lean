-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_opD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:15.147926+00:00
-- url     : https://prove2.me/submissions/8cc57663-a2c6-401c-b4f0-801562f3bd5b

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_homeo
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_smul


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
theorem _root_.solution (m : ℝ) (a : Rˣ) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opD m (a : R) φ) := by
  have := H.1
  exact sb_smul (m : ℂ) (sb_homeo hφ (Homeomorph.smul a))
end PositivityTheory.PlacePermOperatorBicommutantSpan
