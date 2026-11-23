-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.bsym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:22.966521+00:00
-- url     : https://prove2.me/submissions/d840ecc5-6656-49f8-880e-afec6d11a1d0

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
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {B : Matrix ι ι R} (hB : B.IsSymm) (x y : ι → R) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq, dotProduct_comm]
end PositivityTheory.PlacePermOperatorBicommutantSpan
