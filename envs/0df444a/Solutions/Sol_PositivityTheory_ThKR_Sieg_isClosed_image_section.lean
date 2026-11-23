-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.isClosed_image_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.284517+00:00
-- url     : https://prove2.me/submissions/b28c776c-30db-4e15-ab74-c63d359078ad

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}
namespace PositivityTheory.ThKR.Sieg
theorem _root_.solution {X : Type} [TopologicalSpace X] [T2Space X] (τ : X → Fin r → ℝ) (hτ : Continuous τ)
    (a : (Fin r → ℝ) → X) (ha : Continuous a) (h : ∀ t, τ (a t) = t) {D : Set (Fin r → ℝ)} (hD : IsClosed D) :
    IsClosed (a '' D) :=
  (Function.LeftInverse.isClosedEmbedding h hτ ha).isClosedMap _ hD
end PositivityTheory.ThKR.Sieg
