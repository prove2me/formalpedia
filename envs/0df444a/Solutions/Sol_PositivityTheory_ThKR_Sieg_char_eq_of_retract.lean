-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.char_eq_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:11.884478+00:00
-- url     : https://prove2.me/submissions/f62ed373-113e-49f5-9f98-511010d8dc43

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
import Theorems.Thm_UpperTheory_Reformulated_B_Yhb4_main


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
variable {H N : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
  [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
namespace PositivityTheory.ThKR.Sieg
theorem _root_.solution (ι : N →* H) (hι : Continuous ι) (π : H → N) (hπ : Continuous π)
    (hmul : ∀ x p, π (ι x * p) = x * π p) (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N) (h1 : ∀ p, π (φ p) = ψ (π p))
    (h2 : ∀ p, (ι (π (φ p)))⁻¹ * φ p = (ι (π p))⁻¹ * p) : mulEquivHaarChar φ = mulEquivHaarChar ψ :=
  _root_.UpperTheory.Reformulated.B.Yhb4.main ι hι π hπ hmul φ ψ h1 h2
end PositivityTheory.ThKR.Sieg
