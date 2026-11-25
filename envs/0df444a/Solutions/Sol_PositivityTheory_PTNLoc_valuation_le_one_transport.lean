-- Prove2me | solution 1 for PositivityTheory.PTNLoc.valuation_le_one_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:08.082311+00:00
-- url     : https://prove2.me/submissions/1c5f34d7-6d10-43e4-8b99-47de2e0d885b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_MemDecompositionSubgroupIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise
open PositivityTheory PositivityTheory.PTNLoc
namespace PositivityTheory.PTNLoc
theorem _root_.solution {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff]
  exact hA x
end PositivityTheory.PTNLoc
