-- Prove2me | solution 1 for PositivityTheory.PTNLoc.valuation_lt_one_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:10.696609+00:00
-- url     : https://prove2.me/submissions/3ed7a336-e4fe-42f4-b88e-51cc053086e5

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
    A'.valuation (E x) < 1 ↔ A.valuation x < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ← map_inv₀ E x,
    hA, hA, map_eq_zero_iff E E.injective]
end PositivityTheory.PTNLoc
