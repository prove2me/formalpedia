-- Prove2me | solution 1 for PositivityTheory.PTNLoc.mem_decompositionSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:35:59.660909+00:00
-- url     : https://prove2.me/submissions/56fec87b-489d-408d-a5f3-bc1118122c17

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
theorem _root_.solution {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (σ : G F Ω) :
    σ ∈ A.decompositionSubgroup F ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    exact ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec (F := F) h x
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have := h ((σ⁻¹ : G F Ω) y)
    rw [ReciprocityTheory.Gal.mul_inv_apply] at this
    exact this.symm
end PositivityTheory.PTNLoc
