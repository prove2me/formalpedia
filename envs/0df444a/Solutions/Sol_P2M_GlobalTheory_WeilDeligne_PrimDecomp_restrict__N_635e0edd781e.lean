-- Prove2me | solution 1 for P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict__N_635e0edd781e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:38.657844+00:00
-- url     : https://prove2.me/submissions/cf392ddf-fefc-4c51-8911-e844868f5a1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RestrictHomApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory.WeilDeligne.PrimDecomp
theorem _root_.solution (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) : (restrictρ a S hS).N = 0 := rfl
end GlobalTheory.WeilDeligne.PrimDecomp
