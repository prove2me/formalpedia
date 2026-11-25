-- Prove2me | solution 1 for P2M_GlobalTheory_WeilDeligne_PrimDecomp_restrict____apply_2c121a83bcca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:17.716275+00:00
-- url     : https://prove2.me/submissions/fb09c475-7b37-4889-9ff0-ce0f5e893ebd

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
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    (((restrictρ a S hS).ρ σ v : S) : V) = a.ρ σ v := rfl
end GlobalTheory.WeilDeligne.PrimDecomp
