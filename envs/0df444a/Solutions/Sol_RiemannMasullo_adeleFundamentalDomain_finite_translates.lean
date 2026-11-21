-- Prove2me | solution 1 for RiemannMasullo.adeleFundamentalDomain_finite_translates
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:51:37.79111+00:00
-- url     : https://prove2.me/submissions/cfc6eaaa-9099-461c-9893-8ff5db4851f4

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L87-L89
import Mathlib
import Theorems.Thm_RiemannMasullo_isDiscrete_principalAdeles
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_precompact
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open scoped RestrictedProduct IsDedekindDomain.FiniteAdeleRing
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution (K : Set 𝔸[F]) (hK : IsCompact K) :
    {x : F | ((algebraMap F 𝔸[F] x +ᵥ closure (adeleFundamentalDomain F b)) ∩ K).Nonempty}.Finite := by
  classical
  haveI : T2Space 𝔸[F] := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let D := closure (adeleFundamentalDomain F b)
  have hD : IsCompact D := adeleFundamentalDomain_precompact F b
  have hdisc : IsDiscrete (P : Set 𝔸[F]) := isDiscrete_principalAdeles F
  haveI : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hdisc
  have hclosed : IsClosed (P : Set 𝔸[F]) := AddSubgroup.isClosed_of_discrete
  have hdif : IsCompact (K - D) := by
    change IsCompact (Set.image2 (· - ·) K D)
    rw [← Set.image_prod]
    exact (hK.prod hD).image continuous_sub
  have hf : ((K - D) ∩ (P : Set 𝔸[F])).Finite :=
    (hdif.inter_right hclosed).finite (hdisc.mono Set.inter_subset_right)
  apply (hf.preimage (AdeleRing.algebraMap_injective (𝓞 F) F).injOn).subset
  rintro x ⟨_, ⟨d, hd, rfl⟩, hk⟩
  refine ⟨⟨algebraMap F 𝔸[F] x + d, hk, d, hd, add_sub_cancel_right ..⟩, ?_⟩
  exact ⟨x, rfl⟩
