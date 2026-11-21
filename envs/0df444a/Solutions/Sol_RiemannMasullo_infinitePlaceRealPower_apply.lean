-- Prove2me | solution 1 for RiemannMasullo.infinitePlaceRealPower_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T01:56:47.287765+00:00
-- url     : https://prove2.me/submissions/497a4d89-2b19-4896-a02a-56ffb69bc340

module
public import Mathlib
public import Definitions.Def_RiemannMasullo_InfinitePlaceRealPowers

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
namespace RiemannMasullo
theorem _root_.solution (v : InfinitePlace F) (r : ℝ) (t : ℝ≥0ˣ) :
    extensionEmbedding v (infinitePlaceRealPower F v r t).val = (((t.val : ℝ) ^ r : ℝ) : ℂ) := by
  let x : ℝ := (t.val : ℝ) ^ r
  let y := algebraMap ℝ (mixedEmbedding.mixedSpace F) x
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  change extensionEmbedding v (e.symm y v) = (x : ℂ)
  have h := e.apply_symm_apply y
  by_cases hv : v.IsReal
  · simpa only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, y, Prod.algebraMap_apply,
      Pi.algebraMap_apply, Algebra.algebraMap_self_apply, extensionEmbeddingOfIsReal_apply] using
      congrArg (fun z : mixedEmbedding.mixedSpace F => (z.1 ⟨v, hv⟩ : ℂ)) h
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    simpa only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, y, Prod.algebraMap_apply,
      Pi.algebraMap_apply] using!
      congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩) h
end RiemannMasullo
