-- Prove2me | solution 1 for RiemannMasullo.ratAdeleFundamentalDomain_precompact_translate
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:52:02.571768+00:00
-- url     : https://prove2.me/submissions/90f387a6-407e-4fef-9527-f6d161db0089

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L105-L107
import Mathlib
import Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Definitions.Def_RiemannMasullo_RationalAdeleFundamentalDomain
open NumberField InfinitePlace.Completion RiemannMasullo IsDedekindDomain
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing Pointwise

theorem solution (q : ℚ) :
    IsCompact (closure (algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain)) := by
  classical
  let h : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans
      (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph
  let K := h ⁻¹' Set.Icc (0 : ℝ) 1
  have hk : IsCompact K := h.isCompact_preimage.mpr isCompact_Icc
  let A (v : HeightOneSpectrum (𝓞 ℚ)) : Set (v.adicCompletion ℚ) := v.adicCompletionIntegers ℚ
  let H : Set 𝔸ᶠ[𝓞 ℚ, ℚ] := {a | ∀ v, a v ∈ A v}
  have hA (v : HeightOneSpectrum (𝓞 ℚ)) : IsCompact (A v) :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := ℚ) v)
  have hf : IsCompact (closure H) :=
    (isCompact_closure_restrictedProduct_iff (A := A)
      (Filter.Eventually.of_forall fun v ↦ ⟨hA v, Valued.isOpen_integer _⟩) H).mpr
      ⟨A, hA, Filter.Eventually.of_forall fun _ ↦ rfl, fun _ ha ↦ ha⟩
  have hsub : ratAdeleFundamentalDomain ⊆ K ×ˢ closure H := by
    rintro a ⟨hr, hi⟩
    refine ⟨⟨hr.1, hr.2.le⟩, subset_closure ?_⟩
    intro v
    exact Subring.mem_iInf.mp (Subring.mem_iInf.mp hi v) (Finset.notMem_empty v)
  let f := Homeomorph.addLeft (algebraMap ℚ 𝔸[ℚ] q)
  have hbound : IsCompact (f '' (K ×ˢ closure H : Set 𝔸[ℚ])) := (hk.prod hf).image f.continuous
  have hclosed : IsClosed (f '' (K ×ˢ closure H : Set 𝔸[ℚ])) :=
    f.isClosedMap _ ((isClosed_Icc.preimage h.continuous).prod isClosed_closure)
  exact hbound.of_isClosed_subset isClosed_closure
    (closure_minimal (Set.image_mono hsub : f '' _ ⊆ f '' _) hclosed)
