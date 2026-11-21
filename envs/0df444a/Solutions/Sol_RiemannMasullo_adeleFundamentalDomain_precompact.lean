-- Prove2me | solution 1 for RiemannMasullo.adeleFundamentalDomain_precompact
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:33:05.887688+00:00
-- url     : https://prove2.me/submissions/e1ca3a5e-79b8-495d-8ee4-85e96022b58a

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L66-L67
import Mathlib
import Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open scoped IsDedekindDomain.FiniteAdeleRing
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution : IsCompact (closure (adeleFundamentalDomain F b)) := by
  classical
  haveI : Finite ι := Module.Finite.finite_basis b
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans
      (Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  let K := h ⁻¹' closure (ZSpan.fundamentalDomain B)
  have hk : IsCompact K := h.isCompact_preimage.mpr
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, (ZSpan.fundamentalDomain_isBounded B).closure⟩)
  let A (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F) := v.adicCompletionIntegers F
  let H : Set 𝔸ᶠ[𝓞 F, F] := {a | ∀ v, a v ∈ A v}
  have hA (v : HeightOneSpectrum (𝓞 F)) : IsCompact (A v) :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := F) v)
  have hf : IsCompact (closure H) :=
    (isCompact_closure_restrictedProduct_iff (A := A)
      (Filter.Eventually.of_forall fun v ↦ ⟨hA v, Valued.isOpen_integer _⟩) H).mpr
      ⟨A, hA, Filter.Eventually.of_forall fun _ ↦ rfl, fun _ ha ↦ ha⟩
  have hsub : adeleFundamentalDomain F b ⊆ K ×ˢ closure H := by
    rintro a ⟨h₁, h₂⟩
    refine ⟨subset_closure h₁, subset_closure ?_⟩
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies] at h₂
    exact h₂
  exact (hk.prod hf).of_isClosed_subset isClosed_closure
    (closure_minimal hsub ((isClosed_closure.preimage h.continuous).prod isClosed_closure))
