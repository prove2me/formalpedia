-- Prove2me | solution 1 for RiemannMasullo.adeleFundamentalDomain_interior
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:35:49.305182+00:00
-- url     : https://prove2.me/submissions/9066b71f-2a1e-4659-9f5c-966171d7ac14

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L70-L71
import Mathlib
import Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open scoped IsDedekindDomain.FiniteAdeleRing
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
theorem solution : (interior (adeleFundamentalDomain F b)).Nonempty := by
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
  letI := Fintype.ofFinite ι
  let φ := B.equivFun.toContinuousLinearEquiv
  let U : Set (InfiniteAdeleRing F) := (fun a ↦ φ (h a)) ⁻¹' (Set.univ.pi fun _ ↦ Set.Ioo 0 1)
  have hu : IsOpen U := (isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)).preimage
    (φ.continuous.comp h.continuous)
  let A (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F) := v.adicCompletionIntegers F
  let H : Set 𝔸ᶠ[𝓞 F, F] := {a | ∀ v, a v ∈ A v}
  have hh : IsOpen H := by
    have hopen := isOpen_restrictedProduct_forall_mem (A := A) Set.univ
      (fun v _ ↦ Valued.isOpen_integer (v.adicCompletion F))
    simp only [Set.mem_univ, forall_const] at hopen
    exact hopen
  have hsub : U ×ˢ H ⊆ adeleFundamentalDomain F b := by
    rintro a ⟨hu₁, hh₁⟩
    constructor
    · change ∀ i, B.repr (h a.1) i ∈ Set.Ico 0 1
      exact fun i ↦ ⟨(hu₁ i (Set.mem_univ i)).1.le, (hu₁ i (Set.mem_univ i)).2⟩
    · change a ∈ integralAdelesOutside F ∅
      unfold integralAdelesOutside
      exact Subring.mem_iInf.mpr fun v ↦ Subring.mem_iInf.mpr fun _ ↦ hh₁ v
  let x := h.symm (φ.symm (fun _ ↦ (1/2 : ℝ)))
  refine ⟨(x, 0), interior_maximal hsub (hu.prod hh) ?_⟩
  constructor
  · change φ (h (h.symm _)) ∈ Set.univ.pi _
    rw [Homeomorph.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    intro i _
    constructor <;> norm_num
  · exact fun v ↦ (v.adicCompletionIntegers F).zero_mem
