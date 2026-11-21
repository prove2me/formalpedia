-- Prove2me | solution 1 for RiemannMasullo.adeleRing_factors
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:47:30.518737+00:00
-- url     : https://prove2.me/submissions/865f7ea7-9ba1-4f8f-aa32-35bc7fc6bcff

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L161-L210
import Mathlib


open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

theorem solution :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] F)
    (∃ e : (ℝ ⊗[ℚ] F) ≃+* InfiniteAdeleRing F, Continuous e ∧ Continuous e.symm ∧
      ∀ x : F, e (1 ⊗ₜ[ℚ] x) = algebraMap F (InfiniteAdeleRing F) x) ∧
    IsHomeomorph (fun a : 𝔸ᶠ[𝓞 F, F] ↦
      (a : Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])) ∧
    IsHomeomorph (fun a : 𝔸[F] ↦ (a.1, a.2) : 𝔸[F] → InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F]) ∧
    ∀ x : F, (∀ w, (algebraMap F 𝔸[F] x).1 w = algebraMap F w.Completion x) ∧
      ∀ v : Primes(F), (algebraMap F 𝔸[F] x).2 v = algebraMap F (v.adicCompletion F) x := by
  classical
  let _ := moduleTopology ℝ (ℝ ⊗[ℚ] F)
  refine ⟨?_, IsHomeomorph.id, IsHomeomorph.id, ?_⟩
  · let f : (ℝ ⊗[ℚ] F) →ₐ[ℝ] mixedEmbedding.mixedSpace F :=
      AlgHom.liftEquiv ℚ ℝ F _ (mixedEmbedding F).toRatAlgHom
    have hf (x : F) : f (1 ⊗ₜ[ℚ] x) = mixedEmbedding F x := by
      simp [f]
    let b := (integralBasis F).baseChange ℝ
    let l := b.equiv (mixedEmbedding.latticeBasis F) (Equiv.refl _)
    have hfl : f.toLinearMap = l.toLinearMap := by
      apply b.ext
      intro i
      change f (b i) = l (b i)
      rw [show l (b i) = mixedEmbedding.latticeBasis F i from
        Module.Basis.equiv_apply .., mixedEmbedding.latticeBasis_apply]
      simpa only [b, Module.Basis.baseChange_apply] using hf (integralBasis F i)
    let e := AlgEquiv.ofBijective f (show Bijective f.toLinearMap from hfl ▸ l.bijective)
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
    let g := InfiniteAdeleRing.ringEquiv_mixedSpace F
    have : ContinuousAdd (ℝ ⊗[ℚ] F) := IsModuleTopology.toContinuousAdd ℝ _
    have : IsModuleTopology ℝ (mixedEmbedding.mixedSpace F) := isModuleTopologyOfFiniteDimensional
    refine ⟨e.toRingEquiv.trans g.symm, ?_, ?_, ?_⟩
    · exact h.symm.continuous.comp (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
    · exact (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap).comp h.continuous
    · intro x
      change g.symm (f (1 ⊗ₜ[ℚ] x)) = _
      rw [hf, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
  · intro x
    refine ⟨fun w ↦ ?_, fun _ ↦ rfl⟩
    rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.algebraMap_apply]
