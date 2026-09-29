-- Prove2me | solution 1 for SchwartzMap.exists_coe_eq_vectorFourierIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9c3be6ae-9287-5249-b6dd-215d695297f2

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SchwartzMap_exists_coe_eq_vectorFourierIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace PiFourier

variable {d : Type*} [Fintype d]

def piFourierIntegral (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ :=
  ∫ v, f v * (𝐞 (-∑ i, v i * ξ i) : ℂ) ∂(volume : Measure (d → ℝ))

abbrev euclideanToPi : EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)

theorem piFourierIntegral_eq_fourier_euclidean (g : (d → ℝ) → ℂ) (ξ : d → ℝ) :
    piFourierIntegral g ξ
      = 𝓕 (fun v : EuclideanSpace ℝ d => g (ofLp v)) (toLp 2 ξ) := by
  unfold piFourierIntegral
  rw [Real.fourier_eq]
  rw [← MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  have hinner : ∑ i, (ofLp v) i * ξ i = ⟪v, toLp 2 ξ⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← hinner, mul_comm]

theorem exists_schwartz_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) :
    ∃ g : SchwartzMap (d → ℝ) ℂ, ∀ ξ, piFourierIntegral (⇑h) ξ = g ξ := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  let g' : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕 h'
  let g : SchwartzMap (d → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)).symm g'
  refine ⟨g, fun ξ => ?_⟩
  rw [piFourierIntegral_eq_fourier_euclidean]
  simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rfl

theorem piFourierIntegral_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) (u : d → ℝ) :
    piFourierIntegral (piFourierIntegral (⇑h)) u = h (-u) := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  have hh' : ∀ v, h' v = h (ofLp v) := fun v => by
    simp only [h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl

  have h1 : (fun v : EuclideanSpace ℝ d => piFourierIntegral (⇑h) (ofLp v)) = 𝓕 (⇑h') := by
    funext v
    rw [piFourierIntegral_eq_fourier_euclidean, WithLp.toLp_ofLp]
    congr 1
  rw [piFourierIntegral_eq_fourier_euclidean, h1]

  have h2 := Real.fourierInv_eq_fourier_neg (𝓕 (⇑h')) (-(toLp 2 u))
  rw [neg_neg] at h2
  rw [← h2, h'.continuous.fourierInv_fourier_eq h'.integrable]
  · rw [hh', ← WithLp.toLp_neg]
  · exact SchwartzMap.integrable (𝓕 h' : SchwartzMap (EuclideanSpace ℝ d) ℂ)

end PiFourier

section BFourier

open PiFourier LinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

theorem vectorFourierIntegral_eq_smul_piFourierIntegral
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V) (f : V → ℂ) (y : V) :
    VectorFourier.fourierIntegral 𝐞 μ B f y
      = ((μ.real (ZSpan.fundamentalDomain b) : ℝ) : ℂ)
        * piFourierIntegral (fun v => f (b.equivFun.symm v)) (fun i => B (b i) y) := by
  classical
  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]
  have hA' : ∀ v, b.equivFun.symm v = A v := fun v => rfl

  set ν : MeasureTheory.Measure V := Measure.map A volume with hν_def
  haveI : ν.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  set c : NNReal := Measure.addHaarScalarFactor μ ν with hc_def
  have hμν : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  have hνF : ν (ZSpan.fundamentalDomain b) = 1 := by
    rw [hν_def, Measure.map_apply A.continuous.measurable (ZSpan.fundamentalDomain_measurableSet b),
      ← A.image_symm_eq_preimage]
    have : (A.symm : V → ι → ℝ) '' ZSpan.fundamentalDomain b
        = ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) := by
      rw [show ((A.symm : V → ι → ℝ)) = ⇑(b.equivFun : V ≃ₗ[ℝ] ι → ℝ) from rfl,
        ZSpan.map_fundamentalDomain]
      congr 1
      ext i j
      simp [Module.Basis.map_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [this, ZSpan.fundamentalDomain_pi_basisFun]
    simp [volume_pi, Measure.pi_pi, Real.volume_Ico]
  have hμF : μ.real (ZSpan.fundamentalDomain b) = c := by
    rw [Measure.real, hμν, Measure.smul_apply, hνF, ENNReal.smul_def, smul_eq_mul, mul_one,
      ENNReal.coe_toReal]

  have hpair : ∀ v : ι → ℝ, B (A v) y = ∑ i, v i * B (b i) y := fun v => by
    rw [hA, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

  have h2 : ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w y)) : ℂ)) (A v)
      = ∫ w, f w * (𝐞 (-(B w y)) : ℂ) ∂ν := by
    have := MeasurableEmbedding.integral_map A.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun w : V => f w * (𝐞 (-(B w y)) : ℂ)) (μ := volume)
    simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
    rw [hν_def, this]
  rw [hμF, VectorFourier.fourierIntegral, hμν, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  congr 1
  have h3 : ∫ x, 𝐞 (-(B x y)) • f x ∂ν = ∫ w, f w * (𝐞 (-(B w y)) : ℂ) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp only [Circle.smul_def, smul_eq_mul, mul_comm])
  rw [h3, ← h2]
  unfold piFourierIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [hA', hpair]

theorem solution
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f := by
  classical

  let ι := Module.Free.ChooseBasisIndex ℝ V
  let b : Module.Basis ι ℝ V := Module.Free.chooseBasis ℝ V
  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv

  let bd : Module.Basis ι ℝ V := B.flip.dualBasis hB.flip b
  let T : V ≃L[ℝ] (ι → ℝ) := bd.equivFun.toContinuousLinearEquiv
  have hT : ∀ y i, T y i = B (b i) y := fun y i => by
    show bd.repr y i = B (b i) y
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (b.equivFun.symm v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_schwartz_piFourierIntegral h
  refine ⟨((μ.real (ZSpan.fundamentalDomain b) : ℝ) : ℂ)
      • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T g₀, ?_⟩
  funext y
  have e1 : (fun v => f (b.equivFun.symm v)) = ⇑h := funext fun v => (hh v).symm
  have e2 : (fun i => B (b i) y) = T y := funext fun i => (hT y i).symm
  rw [vectorFourierIntegral_eq_smul_piFourierIntegral μ B hB b (⇑f) y, SchwartzMap.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, smul_eq_mul, ← hg₀, e1, e2]

end BFourier

end

end S_SchwartzMap_exists_coe_eq_vectorFourierIntegral
end P2MW
export P2MW.S_SchwartzMap_exists_coe_eq_vectorFourierIntegral (solution)
