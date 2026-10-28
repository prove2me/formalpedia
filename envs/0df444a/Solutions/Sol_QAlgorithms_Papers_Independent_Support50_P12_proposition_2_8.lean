-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.proposition_2_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:35:18.825687+00:00
-- url     : https://prove2.me/submissions/cbfe046c-0669-4a46-bf3f-d986bd178c87

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

lemma S168_herm (x : ℝ) : ((x : ℂ) • (1 : Mat I)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

lemma S168_alg (x : ℝ) : ((x : ℂ) • (1 : Mat I)) = algebraMap ℝ (Mat I) x := by
  rw [Algebra.algebraMap_eq_smul_one]; rfl

lemma S168_spec [Nonempty I] (x : ℝ) : spec ((x : ℂ) • (1 : Mat I)) = {x} := by
  have h := S168_herm (I := I) x
  unfold spec
  rw [dif_pos h]
  have key : ∀ y ∈ spectrum ℝ ((x : ℂ) • (1 : Mat I)), y = x := by
    rw [S168_alg, spectrum.scalar_eq]; simp
  have hall : ∀ i, h.eigenvalues i = x := fun i => key _ (h.eigenvalues_mem_spectrum_real i)
  ext y
  simp [hall, eq_comm]

lemma S168_proj (x : ℝ) : spectralProjector ((x : ℂ) • (1 : Mat I)) x = 1 := by
  unfold spectralProjector QAlgorithms.eigenProjection
  have : (⨆ μ ∈ ({(x : ℂ)} : Set ℂ), Module.End.eigenspace
      ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) ((x : ℂ) • (1 : Mat I)) :
        EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) μ) = ⊤ := by
    rw [iSup_singleton]
    ext v
    simp only [Submodule.mem_top, iff_true, Module.End.mem_eigenspace_iff]
    rw [map_smul, map_one]; rfl
  have gen : ∀ (K : Submodule ℂ (EuclideanSpace ℂ I)) [K.HasOrthogonalProjection], K = ⊤ →
      Matrix.toEuclideanLin.symm ((K.starProjection : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
        EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) = (1 : Mat I) := by
    rintro K _ rfl
    rw [Submodule.starProjection_top]
    apply Matrix.toEuclideanLin.injective
    rw [LinearEquiv.apply_symm_apply]
    ext v i
    simp
  exact gen _ this

lemma S168_sp1 : supportPower (1 : Mat I) (1 / 2) = 1 := by
  unfold supportPower
  rw [← map_one (algebraMap ℝ (Mat I)), cfc_algebraMap]
  simp

lemma S168_quasi [Nonempty I] (f : ℝ → ℝ) (x : ℝ) :
    quasi f ((x : ℂ) • (1 : Mat I)) 1 = f x * Fintype.card I := by
  have h1 : (1 : Mat I) = ((1 : ℝ) : ℂ) • (1 : Mat I) := by simp
  unfold quasi modular
  rw [S168_sp1, S168_spec x, h1, S168_spec 1, ← h1]
  simp only [Finset.sum_singleton, div_one]
  rw [S168_proj x]
  have hp1 : spectralProjector (1 : Mat I) 1 = 1 := by simpa using S168_proj (I := I) 1
  rw [hp1]
  simp only [mul_one, hs, QAlgorithms.Papers.Independent.Frontier18.P17.res]
  rw [PiLp.inner_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, Fintype.sum_prod_type, smul_eq_mul]
  simp [apply_ite, Finset.sum_ite_eq, mul_comm]

lemma S168_div [Nonempty I] (f : ℝ → ℝ) (x : ℝ) :
    div f ((x : ℂ) • (1 : Mat I)) 1 = ((f x * Fintype.card I : ℝ) : EReal) := by
  unfold div
  rw [if_pos, S168_quasi]
  intro v hv
  simp only [Matrix.one_mulVec] at hv
  simp [hv]

lemma S168_first [Nonempty I] (A : Alg I) (D : Mat I → Mat I → EReal)
    (f : ℝ → ℝ)
    (hD : ∀ X ∈ A, ∀ Y ∈ A, X.PosSemidef → Y.PosSemidef → D X Y = div f X Y) :
    ∀ x ≥ 0, f x = (D ((x : ℂ) • 1) 1).toReal / Fintype.card I := by
  intro x hx
  have hpsd : ((x : ℂ) • (1 : Mat I)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hx)
  rw [hD _ (A.smul_mem A.one_mem _) _ A.one_mem hpsd Matrix.PosSemidef.one, S168_div,
    EReal.toReal_coe]
  have : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end QAlgorithms.Papers.Independent.Support50.P12
open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)


open QAlgorithms.Papers.Independent.Support50.P12

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

theorem solution [Nonempty I] (A : Alg I) (D : Mat I → Mat I → EReal)
    (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (hD : ∀ X ∈ A, ∀ Y ∈ A, X.PosSemidef → Y.PosSemidef → D X Y = div f X Y) :
    (∀ x ≥ 0, f x = (D ((x : ℂ) • 1) 1).toReal / Fintype.card I) ∧
    (∀ g : ℝ → ℝ, DivergenceGenerator g →
      (∀ X ∈ A, ∀ Y ∈ A, X.PosSemidef → Y.PosSemidef → D X Y = div g X Y) →
      ∀ x ≥ 0, f x = g x) := by
  refine ⟨S168_first A D f hD, fun g _ hg x hx => ?_⟩
  rw [S168_first A D f hD x hx, S168_first A D g hg x hx]

end
