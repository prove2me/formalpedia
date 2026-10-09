-- Prove2me | solution 1 for TroppMatrixConcentration.matrix_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:38:11.700446+00:00
-- url     : https://prove2.me/submissions/b9c0973f-8ac4-49b9-8fbf-cc8968032e9b

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Theorems.Thm_TroppMatrixConcentration_hermitian_bernstein
import Theorems.Thm_TroppMatrixConcentration_dilation_identities
import Theorems.Thm_TroppMatrixConcentration_dilation_variance
import Theorems.Thm_TroppMatrixConcentration_ch6_independent_sum_second_moment
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixBernstein

open TroppMatrixConcentration

/-- The Hermitian dilation is real-linear. -/
noncomputable def dilLin (m n : Type*) :
    Matrix m n ℂ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun := dilation
  map_add' X Y := by
    simp [dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add]
  map_smul' c X := by
    simp [dilation, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

lemma dilLin_apply {m n : Type*} (X : Matrix m n ℂ) : dilLin m n X = dilation X := rfl

/-- The conjugate transpose is real-linear. -/
noncomputable def ctLin (m n : Type*) : Matrix m n ℂ →ₗ[ℝ] Matrix n m ℂ where
  toFun := Matrix.conjTranspose
  map_add' X Y := Matrix.conjTranspose_add X Y
  map_smul' c X := by simp [Matrix.conjTranspose_smul]

/-- The reindexed dilation `A ↦ reindex (dilation A)` on `Fin (m + n)`. -/
noncomputable def phiLin (m n : ℕ) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
  (Matrix.reindexLinearEquiv ℝ ℂ finSumFinEquiv finSumFinEquiv).toLinearMap ∘ₗ
    dilLin (Fin m) (Fin n)

lemma phiLin_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    phiLin m n A = Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation A) := rfl

/-- Reindexing as a `⋆`-algebra equivalence over `ℂ`. -/
noncomputable def reindexStarC {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; rfl
    map_smul' := by intro r A; rfl }

lemma norm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (reindexStarC e) A

lemma lambdaMax_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    lambdaMax (Matrix.reindex e e A) = lambdaMax A := by
  have h := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e) A
  rw [Matrix.coe_reindexAlgEquiv] at h
  unfold lambdaMax
  rw [h]

lemma integral_reindex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (X : Ω → Matrix ι ι ℂ) :
    ∫ ω, Matrix.reindex e e (X ω) ∂μ = Matrix.reindex e e (∫ ω, X ω ∂μ) := by
  let L : Matrix ι ι ℂ ≃L[ℝ] Matrix κ κ ℂ :=
    (Matrix.reindexLinearEquiv ℝ ℂ e e).toContinuousLinearEquiv
  exact L.integral_comp_comm X

lemma measurable_phiLin (m n : ℕ) : Measurable (phiLin m n) :=
  (phiLin m n).continuous_of_finiteDimensional.measurable

lemma measurable_ct (m n : ℕ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℂ => A.conjTranspose) :=
  (continuous_id.matrix_conjTranspose).measurable

lemma integral_phiLin {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) (hX : Integrable X μ) :
    ∫ ω, phiLin m n (X ω) ∂μ = phiLin m n (∫ ω, X ω ∂μ) :=
  (LinearMap.toContinuousLinearMap (phiLin m n)).integral_comp_comm hX

lemma integral_ct {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) (hX : Integrable X μ) :
    ∫ ω, (X ω).conjTranspose ∂μ = (∫ ω, X ω ∂μ).conjTranspose :=
  (LinearMap.toContinuousLinearMap (ctLin (Fin m) (Fin n))).integral_comp_comm hX

lemma lambdaMax_phiLin {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) :
    lambdaMax (phiLin m n A) = spectralNorm A := by
  rw [phiLin_apply, lambdaMax_reindex]
  exact (dilation_identities A).2.2.1.trans (dilation_identities A).2.2.2

lemma norm_phiLin {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖phiLin m n A‖ = ‖A‖ := by
  rw [phiLin_apply, norm_reindex]
  exact (dilation_identities A).2.2.2

end TroppMatrixBernstein

open TroppMatrixConcentration TroppMatrixBernstein

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ L) :
    let Z := fun ω => ∑ k, S k ω
    let v := rectSecondMoment μ Z
    v = max (spectralNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
      (spectralNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) ∧
    (∫ ω, spectralNorm (Z ω) ∂μ) ≤
      Real.sqrt (2 * v * Real.log (m + n)) + L * Real.log (m + n) / 3 ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
      bernsteinTail (m + n) v L t := by
  intro Z v
  -- Square integrability of the summands and their adjoints.
  have hSL2 : ∀ k, MemLp (S k) 2 μ := fun k =>
    MemLp.of_bound (hMeas k).aestronglyMeasurable L (hBound k)
  have hSint : ∀ k, Integrable (S k) μ := fun k => (hSL2 k).integrable (by norm_num)
  have hSL2h : ∀ k, MemLp (fun ω => (S k ω).conjTranspose) 2 μ := by
    intro k
    refine MemLp.of_bound ((measurable_ct m n).comp (hMeas k)).aestronglyMeasurable L ?_
    filter_upwards [hBound k] with ω hω
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hω
  have hSmeanh : ∀ k, (∫ ω, (S k ω).conjTranspose ∂μ) = 0 := by
    intro k
    rw [integral_ct μ (S k) (hSint k), hMean k, Matrix.conjTranspose_zero]
  -- Step 1: the variance statistic.
  have hZh : ∀ ω, (Z ω).conjTranspose = ∑ k, (S k ω).conjTranspose := by
    intro ω
    simp only [Z, Matrix.conjTranspose_sum]
  have hZZ : ∫ ω, Z ω * (Z ω).conjTranspose ∂μ =
      ∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ := by
    simp_rw [hZh]
    exact ch6_independent_sum_second_moment μ S id Matrix.conjTranspose measurable_id
      (measurable_ct m n) hMeas hIndep hSL2 hSL2h hMean
  have hZhZ : ∫ ω, (Z ω).conjTranspose * Z ω ∂μ =
      ∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ := by
    simp_rw [hZh]
    exact ch6_independent_sum_second_moment μ S Matrix.conjTranspose id
      (measurable_ct m n) measurable_id hMeas hIndep hSL2h hSL2 hSmeanh
  have hv1 : v = max (spectralNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
      (spectralNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) := by
    show max (spectralNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (spectralNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ)) = _
    rw [hZZ, hZhZ]
  -- Step 2: `Z` is centered, measurable and square integrable.
  have hZint : ∫ ω, Z ω ∂μ = 0 := by
    simp only [Z]
    rw [integral_finsetSum _ (fun k _ => hSint k)]
    simp [hMean]
  have hZmeas : Measurable Z := Finset.measurable_sum _ (fun k _ => hMeas k)
  have hZL2 : MemLp Z 2 μ := memLp_finsetSum _ (fun k _ => hSL2 k)
  have hdv := dilation_variance μ Z hZmeas hZL2
  rw [hZint] at hdv
  simp only [sub_zero] at hdv
  -- Step 3: the Hermitian dilations on `Fin (m + n)`.
  have : NeZero (m + n) := ⟨by have := NeZero.ne m; omega⟩
  let X : Fin N → Ω → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k ω => phiLin m n (S k ω)
  have hXmeas : ∀ k, Measurable (X k) := fun k => (measurable_phiLin m n).comp (hMeas k)
  have hXherm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian := fun k =>
    Filter.Eventually.of_forall (fun ω => (dilation_identities (S k ω)).1.submatrix _)
  have hXL2 : ∀ k, MemLp (X k) 2 μ := by
    intro k
    refine MemLp.of_bound (hXmeas k).aestronglyMeasurable L ?_
    filter_upwards [hBound k] with ω hω
    simp only [X]
    rw [norm_phiLin]
    exact hω
  have hXindep : iIndepFun X μ :=
    hIndep.comp (fun _ => phiLin m n) (fun _ => measurable_phiLin m n)
  have hXmean : ∀ k, (∫ ω, X k ω ∂μ) = 0 := by
    intro k
    simp only [X]
    rw [integral_phiLin μ (S k) (hSint k), hMean k, map_zero]
  have hXbound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L := by
    intro k
    filter_upwards [hBound k] with ω hω
    simp only [X]
    rw [lambdaMax_phiLin]
    exact hω
  have hY : ∀ ω, ∑ k, phiLin m n (S k ω) = phiLin m n (Z ω) := by
    intro ω
    simp only [Z, map_sum]
  have hlam : ∀ ω, lambdaMax (∑ k, phiLin m n (S k ω)) = spectralNorm (Z ω) := by
    intro ω
    rw [hY ω, lambdaMax_phiLin]
  have hvY : hermitianSecondMoment μ (fun ω => ∑ k, phiLin m n (S k ω)) = v := by
    have hsq : ∀ ω, (phiLin m n (Z ω)) ^ 2 =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation (Z ω) ^ 2) := by
      intro ω
      rw [phiLin_apply, ← Matrix.coe_reindexAlgEquiv ℝ, map_pow]
    unfold hermitianSecondMoment
    simp_rw [hY, hsq]
    rw [integral_reindex, spectralNorm, norm_reindex]
    exact hdv
  have H := hermitian_bernstein μ X L hL hXmeas hXherm hXL2 hXindep hXmean hXbound
  obtain ⟨-, H2, H3⟩ := H
  refine ⟨hv1, ?_, ?_⟩
  · simp only [X, hlam, hvY] at H2
    simpa [Nat.cast_add] using H2
  · intro t ht
    have := H3 t ht
    simp only [X, hlam, hvY] at this
    exact this
