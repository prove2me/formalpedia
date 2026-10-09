-- Prove2me | solution 1 for TroppMatrixConcentration.ch7_intrinsic_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:41:44.822072+00:00
-- url     : https://prove2.me/submissions/8c0c318c-f868-4c2c-ac11-3ca39a91877c

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_hermitian_bernstein
import Theorems.Thm_TroppMatrixConcentration_dilation_identities
import Theorems.Thm_TroppMatrixConcentration_ch7_block_intrinsic
import Theorems.Thm_TroppMatrixConcentration_ch6_independent_sum_second_moment
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TroppCh7IntrinsicBernstein

open TroppMatrixConcentration Matrix

/-- The Hermitian dilation is real-linear. -/
noncomputable def dilLin (m n : Type*) :
    Matrix m n ℂ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun := dilation
  map_add' X Y := by
    simp [dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add]
  map_smul' c X := by
    simp [dilation, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

/-- Reindexing as a `⋆`-algebra equivalence over `ℂ`. -/
noncomputable def reindexStarC {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; rfl
    map_smul' := by intro r A; rfl }

/-- Reindexing preserves the L2 operator norm. -/
lemma norm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (reindexStarC e) A

/-- Reindexing preserves the real spectrum, hence `lambdaMax`. -/
lemma lambdaMax_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    lambdaMax (Matrix.reindex e e A) = lambdaMax A := by
  have h := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e) A
  rw [Matrix.coe_reindexAlgEquiv] at h
  unfold lambdaMax
  rw [h]

/-- The Bochner integral commutes with reindexing. -/
lemma integral_reindex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (X : Ω → Matrix ι ι ℂ) :
    ∫ ω, Matrix.reindex e e (X ω) ∂μ = Matrix.reindex e e (∫ ω, X ω ∂μ) := by
  let L : Matrix ι ι ℂ ≃L[ℝ] Matrix κ κ ℂ :=
    (Matrix.reindexLinearEquiv ℝ ℂ e e).toContinuousLinearEquiv
  exact L.integral_comp_comm X

/-- Reindexing preserves the trace. -/
lemma trace_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- Reindexing preserves the intrinsic dimension. -/
lemma intrinsicDimension_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    intrinsicDimension (Matrix.reindex e e A) = intrinsicDimension A := by
  unfold intrinsicDimension spectralNorm
  rw [trace_reindex, norm_reindex]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The square of the dilation is block diagonal. -/
lemma dilation_sq (X : Matrix m n ℂ) :
    dilation X ^ 2 = fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
  simp [dilation, sq, fromBlocks_multiply]

/-- Upper-left block inclusion as a continuous linear map. -/
noncomputable def incl₁ : Matrix m m ℂ →L[ℂ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => fromBlocks P 0 0 0
      map_add' := fun P P' => by rw [fromBlocks_add]; simp
      map_smul' := fun c P => by rw [fromBlocks_smul]; simp }

/-- Lower-right block inclusion as a continuous linear map. -/
noncomputable def incl₂ : Matrix n n ℂ →L[ℂ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Q => fromBlocks 0 0 0 Q
      map_add' := fun Q Q' => by rw [fromBlocks_add]; simp
      map_smul' := fun c Q => by rw [fromBlocks_smul]; simp }

lemma integral_fromBlocks_diag {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Ω → Matrix m m ℂ) (Q : Ω → Matrix n n ℂ) (hP : Integrable P μ) (hQ : Integrable Q μ) :
    ∫ ω, fromBlocks (P ω) 0 0 (Q ω) ∂μ = fromBlocks (∫ ω, P ω ∂μ) 0 0 (∫ ω, Q ω ∂μ) := by
  have hsplit : ∀ (A : Matrix m m ℂ) (B : Matrix n n ℂ),
      fromBlocks A 0 0 B = incl₁ (n := n) A + incl₂ (m := m) B := by
    intro A B
    simp only [incl₁, incl₂, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [fromBlocks_add]; simp
  simp_rw [hsplit]
  rw [integral_add ((incl₁ (n := n)).integrable_comp hP) ((incl₂ (m := m)).integrable_comp hQ),
    ContinuousLinearMap.integral_comp_comm _ hP, ContinuousLinearMap.integral_comp_comm _ hQ]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma fromBlocks_diag_sub (A A' : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    fromBlocks A 0 0 B - fromBlocks A' 0 0 B' = fromBlocks (A - A') 0 0 (B - B') := by
  rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

/-- Conjugate transposition as a real-linear continuous map. -/
noncomputable def ctCLM (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ →L[ℝ] Matrix n m ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by simp [Matrix.conjTranspose_smul] }

lemma ctCLM_apply {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ctCLM m n A = Aᴴ := rfl

/-- The transported dilation `A ↦ reindex (dilation A)` as a real-linear continuous map. -/
noncomputable def Φ (p q : ℕ) :
    Matrix (Fin p) (Fin q) ℂ →L[ℝ] Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.reindexLinearEquiv ℝ ℂ finSumFinEquiv finSumFinEquiv).toLinearMap ∘ₗ
      dilLin (Fin p) (Fin q))

lemma Φ_apply {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    Φ p q A = Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation A) := rfl

end TroppCh7IntrinsicBernstein

open TroppMatrixConcentration TroppCh7IntrinsicBernstein

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ)
    (hV : V₁ ≠ 0 ∨ V₂ ≠ 0)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ L)
    (hVariance₁ : loewnerLE
      (∫ ω, (∑ k, S k ω) * (∑ k, S k ω).conjTranspose ∂μ) V₁)
    (hVariance₂ : loewnerLE
      (∫ ω, (∑ k, S k ω).conjTranspose * (∑ k, S k ω) ∂μ) V₂) :
    let Z := fun ω => ∑ k, S k ω
    let r := intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂)
    let v := max (spectralNorm V₁) (spectralNorm V₂)
    (∫ ω, Z ω * (Z ω).conjTranspose ∂μ) =
      ∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ ∧
    (∫ ω, (Z ω).conjTranspose * Z ω ∂μ) =
      ∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ ∧
    ∀ t : ℝ, Real.sqrt v + L / 3 ≤ t →
      (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
        4 * r * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  intro Z r v
  -- Step 0: integrability and centering of the summands and their adjoints.
  have hSL2 : ∀ k, MemLp (S k) 2 μ := fun k =>
    MemLp.of_bound (hMeas k).aestronglyMeasurable L (by
      filter_upwards [hBound k] with ω h
      simpa [spectralNorm] using h)
  have hct_meas : Measurable (fun A : Matrix (Fin m) (Fin n) ℂ => A.conjTranspose) :=
    (ctCLM (Fin m) (Fin n)).continuous.measurable
  have hSHL2 : ∀ k, MemLp (fun ω => (S k ω).conjTranspose) 2 μ := fun k =>
    (ctCLM (Fin m) (Fin n)).comp_memLp' (hSL2 k)
  have hSHmean : ∀ k, (∫ ω, (S k ω).conjTranspose ∂μ) = 0 := by
    intro k
    have := (ctCLM (Fin m) (Fin n)).integral_comp_comm ((hSL2 k).integrable one_le_two)
    simp only [ctCLM_apply, hMean k, Matrix.conjTranspose_zero] at this
    exact this
  -- Step 1: the two variance identities.
  have h1 : (∫ ω, Z ω * (Z ω).conjTranspose ∂μ) =
      ∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ := by
    have := ch6_independent_sum_second_moment μ S id Matrix.conjTranspose measurable_id
      hct_meas hMeas hIndep hSL2 hSHL2 hMean
    show (∫ ω, (∑ k, S k ω) * (∑ k, S k ω).conjTranspose ∂μ) = _
    simp_rw [Matrix.conjTranspose_sum]
    exact this
  have h2 : (∫ ω, (Z ω).conjTranspose * Z ω ∂μ) =
      ∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ := by
    have := ch6_independent_sum_second_moment μ S Matrix.conjTranspose id hct_meas
      measurable_id hMeas hIndep hSHL2 hSL2 hSHmean
    show (∫ ω, (∑ k, S k ω).conjTranspose * (∑ k, S k ω) ∂μ) = _
    simp_rw [Matrix.conjTranspose_sum]
    exact this
  refine ⟨h1, h2, ?_⟩
  -- Step 2: square integrability of `Z` and of its Gram matrices.
  have hZL2 : MemLp Z 2 μ := memLp_finsetSum _ (fun k _ => hSL2 k)
  have hZsq : Integrable (fun ω => ‖Z ω‖ ^ 2) μ :=
    hZL2.integrable_norm_pow (p := 2) two_ne_zero
  have hP : Integrable (fun ω => Z ω * (Z ω).conjTranspose) μ := by
    refine Integrable.mono' hZsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℂ => X * X.conjTranspose) :=
        continuous_id.matrix_mul continuous_id.matrix_conjTranspose
      exact hc.comp_aestronglyMeasurable hZL2.1
    · calc _ ≤ ‖Z ω‖ * ‖(Z ω).conjTranspose‖ := Matrix.l2_opNorm_mul _ _
        _ = _ := by rw [Matrix.l2_opNorm_conjTranspose, sq]
  have hQ : Integrable (fun ω => (Z ω).conjTranspose * Z ω) μ := by
    refine Integrable.mono' hZsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℂ => X.conjTranspose * X) :=
        continuous_id.matrix_conjTranspose.matrix_mul continuous_id
      exact hc.comp_aestronglyMeasurable hZL2.1
    · rw [Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  -- Step 3: the Gram matrices are positive semidefinite, hence so are `V₁`, `V₂`.
  have hPpsd : (∫ ω, Z ω * (Z ω).conjTranspose ∂μ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae (Filter.Eventually.of_forall
      fun ω => Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_self_mul_conjTranspose (Z ω))))
  have hQpsd : (∫ ω, (Z ω).conjTranspose * Z ω ∂μ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae (Filter.Eventually.of_forall
      fun ω => Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self (Z ω))))
  have hD₁ : (V₁ - ∫ ω, Z ω * (Z ω).conjTranspose ∂μ).PosSemidef := hVariance₁
  have hD₂ : (V₂ - ∫ ω, (Z ω).conjTranspose * Z ω ∂μ).PosSemidef := hVariance₂
  have hV₁ : V₁.PosSemidef := by simpa using hD₁.add hPpsd
  have hV₂ : V₂.PosSemidef := by simpa using hD₂.add hQpsd
  -- Step 4: transport to the Hermitian dilation on `Fin (m + n)`.
  have : NeZero (m + n) := ⟨by have := NeZero.ne m; omega⟩
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin (m + n)) (Fin (m + n)) ℂ,
      V = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks V₁ 0 0 V₂) :=
    ⟨_, rfl⟩
  have hVne : V ≠ 0 := by
    intro h
    rw [hVdef] at h
    have h' : Matrix.fromBlocks V₁ 0 0 V₂ = 0 := by
      have := congrArg (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm) h
      simpa using this
    have h0 : Matrix.fromBlocks V₁ 0 0 V₂ =
        Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) 0 0 (0 : Matrix (Fin n) (Fin n) ℂ) :=
      h'.trans Matrix.fromBlocks_zero.symm
    have h00 := Matrix.fromBlocks_inj.mp h0
    rcases hV with hv | hv
    · exact hv h00.1
    · exact hv h00.2.2.2
  obtain ⟨-, hnorm, -⟩ := ch7_block_intrinsic V₁ V₂ hV₁ hV₂
  have hvV : spectralNorm V = v := by
    rw [hVdef]
    unfold spectralNorm
    rw [norm_reindex]
    exact hnorm
  have hrV : intrinsicDimension V = r := by
    rw [hVdef, intrinsicDimension_reindex]
  have hY : ∀ ω, ∑ k, Φ m n (S k ω) = Φ m n (Z ω) := fun ω =>
    (map_sum (Φ m n) (fun k => S k ω) Finset.univ).symm
  have hlam : ∀ A : Matrix (Fin m) (Fin n) ℂ, lambdaMax (Φ m n A) = spectralNorm A := by
    intro A
    rw [Φ_apply, lambdaMax_reindex]
    exact (dilation_identities A).2.2.1.trans (dilation_identities A).2.2.2
  have hXmeas : ∀ k, Measurable (fun ω => Φ m n (S k ω)) := fun k =>
    (Φ m n).continuous.measurable.comp (hMeas k)
  have hXindep : iIndepFun (fun k ω => Φ m n (S k ω)) μ :=
    hIndep.comp (fun _ => Φ m n) (fun _ => (Φ m n).continuous.measurable)
  have hXherm : ∀ k, ∀ᵐ ω ∂μ, (Φ m n (S k ω)).IsHermitian := fun k =>
    Filter.Eventually.of_forall fun ω => (dilation_identities (S k ω)).1.reindex _
  have hXL2 : ∀ k, MemLp (fun ω => Φ m n (S k ω)) 2 μ := fun k =>
    (Φ m n).comp_memLp' (hSL2 k)
  have hXmean : ∀ k, (∫ ω, Φ m n (S k ω) ∂μ) = 0 := by
    intro k
    rw [(Φ m n).integral_comp_comm ((hSL2 k).integrable one_le_two), hMean k, map_zero]
  have hXbound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (Φ m n (S k ω)) ≤ L := fun k => by
    filter_upwards [hBound k] with ω h
    rw [hlam]; exact h
  have hVar : loewnerLE (∫ ω, (∑ k, Φ m n (S k ω)) ^ 2 ∂μ) V := by
    have hsq : ∀ ω, (Φ m n (Z ω)) ^ 2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Z ω * (Z ω).conjTranspose) 0 0 ((Z ω).conjTranspose * Z ω)) := by
      intro ω
      rw [Φ_apply, ← dilation_sq, ← Matrix.coe_reindexAlgEquiv ℝ, map_pow]
    simp_rw [hY, hsq]
    rw [integral_reindex, integral_fromBlocks_diag μ _ _ hP hQ, hVdef]
    unfold loewnerLE
    rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, ← map_sub, Matrix.coe_reindexLinearEquiv,
      fromBlocks_diag_sub, Matrix.reindex_apply]
    obtain ⟨hpsd, -⟩ := ch7_block_intrinsic _ _ hD₁ hD₂
    exact hpsd.submatrix _
  -- Step 5: apply the intrinsic Hermitian Bernstein inequality.
  obtain ⟨-, H⟩ := ch7_intrinsic_hermitian_bernstein μ (fun k ω => Φ m n (S k ω)) L hL V hVne
    hXmeas hXindep hXherm hXL2 hXmean hXbound hVar
  intro t ht
  have := H t (by rw [hvV]; exact ht)
  simp only [hY, hlam, hvV, hrV] at this
  exact this
