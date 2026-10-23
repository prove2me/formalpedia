-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P32.preparation_reductions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:55:38.509629+00:00
-- url     : https://prove2.me/submissions/a74204ec-9d70-44cc-b061-d94044f6eae2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32.X7B12

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P07 (support operatorRange projection)

/-! ### General matrix facts -/

open scoped MatrixOrder in
lemma X7_fac {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, rfl⟩

lemma X7_psd_trace_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ X : Matrix ι ι ℂ, (A * B).trace = (Xᴴ * X).trace ∧ (X = 0 → A * B = 0) := by
  obtain ⟨C, rfl⟩ := X7_fac hA
  obtain ⟨D, rfl⟩ := X7_fac hB
  refine ⟨C * Dᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Cᴴ * C * (Dᴴ * D) = (Cᴴ * C * Dᴴ) * D by simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  · intro h
    rw [show Cᴴ * C * (Dᴴ * D) = Cᴴ * (C * Dᴴ) * D by simp [Matrix.mul_assoc], h]
    simp

lemma X7_trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ effectProb A B := by
  obtain ⟨X, hX, -⟩ := X7_psd_trace_mul hA hB
  unfold effectProb
  rw [hX]
  have := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma X7_trace_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (h : effectProb A B = 0) : A * B = 0 := by
  obtain ⟨X, hX, hX0⟩ := X7_psd_trace_mul hA hB
  apply hX0
  rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
  have hnn := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  unfold effectProb at h
  rw [hX] at h
  apply Complex.ext
  · simpa using h
  · simpa using hnn.2.symm

lemma X7_toE_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (x) :
    Matrix.toEuclideanLin (A * B) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma X7_toE_ext {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (h : ∀ x, Matrix.toEuclideanLin A x = Matrix.toEuclideanLin B x) : A = B := by
  apply Matrix.toEuclideanLin.injective
  ext1 x
  exact h x

lemma X7_toE_support {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    Matrix.toEuclideanLin (support ρ) =
      ((operatorRange ρ).starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
  simp [support, projection]

lemma X7_support_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    (support ρ).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, X7_toE_support]
  exact (Submodule.isSymmetricProjection_starProjection _).isPositive

lemma X7_one_sub_support_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    (1 - support ρ).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  have : Matrix.toEuclideanLin (1 - support ρ) =
      ((operatorRange ρ)ᗮ.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
    rw [map_sub, X7_toE_support, Submodule.starProjection_orthogonal']
    ext x
    simp
  rw [this]
  exact (Submodule.isSymmetricProjection_starProjection _).isPositive

lemma X7_support_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    support ρ * ρ = ρ := by
  apply X7_toE_ext
  intro x
  rw [X7_toE_mul, X7_toE_support]
  apply Submodule.starProjection_eq_self_iff.mpr
  exact LinearMap.mem_range_self _ x

lemma X7_support_idem {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    support ρ * support ρ = support ρ := by
  apply X7_toE_ext
  intro x
  rw [X7_toE_mul, X7_toE_support]
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.starProjection_apply_mem _ _

lemma X7_kill_support {ι : Type*} [Fintype ι] [DecidableEq ι] {A ρ : Matrix ι ι ℂ}
    (h : A * ρ = 0) : A * support ρ = 0 := by
  apply X7_toE_ext
  intro x
  rw [X7_toE_mul, X7_toE_support]
  have hm : (operatorRange ρ).starProjection x ∈ operatorRange ρ :=
    Submodule.starProjection_apply_mem _ _
  obtain ⟨y, hy⟩ := hm
  rw [ContinuousLinearMap.coe_coe, ← hy, ← X7_toE_mul, h]
  simp

/-- The support projector minimizes `Tr(P σ)` among effects accepting `ρ` with certainty. -/
lemma X7_support_least {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : σ.PosSemidef) :
    IsEffect (support ρ) ∧ 1 ≤ effectProb (support ρ) ρ ∧
    ∀ P, IsEffect P → 1 ≤ effectProb P ρ → effectProb (support ρ) σ ≤ effectProb P σ := by
  refine ⟨⟨X7_support_psd ρ, X7_one_sub_support_psd ρ⟩, ?_, ?_⟩
  · unfold effectProb
    rw [X7_support_mul_self, hρ.2]
    simp
  · intro P hP h1
    set S0 := support ρ
    have hA : effectProb (1 - P) ρ = 0 := by
      have h0 := X7_trace_nonneg hP.2 hρ.1
      have : effectProb (1 - P) ρ = 1 - effectProb P ρ := by
        unfold effectProb
        rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.one_mul, hρ.2]
        simp
      linarith
    have hAρ := X7_trace_zero hP.2 hρ.1 hA
    have hAS0 : (1 - P) * S0 = 0 := X7_kill_support hAρ
    have hPS0 : P * S0 = S0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hAS0
      exact hAS0.symm
    have hS0h : S0ᴴ = S0 := (X7_support_psd ρ).isHermitian.eq
    have hPh : Pᴴ = P := hP.1.isHermitian.eq
    have hS0P : S0 * P = S0 := by
      have := congrArg Matrix.conjTranspose hPS0
      rwa [Matrix.conjTranspose_mul, hS0h, hPh] at this
    have hidem : S0 * S0 = S0 := X7_support_idem ρ
    have hdiff : P - S0 = (1 - S0)ᴴ * P * (1 - S0) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hS0h]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPS0, hS0P,
        hidem]
      abel
    have hpsd : (P - S0).PosSemidef := by
      rw [hdiff]; exact hP.1.conjTranspose_mul_mul_same _
    have := X7_trace_nonneg hpsd hσ
    have hlin : effectProb (P - S0) σ = effectProb P σ - effectProb S0 σ := by
      unfold effectProb
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    linarith

/-! ### Preparation-port facts -/

lemma X7_fin1 {d : ℕ+} : ((preparationPort d).din : ℕ) = 1 := rfl

def X7_blk {d : ℕ+} (J : ChannelChoi (preparationPort d)) : Matrix (Fin d) (Fin d) ℂ :=
  fun b c => J (0, b) (0, c)

lemma X7_eq_prep {d : ℕ+} (J : ChannelChoi (preparationPort d)) :
    preparationChoi (X7_blk J) = J := by
  funext i j
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  have h1 : i1 = 0 := Subsingleton.elim (h := Fin.subsingleton_one) _ _
  have h2 : j1 = 0 := Subsingleton.elim (h := Fin.subsingleton_one) _ _
  subst h1 h2
  rfl

lemma X7_blk_prep {d : ℕ+} (σ : Matrix (Fin d) (Fin d) ℂ) :
    X7_blk (preparationChoi σ) = σ := rfl

def X7_e (d : ℕ+) : Fin ((preparationPort d).din : ℕ) × Fin d ≃ Fin d :=
  Equiv.uniqueProd (Fin d) (Fin 1)

lemma X7_prep_submatrix {d : ℕ+} (σ : Matrix (Fin d) (Fin d) ℂ) :
    (preparationChoi σ : Matrix _ _ ℂ) = σ.submatrix (X7_e d) (X7_e d) := rfl

lemma X7_prep_psd {d : ℕ+} (σ : Matrix (Fin d) (Fin d) ℂ) :
    (preparationChoi σ : Matrix _ _ ℂ).PosSemidef ↔ σ.PosSemidef := by
  rw [X7_prep_submatrix]
  exact Matrix.posSemidef_submatrix_equiv (X7_e d)

lemma X7_cptp_prep {d : ℕ+} (σ : Matrix (Fin d) (Fin d) ℂ) :
    CPTP (preparationChoi σ) ↔ IsDensityMatrix σ := by
  unfold CPTP IsDensityMatrix
  rw [X7_prep_psd]
  apply and_congr_right
  intro _
  constructor
  · intro h
    have := h 0 0
    simp [preparationChoi] at this
    exact this
  · intro h i j
    have hi : i = 0 := Subsingleton.elim (h := Fin.subsingleton_one) _ _
    have hj : j = 0 := Subsingleton.elim (h := Fin.subsingleton_one) _ _
    subst hi hj
    simp [preparationChoi]
    exact h

lemma X7_prep_add {d : ℕ+} (σ τ : Matrix (Fin d) (Fin d) ℂ) (r : ℂ) :
    preparationChoi (σ + r • τ) = preparationChoi σ + r • preparationChoi τ := by
  funext i j; rfl

lemma X7_prep_smul {d : ℕ+} (σ : Matrix (Fin d) (Fin d) ℂ) (r : ℂ) :
    preparationChoi (r • σ) = r • preparationChoi σ := by
  funext i j; rfl

lemma X7_prep_inj {d : ℕ+} {σ τ : Matrix (Fin d) (Fin d) ℂ}
    (h : preparationChoi σ = preparationChoi τ) : σ = τ := by
  rw [← X7_blk_prep σ, ← X7_blk_prep τ, h]

lemma X7_prep_one (d : ℕ+) :
    (preparationChoi (1 : Matrix (Fin d) (Fin d) ℂ) : Matrix _ _ ℂ) = 1 := by
  rw [X7_prep_submatrix, Matrix.submatrix_one_equiv]; rfl

lemma X7_effect_prep {d : ℕ+} (Q : Matrix (Fin d) (Fin d) ℂ) :
    IsEffect (preparationChoi Q : Matrix _ _ ℂ) ↔ IsEffect Q := by
  unfold IsEffect
  rw [X7_prep_psd, ← X7_prep_one, show preparationChoi (1 : Matrix (Fin d) (Fin d) ℂ) -
    preparationChoi Q = preparationChoi (1 - Q) from by funext i j; rfl, X7_prep_psd]

lemma X7_effectProb_prep {d : ℕ+} (Q σ : Matrix (Fin d) (Fin d) ℂ) :
    effectProb (preparationChoi Q : Matrix _ _ ℂ) (preparationChoi σ) = effectProb Q σ := by
  have h : ((preparationChoi Q : Matrix _ _ ℂ) * preparationChoi σ) =
      (Q * σ).submatrix (X7_e d) (X7_e d) := by
    rw [X7_prep_submatrix, X7_prep_submatrix]
    exact Matrix.submatrix_mul_equiv Q σ (X7_e d) (X7_e d) (X7_e d)
  unfold effectProb
  rw [h]
  congr 1
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp (X7_e d) (fun j => (Q * σ) j j)

instance X7_uniq (d : ℕ+) : Unique (Fin ((preparationPort d).din : ℕ)) :=
  inferInstanceAs (Unique (Fin 1))

instance X7_uniq2 (d : ℕ+) :
    Unique (Fin ((preparationPort d).din : ℕ) × Fin ((preparationPort d).din : ℕ)) :=
  { default := (default, default)
    uniq := fun x => Prod.ext (Unique.eq_default _) (Unique.eq_default _) }

lemma X7_pureOutput {d : ℕ+} (J : ChannelChoi (preparationPort d))
    (v : PureInput (preparationPort d)) : pureChannelOutput J v = J := by
  have hv : v.1 (default, default) * conj (v.1 (default, default)) = 1 := by
    have h := v.2
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)] at h
    have h' : ‖v.1 (default, default)‖ = 1 := h
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h']
    norm_num
  funext i j
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  have h1 : i1 = default := Subsingleton.elim _ _
  have h2 : j1 = default := Subsingleton.elim _ _
  subst h1 h2
  simp only [pureChannelOutput, idTensorSuperop, applyChoi, pureDensity, Matrix.of_apply,
    Fintype.sum_unique]
  rw [hv, one_mul]

lemma X7_rob (O : ResourceTheory) {d : ℕ+} (noise : Set (ChannelChoi (preparationPort d)))
    (noise' Fd : Set (Matrix (Fin d) (Fin d) ℂ))
    (hN : ∀ M, M ∈ noise ↔ X7_blk M ∈ noise') (hFr : ∀ M, M ∈ O.free _ ↔ X7_blk M ∈ Fd)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    robustness O noise (preparationChoi ρ) = stateRobustness Fd noise' ρ := by
  unfold robustness stateRobustness
  congr 1
  ext z
  constructor
  · rintro ⟨r, hr, hz, M, hM, F, hF, heq⟩
    refine ⟨r, hr, hz, X7_blk M, (hN M).1 hM, X7_blk F, (hFr F).1 hF, ?_⟩
    funext b c
    have := congrFun (congrFun heq (default, b)) (default, c)
    simpa [X7_blk, preparationChoi] using this
  · rintro ⟨r, hr, hz, σ, hσ, τ, hτ, heq⟩
    refine ⟨r, hr, hz, preparationChoi σ, (hN _).2 hσ, preparationChoi τ, (hFr _).2 hτ, ?_⟩
    rw [← X7_prep_add, heq, X7_prep_smul]

lemma X7_unit (d : ℕ+) : ∃ v : PureInput (preparationPort d), True :=
  ⟨⟨EuclideanSpace.single default 1, by simp⟩, trivial⟩

lemma X7_inner {d : ℕ+} {ρ σ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : σ.PosSemidef) :
    sInf {t | ∃ v : PureInput (preparationPort d), ∃ P, Test (preparationChoi ρ) 0 v P ∧
      t = ENNReal.ofReal (effectProb P (pureChannelOutput (preparationChoi σ) v))} =
    ENNReal.ofReal (effectProb (support ρ) σ) := by
  obtain ⟨hS, hS1, hleast⟩ := X7_support_least hρ hσ
  apply le_antisymm
  · obtain ⟨v, -⟩ := X7_unit d
    apply sInf_le
    refine ⟨v, preparationChoi (support ρ), ⟨(X7_effect_prep _).2 hS, ?_⟩, ?_⟩
    · rw [X7_pureOutput, X7_effectProb_prep]; linarith
    · rw [X7_pureOutput, X7_effectProb_prep]
  · apply le_sInf
    rintro t ⟨v, P, ⟨hP, hP1⟩, rfl⟩
    rw [X7_pureOutput] at hP1 ⊢
    rw [← X7_eq_prep P] at hP hP1 ⊢
    rw [X7_effectProb_prep] at hP1 ⊢
    rw [X7_effect_prep] at hP
    exact ENNReal.ofReal_le_ofReal (hleast _ hP (by linarith))

end QAlgorithms.Papers.Independent.Dependency50.P32.X7B12

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

end QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P32
  QAlgorithms.Papers.Independent.Dependency50.P32.X7B12 in
open QAlgorithms.Papers.Independent.Information100.P07 (support) in
theorem solution (O : ResourceTheory) (hO : Regular O)
    (F : ∀ d : ℕ+, Set (Matrix (Fin d) (Fin d) ℂ)) (hF : PreparationTheory O F)
    {d : ℕ+} (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    maximal O (preparationChoi rho) = stateMaximal (F d) rho ∧
    standard O (preparationChoi rho) = stateStandard (F d) rho ∧
    minimum O (preparationChoi rho) = stateMinimum (F d) rho := by
  obtain ⟨-, -, -, hFd, hall, hfr⟩ := hF d
  have hfree : ∀ M, M ∈ O.free (preparationPort d) ↔ X7_blk M ∈ F d := by
    intro M
    constructor
    · intro hM
      have hc : CPTP M := (hO _).2.2.2.2 M ((hO _).2.2.2.1 hM)
      have hd : IsDensityMatrix (X7_blk M) := (X7_cptp_prep _).1 (by rw [X7_eq_prep]; exact hc)
      exact (hfr _ hd).1 (by rw [X7_eq_prep]; exact hM)
    · intro h
      have := (hfr _ (hFd _ h)).2 h
      rwa [X7_eq_prep] at this
  have hallow : ∀ M, M ∈ O.allowed (preparationPort d) ↔
      X7_blk M ∈ {σ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix σ} := by
    intro M
    rw [hall M, Set.mem_setOf_eq, ← X7_cptp_prep, X7_eq_prep]
  refine ⟨X7_rob O _ _ _ hallow hfree rho, X7_rob O _ _ _ hfree hfree rho, ?_⟩
  show (inverseTestingValue O _ 0)⁻¹ = _
  unfold stateMinimum inverseTestingValue
  congr 1
  congr 1
  ext z
  constructor
  · rintro ⟨M, hM, rfl⟩
    refine ⟨X7_blk M, (hfree M).1 hM, ?_⟩
    rw [← X7_inner hrho (hFd _ ((hfree M).1 hM)).1, X7_eq_prep]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨preparationChoi σ, (hfree _).2 hσ, ?_⟩
    rw [X7_inner hrho (hFd _ hσ).1]
