-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:42:30.295692+00:00
-- url     : https://prove2.me/submissions/50caf25f-af84-4711-9380-e7423c37141a

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

namespace A3S55L32
open scoped MatrixOrder

/-- indicator -/
def ind (l : ℝ) (x : ℝ) : ℝ := if x = l then 1 else 0

lemma cont (X : Mat I) (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ X) :=
  X.finite_real_spectrum.continuousOn g

lemma cmul (X : Mat I) (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun x => f x * g x) X :=
  (cfc_mul f g X (cont X f) (cont X g)).symm

lemma toCLM_eq (X : Mat I) :
    ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) X : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
      EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) = Matrix.toEuclideanLin X :=
  Matrix.coe_toEuclideanCLM_eq_toEuclideanLin X

lemma algebraMap_eq (l : ℝ) : (algebraMap ℝ (Mat I) l) = (l : ℂ) • (1 : Mat I) := by
  rw [Algebra.algebraMap_eq_smul_one]; rfl

theorem proj_eq_cfc (H : Mat I) (hH : H.IsHermitian) (l : ℝ) :
    spectralProjector H l = cfc (ind l) H := by
  have hsa : IsSelfAdjoint H := hH
  set P := cfc (ind l) H with hPdef
  set φ := (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ))
  set T := φ H
  set p := φ P
  have hPP : P * P = P := by
    rw [hPdef, cmul]; congr 1; funext x; unfold ind; split_ifs <;> simp
  have hPsa : IsSelfAdjoint P := cfc_predicate _ _
  have hstar : IsStarProjection p := ⟨by
      show p * p = p
      rw [← map_mul, hPP], by
      show star p = p
      rw [← map_star, hPsa.star_eq]⟩
  -- (H - l) P = 0
  have h1 : (H - (l : ℂ) • 1) * P = 0 := by
    have : H - (l : ℂ) • 1 = cfc (fun x => x - l) H := by
      rw [cfc_sub (fun x => x) (fun _ => l) H, cfc_id' ℝ H, cfc_const l H, algebraMap_eq]
    rw [this, hPdef, cmul]
    rw [← cfc_zero ℝ H]; congr 1; funext x; unfold ind; split_ifs with h <;> simp [h]
  -- 1 - P = Q (H - l)
  have h2 : 1 - P = cfc (fun x => if x = l then 0 else (x - l)⁻¹) H * (H - (l : ℂ) • 1) := by
    have : H - (l : ℂ) • 1 = cfc (fun x => x - l) H := by
      rw [cfc_sub (fun x => x) (fun _ => l) H, cfc_id' ℝ H, cfc_const l H, algebraMap_eq]
    rw [this, cmul, hPdef, ← cfc_one ℝ H, ← cfc_sub (1 : ℝ → ℝ) (ind l) H (cont _ _) (cont _ _)]
    congr 1; funext x; unfold ind; split_ifs with h
    · simp
    · have : x - l ≠ 0 := sub_ne_zero.mpr h
      simp [this]
  have hT : φ (H - (l : ℂ) • 1) = T - (l : ℂ) • 1 := by
    rw [map_sub, map_smul, map_one]
  have hrange : LinearMap.range (p : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) =
      Module.End.eigenspace (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) (l : ℂ) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      have := congrArg (fun M => φ M w) h1
      simp only [map_mul, map_zero, hT] at this
      have h' := this
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.zero_apply, sub_eq_zero] at h'
      exact h'
    · intro hv
      refine ⟨v, ?_⟩
      have := congrArg (fun M => φ M v) h2
      simp only [map_mul, map_sub, map_one, hT] at this
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
      change T v = (l:ℂ) • v at hv
      rw [hv, sub_self, map_zero, sub_eq_zero] at this
      exact this.symm
  obtain ⟨_, hp⟩ := _root_.isStarProjection_iff_eq_starProjection_range.mp hstar
  unfold spectralProjector eigenProjection
  have hK : (⨆ μ ∈ ({(l : ℂ)} : Set ℂ), Module.End.eigenspace (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) μ)
      = LinearMap.range (p : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) := by
    rw [hrange]; simp
  have : (⨆ μ ∈ ({(l : ℂ)} : Set ℂ), Module.End.eigenspace (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) μ).starProjection = p := by
    rw [hp]; congr 1
  rw [this, toCLM_eq]; exact LinearEquiv.symm_apply_apply _ _


lemma mem_spec (X : Mat I) (hX : X.IsHermitian) (x : ℝ) : x ∈ spec X ↔ x ∈ spectrum ℝ X := by
  rw [hX.spectrum_real_eq_range_eigenvalues]
  simp [spec, hX]

lemma isClosed_alg (A : StarSubalgebra ℂ (Mat I)) : IsClosed (A : Set (Mat I)) :=
  (Subalgebra.toSubmodule A.toSubalgebra).closed_of_finiteDimensional

lemma supp_herm (X : Mat I) : (supp X)ᴴ = supp X := by
  unfold supp supportPower
  have : IsSelfAdjoint (cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x 0) X) := cfc_predicate _ _
  exact this

lemma supp_idem (X : Mat I) : supp X * supp X = supp X := by
  unfold supp supportPower
  rw [cmul]
  congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]

lemma mul_supp {X : Mat I} (hX : X.IsHermitian) : X * supp X = X := by
  unfold supp supportPower
  conv_lhs => arg 1; rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [cmul]
  conv_rhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]

lemma supp_mul {X : Mat I} (hX : X.IsHermitian) : supp X * X = X := by
  have := congrArg Matrix.conjTranspose (mul_supp hX)
  rwa [Matrix.conjTranspose_mul, supp_herm, hX.eq] at this

lemma spec_nn {X : Mat I} (hX : X.PosSemidef) : ∀ x ∈ spectrum ℝ X, 0 ≤ x := by
  intro x hx
  obtain ⟨j, rfl⟩ := hX.1.spectrum_real_eq_range_eigenvalues ▸ hx
  exact hX.eigenvalues_nonneg j

lemma sqrt_herm (X : Mat I) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X := by
  have : IsSelfAdjoint (cfc Real.sqrt X) := cfc_predicate _ _
  exact this

lemma sqrt_sq {X : Mat I} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  rw [cmul]
  conv_rhs => rw [← cfc_id' ℝ X hX.1.isSelfAdjoint]
  apply cfc_congr
  intro x hx
  exact Real.mul_self_sqrt (spec_nn hX x hx)

lemma supp_sqrt (X : Mat I) : supp X * cfc Real.sqrt X = cfc Real.sqrt X := by
  unfold supp supportPower
  rw [cmul]
  congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]

lemma sqrt_inv {X : Mat I} (hX : X.PosSemidef) :
    cfc Real.sqrt X * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) X = supp X := by
  unfold supp supportPower
  rw [cmul]
  apply cfc_congr
  intro x hx
  have h0 := spec_nn hX x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have : 0 < Real.sqrt x := Real.sqrt_pos.2 (lt_of_le_of_ne h0 (Ne.symm hx0))
    simp [hx0, this.ne']

lemma inv_mid {X : Mat I} (hX : X.PosSemidef) :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) X * X * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) X = supp X := by
  have e : X = cfc (fun x : ℝ => x) X := (cfc_id' ℝ X hX.1.isSelfAdjoint).symm
  conv_lhs => arg 1; arg 2; rw [e]
  rw [cmul, cmul]
  unfold supp supportPower
  apply cfc_congr
  intro x hx
  have h0 := spec_nn hX x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (lt_of_le_of_ne h0 (Ne.symm hx0))
    have hsq := Real.mul_self_sqrt h0
    have hr : x.rpow 0 = 1 := Real.rpow_zero x
    simp only [hx0, if_false, hr]
    field_simp
    linarith

/-- If P is PSD and Vᴴ P V = 0 then P V = 0. -/
lemma zero_of {P V : Mat I} (hP : P.PosSemidef) (h : Vᴴ * P * V = 0) : P * V = 0 := by
  set Q := cfc Real.sqrt P
  have hQ : Qᴴ = Q := sqrt_herm P
  have hQQ : Q * Q = P := sqrt_sq hP
  have : (Q * V)ᴴ * (Q * V) = 0 := by
    rw [Matrix.conjTranspose_mul, hQ, ← h, ← hQQ]; simp only [Matrix.mul_assoc]
  have hQV : Q * V = 0 := Matrix.conjTranspose_mul_self_eq_zero.1 this
  rw [← hQQ, Matrix.mul_assoc, hQV, Matrix.mul_zero]

lemma psd_antisymm {X : Mat I} (h1 : X.PosSemidef) (h2 : (-X).PosSemidef) : X = 0 := by
  have t1 := h1.trace_nonneg
  have t2 := h2.trace_nonneg
  rw [Matrix.trace_neg, neg_nonneg] at t2
  exact h1.trace_eq_zero_iff.1 (le_antisymm t2 t1)

lemma tr_re_zero {X : Mat I} (h : X.PosSemidef) (h0 : X.trace.re = 0) : X = 0 := by
  have := (Complex.nonneg_iff.mp h.trace_nonneg)
  apply h.trace_eq_zero_iff.1
  apply Complex.ext
  · simpa using h0
  · simpa using this.2.symm

lemma tr_re_nonneg {X : Mat I} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma sum4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, F a b c d :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Hilbert–Schmidt duality for channelAdjoint. -/
lemma duality (N : MatrixMap I J) (Z : Mat I) (X : Mat J) :
    (Zᴴ * channelAdjoint N X).trace = ((N Z)ᴴ * X).trace := by
  have hNZ : ∀ k l, N Z k l = ∑ j, ∑ i, Z j i * N (Matrix.single j i 1) k l := by
    intro k l
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    have : ∀ j i, Matrix.single j i (Z j i) = Z j i • Matrix.single j i (1 : ℂ) := by
      intro j i; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    simp only [this, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, hNZ,
    channelAdjoint, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact (sum4 _).trans rfl

lemma herm_decomp (A : Alg I) {H : Mat I} (hH : H ∈ A) (hHs : H.IsHermitian) :
    ∃ P N, P ∈ A ∧ N ∈ A ∧ P.PosSemidef ∧ N.PosSemidef ∧ H = P - N := by
  have hcl := isClosed_alg A
  refine ⟨cfc (fun x : ℝ => max x 0) H, cfc (fun x : ℝ => max (-x) 0) H,
    cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (fun x : ℝ => max x 0) hH,
    cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (fun x : ℝ => max (-x) 0) hH, ?_, ?_, ?_⟩
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg (f := fun x : ℝ => max x 0) (a := H) fun x _ => le_max_right _ _
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg (f := fun x : ℝ => max (-x) 0) (a := H) fun x _ => le_max_right _ _
  · rw [← cfc_sub _ _ H (cont H _) (cont H _)]
    conv_lhs => rw [← cfc_id' ℝ H hHs.isSelfAdjoint]
    congr 1; funext x
    rcases le_total x 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.2 h)]

lemma decomp4 (A : Alg I) {X : Mat I} (hX : X ∈ A) :
    ∃ P1 N1 P2 N2, P1 ∈ A ∧ N1 ∈ A ∧ P2 ∈ A ∧ N2 ∈ A ∧ P1.PosSemidef ∧ N1.PosSemidef ∧
      P2.PosSemidef ∧ N2.PosSemidef ∧ X = (P1 - N1) + Complex.I • (P2 - N2) := by
  have hXs : Xᴴ ∈ A := star_mem hX
  set H1 := (1 / 2 : ℂ) • (X + Xᴴ)
  set H2 := (-Complex.I / 2) • (X - Xᴴ)
  have h1A : H1 ∈ A := A.smul_mem (add_mem hX hXs) _
  have h2A : H2 ∈ A := A.smul_mem (sub_mem hX hXs) _
  have h1h : H1.IsHermitian := by
    simp only [H1, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp [Complex.ext_iff]
  have h2h : H2.IsHermitian := by
    simp only [H2, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    rw [← neg_sub, smul_neg, ← neg_smul]; congr 1; simp [Complex.ext_iff]; norm_num
  obtain ⟨P1, N1, a1, b1, c1, d1, e1⟩ := herm_decomp A h1A h1h
  obtain ⟨P2, N2, a2, b2, c2, d2, e2⟩ := herm_decomp A h2A h2h
  refine ⟨P1, N1, P2, N2, a1, b1, a2, b2, c1, d1, c2, d2, ?_⟩
  rw [← e1, ← e2]
  simp only [H1, H2, smul_smul, smul_add, smul_sub]
  have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num
  rw [this]
  module

/-- K0-related: spectral function with f 0 = 0 (if 0 ∈ spec) is absorbed by the support. -/
lemma sf_real {X : Mat I} (hX : X.IsHermitian) (g : ℝ → ℝ) :
    spectralFunction (fun x => (g x : ℂ)) X = cfc g X := by
  rw [hX.cfc_eq]
  unfold spectralFunction Matrix.IsHermitian.cfc
  rw [dif_pos hX, Unitary.conjStarAlgAut_apply]
  rfl

lemma sf_split {X : Mat I} (hX : X.IsHermitian) (f : ℝ → ℂ) :
    spectralFunction f X = spectralFunction (fun x => ((f x).re : ℂ)) X +
      Complex.I • spectralFunction (fun x => ((f x).im : ℂ)) X := by
  unfold spectralFunction
  simp only [dif_pos hX]
  have : Matrix.diagonal (fun j => f (hX.eigenvalues j)) =
      Matrix.diagonal (fun j => ((f (hX.eigenvalues j)).re : ℂ)) +
      Complex.I • Matrix.diagonal (fun j => ((f (hX.eigenvalues j)).im : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply, Complex.ext_iff]
    · simp [Matrix.diagonal_apply, h]
  rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma cfc_supp {X : Mat I} (g : ℝ → ℝ) (hg : 0 ∈ spectrum ℝ X → g 0 = 0) :
    cfc g X * supp X = cfc g X ∧ supp X * cfc g X = cfc g X := by
  unfold supp supportPower
  rw [cmul, cmul]
  constructor <;> apply cfc_congr <;> intro x hx <;> by_cases h0 : x = 0
  · subst h0; simp [hg hx]
  · simp [h0]
  · subst h0; simp [hg hx]
  · simp [h0]

lemma sf_supp {X : Mat I} (hX : X.IsHermitian) (f : ℝ → ℂ) (hf : 0 ∈ spec X → f 0 = 0) :
    spectralFunction f X * supp X = spectralFunction f X ∧
      supp X * spectralFunction f X = spectralFunction f X := by
  have h0 : 0 ∈ spectrum ℝ X → 0 ∈ spec X := fun h => (mem_spec X hX 0).2 h
  rw [sf_split hX, sf_real hX, sf_real hX]
  obtain ⟨a1, a2⟩ := cfc_supp (X := X) (fun x => (f x).re) (fun h => by simp [hf (h0 h)])
  obtain ⟨b1, b2⟩ := cfc_supp (X := X) (fun x => (f x).im) (fun h => by simp [hf (h0 h)])
  constructor
  · rw [Matrix.add_mul, Matrix.smul_mul, a1, b1]
  · rw [Matrix.mul_add, Matrix.mul_smul, a2, b2]


lemma supp_le {X : Mat I} (hX : X.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ (c • X - supp X).PosSemidef := by
  refine ⟨∑ i, (hX.1.eigenvalues i)⁻¹, Finset.sum_nonneg fun i _ => inv_nonneg.2 (hX.eigenvalues_nonneg i), ?_⟩
  set c := ∑ i, (hX.1.eigenvalues i)⁻¹
  have h : c • X - supp X =
      cfc (fun x : ℝ => c * x - (if x = 0 then 0 else Real.rpow x 0)) X := by
    rw [cfc_sub _ _ X (cont X _) (cont X _), cfc_const_mul _ _ X (cont X _),
      cfc_id' ℝ X hX.1.isSelfAdjoint]
    rfl
  rw [h, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro x hx
  obtain ⟨j, rfl⟩ := hX.1.spectrum_real_eq_range_eigenvalues ▸ hx
  have hj := hX.eigenvalues_nonneg j
  by_cases h0 : hX.1.eigenvalues j = 0
  · simp [h0]
  · have hpos : 0 < hX.1.eigenvalues j := lt_of_le_of_ne hj (Ne.symm h0)
    have : (hX.1.eigenvalues j)⁻¹ ≤ c :=
      Finset.single_le_sum (f := fun i => (hX.1.eigenvalues i)⁻¹)
        (fun i _ => inv_nonneg.2 (hX.eigenvalues_nonneg i)) (Finset.mem_univ j)
    have hr : (hX.1.eigenvalues j).rpow 0 = 1 := Real.rpow_zero _
    simp only [h0, if_false, hr]
    have : 1 ≤ c * hX.1.eigenvalues j := by
      calc (1:ℝ) = (hX.1.eigenvalues j)⁻¹ * hX.1.eigenvalues j := by field_simp
        _ ≤ c * hX.1.eigenvalues j := by gcongr
    linarith

lemma le_const {Y : Mat I} (hY : Y.PosSemidef) :
    ∃ T : ℝ, 0 ≤ T ∧ (T • (1 : Mat I) - Y).PosSemidef := by
  refine ⟨∑ i, hY.1.eigenvalues i, Finset.sum_nonneg fun i _ => hY.eigenvalues_nonneg i, ?_⟩
  set T := ∑ i, hY.1.eigenvalues i
  have h : T • (1 : Mat I) - Y = cfc (fun x : ℝ => T - x) Y := by
    rw [cfc_sub _ _ Y (cont Y _) (cont Y _), cfc_const T Y, cfc_id' ℝ Y hY.1.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  rw [h, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro x hx
  obtain ⟨j, rfl⟩ := hY.1.spectrum_real_eq_range_eigenvalues ▸ hx
  have := Finset.single_le_sum (f := fun i => hY.1.eigenvalues i)
        (fun i _ => hY.eigenvalues_nonneg i) (Finset.mem_univ j)
  exact sub_nonneg.2 this

lemma dom {X Y : Mat I} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∃ K : ℝ, (K • X - supp X * Y * supp X).PosSemidef := by
  obtain ⟨c, hc0, hc⟩ := supp_le hX
  obtain ⟨T, hT0, hT⟩ := le_const hY
  set s := supp X
  have h1 : (s * (T • (1 : Mat I) - Y) * sᴴ).PosSemidef := hT.mul_mul_conjTranspose_same s
  rw [supp_herm] at h1
  have h2 : (T • (c • X - s)).PosSemidef := hc.smul hT0
  refine ⟨T * c, ?_⟩
  have : (T * c) • X - s * Y * s = s * (T • (1 : Mat I) - Y) * s + T • (c • X - s) := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, supp_idem, smul_sub, smul_smul]
    abel
  rw [this]; exact h1.add h2

lemma corner (A : Alg I) (Phi : MatrixMap I J) (hp : PositiveOnConcreteAlgebra A Phi)
    {Y : Mat I} (hY : Y ∈ A) (hYp : Y.PosSemidef)
    (hsS : supp Y * channelAdjoint Phi (supp (Phi Y)) = supp Y)
    {W : Mat I} (hW : W ∈ A) (hWp : W.PosSemidef) :
    (Phi (supp Y * W * supp Y)).trace = (supp Y * W * supp Y).trace := by
  have hPY := hp Y hY hYp
  have hsA : supp Y ∈ A := by
    have := isClosed_alg A; exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) _ hY
  set s := supp Y
  set p := supp (Phi Y)
  set Z := s * W * s with hZ
  have hZA : Z ∈ A := mul_mem (mul_mem hsA hW) hsA
  have hZp : Z.PosSemidef := by
    have := hWp.mul_mul_conjTranspose_same s; rwa [supp_herm] at this
  obtain ⟨K, hK⟩ := dom hYp hWp
  have hKA : K • Y - Z ∈ A :=
    sub_mem (by rw [← algebraMap_smul ℂ K Y]; exact A.smul_mem hY _) hZA
  have hPK := hp _ hKA hK
  have hPZ := hp Z hZA hZp
  have hq : (1 - p)ᴴ = 1 - p := by simp [p, Matrix.conjTranspose_sub, supp_herm]
  have hqY : (1 - p) * Phi Y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, supp_mul hPY.1, sub_self]
  have h1 := hPK.mul_mul_conjTranspose_same (1 - p); rw [hq] at h1
  have h2 := hPZ.mul_mul_conjTranspose_same (1 - p); rw [hq] at h2
  have e : (1 - p) * Phi (K • Y - Z) * (1 - p) = -((1 - p) * Phi Z * (1 - p)) := by
    rw [map_sub, LinearMap.map_smul_of_tower, Matrix.mul_sub (1 - p) (K • Phi Y) (Phi Z),
      mul_smul_comm, hqY, smul_zero, zero_sub, Matrix.neg_mul]
  rw [e] at h1
  have h0 := psd_antisymm h2 h1
  have hZq : Phi Z * (1 - p) = 0 := zero_of hPZ (by rw [hq]; exact h0)
  have hZp' : Phi Z * p = Phi Z := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hZq; exact hZq.symm
  have hd := duality Phi Z p
  rw [hZp.1.eq, hPZ.1.eq, hZp'] at hd
  rw [← hd, hZ, Matrix.mul_assoc (s * W) s, hsS]

lemma corner_all (A : Alg I) (Phi : MatrixMap I J) (hp : PositiveOnConcreteAlgebra A Phi)
    {Y : Mat I} (hY : Y ∈ A) (hYp : Y.PosSemidef)
    (hsS : supp Y * channelAdjoint Phi (supp (Phi Y)) = supp Y)
    {X : Mat I} (hX : X ∈ A) :
    (Phi (supp Y * X * supp Y)).trace = (supp Y * X * supp Y).trace := by
  obtain ⟨P1, N1, P2, N2, a1, b1, a2, b2, c1, d1, c2, d2, e⟩ := decomp4 A hX
  set s := supp Y
  have ex : s * X * s = (s * P1 * s - s * N1 * s) + Complex.I • (s * P2 * s - s * N2 * s) := by
    rw [e]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [ex, map_add, map_sub, map_smul, map_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_sub, corner A Phi hp hY hYp hsS a1 c1, corner A Phi hp hY hYp hsS b1 d1,
    corner A Phi hp hY hYp hsS a2 c2, corner A Phi hp hY hYp hsS b2 d2]

theorem main [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (Y : Mat I) (hY : Y ∈ A) (hYp : Y.PosSemidef)
    (hb : LE (channelAdjoint Phi (supp (Phi Y))) 1) :
    let S := channelAdjoint Phi (supp (Phi Y))
    let c1 := tr (Phi Y) = tr Y
    let c2 := ∀ f : ℝ → ℂ, (0 ∈ spec Y → f 0 = 0) →
      spectralFunction f Y * S = spectralFunction f Y ∧ S * spectralFunction f Y = spectralFunction f Y
    let c3 := LE (supp Y) (spectralProjector S 1)
    let c4 := CornerTP A Phi (supp Y)
    let c5 := petz Y Phi (Phi Y) = Y
    tr (Phi Y) ≤ tr Y ∧ (c1 ↔ c2) ∧ (c2 ↔ c3) ∧ (c3 ↔ c4) ∧ (c4 ↔ c5) ∧
      (c1 → ∀ X ∈ A, X.PosSemidef → Supports X Y → tr (Phi X) = tr X) := by
  intro S c1 c2 c3 c4 c5
  have hPY := hp Y hY hYp
  have hb' : (1 - S).PosSemidef := hb
  have hSh : S.IsHermitian := by
    have := (Matrix.isHermitian_one (n := I) (α := ℂ)).sub hb'.1; simpa using this
  have hSY : (Y * S).trace = (Phi Y).trace := by
    have := duality Phi Y (supp (Phi Y))
    rw [hYp.1.eq, hPY.1.eq, mul_supp hPY.1] at this; exact this
  set s := supp Y with hs_def
  set R := cfc Real.sqrt Y with hR_def
  have hRh : Rᴴ = R := sqrt_herm Y
  have hRR : R * R = Y := sqrt_sq hYp
  set M := R * (1 - S) * R with hM
  have hMp : M.PosSemidef := by
    have := hb'.mul_mul_conjTranspose_same R; rwa [hRh] at this
  have hMtr : M.trace = Y.trace - (Phi Y).trace := by
    rw [hM, Matrix.trace_mul_cycle, hRR, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hSY]
  have htr : tr Y - tr (Phi Y) = M.trace.re := by unfold tr; rw [hMtr, Complex.sub_re]
  have hle : tr (Phi Y) ≤ tr Y := by have := tr_re_nonneg hMp; linarith
  have e1 : c1 ↔ M = 0 := by
    constructor
    · intro h
      have h' : tr (Phi Y) = tr Y := h
      apply tr_re_zero hMp; rw [← htr]; linarith
    · intro h
      have : M.trace.re = 0 := by rw [h]; simp
      show tr (Phi Y) = tr Y; linarith
  have eM : M = 0 ↔ S * s = s := by
    constructor
    · intro h
      have hQR : (1 - S) * R = 0 := zero_of hb' (by rw [hRh]; exact h)
      have : (1 - S) * s = 0 := by
        rw [hs_def, ← sqrt_inv hYp, ← hR_def, ← Matrix.mul_assoc, hQR, Matrix.zero_mul]
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this; exact this.symm
    · intro h
      have hQs : (1 - S) * s = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
      have hQR : (1 - S) * R = 0 := by
        rw [hR_def, ← supp_sqrt Y, ← hs_def, ← Matrix.mul_assoc, hQs, Matrix.zero_mul]
      rw [hM, Matrix.mul_assoc, hQR, Matrix.mul_zero]
  have hsS : S * s = s → s * S = s := fun h => by
    have := congrArg Matrix.conjTranspose h
    rwa [Matrix.conjTranspose_mul, hSh.eq, hs_def, supp_herm] at this
  have e2 : c2 ↔ S * s = s := by
    constructor
    · intro h
      have := (h (fun x => ((if x = 0 then 0 else Real.rpow x 0 : ℝ) : ℂ)) (fun _ => by simp)).2
      rw [sf_real hYp.1] at this
      exact this
    · intro h f hf
      obtain ⟨a1, a2⟩ := sf_supp hYp.1 f hf
      have h' := hsS h
      constructor
      · conv_lhs => rw [← a1]
        rw [Matrix.mul_assoc, h', a1]
      · conv_lhs => rw [← a2]
        rw [← Matrix.mul_assoc, h, a2]
  have e3 : c3 ↔ S * s = s := by
    have hP := proj_eq_cfc S hSh 1
    have hP1h : (spectralProjector S 1)ᴴ = spectralProjector S 1 := by
      rw [hP]; have : IsSelfAdjoint (cfc (ind 1) S) := cfc_predicate _ _; exact this
    have hP1i : spectralProjector S 1 * spectralProjector S 1 = spectralProjector S 1 := by
      rw [hP, cmul]; congr 1; funext x; unfold ind; split_ifs <;> simp
    have hSP : S * spectralProjector S 1 = spectralProjector S 1 := by
      rw [hP]; conv_lhs => arg 1; rw [← cfc_id' ℝ S hSh.isSelfAdjoint]
      rw [cmul]; congr 1; funext x; unfold ind; split_ifs with h <;> simp [h]
    have h2 : 1 - spectralProjector S 1 =
        cfc (fun x : ℝ => if x = 1 then 0 else (x - 1)⁻¹) S * (S - ((1 : ℝ) : ℂ) • 1) := by
      have : S - ((1 : ℝ) : ℂ) • 1 = cfc (fun x : ℝ => x - 1) S := by
        rw [cfc_sub (fun x => x) (fun _ => 1) S, cfc_id' ℝ S hSh.isSelfAdjoint, cfc_const 1 S,
          algebraMap_eq]
      rw [this, cmul, hP, ← cfc_one ℝ S, ← cfc_sub (1 : ℝ → ℝ) (ind 1) S (cont _ _) (cont _ _)]
      congr 1; funext x; unfold ind; split_ifs with h
      · simp
      · have : x - 1 ≠ 0 := sub_ne_zero.mpr h
        simp [this]
    set P1 := spectralProjector S 1
    have hsh : sᴴ = s := supp_herm Y
    have hsi : s * s = s := supp_idem Y
    constructor
    · intro h
      have h' : (P1 - s).PosSemidef := h
      have hq : (1 - P1)ᴴ = 1 - P1 := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP1h]
      have hE := h'.mul_mul_conjTranspose_same (1 - P1)
      rw [hq] at hE
      have h0 : (1 - P1) * P1 = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hP1i, sub_self]
      have hF : (1 - P1) * (P1 - s) * (1 - P1) = -((s * (1 - P1))ᴴ * (s * (1 - P1))) := by
        rw [Matrix.conjTranspose_mul, hq, hsh, Matrix.mul_sub (1 - P1) P1 s, h0, zero_sub,
          Matrix.neg_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (1 - P1) s s, hsi]
      rw [hF] at hE
      have hF0 := psd_antisymm (Matrix.posSemidef_conjTranspose_mul_self _) hE
      have hs1 : s * (1 - P1) = 0 := Matrix.conjTranspose_mul_self_eq_zero.1 hF0
      have hsP : s * P1 = s := by
        rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hs1; exact hs1.symm
      have hPs : P1 * s = s := by
        have := congrArg Matrix.conjTranspose hsP
        rwa [Matrix.conjTranspose_mul, hP1h, hsh] at this
      rw [← hPs, ← Matrix.mul_assoc, hSP]
    · intro h
      have hS1 : (S - ((1 : ℝ) : ℂ) • 1) * s = 0 := by
        rw [Complex.ofReal_one, one_smul, Matrix.sub_mul, Matrix.one_mul, h, sub_self]
      have hPs : P1 * s = s := by
        have : (1 - P1) * s = 0 := by rw [h2, Matrix.mul_assoc, hS1, Matrix.mul_zero]
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this; exact this.symm
      have hsP : s * P1 = s := by
        have := congrArg Matrix.conjTranspose hPs
        rwa [Matrix.conjTranspose_mul, hP1h, hsh] at this
      show (P1 - s).PosSemidef
      have : P1 - s = (P1 - s)ᴴ * (P1 - s) := by
        rw [Matrix.conjTranspose_sub, hP1h, hsh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
          hP1i, hPs, hsP, hsi]
        abel
      rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have e4 : c4 ↔ S * s = s := by
    constructor
    · intro h
      have := h Y hY
      rw [Matrix.mul_assoc, mul_supp hYp.1, supp_mul hYp.1] at this
      rw [← eM, ← e1]; show tr (Phi Y) = tr Y; unfold tr; rw [this]
    · intro h X hX
      exact corner_all A Phi hp hY hYp (hsS h) hX
  have e5 : c5 ↔ M = 0 := by
    have hpetz : petz Y Phi (Phi Y) = R * S * R := by
      show R * channelAdjoint Phi (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (Phi Y) * Phi Y *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (Phi Y)) * R = R * S * R
      rw [inv_mid hPY]
    show petz Y Phi (Phi Y) = Y ↔ M = 0
    rw [hpetz, hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRR]
    constructor
    · intro h; rw [h, sub_self]
    · intro h; exact (sub_eq_zero.1 h).symm
  have e6 : c1 → ∀ X ∈ A, X.PosSemidef → Supports X Y → tr (Phi X) = tr X := by
    intro h X hX hXp hsup
    have hc4 : c4 := e4.2 (eM.1 (e1.1 h))
    have hY1 : Y * (1 - s) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, mul_supp hYp.1, sub_self]
    have hX1 : X * (1 - s) = 0 := by
      ext i j
      have hv : Y.mulVec (fun k => (1 - s) k j) = 0 := funext fun a => congrFun (congrFun hY1 a) j
      exact congrFun (hsup _ hv) i
    have hXs : X * s = X := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hX1; exact hX1.symm
    have hsX : s * X = X := by
      have := congrArg Matrix.conjTranspose hXs
      rwa [Matrix.conjTranspose_mul, hXp.1.eq, hs_def, supp_herm] at this
    have := hc4 X hX
    rw [hsX, hXs] at this
    unfold tr; rw [this]
  exact ⟨hle, (e1.trans eM).trans e2.symm, e2.trans e3.symm, e3.trans e4.symm,
    e4.trans (eM.symm.trans e5.symm), e6⟩

end A3S55L32

end QAlgorithms.Papers.Independent.Support50.P12

open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz)
open QAlgorithms.Papers.Independent.Next46.P23 (Supports)
open QAlgorithms (spectralProjector)
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (Y : Mat I) (hY : Y ∈ A) (hYp : Y.PosSemidef)
    (hb : LE (channelAdjoint Phi (supp (Phi Y))) 1) :
    let S := channelAdjoint Phi (supp (Phi Y))
    let c1 := tr (Phi Y) = tr Y
    let c2 := ∀ f : ℝ → ℂ, (0 ∈ spec Y → f 0 = 0) →
      spectralFunction f Y * S = spectralFunction f Y ∧ S * spectralFunction f Y = spectralFunction f Y
    let c3 := LE (supp Y) (spectralProjector S 1)
    let c4 := CornerTP A Phi (supp Y)
    let c5 := petz Y Phi (Phi Y) = Y
    tr (Phi Y) ≤ tr Y ∧ (c1 ↔ c2) ∧ (c2 ↔ c3) ∧ (c3 ↔ c4) ∧ (c4 ↔ c5) ∧
      (c1 → ∀ X ∈ A, X.PosSemidef → Supports X Y → tr (Phi X) = tr X) :=
  A3S55L32.main A B Phi hc hp Y hY hYp hb

end
