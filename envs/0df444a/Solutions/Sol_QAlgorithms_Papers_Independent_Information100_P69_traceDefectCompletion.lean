-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P69.traceDefectCompletion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:09:51.774482+00:00
-- url     : https://prove2.me/submissions/41d12425-fcf9-4d6d-a049-737b7bfc3dba

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P69

/-- Euclidean norm of a plain vector. -/
def S200T_nv {n : Type*} [Fintype n] (x : n → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖

lemma S200T_nv_sq {n : Type*} [Fintype n] (x : n → ℂ) : S200T_nv x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold S200T_nv; rw [EuclideanSpace.norm_sq_eq]

lemma S200T_nv_nonneg {n : Type*} [Fintype n] (x : n → ℂ) : 0 ≤ S200T_nv x := norm_nonneg _

lemma S200T_cs {n : Type*} [Fintype n] (a b : n → ℂ) :
    ‖∑ i, star (a i) * b i‖ ≤ S200T_nv a * S200T_nv b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ n) (WithLp.toLp 2 b)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  unfold S200T_nv
  have e : ∑ i, star (a i) * b i = b ⬝ᵥ star a := by
    simp only [dotProduct, Pi.star_apply]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]; exact h

lemma S200T_dot_self {n : Type*} [Fintype n] (x : n → ℂ) :
    (∑ i, star (x i) * x i) = ((S200T_nv x ^ 2 : ℝ) : ℂ) := by
  rw [S200T_nv_sq]; push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul]; norm_cast

lemma S200T_opnorm_vec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (Z : Matrix m n ℂ)
    (x : n → ℂ) : S200T_nv (Z *ᵥ x) ≤ specNorm Z * S200T_nv x := by
  have := Matrix.l2_opNorm_mulVec Z (WithLp.toLp 2 x)
  exact this

/-- (a): duality upper bound. -/
lemma S200T_tn_eq {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    traceNorm M = ∑ k, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues k) := by
  have hY := Matrix.isHermitian_conjTranspose_mul_self M
  unfold traceNorm
  rw [hY.cfc_eq Real.sqrt, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  simp [Complex.re_sum]

lemma S200T_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma S200T_NN {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    let hY := Matrix.isHermitian_conjTranspose_mul_self M
    (M * (hY.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (M * (hY.eigenvectorUnitary : Matrix n n ℂ)) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  intro hY
  rw [← S200T_conj_eig hY, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]

lemma S200T_col {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ) (mu : n → ℝ)
    (h : Nᴴ * N = Matrix.diagonal (RCLike.ofReal ∘ mu)) (k : n) :
    S200T_nv (fun i => N i k) ^ 2 = mu k := by
  have := congrFun (congrFun h k) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
    Function.comp] at this
  have h2 := S200T_dot_self (fun i => N i k)
  rw [this] at h2
  exact_mod_cast (Complex.ofReal_injective h2).symm

lemma S200T_unit_col {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (h : star U * U = 1) (k : n) : S200T_nv (fun i => U i k) = 1 := by
  have h' : Uᴴ * U = Matrix.diagonal (RCLike.ofReal ∘ fun _ => (1:ℝ)) := by
    rw [← Matrix.star_eq_conjTranspose, h]; ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  have := S200T_col U _ h' k
  nlinarith [S200T_nv_nonneg (fun i => U i k)]

lemma S200T_tr_le {n : Type*} [Fintype n] [DecidableEq n] (M Z : Matrix n n ℂ) (c : ℝ)
    (hZ : ∀ x : n → ℂ, S200T_nv (Z *ᵥ x) ≤ c * S200T_nv x) :
    ‖(Z * M).trace‖ ≤ c * traceNorm M := by
  have hY := Matrix.isHermitian_conjTranspose_mul_self M
  set U := (hY.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hu1 : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  have hu2 : U * star U = 1 := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  set N := M * U
  have hNN : Nᴴ * N = Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := S200T_NN M
  have htr : (Z * M).trace = ∑ k, ∑ i, star (U i k) * (Z *ᵥ (fun i => N i k)) i := by
    have : (Z * M).trace = (star U * (Z * N)).trace := by
      rw [Matrix.trace_mul_comm (star U) (Z * N)]
      simp only [N]
      calc (Z * M).trace = (Z * M * (U * star U)).trace := by rw [hu2, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Matrix.mulVec,
      dotProduct]
  rw [htr, S200T_tn_eq, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (S200T_cs _ _).trans ?_
  rw [S200T_unit_col U hu1 k, one_mul]
  refine (hZ _).trans (le_of_eq ?_)
  congr 1
  rw [← S200T_col N _ hNN k, Real.sqrt_sq (S200T_nv_nonneg _)]

open scoped Matrix.Norms.L2Operator in
lemma S200T_exists {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    ∃ Z : Matrix n n ℂ, specNorm Z ≤ 1 ∧ (Z * M).trace = (traceNorm M : ℂ) := by
  have hY := Matrix.isHermitian_conjTranspose_mul_self M
  set U := (hY.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hu1 : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  set N := M * U
  have hNN : Nᴴ * N = Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := S200T_NN M
  set mu := hY.eigenvalues
  have hmu : ∀ k, 0 ≤ mu k := fun k => Matrix.eigenvalues_conjTranspose_mul_self_nonneg M k
  set c : n → ℝ := fun k => if 0 < mu k then (Real.sqrt (mu k))⁻¹ else 0 with hc
  set G := Matrix.diagonal (fun k => (c k : ℂ)) * Nᴴ
  have hGG : G * Gᴴ = Matrix.diagonal (fun k => ((c k * mu k * c k : ℝ) : ℂ)) := by
    simp only [G, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Nᴴ, hNN, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext k; simp [Complex.conj_ofReal]; ring
  have hpi : ∀ k, |c k * mu k * c k| ≤ 1 := by
    intro k
    simp only [c]
    split_ifs with h
    · have hs := Real.sq_sqrt (hmu k)
      have hs0 : 0 < Real.sqrt (mu k) := Real.sqrt_pos.2 h
      have : (Real.sqrt (mu k))⁻¹ * mu k * (Real.sqrt (mu k))⁻¹ = 1 := by
        calc (Real.sqrt (mu k))⁻¹ * mu k * (Real.sqrt (mu k))⁻¹
            = (Real.sqrt (mu k))⁻¹ * (Real.sqrt (mu k))^2 * (Real.sqrt (mu k))⁻¹ := by rw [hs]
          _ = 1 := by field_simp
      rw [this]; simp
    · simp
  have hGn : ‖G‖ ≤ 1 := by
    have h1 : ‖G‖ * ‖G‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose G, ← Matrix.l2_opNorm_conjTranspose_mul_self,
        Matrix.conjTranspose_conjTranspose, hGG, Matrix.l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hpi k
    nlinarith [norm_nonneg G]
  have hUn : ‖U‖ ≤ 1 := by
    have h1 : ‖U‖ * ‖U‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose, hu1,
        ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
      simp
    nlinarith [norm_nonneg U]
  refine ⟨U * G, ?_, ?_⟩
  · show ‖U * G‖ ≤ 1
    calc ‖U * G‖ ≤ ‖U‖ * ‖G‖ := Matrix.l2_opNorm_mul U G
      _ ≤ 1 * 1 := mul_le_mul hUn hGn (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    have : G * (M * U) = Matrix.diagonal (fun k => ((c k * mu k : ℝ) : ℂ)) := by
      show G * N = _
      simp only [G]
      rw [Matrix.mul_assoc, hNN, Matrix.diagonal_mul_diagonal]
      congr 1; funext k; simp
    rw [this, Matrix.trace_diagonal, S200T_tn_eq]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    norm_cast
    simp only [c, mu]
    split_ifs with h
    · have hs := Real.sq_sqrt (hmu k)
      have hs0 : 0 < Real.sqrt (mu k) := Real.sqrt_pos.2 h
      simp only [mu] at hs hs0
      calc (Real.sqrt (hY.eigenvalues k))⁻¹ * hY.eigenvalues k
          = (Real.sqrt (hY.eigenvalues k))⁻¹ * (Real.sqrt (hY.eigenvalues k))^2 := by rw [hs]
        _ = _ := by field_simp
    · have : mu k = 0 := le_antisymm (not_lt.1 h) (hmu k)
      simp only [mu] at this
      rw [this]; simp

lemma S200T_nv_eq {n : Type*} [Fintype n] (x : n → ℂ) :
    S200T_nv x = Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  rw [← S200T_nv_sq, Real.sqrt_sq (S200T_nv_nonneg x)]

lemma S200T_exists' {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    ∃ Z : Matrix n n ℂ, (∀ x, S200T_nv (Z *ᵥ x) ≤ 1 * S200T_nv x) ∧
      (Z * M).trace = (traceNorm M : ℂ) := by
  obtain ⟨Z, h1, h2⟩ := S200T_exists M
  exact ⟨Z, fun x => (S200T_opnorm_vec Z x).trans
    (mul_le_mul_of_nonneg_right h1 (S200T_nv_nonneg _)), h2⟩

lemma S200T_tn_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    0 ≤ traceNorm M := by
  rw [S200T_tn_eq]; exact Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _

lemma S200T_tn_re {n : Type*} [Fintype n] [DecidableEq n] (M Z : Matrix n n ℂ)
    (h : (Z * M).trace = (traceNorm M : ℂ)) : traceNorm M = (Z * M).trace.re := by
  rw [h, Complex.ofReal_re]

lemma S200T_tn_add {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) :
    traceNorm (X + Y) ≤ traceNorm X + traceNorm Y := by
  obtain ⟨Z, h1, h2⟩ := S200T_exists' (X + Y)
  rw [S200T_tn_re _ _ h2, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have a := S200T_tr_le X Z 1 h1
  have b := S200T_tr_le Y Z 1 h1
  have a' := Complex.re_le_norm (Z * X).trace
  have b' := Complex.re_le_norm (Z * Y).trace
  linarith

lemma S200T_tn_smul {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) (X : Matrix n n ℂ) :
    traceNorm (c • X) ≤ ‖c‖ * traceNorm X := by
  obtain ⟨Z, h1, h2⟩ := S200T_exists' (c • X)
  rw [S200T_tn_re _ _ h2, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have a := S200T_tr_le X Z 1 h1
  calc (c * (Z * X).trace).re ≤ ‖c * (Z * X).trace‖ := Complex.re_le_norm _
    _ = ‖c‖ * ‖(Z * X).trace‖ := norm_mul _ _
    _ ≤ ‖c‖ * traceNorm X := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

lemma S200T_tn_zero {n : Type*} [Fintype n] [DecidableEq n] : traceNorm (0 : Matrix n n ℂ) = 0 := by
  have := S200T_tn_smul 0 (0 : Matrix n n ℂ)
  simp at this
  exact le_antisymm (by simpa using this) (S200T_tn_nonneg _)

lemma S200T_tn_sum {n ι : Type*} [Fintype n] [DecidableEq n] (s : Finset ι) (f : ι → Matrix n n ℂ) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S200T_tn_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (S200T_tn_add _ _).trans (by linarith)

lemma S200T_abs_tr {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    ‖M.trace‖ ≤ traceNorm M := by
  have := S200T_tr_le M 1 1 (fun x => by simp)
  simpa using this

lemma S200T_entry {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (a b : n) :
    ‖M a b‖ ≤ traceNorm M := by
  have h := S200T_tr_le M (Matrix.single b a 1) 1 (fun x => by
    rw [one_mul, S200T_nv_eq, S200T_nv_eq]
    refine Real.sqrt_le_sqrt ?_
    have : ∀ i, (Matrix.single b a (1:ℂ) *ᵥ x) i = if i = b then x a else 0 := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
      by_cases h : i = b
      · subst h; simp
      · have h' : ¬ b = i := fun e => h e.symm
        simp [h', h]
    simp only [this]
    rw [Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
    simp only [if_true]
    exact Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ a))
  have e : (Matrix.single b a (1:ℂ) * M).trace = M a b := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [e] at h; simpa using h

lemma S200T_lin_bound {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix k k ℂ) :
    ∃ C, ∀ X, traceNorm (Φ X) ≤ C * traceNorm X := by
  refine ⟨∑ a, ∑ b, traceNorm (Φ (Matrix.single a b (1:ℂ))), fun X => ?_⟩
  have hX : Φ X = ∑ a, ∑ b, X a b • Φ (Matrix.single a b (1:ℂ)) := by
    have e : X = ∑ a, ∑ b, X a b • Matrix.single a b (1:ℂ) := by
      ext i j; simp [Matrix.sum_apply, Matrix.single_apply, ite_and]
    conv_lhs => rw [e]
    simp only [map_sum, map_smul]
  rw [hX]
  refine (S200T_tn_sum _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (S200T_tn_sum _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  refine (S200T_tn_smul _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (S200T_entry X a b) (S200T_tn_nonneg _)

lemma S200T_dot_eq {n : Type*} [Fintype n] (x : n → ℂ) :
    star x ⬝ᵥ x = ((S200T_nv x ^ 2 : ℝ) : ℂ) := by
  rw [← S200T_dot_self]; rfl

lemma S200T_dot_le {n : Type*} [Fintype n] (a b : n → ℂ) :
    ‖star a ⬝ᵥ b‖ ≤ S200T_nv a * S200T_nv b := S200T_cs a b

lemma S200T_dot_adj {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (y : n → ℂ)
    (u : m → ℂ) : star y ⬝ᵥ (Aᴴ *ᵥ u) = star (A *ᵥ y) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

lemma S200T_kraus_vec {m n J : Type*} [Fintype m] [Fintype n] [Fintype J]
    (S : J → Matrix m n ℂ) (c : ℝ) (hc0 : 0 ≤ c) (Z : Matrix m m ℂ)
    (hZ : ∀ x, S200T_nv (Z *ᵥ x) ≤ 1 * S200T_nv x)
    (hS : ∀ x, ∑ j, S200T_nv (S j *ᵥ x) ^ 2 ≤ c * S200T_nv x ^ 2) (x : n → ℂ) :
    S200T_nv ((∑ j, (S j)ᴴ * Z * S j) *ᵥ x) ≤ c * S200T_nv x := by
  obtain ⟨y, hydef⟩ : ∃ y, y = (∑ j, (S j)ᴴ * Z * S j) *ᵥ x := ⟨_, rfl⟩
  rw [← hydef]
  have e1 : star y ⬝ᵥ y = ∑ j, star (S j *ᵥ y) ⬝ᵥ (Z *ᵥ (S j *ᵥ x)) := by
    nth_rewrite 2 [hydef]
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, S200T_dot_adj]
  have e2 : S200T_nv y ^ 2 ≤ ∑ j, S200T_nv (S j *ᵥ y) * S200T_nv (S j *ᵥ x) := by
    have h := congrArg Complex.re e1
    rw [S200T_dot_eq, Complex.ofReal_re] at h
    rw [h, Complex.re_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Complex.re_le_norm _).trans ((S200T_dot_le _ _).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (S200T_nv_nonneg _)
    simpa using hZ (S j *ᵥ x)
  have e3 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => S200T_nv (S j *ᵥ y))
    (fun j => S200T_nv (S j *ᵥ x))
  have hy := hS y
  have hx := hS x
  have e4 : Real.sqrt (∑ j, S200T_nv (S j *ᵥ y) ^ 2) ≤ Real.sqrt c * S200T_nv y := by
    rw [← Real.sqrt_sq (S200T_nv_nonneg y), ← Real.sqrt_mul hc0]
    exact Real.sqrt_le_sqrt hy
  have e5 : Real.sqrt (∑ j, S200T_nv (S j *ᵥ x) ^ 2) ≤ Real.sqrt c * S200T_nv x := by
    rw [← Real.sqrt_sq (S200T_nv_nonneg x), ← Real.sqrt_mul hc0]
    exact Real.sqrt_le_sqrt hx
  have hsc := Real.mul_self_sqrt hc0
  have hsc0 := Real.sqrt_nonneg c
  have hny := S200T_nv_nonneg y
  have hnx := S200T_nv_nonneg x
  have e6 : S200T_nv y ^ 2 ≤ c * S200T_nv y * S200T_nv x := by
    calc S200T_nv y ^ 2 ≤ (Real.sqrt c * S200T_nv y) * (Real.sqrt c * S200T_nv x) :=
          e2.trans (e3.trans (mul_le_mul e4 e5 (Real.sqrt_nonneg _) (by positivity)))
      _ = c * S200T_nv y * S200T_nv x := by linear_combination (S200T_nv y * S200T_nv x) * hsc
  rcases eq_or_lt_of_le hny with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

lemma S200T_kraus_bound {m n J : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype J] (S : J → Matrix m n ℂ) (c : ℝ) (hc0 : 0 ≤ c)
    (hS : ∀ x, ∑ j, S200T_nv (S j *ᵥ x) ^ 2 ≤ c * S200T_nv x ^ 2) (X : Matrix n n ℂ) :
    traceNorm (krausApply S X) ≤ c * traceNorm X := by
  obtain ⟨Z, hZ, htr⟩ := S200T_exists' (krausApply S X)
  have e : (Z * krausApply S X).trace = ((∑ j, (S j)ᴴ * Z * S j) * X).trace := by
    unfold krausApply
    rw [Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc (Z * (S j * X * (S j)ᴴ)).trace = ((Z * S j * X) * (S j)ᴴ).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((S j)ᴴ * (Z * S j * X)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [S200T_tn_re _ _ htr, e]
  exact (Complex.re_le_norm _).trans
    (S200T_tr_le X _ c (S200T_kraus_vec S c hc0 Z hZ hS))

/-- Lift of a Kraus operator to `id_R ⊗ K`. -/
def S200T_lift {R α β : Type*} [DecidableEq R] (K : Matrix β α ℂ) : Matrix (R × β) (R × α) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then K p.2 q.2 else 0

lemma S200T_idT_kraus {R α β J : Type*} [Fintype R] [DecidableEq R] [Fintype α] [Fintype β]
    [Fintype J] (K : J → Matrix β α ℂ) (X : Matrix (R × α) (R × α) ℂ) :
    idTensorSuperop (R := R) (krausApply K) X =
      krausApply (fun j => S200T_lift (R := R) (K j)) X := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, S200T_lift, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, apply_ite (star : ℂ → ℂ), star_zero, mul_ite,
    mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

lemma S200T_lift_nv {R α β J : Type*} [Fintype R] [DecidableEq R] [Fintype α] [Fintype β]
    [Fintype J] (K : J → Matrix β α ℂ) (x : R × α → ℂ) :
    ∑ j, S200T_nv (S200T_lift (R := R) (K j) *ᵥ x) ^ 2 =
      ∑ r, ∑ j, S200T_nv (K j *ᵥ fun a => x (r, a)) ^ 2 := by
  simp only [S200T_nv_sq, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 2
  simp [S200T_lift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

lemma S200T_kraus_quad {α β J : Type*} [Fintype α] [Fintype β] [Fintype J]
    (K : J → Matrix β α ℂ) (w : α → ℂ) :
    ((∑ j, S200T_nv (K j *ᵥ w) ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ ((∑ j, (K j)ᴴ * K j) *ᵥ w) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mulVec_mulVec, S200T_dot_adj, S200T_dot_eq]
  push_cast; ring

lemma S200T_cp_contr {R α β J : Type*} [Fintype R] [DecidableEq R] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype J] (K : J → Matrix β α ℂ) (c : ℝ) (hc0 : 0 ≤ c)
    (hK : ((c : ℂ) • (1 : Matrix α α ℂ) - ∑ j, (K j)ᴴ * K j).PosSemidef)
    (X : Matrix (R × α) (R × α) ℂ) :
    traceNorm (idTensorSuperop (R := R) (krausApply K) X) ≤ c * traceNorm X := by
  rw [S200T_idT_kraus]
  refine S200T_kraus_bound _ c hc0 (fun x => ?_) X
  rw [S200T_lift_nv]
  have hw : ∀ w : α → ℂ, ∑ j, S200T_nv (K j *ᵥ w) ^ 2 ≤ c * S200T_nv w ^ 2 := by
    intro w
    have h := hK.dotProduct_mulVec_nonneg w
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, S200T_dot_eq, ← S200T_kraus_quad, smul_eq_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.zero_le_real] at h
    linarith
  calc ∑ r, ∑ j, S200T_nv (K j *ᵥ fun a => x (r, a)) ^ 2
      ≤ ∑ r, c * S200T_nv (fun a => x (r, a)) ^ 2 := Finset.sum_le_sum fun r _ => hw _
    _ = c * S200T_nv x ^ 2 := by
      rw [← Finset.mul_sum]; congr 1
      simp only [S200T_nv_sq, Fintype.sum_prod_type]

lemma S200T_trace_kraus {α β J : Type*} [Fintype α] [Fintype β] [Fintype J]
    (K : J → Matrix β α ℂ) (X : Matrix α α ℂ) :
    (krausApply K X).trace = ((∑ j, ((K j)ᴴ * K j : Matrix α α ℂ)) * X).trace := by
  unfold krausApply
  rw [Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]

lemma S200T_adj_kraus {α β J : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Fintype J]
    (Q : Superop α β) (K : J → Matrix β α ℂ) (hQ : ∀ X, Q X = krausApply K X) :
    adjointIdentity Q = ∑ j, ((K j)ᴴ * K j : Matrix α α ℂ) := by
  ext i j
  simp only [adjointIdentity, hQ, S200T_trace_kraus]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- Kraus operators of `X ↦ tr(Tᴴ T X) • P Pᴴ`. -/
def S200T_Kr {α β γ δ : Type*} (P : Matrix β γ ℂ) (T : Matrix δ α ℂ) (j : γ × δ) :
    Matrix β α ℂ := Matrix.of fun y x => P y j.1 * T j.2 x

lemma S200T_Kr_apply {α β γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (P : Matrix β γ ℂ) (T : Matrix δ α ℂ) (X : Matrix α α ℂ) :
    krausApply (S200T_Kr P T) X = ((Tᴴ * T : Matrix α α ℂ) * X).trace • (P * Pᴴ : Matrix β β ℂ) := by
  ext y y'
  simp only [krausApply, S200T_Kr, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul,
    Fintype.sum_prod_type, star_mul']
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma S200T_Kr_sum {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : Matrix β γ ℂ) (T : Matrix δ α ℂ) :
    ∑ j, ((S200T_Kr P T j)ᴴ * S200T_Kr P T j : Matrix α α ℂ) =
      (P * Pᴴ : Matrix β β ℂ).trace • (Tᴴ * T : Matrix α α ℂ) := by
  ext x x'
  simp only [S200T_Kr, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul,
    Fintype.sum_prod_type, star_mul']
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun c _ => ?_
  ring

lemma S200T_mp_mul {α β γ : Type*} [Fintype γ] (A : Matrix β γ ℂ) (B : Matrix γ α ℂ) (n : ℕ) :
    matrixPower (A * B : Matrix β α ℂ) n =
      (matrixPower A n * matrixPower B n : Matrix (Sites β n) (Sites α n) ℂ) := by
  ext x y
  simp only [matrixPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma S200T_mp_conj {α β : Type*} (A : Matrix β α ℂ) (n : ℕ) :
    matrixPower Aᴴ n = (matrixPower A n)ᴴ := by
  ext x y
  simp only [matrixPower, Matrix.conjTranspose_apply]
  exact (map_prod (starRingEnd ℂ) (fun i => A (y i) (x i)) Finset.univ).symm

lemma S200T_mp_trace {α : Type*} [Fintype α] (A : Matrix α α ℂ) (n : ℕ) :
    (matrixPower A n).trace = A.trace ^ n := by
  simp only [Matrix.trace, Matrix.diag, matrixPower]
  rw [← Fin.prod_const n (∑ a, A a a), Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma S200T_tr_single {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    (Matrix.single a b (1:ℂ)).trace = if a = b then 1 else 0 := by
  rw [Matrix.trace, Finset.sum_eq_single a]
  · by_cases h : a = b
    · subst h; simp
    · simp [Matrix.single_apply, h, Ne.symm h]
  · intro c _ hc; simp [Matrix.single_apply, Ne.symm hc]
  · simp

lemma S200T_prod_delta {α : Type*} [DecidableEq α] {n : ℕ} (x x' : Fin n → α) :
    (∏ i, (if x i = x' i then (1:ℂ) else 0)) = if x = x' then 1 else 0 := by
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma S200T_pi_trace {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] {n : ℕ}
    (N : Superop α β) (hN : ∀ a b : α, (N (Matrix.single a b 1)).trace = if a = b then 1 else 0)
    (X : Matrix (Sites α n) (Sites α n) ℂ) : (power N n X).trace = X.trace := by
  simp only [power, piSuperop, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have : ∀ x' : Sites α n, ∑ y : Sites β n, ∏ i, N (Matrix.single (x i) (x' i) 1) (y i) (y i) =
      if x = x' then 1 else 0 := by
    intro x'
    have h := Finset.prod_univ_sum (fun _ => (Finset.univ : Finset β))
      (fun i a => N (Matrix.single (x i) (x' i) 1) a a)
    simp only [Fintype.piFinset_univ] at h
    rw [← S200T_prod_delta, ← h]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hN]; rfl
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma S200T_pow_repl {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] {n : ℕ}
    (omega : Matrix β β ℂ) (X : Matrix (Sites α n) (Sites α n) ℂ) :
    power (replacer (A := α) omega) n X = X.trace • matrixPower omega n := by
  ext y y'
  simp only [power, piSuperop, replacer, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    matrixPower]
  simp only [Finset.prod_mul_distrib]
  have : ∀ x x' : Sites α n, (∏ i, (Matrix.single (x i) (x' i) (1:ℂ)).trace) =
      if x = x' then 1 else 0 := by
    intro x x'
    rw [← S200T_prod_delta]
    exact Finset.prod_congr rfl fun i _ => S200T_tr_single _ _
  simp only [this]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]
open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma S200T_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (D : Matrix ι ι ℂ)
    (hD : D.PosSemidef) :
    ((specNorm D : ℂ) • (1 : Matrix ι ι ℂ) - D).PosSemidef ∧
      ∃ v : ι → ℂ, star v ⬝ᵥ v = 1 ∧ D *ᵥ v = (specNorm D : ℂ) • v := by
  have h0 : 0 ≤ D := hD.nonneg
  have hsa : IsSelfAdjoint D := hD.isHermitian.isSelfAdjoint
  constructor
  · have h1 := IsSelfAdjoint.le_algebraMap_norm_self hsa
    rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h1
    have e : ((specNorm D : ℂ) • (1 : Matrix ι ι ℂ)) = ‖D‖ • (1 : Matrix ι ι ℂ) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
    rw [e]; exact h1
  · have h2 := CStarAlgebra.norm_mem_spectrum_of_nonneg h0
    rw [hD.isHermitian.spectrum_real_eq_range_eigenvalues] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨⇑(hD.isHermitian.eigenvectorBasis k), ?_, ?_⟩
    · have hn := (hD.isHermitian.eigenvectorBasis).norm_eq_one k
      have := S200T_dot_eq ⇑(hD.isHermitian.eigenvectorBasis k)
      rw [this]
      unfold S200T_nv
      simp [hn]
    · rw [hD.isHermitian.mulVec_eigenvectorBasis, hk, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl

def S200T_IsLin {ι κ : Type*} [Fintype ι] (T : Superop ι κ) : Prop :=
  (∀ X Y, T (X + Y) = T X + T Y) ∧ ∀ (c : ℂ) X, T (c • X) = c • T X

lemma S200T_lin_kraus {α β J : Type*} [Fintype α] [Fintype J] (K : J → Matrix β α ℂ) :
    S200T_IsLin (krausApply K) := by
  constructor
  · intro X Y; simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro c X; simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma S200T_lin_power {α β : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (N : Superop α β) :
    S200T_IsLin (power N n) := by
  constructor
  · intro X Y; ext y y'
    simp [power, piSuperop, add_mul, Finset.sum_add_distrib]
  · intro c X; ext y y'
    simp [power, piSuperop, Finset.mul_sum, mul_assoc]

lemma S200T_lin_sub {ι κ : Type*} [Fintype ι] {T1 T2 : Superop ι κ} (h1 : S200T_IsLin T1)
    (h2 : S200T_IsLin T2) : S200T_IsLin (T1 - T2) := by
  constructor
  · intro X Y; simp only [Pi.sub_apply, h1.1, h2.1]; abel
  · intro c X; simp only [Pi.sub_apply, h1.2, h2.2, smul_sub]

lemma S200T_lin_zero {ι κ : Type*} [Fintype ι] {T : Superop ι κ} (h : S200T_IsLin T) :
    T 0 = 0 := by
  have := h.2 0 0; simpa using this

lemma S200T_lin_idT {R ι κ : Type*} [Fintype R] [Fintype ι] {T : Superop ι κ}
    (h : S200T_IsLin T) : S200T_IsLin (idTensorSuperop (R := R) T) := by
  constructor
  · intro X Y; ext p q
    simp only [idTensorSuperop, Matrix.of_apply, Matrix.add_apply]
    have : (Matrix.of fun i i' => X (p.1, i) (q.1, i') + Y (p.1, i) (q.1, i')) =
        Matrix.of (fun i i' => X (p.1, i) (q.1, i')) + Matrix.of (fun i i' => Y (p.1, i) (q.1, i')) := by
      ext; rfl
    rw [this, h.1]; rfl
  · intro c X; ext p q
    simp only [idTensorSuperop, Matrix.of_apply, Matrix.smul_apply]
    have : (Matrix.of fun i i' => c • X (p.1, i) (q.1, i')) =
        c • Matrix.of (fun i i' => X (p.1, i) (q.1, i')) := by
      ext; rfl
    rw [this, h.2]; rfl

lemma S200T_lin_bnd {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {Φ : Superop m k} (h : S200T_IsLin Φ) : ∃ C, ∀ X, traceNorm (Φ X) ≤ C * traceNorm X :=
  S200T_lin_bound ⟨⟨Φ, h.1⟩, h.2⟩

lemma S200T_idT_add {R ι κ : Type*} {T T1 T2 : Superop ι κ} (h : ∀ Y, T Y = T1 Y + T2 Y)
    (X : Matrix (R × ι) (R × ι) ℂ) :
    idTensorSuperop (R := R) T X = idTensorSuperop T1 X + idTensorSuperop T2 X := by
  ext p q
  simp only [idTensorSuperop, Matrix.of_apply, Matrix.add_apply, h]

lemma S200T_factor {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    ∃ (m : ℕ) (B : Matrix (Fin m) ι ℂ), M = (Bᴴ * B : Matrix ι ι ℂ) := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hM
  refine ⟨m, Matrix.of fun i b => star (v i b), ?_⟩
  rw [hv]; ext a b
  simp [Matrix.vecMulVec, Matrix.mul_apply, Matrix.sum_apply]

lemma S200T_cp_of {α β J : Type*} [Fintype α] [Fintype β] [Fintype J] {m : ℕ}
    (F : Superop α β) (K1 : Fin m → Matrix β α ℂ) (K2 : J → Matrix β α ℂ)
    (hF : ∀ X, F X = krausApply K1 X + krausApply K2 X) :
    ∃ (k : ℕ) (E : Fin k → Matrix β α ℂ),
      (∑ j, ((E j)ᴴ * E j : Matrix α α ℂ)) =
        (∑ j, ((K1 j)ᴴ * K1 j : Matrix α α ℂ)) + ∑ j, ((K2 j)ᴴ * K2 j : Matrix α α ℂ) ∧
      ∀ X, F X = krausApply E X := by
  classical
  let e := Fintype.equivFin (Fin m ⊕ J)
  refine ⟨Fintype.card (Fin m ⊕ J), fun i => Sum.elim K1 K2 (e.symm i), ?_, fun X => ?_⟩
  · rw [Equiv.sum_comp e.symm (fun s => ((Sum.elim K1 K2 s)ᴴ * Sum.elim K1 K2 s : Matrix α α ℂ)),
      Fintype.sum_sum_type]
    rfl
  · rw [hF]
    simp only [krausApply]
    rw [Equiv.sum_comp e.symm (fun s => (Sum.elim K1 K2 s * X * (Sum.elim K1 K2 s)ᴴ)),
      Fintype.sum_sum_type]
    rfl

lemma S200T_tr_vmv {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    (A * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ (A *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma S200T_tn_vmv {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) :
    traceNorm (Matrix.vecMulVec w (star w)) ≤ S200T_nv w ^ 2 := by
  obtain ⟨Z, hZ, htr⟩ := S200T_exists' (Matrix.vecMulVec w (star w))
  rw [S200T_tn_re _ _ htr, S200T_tr_vmv]
  refine (Complex.re_le_norm _).trans ((S200T_dot_le _ _).trans ?_)
  have := hZ w
  rw [sq]
  exact mul_le_mul_of_nonneg_left (by simpa using this) (S200T_nv_nonneg _)

open scoped Matrix.Norms.L2Operator in
lemma S200T_specNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℂ) :
    0 ≤ specNorm D := norm_nonneg D


open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem solution [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (n : ℕ) (hn : 1 ≤ n)
    (F : Set (Superop (Sites A n) (Sites B n))) (hF : Convex ℝ F)
    (hchan : ∀ M ∈ F, IsChannel M) (omega : Matrix B B ℂ) (homega : Faithful omega)
    (hR : power (replacer omega) n ∈ F)
    (Q : Superop (Sites A n) (Sites B n)) (hQ : CP Q) (hdef : (defect Q).PosSemidef)
    (M : Superop (Sites A n) (Sites B n)) (hM : M ∈ F)
    (lam : ℝ) (hlam : 1 ≤ lam) (hdom : CPLe Q ((lam:ℂ) • M)) :
    let D := defect Q
    let d := specNorm D
    let L := complete Q D (matrixPower omega n)
    let S := ((lam+d:ℂ)⁻¹) • ((lam:ℂ) • M + (d:ℂ) • power (replacer omega) n)
    IsChannel L ∧ S ∈ F ∧ CPLe L ((lam+d:ℂ) • S) ∧
      diamond (L-power N n) ≤ 2*diamond (Q-power N n) ∧
      0 ≤ d ∧ d ≤ min 1 (diamond (Q-power N n)) := by
  intro D d L S
  obtain ⟨mQ, KQ, hQK⟩ := hQ
  have hadj := S200T_adj_kraus Q KQ hQK
  set E := ∑ j, ((KQ j)ᴴ * KQ j : Matrix (Sites A n) (Sites A n) ℂ) with hE
  have hD : D = 1 - E := by show defect Q = _; rw [defect, hadj]
  obtain ⟨⟨hωpsd, hωtr⟩, -⟩ := homega
  set w' := matrixPower omega n with hw'
  have htrw : w'.trace = 1 := by rw [hw', S200T_mp_trace, hωtr, one_pow]
  obtain ⟨mB, Bm, hB⟩ := S200T_factor omega hωpsd
  set P := (matrixPower Bm n)ᴴ with hPdef
  have hP : (P * Pᴴ : Matrix (Sites B n) (Sites B n) ℂ) = w' := by
    rw [hPdef, Matrix.conjTranspose_conjTranspose, hw', hB, S200T_mp_mul, S200T_mp_conj]
  obtain ⟨mD, TD, hTD⟩ := S200T_factor D hdef
  have hspec := S200T_spec D hdef
  obtain ⟨m2, T2, hT2⟩ := S200T_factor _ hspec.1
  have hG : ∀ X, krausApply (S200T_Kr P TD) X = (D * X).trace • w' := by
    intro X; rw [S200T_Kr_apply, ← hTD, hP]
  have hGs : ∑ j, ((S200T_Kr P TD j)ᴴ * S200T_Kr P TD j : Matrix _ _ ℂ) = D := by
    rw [S200T_Kr_sum, hP, htrw, one_smul, ← hTD]
  have hG2 : ∀ X, krausApply (S200T_Kr P T2) X = (((d:ℂ) • 1 - D) * X).trace • w' := by
    intro X; rw [S200T_Kr_apply, ← hT2, hP]
  have hd0 : 0 ≤ d := by show 0 ≤ specNorm D; exact S200T_specNorm_nonneg D
  obtain ⟨v, hv1, hvD⟩ := hspec.2
  have hs : star v ⬝ᵥ (E *ᵥ v) = ((∑ j, S200T_nv (KQ j *ᵥ v) ^ 2 : ℝ) : ℂ) :=
    (S200T_kraus_quad KQ v).symm
  have hdv : (d : ℂ) = 1 - ((∑ j, S200T_nv (KQ j *ᵥ v) ^ 2 : ℝ) : ℂ) := by
    have : star v ⬝ᵥ (D *ᵥ v) = d := by rw [hvD, dotProduct_smul, hv1, smul_eq_mul, mul_one]
    rw [← this, hD, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hv1, hs]
  have hdreal : d = 1 - ∑ j, S200T_nv (KQ j *ᵥ v) ^ 2 := by exact_mod_cast hdv
  have hd1 : d ≤ 1 := by
    rw [hdreal]; linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg (S200T_nv (KQ j *ᵥ v)))]
  set T0 := Q - power N n with hT0def
  have hQlin : S200T_IsLin Q := by
    have h := S200T_lin_kraus KQ
    exact ⟨fun X Y => by rw [hQK, hQK, hQK]; exact h.1 X Y,
      fun c X => by rw [hQK, hQK]; exact h.2 c X⟩
  have hT0 : S200T_IsLin T0 := S200T_lin_sub hQlin (S200T_lin_power N)
  obtain ⟨C, hC⟩ := S200T_lin_bnd (S200T_lin_idT (R := Sites A n) hT0)
  have hdiam : ∀ X : Matrix (Sites A n × Sites A n) (Sites A n × Sites A n) ℂ, traceNorm X ≤ 1 →
      traceNorm (idTensorSuperop (R := Sites A n) T0 X) ≤ diamond T0 := by
    intro X hX
    refine le_csSup ⟨|C|, ?_⟩ ⟨X, hX, rfl⟩
    rintro _ ⟨Y, hY, rfl⟩
    have h0 := S200T_tn_nonneg Y
    calc traceNorm (idTensorSuperop T0 Y) ≤ C * traceNorm Y := hC Y
      _ ≤ |C| * traceNorm Y := mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hY (abs_nonneg C)
      _ = |C| := mul_one _
  have hN1 : ∀ a b : A, (N (Matrix.single a b 1)).trace = if a = b then 1 else 0 := by
    obtain ⟨mN, EN, hEN, hNE⟩ := hN
    intro a b
    rw [hNE, S200T_trace_kraus]
    unfold IsKrausFamily at hEN
    rw [hEN, Matrix.one_mul, S200T_tr_single]
  obtain r : Sites A n := Classical.arbitrary _
  set wv : Sites A n × Sites A n → ℂ := fun p => if p.1 = r then v p.2 else 0 with hwv
  have hnv1 : S200T_nv v ^ 2 = 1 := by
    have := S200T_dot_eq v; rw [hv1] at this; exact_mod_cast this.symm
  have hX0 : traceNorm (Matrix.vecMulVec wv (star wv)) ≤ 1 := by
    refine (S200T_tn_vmv wv).trans (le_of_eq ?_)
    rw [S200T_nv_sq, Fintype.sum_prod_type, Finset.sum_eq_single r, ← hnv1, S200T_nv_sq]
    · simp [hwv]
    · intro b _ hb; simp [hwv, hb]
    · simp
  have hY : ∀ p1 : Sites A n, (Matrix.of fun i i' => Matrix.vecMulVec wv (star wv) (p1, i) (p1, i')) =
      if p1 = r then Matrix.vecMulVec v (star v) else 0 := by
    intro p1
    by_cases h : p1 = r
    · subst h; ext i i'; simp [hwv, Matrix.vecMulVec_apply]
    · ext i i'; simp [hwv, Matrix.vecMulVec_apply, h]
  have htr0 : (idTensorSuperop (R := Sites A n) T0 (Matrix.vecMulVec wv (star wv))).trace =
      (T0 (Matrix.vecMulVec v (star v))).trace := by
    simp only [Matrix.trace, Matrix.diag, idTensorSuperop, Matrix.of_apply, Fintype.sum_prod_type]
    simp only [hY, apply_ite T0, S200T_lin_zero hT0]
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hT0Y : (T0 (Matrix.vecMulVec v (star v))).trace = -(d:ℂ) := by
    rw [hT0def, Pi.sub_apply, Matrix.trace_sub, hQK, S200T_trace_kraus, ← hE, S200T_tr_vmv, hs,
      S200T_pi_trace N hN1, ← Matrix.one_mul (Matrix.vecMulVec v (star v)), S200T_tr_vmv,
      Matrix.one_mulVec, hv1, hdv]
    ring
  have hdD : d ≤ diamond T0 := by
    have h1 := S200T_abs_tr (idTensorSuperop (R := Sites A n) T0 (Matrix.vecMulVec wv (star wv)))
    rw [htr0, hT0Y, norm_neg, Complex.norm_real, Real.norm_of_nonneg hd0] at h1
    exact h1.trans (hdiam _ hX0)
  have hld : (0:ℝ) < lam + d := by linarith
  have hne : ((lam:ℂ) + (d:ℂ)) ≠ 0 := by exact_mod_cast hld.ne'
  refine ⟨?_, ?_, ?_, ?_, hd0, le_min hd1 hdD⟩
  · obtain ⟨k, Ek, hsum, hFk⟩ := S200T_cp_of L KQ (S200T_Kr P TD)
      (fun X => by show Q X + (D * X).trace • w' = _; rw [hQK, hG])
    refine ⟨k, Ek, ?_, hFk⟩
    unfold IsKrausFamily
    rw [hsum, hGs, hD, ← hE]; abel
  · have e : S = (lam/(lam+d)) • M + (d/(lam+d)) • power (replacer omega) n := by
      funext X
      show ((lam+d:ℂ)⁻¹) • ((lam:ℂ) • M X + (d:ℂ) • power (replacer omega) n X) =
        (lam/(lam+d)) • M X + (d/(lam+d)) • power (replacer omega) n X
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_add, smul_smul, smul_smul]
      congr 2 <;> push_cast <;> field_simp
    rw [e]
    exact hF hM hR (div_nonneg (by linarith) hld.le) (div_nonneg hd0 hld.le) (by field_simp)
  · obtain ⟨m1, K1, hK1⟩ := hdom
    obtain ⟨k, Ek, -, hFk⟩ := S200T_cp_of (((lam:ℂ) + (d:ℂ)) • S - L) K1 (S200T_Kr P T2)
      (fun X => by
        rw [← hK1, hG2]
        show ((lam:ℂ)+(d:ℂ)) • (((lam+d:ℂ)⁻¹) • ((lam:ℂ) • M X + (d:ℂ) • power (replacer omega) n X))
          - (Q X + (D * X).trace • w') = ((lam:ℂ) • M X - Q X) + (((d:ℂ) • 1 - D) * X).trace • w'
        rw [smul_smul, mul_inv_cancel₀ hne, one_smul, S200T_pow_repl, Matrix.sub_mul,
          Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, sub_smul, smul_smul,
          smul_eq_mul]
        abel)
    exact ⟨k, Ek, hFk⟩
  · have key : ∀ X : Matrix (Sites A n × Sites A n) (Sites A n × Sites A n) ℂ, traceNorm X ≤ 1 →
        traceNorm (idTensorSuperop (R := Sites A n) (L - power N n) X) ≤ 2 * diamond T0 := by
      intro X hX
      rw [S200T_idT_add (T1 := T0) (T2 := krausApply (S200T_Kr P TD)) (fun Y => ?_) X]
      · have h0 := S200T_tn_nonneg X
        calc _ ≤ traceNorm (idTensorSuperop (R := Sites A n) T0 X) +
              traceNorm (idTensorSuperop (R := Sites A n) (krausApply (S200T_Kr P TD)) X) :=
              S200T_tn_add _ _
          _ ≤ diamond T0 + d * traceNorm X := add_le_add (hdiam X hX)
              (S200T_cp_contr (R := Sites A n) (S200T_Kr P TD) d hd0 (by rw [hGs]; exact hspec.1) X)
          _ ≤ diamond T0 + d * 1 := by gcongr
          _ ≤ 2 * diamond T0 := by linarith
      · show Q Y + (D * Y).trace • w' - power N n Y = (Q Y - power N n Y) + krausApply (S200T_Kr P TD) Y
        rw [hG]; abel
    exact csSup_le ⟨_, ⟨0, by rw [S200T_tn_zero]; exact zero_le_one, rfl⟩⟩
      (by rintro _ ⟨X, hX, rfl⟩; exact key X hX)

end Statements

end
