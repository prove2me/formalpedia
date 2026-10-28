-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.pure_entropy_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:59:19.869796+00:00
-- url     : https://prove2.me/submissions/acdf7e43-7b3e-4ffc-bc02-3f82fb2dfd54

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement

open Matrix ComplexConjugate

def PEC_R {n : Type*} (a b : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.of fun i j => a i * conj (b j)

lemma PEC_inner_eq {n : Type*} [Fintype n] (a b : EuclideanSpace ℂ n) :
    inner ℂ a b = ∑ i, conj (a i) * b i := by
  rw [PiLp.inner_apply]; simp [mul_comm]

lemma PEC_R_mul {n : Type*} [Fintype n] (a b c d : EuclideanSpace ℂ n) :
    PEC_R a b * PEC_R c d = (inner ℂ b c) • PEC_R a d := by
  ext i j
  simp only [PEC_R, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, PEC_inner_eq,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma PEC_R_conjTranspose {n : Type*} (a b : EuclideanSpace ℂ n) :
    (PEC_R a b)ᴴ = PEC_R b a := by
  ext i j; simp [PEC_R, mul_comm]

lemma PEC_R_trace {n : Type*} [Fintype n] (a b : EuclideanSpace ℂ n) :
    (PEC_R a b).trace = inner ℂ b a := by
  simp [PEC_R, Matrix.trace, PEC_inner_eq, mul_comm]

def PEC_D {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (g : K → ℝ) :
    Matrix n n ℂ := ∑ k, ((g k : ℝ) : ℂ) • PEC_R (w k) (w k)

lemma PEC_D_mul {n K : Type*} [Fintype n] [Fintype K] (w : K → EuclideanSpace ℂ n)
    (hw : Orthonormal ℂ w) (g h : K → ℝ) :
    PEC_D w g * PEC_D w h = PEC_D w (g * h) := by
  classical
  rw [orthonormal_iff_ite] at hw
  simp only [PEC_D, Finset.sum_mul, Finset.mul_sum, smul_mul_smul, PEC_R_mul, hw, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma PEC_D_add {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (g h : K → ℝ) :
    PEC_D w (g + h) = PEC_D w g + PEC_D w h := by
  simp [PEC_D, add_smul, Finset.sum_add_distrib]

lemma PEC_D_smul {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (a : ℝ) (g : K → ℝ) :
    PEC_D w (a • g) = a • PEC_D w g := by
  simp [PEC_D, Finset.smul_sum, smul_smul, ← Complex.coe_smul]

lemma PEC_D_trace {n K : Type*} [Fintype n] [Fintype K] (w : K → EuclideanSpace ℂ n)
    (hw : Orthonormal ℂ w) (g : K → ℝ) :
    (PEC_D w g).trace = ((∑ k, g k : ℝ) : ℂ) := by
  simp [PEC_D, Matrix.trace_sum, PEC_R_trace, hw.1]

lemma PEC_D_selfAdjoint {n K : Type*} [Fintype K] (w : K → EuclideanSpace ℂ n) (g : K → ℝ) :
    IsSelfAdjoint (PEC_D w g) := by
  show (PEC_D w g)ᴴ = PEC_D w g
  simp [PEC_D, Matrix.conjTranspose_sum, PEC_R_conjTranspose]

lemma PEC_Q_mul {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (g : K → ℝ) :
    (1 - PEC_D w 1) * PEC_D w g = 0 := by
  rw [sub_mul, one_mul, PEC_D_mul w hw, one_mul, sub_self]

lemma PEC_aeval {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (μ : K → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (PEC_D w μ) p
      = (p.eval 0) • (1 - PEC_D w 1) + PEC_D w (fun k => p.eval (μ k)) := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Polynomial.eval_C, Algebra.algebraMap_eq_smul_one]
    have : (fun _ : K => a) = a • (1 : K → ℝ) := by ext; simp
    rw [this, PEC_D_smul, smul_sub]; abel
  | add p q hp hq =>
    rw [map_add, hp, hq, Polynomial.eval_add, add_smul]
    have : (fun k => (p + q).eval (μ k)) = (fun k => p.eval (μ k)) + (fun k => q.eval (μ k)) := by
      ext; simp
    rw [this, PEC_D_add]; abel
  | monomial m a h =>
    rw [pow_succ, ← mul_assoc, map_mul, h, Polynomial.aeval_X, add_mul, smul_mul_assoc,
      PEC_Q_mul w hw, smul_zero, zero_add, PEC_D_mul w hw]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, mul_zero, zero_smul, zero_add]
    rfl

lemma PEC_spectrum {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (μ : K → ℝ) (x : ℝ)
    (hx : x ∈ spectrum ℝ (PEC_D w μ)) : x = 0 ∨ ∃ k, x = μ k := by
  set q : Polynomial ℝ := Polynomial.X * ∏ k, (Polynomial.X - Polynomial.C (μ k)) with hq
  have h0 : Polynomial.aeval (PEC_D w μ) q = 0 := by
    rw [PEC_aeval w hw]
    have h1 : q.eval 0 = 0 := by simp [hq]
    have h2 : (fun k => q.eval (μ k)) = 0 := by
      ext k; simp only [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C, Pi.zero_apply]
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp), mul_zero]
    rw [h1, h2]; simp [PEC_D]
  have hmem := spectrum.subset_polynomial_aeval (PEC_D w μ) q ⟨x, hx, rfl⟩
  rw [h0] at hmem
  have hev : q.eval x = 0 := by
    by_contra hne
    apply spectrum.notMem_iff.mpr _ hmem
    simpa using (IsUnit.mk0 _ hne).map (algebraMap ℝ (Matrix n n ℂ))
  simp only [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
        sub_eq_zero] at hev
  rcases hev with h | ⟨k, _, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk⟩

lemma PEC_cfc {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (w : K → EuclideanSpace ℂ n) (hw : Orthonormal ℂ w) (μ : K → ℝ) (f : ℝ → ℝ)
    (hf : f 0 = 0) : cfc f (PEC_D w μ) = PEC_D w (fun k => f (μ k)) := by
  classical
  set s : Finset ℝ := insert 0 (Finset.univ.image μ)
  set p : Polynomial ℝ := Lagrange.interpolate s id f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
  have hA := PEC_D_selfAdjoint w μ
  rw [cfc_congr (g := fun x => p.eval x) (a := PEC_D w μ)]
  · rw [cfc_polynomial p (PEC_D w μ) hA, PEC_aeval w hw, hp 0 (by simp [s]), hf, zero_smul,
      zero_add]
    congr 1; ext k; exact hp _ (by simp [s])
  · intro x hx
    refine (hp x ?_).symm
    rcases PEC_spectrum w hw μ x hx with h | ⟨k, h⟩ <;> simp [s, h]

lemma PEC_schmidt_apply {I J : Type*} {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) (p : I × J) :
    (schmidtState c u v) p = ∑ i, (c i : ℂ) * (u i p.1 * v i p.2) := by
  simp [schmidtState, tensorVec]

lemma PEC_traceRight {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hv : Orthonormal ℂ v) :
    traceRight (pureDensity (schmidtState c u v)) = PEC_D u (fun i => c i ^ 2) := by
  classical
  rw [orthonormal_iff_ite] at hv
  ext j k
  simp only [traceRight, pureDensity, Matrix.of_apply, PEC_schmidt_apply, PEC_D, PEC_R,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal,
    Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ l, ∑ h, (c i : ℂ) * (u i j * v i h) * ((c l : ℂ) * ((starRingEnd ℂ) (u l k) *
      (starRingEnd ℂ) (v l h))) = (c i : ℂ) * c l * u i j * (starRingEnd ℂ) (u l k) *
      inner ℂ (v l) (v i) := by
    intro l
    rw [PEC_inner_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => by ring
  simp only [this, hv]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp; ring

lemma PEC_part1 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    vnEntropy (traceRight (pureDensity (schmidtState c u v))) =
      2*∑ i, c i^2*Real.logb 2 ((c i)⁻¹) := by
  rw [PEC_traceRight c u v hv, vnEntropy, PEC_cfc u hu _ _ (by simp), PEC_D_trace u hu]
  simp only [Complex.ofReal_re, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.logb_pow, Real.logb_inv]; push_cast; ring

lemma PEC_MHM {n K : Type*} [Fintype n] [Fintype K] (w : K → EuclideanSpace ℂ n)
    (hw : Orthonormal ℂ w) (σ : K → K) (hσ : Function.Injective σ) (a : K → ℝ) :
    (∑ k, ((a k : ℝ) : ℂ) • PEC_R (w (σ k)) (w k))ᴴ * (∑ k, ((a k : ℝ) : ℂ) • PEC_R (w (σ k)) (w k))
      = PEC_D w (fun k => a k ^ 2) := by
  classical
  rw [orthonormal_iff_ite] at hw
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, PEC_R_conjTranspose,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul, PEC_R_mul, hw, hσ.eq_iff, smul_smul, PEC_D,
    Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp [sq]

def PEC_cv {n : Type*} (a : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun i => conj (a i))

lemma PEC_inner_tensor {I J : Type*} [Fintype I] [Fintype J] (a c : EuclideanSpace ℂ I)
    (b d : EuclideanSpace ℂ J) :
    inner ℂ (tensorVec a b) (tensorVec c d) = inner ℂ a c * inner ℂ b d := by
  simp only [PEC_inner_eq, tensorVec, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp; ring

lemma PEC_inner_cv {I : Type*} [Fintype I] (a c : EuclideanSpace ℂ I) :
    inner ℂ (PEC_cv a) (PEC_cv c) = inner ℂ c a := by
  simp only [PEC_inner_eq, PEC_cv]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp; ring

lemma PEC_x_orth {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    Orthonormal ℂ (fun p : Fin r × Fin r => tensorVec (PEC_cv (u p.1)) (v p.2)) := by
  classical
  rw [orthonormal_iff_ite] at hu hv ⊢
  rintro ⟨i, l⟩ ⟨i', l'⟩
  simp only [PEC_inner_tensor, PEC_inner_cv, hu, hv, Prod.mk.injEq]
  by_cases h1 : i = i' <;> by_cases h2 : l = l' <;> simp [h1, h2, eq_comm]

lemma PEC_PT {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (c : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J) :
    partialTransposeFirst (pureDensity (schmidtState c u v)) =
      ∑ k : Fin r × Fin r, ((c k.1 * c k.2 : ℝ) : ℂ) •
        PEC_R ((fun p : Fin r × Fin r => tensorVec (PEC_cv (u p.1)) (v p.2)) (Prod.swap k))
          ((fun p : Fin r × Fin r => tensorVec (PEC_cv (u p.1)) (v p.2)) k) := by
  ext p q
  simp only [partialTransposeFirst, pureDensity, Matrix.of_apply, PEC_schmidt_apply,
    Matrix.sum_apply, Matrix.smul_apply, PEC_R, tensorVec, PEC_cv, Prod.fst_swap, Prod.snd_swap,
    map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  simp; ring

lemma PEC_part3 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {r : ℕ}
    (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I) (v : Fin r → EuclideanSpace ℂ J)
    (hc : ∀ i, 0 ≤ c i) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    logNeg (pureDensity (schmidtState c u v)) = 2*Real.logb 2 (∑ i, c i) := by
  rw [logNeg, traceNorm, PEC_PT,
    PEC_MHM _ (PEC_x_orth u v hu hv) Prod.swap Prod.swap_injective,
    PEC_cfc _ (PEC_x_orth u v hu hv) _ _ Real.sqrt_zero, PEC_D_trace _ (PEC_x_orth u v hu hv),
    Complex.ofReal_re]
  have : ∑ k : Fin r × Fin r, √((c k.1 * c k.2) ^ 2) = (∑ i, c i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Real.sqrt_sq (mul_nonneg (hc _) (hc _))
  rw [this, Real.logb_pow]; push_cast; ring

lemma PEC_jensen {r : ℕ} (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i, c i^2 = 1) :
    (∑ i, c i^2 * Real.log ((c i)⁻¹) ≤ Real.log (∑ i, c i)) ∧
    (∑ i, c i^2 * Real.log ((c i)⁻¹) = Real.log (∑ i, c i) ↔
      ∀ i j, c i ≠ 0 → c j ≠ 0 → c i = c j) := by
  classical
  set t := Finset.univ.filter (fun i => c i ≠ 0) with ht
  have key : ∀ g : Fin r → ℝ, (∀ i, c i = 0 → g i = 0) → ∑ i ∈ t, g i = ∑ i, g i := by
    intro g hg
    rw [ht, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · exact (hg i (not_not.mp h)).symm
  have hw1 : ∑ i ∈ t, c i ^ 2 = 1 := by rw [key _ (fun i h => by simp [h]), hs]
  have hwp : ∀ i ∈ t, 0 < c i ^ 2 := fun i hi => by
    have : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    positivity
  have hpt : ∀ i ∈ t, (c i)⁻¹ ∈ Set.Ioi (0:ℝ) := fun i hi => by
    have : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact inv_pos.mpr (lt_of_le_of_ne (hc i) (Ne.symm this))
  have hS : ∑ i ∈ t, c i ^ 2 • (c i)⁻¹ = ∑ i, c i := by
    rw [← key _ (fun i h => h)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [smul_eq_mul]; field_simp
  have hL : ∑ i ∈ t, c i ^ 2 • Real.log (c i)⁻¹ = ∑ i, c i^2 * Real.log ((c i)⁻¹) := by
    rw [← key _ (fun i h => by simp [h])]; rfl
  have hle := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (fun i hi => (hwp i hi).le) hw1 hpt
  have heq := strictConcaveOn_log_Ioi.map_sum_eq_iff hwp hw1 hpt
  rw [hS, hL] at hle heq
  refine ⟨hle, ?_⟩
  rw [eq_comm, heq]
  constructor
  · intro h i j hi hj
    have h1 := h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have h2 := h j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    exact inv_injective (h1.trans h2.symm)
  · intro h j hj
    have hj0 : c j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hall : ∀ i ∈ t, c i = c j := fun i hi => h i j (Finset.mem_filter.mp hi).2 hj0
    rw [← hS, Finset.sum_congr rfl fun i hi => by rw [hall i hi]]
    rw [Finset.sum_congr rfl fun i hi => by rw [hall i hi]] at hw1
    simp only [Finset.sum_const, nsmul_eq_mul, smul_eq_mul] at hw1 ⊢
    field_simp
    linear_combination (-1) * hw1

end QAlgorithms.Papers.Independent.Independent1.P07

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
/-- Eq. (50) and equality characterization, PDF p. 7. Equal coefficients are
required only on the nonzero Schmidt support. -/
theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (v : Fin r → EuclideanSpace ℂ J) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ i, c i^2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    let rho := pureDensity (schmidtState c u v)
    let E := 2*∑ i, c i^2*Real.logb 2 ((c i)⁻¹)
    vnEntropy (traceRight rho) = E ∧ E ≤ 2*Real.logb 2 (∑ i, c i) ∧
    2*Real.logb 2 (∑ i, c i) = logNeg rho ∧
    (E = logNeg rho ↔ ∀ i j, c i ≠ 0 → c j ≠ 0 → c i = c j) := by
  intro rho E
  have h1 := PEC_part1 c u v hu hv
  have h3 := PEC_part3 c u v hc hu hv
  obtain ⟨hle, heq⟩ := PEC_jensen c hc hs
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : E = 2 * (∑ i, c i^2 * Real.log (c i)⁻¹) / Real.log 2 := by
    simp only [E, Real.logb, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hN : 2*Real.logb 2 (∑ i, c i) = 2 * Real.log (∑ i, c i) / Real.log 2 := by
    rw [Real.logb]; ring
  refine ⟨h1, ?_, h3.symm, ?_⟩
  · rw [hE, hN]
    exact div_le_div_of_nonneg_right (by linarith) hl2.le
  · rw [show logNeg rho = 2*Real.logb 2 (∑ i, c i) from h3, hE, hN, ← heq]
    constructor
    · intro h
      have := (div_left_inj' hl2.ne').mp h
      linarith
    · intro h; rw [h]

