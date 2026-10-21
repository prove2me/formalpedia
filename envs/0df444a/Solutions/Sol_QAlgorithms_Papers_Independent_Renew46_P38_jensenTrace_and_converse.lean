-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.jensenTrace_and_converse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T02:01:36.69811+00:00
-- url     : https://prove2.me/submissions/2de5bfdd-c159-4c09-b85d-e99be61d57a5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

theorem g65d_entry {m : ℕ} {x : Matrix (Fin m) (Fin m) ℂ} (hx : x.IsHermitian) (g : ℝ → ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ) (k : Fin m) :
    (star c * hx.cfc g * c) k k =
      ((∑ j, Complex.normSq ((star (hx.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * c) j k)
        * g (hx.eigenvalues j) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set V : Matrix (Fin m) (Fin m) ℂ := (hx.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have : star c * (V * Matrix.diagonal (RCLike.ofReal ∘ g ∘ hx.eigenvalues) * star V) * c
      = star (star V * c) * Matrix.diagonal (RCLike.ofReal ∘ g ∘ hx.eigenvalues) * (star V * c) := by
    simp only [star_mul, star_star, Matrix.mul_assoc]
  rw [this]
  generalize star V * c = B
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  exact mul_right_comm _ _ _

theorem g65d_scalar {ι : Type*} [Fintype ι] {I : Set ℝ} {f : ℝ → ℝ} (hconv : ConvexOn ℝ I f)
    (w μ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hμ : ∀ i, μ i ∈ I) (hs : ∑ i, w i ≤ 1)
    (h : ∑ i, w i = 1 ∨ (0 ∈ I ∧ f 0 ≤ 0)) :
    f (∑ i, w i * μ i) ≤ ∑ i, w i * f (μ i) := by
  rcases h with h | ⟨h0, hf0⟩
  · simpa [smul_eq_mul] using hconv.map_sum_le (t := Finset.univ) (fun i _ => hw i) h (fun i _ => hμ i)
  · have := hconv.map_sum_le (t := Finset.univ) (w := fun o : Option ι => o.elim (1 - ∑ i, w i) w)
      (p := fun o : Option ι => o.elim 0 μ)
      (by intro o _; cases o <;> simp [hw]; linarith)
      (by simp [Fintype.sum_option])
      (by intro o _; cases o <;> simp [hμ, h0])
    simp only [Fintype.sum_option, Option.elim, smul_eq_mul, mul_zero, zero_add] at this
    have h1 : 0 ≤ 1 - ∑ i, w i := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hf0]

open QAlgorithms.Papers.Independent.Renew46.P38 in
theorem g65d_conj_comb {m n : ℕ} (x a : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hxh : ∀ i, (x i).IsHermitian) (U : Matrix (Fin m) (Fin m) ℂ) (h : ℝ → ℝ) (k : Fin m)
    (X : Fin n → Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i, X i = (hxh i).cfc h) :
    (star U * combination a X * U) k k =
      ((∑ p : Fin n × Fin m,
        Complex.normSq ((star ((hxh p.1).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
          (a p.1 * U)) p.2 k) * h ((hxh p.1).eigenvalues p.2) : ℝ) : ℂ) := by
  rw [Fintype.sum_prod_type]
  simp only [combination, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : star U * (star (a i) * X i * a i) * U = star (a i * U) * X i * (a i * U) := by
    simp only [star_mul, Matrix.mul_assoc]
  rw [this, hX i, g65d_entry (hxh i)]
  push_cast; rfl

open QAlgorithms.Papers.Independent.Renew46.P38 in
theorem g65d_core {I : Set ℝ} {f : ℝ → ℝ} (hconv : ConvexOn ℝ I f) {m n : ℕ}
    (x a : Fin n → Matrix (Fin m) (Fin m) ℂ) (hx : ∀ i, InInterval I (x i))
    (hcond : columnSquares a = 1 ∨ ((1 - columnSquares a).PosSemidef ∧ 0 ∈ I ∧ f 0 ≤ 0)) :
    (Matrix.trace (cfc f (combination a x))).re ≤
      (Matrix.trace (combination a (fun i => cfc f (x i)))).re := by
  have hxh : ∀ i, (x i).IsHermitian := fun i => (hx i).1
  have hy : (combination a x).IsHermitian := by
    have : IsSelfAdjoint (combination a x) :=
      isSelfAdjoint_sum _ (fun i _ => (hx i).1.conjugate' (a i))
    exact this
  set y := combination a x with hydef
  set U : Matrix (Fin m) (Fin m) ℂ := (hy.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have htr : ∀ M : Matrix (Fin m) (Fin m) ℂ, Matrix.trace M = ∑ k, (star U * M * U) k k := by
    intro M
    have : Matrix.trace (star U * M * U) = Matrix.trace M := by
      rw [Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
    rw [← this]; rfl
  -- eigen entries of y
  have hdiag : ∀ (g : ℝ → ℝ) (k : Fin m), (star U * hy.cfc g * U) k k = (g (hy.eigenvalues k) : ℂ) := by
    intro g k
    rw [g65d_entry hy, hUU]
    congr 1
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Matrix.one_apply, hj]
    · simp
  set W : Fin m → Fin n × Fin m → ℝ := fun k p => Complex.normSq ((star ((hxh p.1).eigenvectorUnitary :
      Matrix (Fin m) (Fin m) ℂ) * (a p.1 * U)) p.2 k) with hW
  set μ : Fin n × Fin m → ℝ := fun p => (hxh p.1).eigenvalues p.2 with hμ
  have hcomb : ∀ (h : ℝ → ℝ) (k : Fin m) (X : Fin n → Matrix (Fin m) (Fin m) ℂ)
      (hX : ∀ i, X i = (hxh i).cfc h),
      (star U * combination a X * U) k k = ((∑ p, W k p * h (μ p) : ℝ) : ℂ) :=
    fun h k X hX => g65d_conj_comb x a hxh U h k X hX
  have hlam : ∀ k, hy.eigenvalues k = ∑ p, W k p * μ p := by
    intro k
    have h1 := hdiag (fun t => t) k
    have e1 : hy.cfc (fun t => t) = y := hy.spectral_theorem.symm
    rw [e1] at h1
    have h2 := hcomb (fun t => t) k x (fun i => (hxh i).spectral_theorem)
    rw [← hydef, h1] at h2
    exact_mod_cast h2
  have hsum : ∀ k, (star U * columnSquares a * U) k k = ((∑ p, W k p : ℝ) : ℂ) := by
    intro k
    have h2 := hcomb (fun _ => 1) k (fun _ => 1) (fun i => by
      rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
      have : (RCLike.ofReal ∘ (fun _ : ℝ => (1:ℝ)) ∘ (hxh i).eigenvalues : Fin m → ℂ) = 1 := by
        funext j; simp
      rw [this, show (Matrix.diagonal (1 : Fin m → ℂ)) = 1 from Matrix.diagonal_one, Matrix.mul_one]
      exact (Unitary.coe_mul_star_self _).symm)
    have h3 : combination a (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) = columnSquares a := by
      simp only [combination, columnSquares, Matrix.mul_one]
    rw [h3] at h2
    simpa using h2
  have hcf : ∀ i, cfc f (x i) = (hxh i).cfc f := fun i => (hxh i).cfc_eq f
  rw [htr, htr, hy.cfc_eq]
  simp only [Complex.re_sum, hdiag, hcomb f _ _ hcf, Complex.ofReal_re]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [hlam k]
  have hWnn : ∀ p, 0 ≤ W k p := fun p => Complex.normSq_nonneg _
  have hμI : ∀ p, μ p ∈ I := fun p => (hx p.1).2 ((hxh p.1).eigenvalues_mem_spectrum_real p.2)
  rcases hcond with hC | ⟨hC, h0, hf0⟩
  · have : ∑ p, W k p = 1 := by
      have := hsum k
      rw [hC, Matrix.mul_one, hUU, Matrix.one_apply_eq] at this
      exact_mod_cast this.symm
    exact g65d_scalar hconv _ _ hWnn hμI this.le (Or.inl this)
  · have hle : ∑ p, W k p ≤ 1 := by
      have hps := (hC.conjTranspose_mul_mul_same U).diag_nonneg (i := k)
      rw [← Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU,
        Matrix.sub_apply, hsum k, Matrix.one_apply_eq] at hps
      have := (Complex.nonneg_iff.mp hps).1
      simp at this
      linarith
    exact g65d_scalar hconv _ _ hWnn hμI hle (Or.inr ⟨h0, hf0⟩)

theorem g65d_trace_cfc {m : ℕ} {x : Matrix (Fin m) (Fin m) ℂ} (hx : x.IsHermitian) (g : ℝ → ℝ) :
    Matrix.trace (hx.cfc g) = ∑ k, ((g (hx.eigenvalues k) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

theorem g65d_sa_alg {m : ℕ} (r : ℝ) : IsSelfAdjoint (algebraMap ℝ (Matrix (Fin m) (Fin m) ℂ) r) := by
  rw [IsSelfAdjoint, ← algebraMap_star_comm, star_trivial]

theorem g65d_eig_scalar {m : ℕ} [NeZero m] (r : ℝ)
    (hx : (algebraMap ℝ (Matrix (Fin m) (Fin m) ℂ) r).IsHermitian) (k : Fin m) :
    hx.eigenvalues k = r := by
  have := hx.eigenvalues_mem_spectrum_real k
  rw [spectrum.scalar_eq] at this
  exact this

open QAlgorithms.Papers.Independent.Renew46.P38 in
theorem g65d_converse {I : Set ℝ} {f : ℝ → ℝ} (hI : Set.OrdConnected I) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 2 ≤ n) (h : MatrixTraceJensen I f m n false) : ConvexOn ℝ I f := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  refine ⟨convex_iff_ordConnected.mpr hI, ?_⟩
  intro s hs t ht p q hp hq hpq
  set A := Matrix (Fin m) (Fin m) ℂ
  let α : Fin (k+2) → ℝ := fun i => if i = 0 then Real.sqrt p else if i = 1 then Real.sqrt q else 0
  let σ : Fin (k+2) → ℝ := fun i => if i = 0 then s else t
  let x : Fin (k+2) → A := fun i => algebraMap ℝ A (σ i)
  let a : Fin (k+2) → A := fun i => algebraMap ℝ A (α i)
  have hσI : ∀ i, σ i ∈ I := fun i => by simp only [σ]; split_ifs <;> assumption
  have hxI : ∀ i, InInterval I (x i) := fun i => ⟨g65d_sa_alg _, by
    simp only [x]; rw [spectrum.scalar_eq]; simpa using hσI i⟩
  have hstar : ∀ r : ℝ, star (algebraMap ℝ A r) = algebraMap ℝ A r := fun r => (g65d_sa_alg r)
  have hsq : ∑ i, α i * α i = 1 := by
    simp only [α, Fin.sum_univ_succ, Fin.succ_ne_zero, if_false, Fin.succ_zero_eq_one]
    simp [Fin.succ_ne_zero, Fin.succ_succ_ne_one, Real.mul_self_sqrt hp, Real.mul_self_sqrt hq, hpq]
  have hcs : columnSquares a = 1 := by
    simp only [columnSquares, a, hstar, ← map_mul, ← map_sum, hsq, map_one]
  have key := h x a hxI (by simpa using hcs)
  have hcomb : combination a x = algebraMap ℝ A (∑ i, α i * σ i * α i) := by
    simp only [combination, a, x, hstar, ← map_mul, ← map_sum]
  have hval : ∑ i, α i * σ i * α i = p • s + q • t := by
    simp only [α, σ, Fin.sum_univ_succ, Fin.succ_ne_zero, if_false, Fin.succ_zero_eq_one]
    simp [Fin.succ_ne_zero, Fin.succ_succ_ne_one, smul_eq_mul]
    linear_combination s * Real.mul_self_sqrt hp + t * Real.mul_self_sqrt hq
  -- trace of cfc of a scalar
  have htrs : ∀ r : ℝ, (Matrix.trace (cfc f (algebraMap ℝ A r))).re = m * f r := by
    intro r
    have hh : (algebraMap ℝ A r).IsHermitian := g65d_sa_alg r
    rw [hh.cfc_eq, g65d_trace_cfc]
    simp [g65d_eig_scalar r hh]
  rw [hcomb, htrs, hval] at key
  have hrhs : (Matrix.trace (combination a (fun i => cfc f (x i)))).re
      = ∑ i, α i * α i * (m * f (σ i)) := by
    simp only [combination, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [a, x, hstar]
    rw [Matrix.trace_mul_cycle, ← map_mul, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, ← htrs (σ i)]
    simp
  rw [hrhs] at key
  have hfin : ∑ i, α i * α i * (m * f (σ i)) = m * (p • f s + q • f t) := by
    simp only [α, σ, Fin.sum_univ_succ, Fin.succ_ne_zero, if_false, Fin.succ_zero_eq_one]
    simp [Fin.succ_ne_zero, Fin.succ_succ_ne_one, smul_eq_mul, Real.mul_self_sqrt hp,
      Real.mul_self_sqrt hq]
    ring
  rw [hfin] at key
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact le_of_mul_le_mul_left key hm'

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Theorem 2.4, PDF p. 3 (proof pp. 8--9).
The converse requires positive m and n>1. In the proof, i≥2 is a typo for i>2;
the scalar reduction in (30) uses x=s1_m and y=t1_m. -/
theorem solution (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) :
    (ConvexOn ℝ I f → ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      MatrixTraceJensen I f m n false) ∧
    ((∃ m n : ℕ, 1 ≤ m ∧ 2 ≤ n ∧ MatrixTraceJensen I f m n false) →
      ConvexOn ℝ I f) := by
  refine ⟨fun hconv m n _ _ x a hx hc => g65d_core hconv x a hx (Or.inl (by simpa using hc)), ?_⟩
  rintro ⟨m, n, hm, hn, h⟩
  exact g65d_converse hI hm hn h

end
