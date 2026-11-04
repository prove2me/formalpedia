-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.finiteEntropy_mono_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-04T00:53:35.332692+00:00
-- url     : https://prove2.me/submissions/a4dd06c2-61a1-4ffd-b303-7ece66948874

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

open scoped Matrix ComplexOrder

/-- `η(x) = x log x`. -/
def femEta (x : ℝ) : ℝ := x * Real.log x

/-- Increments of `η` grow with the base point: `x ↦ η(R+x) - η(x)` is monotone on `[0,∞)`. -/
theorem fem_step {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hab : a ≤ b) :
    femEta (R + a) - femEta a ≤ femEta (R + b) - femEta b := by
  let g : ℝ → ℝ := fun x => femEta (R + x) - femEta x
  have hcont : ContinuousOn g (Set.Ici 0) :=
    ((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).sub
      Real.continuous_mul_log).continuousOn
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivAt g ((Real.log (R + x) + 1) - (Real.log x + 1)) x := by
    intro x hx
    rw [interior_Ici] at hx
    have hx' : (0 : ℝ) < x := hx
    have hx0 : x ≠ 0 := ne_of_gt hx'
    have hRx : R + x ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y => (R + y) * Real.log (R + y)) (Real.log (R + x) + 1) x := by
      have := (Real.hasDerivAt_mul_log hRx).comp x ((hasDerivAt_id x).const_add R)
      rw [mul_one] at this; exact this
    exact h1.sub (Real.hasDerivAt_mul_log hx0)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont ?_ ?_
    · intro x hx; exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x hx).deriv]
      rw [interior_Ici] at hx
      have hx' : (0 : ℝ) < x := hx
      have : Real.log x ≤ Real.log (R + x) := Real.log_le_log hx' (by linarith)
      linarith
  exact hmono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab

/-- `h(v) = η(Σ v + c) - Σ η(v)` is coordinatewise monotone on nonnegative vectors. -/
theorem fem_scalar {ι : Type} (s : Finset ι) (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hxy : ∀ i, x i ≤ y i) : ∀ c : ℝ, 0 ≤ c →
    femEta (∑ i ∈ s, x i + c) - ∑ i ∈ s, femEta (x i) ≤
      femEta (∑ i ∈ s, y i + c) - ∑ i ∈ s, femEta (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro c _; simp
  | insert j s hj ih =>
    intro c hc
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    have hsx : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    have step := fem_step (R := ∑ i ∈ s, x i + c) (by linarith) (hx j) (hxy j)
    have hyj : 0 ≤ y j := (hx j).trans (hxy j)
    have ih' := ih (c + y j) (by linarith)
    rw [show x j + ∑ i ∈ s, x i + c = (∑ i ∈ s, x i + c) + x j by ring,
      show y j + ∑ i ∈ s, y i + c = ∑ i ∈ s, y i + (c + y j) by ring]
    rw [show (∑ i ∈ s, x i + c) + y j = ∑ i ∈ s, x i + (c + y j) by ring] at step
    linarith

/-- Jensen with a doubly stochastic matrix (Peierls' inequality in eigen-coordinates). -/
theorem fem_peierls {n : Type} [Fintype n] (w : n → n → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1) (d : n → ℝ) (hd : ∀ j, 0 ≤ d j) :
    ∑ i, femEta (∑ j, w i j * d j) ≤ ∑ j, femEta (d j) := by
  calc ∑ i, femEta (∑ j, w i j * d j) ≤ ∑ i, ∑ j, w i j * femEta (d j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := Real.convexOn_mul_log.map_sum_le (t := Finset.univ) (w := w i) (p := d)
          (fun j _ => hw0 i j) (hrow i) (fun j _ => Set.mem_Ici.2 (hd j))
        simpa [femEta, smul_eq_mul] using this
    _ = ∑ j, femEta (d j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, hcol j, one_mul]

theorem fem_row {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W * star W = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M => (M i i).re) hW
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re] at h
  rw [← h, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem fem_col {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : star W * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M => (M j j).re) hW
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re] at h
  rw [← h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem fem_diag {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (d : n → ℝ) (i : n) :
    (W * Matrix.diagonal (fun j => (d j : ℂ)) * star W) i i =
      ((∑ j, Complex.normSq (W i j) * d j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, mul_right_comm, Complex.mul_conj]

theorem fem_conj {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (V : Matrix n n ℂ) :
    star V * A * V = (star V * (hA.eigenvectorUnitary : Matrix n n ℂ)) *
      Matrix.diagonal (fun j => (hA.eigenvalues j : ℂ)) *
      star (star V * (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, star_mul, star_star, Matrix.mul_assoc]
  rfl

theorem fem_trace_cfc {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ j, f (hA.eigenvalues j) := by
  rw [Matrix.IsHermitian.cfc_eq hA, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem fem_main {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hXY : (Y - X).PosSemidef) :
    finiteEntropy X ≤ finiteEntropy Y := by
  have hY : Y.PosSemidef := by simpa using hX.add hXY
  set V : Matrix n n ℂ := (hY.1.eigenvectorUnitary : Matrix n n ℂ) with hV
  set U : Matrix n n ℂ := (hX.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hVV : star V * V = 1 := Unitary.star_mul_self_of_mem hY.1.eigenvectorUnitary.2
  have hVV' : V * star V = 1 := Unitary.mul_star_self_of_mem hY.1.eigenvectorUnitary.2
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hX.1.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hX.1.eigenvectorUnitary.2
  set W : Matrix n n ℂ := star V * U with hW
  have hWW : W * star W = 1 := by
    rw [hW, star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul,
      hVV]
  have hWW' : star W * W = 1 := by
    rw [hW, star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV', Matrix.one_mul,
      hUU]
  set lx := hX.1.eigenvalues with hlx
  set ly := hY.1.eigenvalues with hly
  set x : n → ℝ := fun i => ∑ j, Complex.normSq (W i j) * lx j with hxdef
  have hMx : ∀ i, ((star V * X * V) i i).re = x i := by
    intro i
    rw [fem_conj hX.1 V, fem_diag, Complex.ofReal_re]
  have hMy : ∀ i, ((star V * Y * V) i i).re = ly i := by
    intro i
    rw [fem_conj hY.1 V, fem_diag, Complex.ofReal_re, ← hV, hVV]
    rw [Finset.sum_eq_single i]
    · simp; rfl
    · intro j _ hj; simp [Matrix.one_apply_ne (Ne.symm hj)]
    · simp
  have hx0 : ∀ i, 0 ≤ x i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (Complex.normSq_nonneg _) (hX.eigenvalues_nonneg j)
  have hxy : ∀ i, x i ≤ ly i := by
    intro i
    have hP := (hXY.conjTranspose_mul_mul_same V).diag_nonneg (i := i)
    have hre := (Complex.le_def.1 hP).1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, Complex.sub_re] at hre
    rw [← Matrix.star_eq_conjTranspose] at hre
    rw [hMx, hMy] at hre
    simpa using hre
  have hsx : X.trace.re = ∑ i, x i := by
    rw [hX.1.trace_eq_sum_eigenvalues, Complex.re_sum, hxdef]
    simp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, fem_col W hWW' j, one_mul]
    simp [hlx]
  have hsy : Y.trace.re = ∑ i, ly i := by
    rw [hY.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp [hly]
  have hcx := fem_trace_cfc hX.1 (fun x : ℝ => x * Real.log x)
  have hcy := fem_trace_cfc hY.1 (fun x : ℝ => x * Real.log x)
  have hpe := fem_peierls (fun i j => Complex.normSq (W i j)) (fun _ _ => Complex.normSq_nonneg _)
    (fem_row W hWW) (fem_col W hWW') lx (hX.eigenvalues_nonneg)
  have hsc := fem_scalar Finset.univ x ly hx0 hxy 0 le_rfl
  simp only [add_zero] at hsc
  unfold finiteEntropy
  apply ENNReal.ofReal_le_ofReal
  rw [hcx, hcy, hsx, hsy]
  simp only [femEta] at hpe hsc ⊢
  rw [← hlx, ← hly]
  simp only [hxdef] at hsc ⊢
  linarith

end QAlgorithms.Papers.Independent.Claimed50.P18

end

open QAlgorithms.Papers.Independent.Claimed50.P18 in
open QAlgorithms.Papers.Independent.Frontier18.P01 in
open scoped Matrix ComplexOrder in
theorem solution {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hXY : (Y - X).PosSemidef) :
    finiteEntropy X ≤ finiteEntropy Y :=
  fem_main hX hXY
