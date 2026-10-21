-- Prove2me | solution 1 for YeIPA.QPApprox.arcsin_entrywise_dominates
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T02:23:10.96634+00:00
-- url     : https://prove2.me/submissions/67d71bdc-bb65-4e93-920f-73638d645ae9

import Definitions.Def_YeIPA_QPApprox_Relaxation
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000



namespace IP8ArcsinSeries

noncomputable def b (n : ℕ) : ℝ := Ring.choose ((1 / 2 : ℝ) + n - 1) n

noncomputable def a (n : ℕ) : ℝ := b n / (2 * n + 1 : ℕ)

theorem b_nonneg (n : ℕ) : 0 ≤ b n := by
  have hp : ∀ k : ℕ, 0 ≤ (ascPochhammer ℕ k).smeval (1 / 2 : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_right, Polynomial.smeval_mul]
      apply mul_nonneg ih
      simp only [Polynomial.smeval_add, Polynomial.smeval_X,
        ← Polynomial.C_eq_natCast, Polynomial.smeval_C, nsmul_eq_mul, mul_one]
      positivity
  have hf := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [nsmul_eq_mul, Ring.multichoose_eq] at hf
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply nonneg_of_mul_nonneg_left (b := (n.factorial : ℝ)) ?_ hn
  rw [mul_comm, b, hf]
  exact hp n

theorem a_nonneg (n : ℕ) : 0 ≤ a n := div_nonneg (b_nonneg n) (by positivity)

theorem hasSum_binomial (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => b n * x ^ n) (1 / (1 - x) ^ (1 / 2 : ℝ)) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one, Real.norm_eq_abs] using hx
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum hmem
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add, b] using h

theorem hasSum_derivative (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => b n * x ^ (2 * n)) (1 / Real.sqrt (1 - x ^ 2)) := by
  have hx2 : |x ^ 2| < 1 := by
    rw [abs_pow, sq_lt_one_iff_abs_lt_one]
    simpa only [abs_abs] using hx
  have h := hasSum_binomial (x ^ 2) hx2
  simpa only [← pow_mul, mul_comm 2, ← Real.sqrt_eq_rpow] using h

theorem term_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a n * y ^ (2 * n + 1)) (b n * x ^ (2 * n)) x := by
  convert! (hasDerivAt_pow (2 * n + 1) x).const_mul (a n) using 1 <;> try rfl
  rw [Nat.add_sub_cancel, a]
  push_cast
  field_simp

theorem derivative_bound (n : ℕ) (r x : ℝ) (hx : |x| ≤ r) :
    ‖b n * x ^ (2 * n)‖ ≤ b n * r ^ (2 * n) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (b_nonneg n), abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hx _) (b_nonneg n)

noncomputable def primitive (x : ℝ) : ℝ := ∑' n : ℕ, a n * x ^ (2 * n + 1)

theorem summable_primitive (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => a n * x ^ (2 * n + 1)) := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hur := (hasSum_derivative r (by rwa [abs_of_pos hr0])).summable
  apply summable_of_summable_hasDerivAt_of_isPreconnected hur isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected
    (fun n y _ => term_hasDerivAt n y)
    (fun n y hy => derivative_bound n r y (abs_lt.mpr hy).le)
    (y₀ := 0)
  · exact ⟨neg_neg_of_pos hr0, hr0⟩
  · simp
  · exact abs_lt.mp hxr

theorem primitive_hasDerivAt (x : ℝ) (hx : |x| < 1) :
    HasDerivAt primitive (1 / Real.sqrt (1 - x ^ 2)) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hur := (hasSum_derivative r (by rwa [abs_of_pos hr0])).summable
  have h := hasDerivAt_tsum_of_isPreconnected hur isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected
    (fun n y _ => term_hasDerivAt n y)
    (fun n y hy => derivative_bound n r y (abs_lt.mpr hy).le)
    (y₀ := 0) (by exact ⟨neg_neg_of_pos hr0, hr0⟩)
    (by simp) (abs_lt.mp hxr)
  rw [(hasSum_derivative x hx).tsum_eq] at h
  convert! h using 1 <;> rfl

theorem primitive_eq_arcsin (x : ℝ) (hx : |x| < 1) : primitive x = Real.arcsin x := by
  have hdarc (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - y ^ 2)) y :=
    Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])
  have hEq := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (fun y hy => (primitive_hasDerivAt y (abs_lt.mpr hy)).differentiableAt.differentiableWithinAt)
    (fun y hy => (hdarc y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (primitive_hasDerivAt y (abs_lt.mpr hy)).deriv.trans (hdarc y hy).deriv.symm)
    (x := 0) (by norm_num) (by simp [primitive])
  exact hEq (abs_lt.mp hx)

theorem hasSum_arcsin (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => a n * x ^ (2 * n + 1)) (Real.arcsin x) := by
  have h := (summable_primitive x hx).hasSum
  change HasSum (fun n : ℕ => a n * x ^ (2 * n + 1)) (primitive x) at h
  rwa [primitive_eq_arcsin x hx] at h

noncomputable def c (n : ℕ) : ℝ := a (n + 1)

theorem c_nonneg (n : ℕ) : 0 ≤ c n := a_nonneg (n + 1)

theorem hasSum_arcsin_sub (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => c n * x ^ (2 * n + 3)) (Real.arcsin x - x) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_arcsin x hx)
  simpa [c, a, b, Nat.mul_add, add_assoc] using h


end IP8ArcsinSeries


open Filter Topology Matrix

namespace IP8ArcsinProbe

/-- Positive semidefiniteness is preserved by entrywise limits of finite
real matrices. This avoids requiring a separately packaged closed-cone API. -/
theorem psd_entrywise_limit {n : ℕ}
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, (A k).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (B i j))) :
    B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    change B j i = B i j
    have hswap : (fun k => A k j i) = (fun k => A k i j) := by
      funext k
      simpa using (hA k).isHermitian.apply i j
    exact tendsto_nhds_unique (hlim j i) (by rw [hswap]; exact hlim i j)
  · intro v
    have hquad : Tendsto
        (fun k => ∑ i : Fin n, ∑ j : Fin n, v i * A k i j * v j) atTop
        (𝓝 (∑ i : Fin n, ∑ j : Fin n, v i * B i j * v j)) := by
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact (tendsto_const_nhds.mul (hlim i j)).mul tendsto_const_nhds
    have hnonneg : ∀ k, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * A k i j * v j := by
      intro k
      simpa only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply,
        star_trivial, mul_assoc] using (hA k).dotProduct_mulVec_nonneg v
    have hresult := ge_of_tendsto hquad (Filter.Eventually.of_forall hnonneg)
    simpa only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply,
      star_trivial, mul_assoc] using hresult


/-- The diagonal bound controls every entry. Testing the two-vector
principal submatrix on (1,1) and (1,-1) suffices. -/
theorem abs_entry_le_one {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosSemidef) (hd : ∀ i, X i i ≤ 1) (i j : Fin n) :
    |X i j| ≤ 1 := by
  classical
  have hsub := hX.submatrix (![i, j] : Fin 2 → Fin n)
  have hplus := hsub.dotProduct_mulVec_nonneg (![1, 1] : Fin 2 → ℝ)
  have hminus := hsub.dotProduct_mulVec_nonneg (![1, -1] : Fin 2 → ℝ)
  norm_num [dotProduct, mulVec, Fin.sum_univ_two, Matrix.submatrix] at hplus hminus
  have hsymm : X j i = X i j := by simpa using hX.isHermitian.apply i j
  rw [hsymm] at hplus hminus
  exact abs_le.mpr ⟨by linarith [hd i, hd j], by linarith [hd i, hd j]⟩


/-- Every positive integer entrywise power is positive semidefinite by the
Schur product theorem. -/
theorem psd_positive_entry_power {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosSemidef) (d : ℕ) (hd : 0 < d) :
    Matrix.PosSemidef (fun i j => X i j ^ d) := by
  have hpow : ∀ a : ℕ, Matrix.PosSemidef (fun i j => X i j ^ (a + 1)) := by
    intro a
    induction a with
    | zero => simpa using hX
    | succ a ih =>
      have heq : (fun i j => X i j ^ ((a + 1) + 1) : Matrix (Fin n) (Fin n) ℝ) =
          (fun i j => X i j ^ (a + 1)) ⊙ X := by
        ext i j
        exact pow_succ _ _
      change Matrix.PosSemidef (fun i j => X i j ^ ((a + 1) + 1))
      rw [heq]
      exact ih.hadamard hX
  simpa [Nat.sub_add_cancel hd] using hpow (d - 1)

/-- A scalar power series with nonnegative coefficients and positive
integer exponents preserves positivity wherever it converges entrywise. -/
theorem psd_of_nonnegative_entrywise_hasSum {n : ℕ}
    (f : ℝ → ℝ) (c : ℕ → ℝ) (e : ℕ → ℕ)
    (hc : ∀ k, 0 ≤ c k) (he : ∀ k, 0 < e k)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hs : ∀ i j, HasSum (fun k => c k * X i j ^ e k) (f (X i j))) :
    Matrix.PosSemidef (fun i j => f (X i j)) := by
  classical
  let P : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N =>
    ∑ k ∈ Finset.range N, c k • ((fun i j => X i j ^ e k) : Matrix (Fin n) (Fin n) ℝ)
  apply psd_entrywise_limit P (fun i j => f (X i j))
  · intro N
    apply Matrix.posSemidef_sum
    intro k _
    exact (psd_positive_entry_power X hX (e k) (he k)).smul (hc k)
  · intro i j
    have hp : ∀ N, P N i j = ∑ k ∈ Finset.range N, c k * X i j ^ e k := by
      intro N
      exact Matrix.sum_apply i j (Finset.range N)
        (fun k => c k • ((fun i j => X i j ^ e k) : Matrix (Fin n) (Fin n) ℝ))
    simpa only [hp] using (hs i j).tendsto_sum_nat


/-- A continuous scalar function with a positive-coefficient series on the
open unit interval preserves PSD up to its boundary. -/
theorem psd_of_nonnegative_series_unit_interval {n : ℕ}
    (f : ℝ → ℝ) (hf : Continuous f) (c : ℕ → ℝ) (e : ℕ → ℕ)
    (hc : ∀ k, 0 ≤ c k) (he : ∀ k, 0 < e k)
    (hs : ∀ t : ℝ, |t| < 1 → HasSum (fun k => c k * t ^ e k) (f t))
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hd : ∀ i, X i i ≤ 1) :
    Matrix.PosSemidef (fun i j => f (X i j)) := by
  let r : ℕ → ℝ := fun N => 1 - 1 / ((N : ℝ) + 2)
  have hrpos : ∀ N, 0 < r N := by
    intro N
    dsimp [r]
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hi : 1 / ((N : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hrlt : ∀ N, r N < 1 := by
    intro N
    dsimp [r]
    have hi : 0 < 1 / ((N : ℝ) + 2) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hn : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hi := tendsto_inv_atTop_zero.comp hn
    simpa only [r, one_div, sub_zero, Function.comp_apply] using tendsto_const_nhds.sub hi
  let B : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N i j => f (r N * X i j)
  apply psd_entrywise_limit B (fun i j => f (X i j))
  · intro N
    apply psd_of_nonnegative_entrywise_hasSum f c e hc he (r N • X) (hX.smul (hrpos N).le)
    intro i j
    apply hs
    change |r N * X i j| < 1
    rw [abs_mul, abs_of_pos (hrpos N)]
    have hb := abs_entry_le_one X hX hd i j
    have hle := mul_le_mul_of_nonneg_left hb (hrpos N).le
    rw [mul_one] at hle
    exact hle.trans_lt (hrlt N)
  · intro i j
    have hl : Tendsto (fun N => r N * X i j) atTop (𝓝 (X i j)) := by
      simpa only [one_mul] using hrlim.mul_const (X i j)
    exact hf.continuousAt.tendsto.comp hl


/-- The exact matrix arcsine inequality, reduced solely to its scalar
positive-coefficient series inside the open unit interval. -/
theorem arcsin_entrywise_dominates_of_series {n : ℕ}
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hs : ∀ t : ℝ, |t| < 1 →
      HasSum (fun k => c k * t ^ (2 * k + 3)) (Real.arcsin t - t))
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hd : ∀ i, X i i ≤ 1) :
    Matrix.PosSemidef (fun i j => Real.arcsin (X i j) - X i j) := by
  exact psd_of_nonnegative_series_unit_interval
    (fun t => Real.arcsin t - t) (Real.continuous_arcsin.sub continuous_id)
    c (fun k => 2 * k + 3) hc (by intro k; omega) hs X hX hd


end IP8ArcsinProbe

open YeIPA.QPApprox

/-- Ye, Interior Point Algorithms (1997), Lemma 9.31. The proof expands arcsin(t)-t
with nonnegative odd coefficients, applies the Schur product theorem to finite
partial sums, and passes first to the series limit and then to the boundary. -/
theorem solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hd : ∀ j, diagVec X j ≤ 1) :
    (entrywise Real.arcsin X - X).PosSemidef := by
  change Matrix.PosSemidef (fun i j => Real.arcsin (X i j) - X i j)
  exact IP8ArcsinProbe.arcsin_entrywise_dominates_of_series
    IP8ArcsinSeries.c IP8ArcsinSeries.c_nonneg IP8ArcsinSeries.hasSum_arcsin_sub X hX hd

#print axioms solution
