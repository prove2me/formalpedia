-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P24.continuousLogDensityEquipartition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T11:01:20.857976+00:00
-- url     : https://prove2.me/submissions/0436c0dd-a0a6-4f90-b1bc-a4b1c6c2cfa2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24


/-! Generic matrix lemmas: Frobenius Cauchy–Schwarz and the projection-state bound
`|tr(P X Y)|² ≤ tr(P X Xᴴ) ‖Y‖² tr P` for a star projection `P` (L2 operator norm). -/

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma cs {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    Complex.normSq (star a ⬝ᵥ b) ≤ (star a ⬝ᵥ a).re * (star b ⬝ᵥ b).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 b) (WithLp.toLp 2 a)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  have e : a ⬝ᵥ star b = star (star a ⬝ᵥ b) := by simp [dotProduct, mul_comm]
  simp only [WithLp.ofLp_toLp] at h
  rw [e, norm_star] at h
  have ha : ‖(WithLp.toLp 2 a : EuclideanSpace ℂ ι)‖ ^ 2 = (star a ⬝ᵥ a).re := by
    rw [← @inner_self_eq_norm_sq ℂ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  have hb : ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖ ^ 2 = (star b ⬝ᵥ b).re := by
    rw [← @inner_self_eq_norm_sq ℂ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  rw [Complex.normSq_eq_norm_sq, ← ha, ← hb, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [h]) 2

lemma trace_conjT_mul (M N : Matrix I I ℂ) :
    (Mᴴ * N).trace = star (fun p : I × I => M p.1 p.2) ⬝ᵥ (fun p : I × I => N p.1 p.2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dotProduct, Pi.star_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma fro_cs (M N : Matrix I I ℂ) :
    Complex.normSq (Mᴴ * N).trace ≤ (Mᴴ * M).trace.re * (Nᴴ * N).trace.re := by
  rw [trace_conjT_mul, trace_conjT_mul M M, trace_conjT_mul N N]
  exact cs _ _

lemma fro_re (N : Matrix I I ℂ) :
    (Nᴴ * N).trace.re = ∑ j, ‖(EuclideanSpace.equiv I ℂ).symm (fun i => N i j)‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    EuclideanSpace.norm_sq_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.equiv, WithLp.linearEquiv_symm_apply]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

lemma col_bound (Y P : Matrix I I ℂ) :
    ((Y * P)ᴴ * (Y * P)).trace.re ≤ ‖Y‖ ^ 2 * (Pᴴ * P).trace.re := by
  rw [fro_re, fro_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hc : (fun i => (Y * P) i j) = Y *ᵥ (fun i => P i j) := by
    funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hc]
  have := Matrix.l2_opNorm_mulVec Y ((EuclideanSpace.equiv I ℂ).symm (fun i => P i j))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- Projection-state Cauchy–Schwarz. -/
lemma key (P X Y : Matrix I I ℂ) (hP : IsStarProjection P) :
    Complex.normSq (P * X * Y).trace ≤ (P * X * Xᴴ).trace.re * (‖Y‖ ^ 2 * P.trace.re) := by
  have hi : P * P = P := hP.isIdempotentElem
  have hs : Pᴴ = P := hP.isSelfAdjoint
  have h1 : (Xᴴ * P)ᴴ * (Y * P) = P * X * Y * P := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hs]; simp [Matrix.mul_assoc]
  have h2 : (Xᴴ * P)ᴴ * (Xᴴ * P) = P * X * Xᴴ * P := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hs]; simp [Matrix.mul_assoc]
  have tr3 : ∀ Z : Matrix I I ℂ, (P * Z * P).trace = (P * Z).trace := by
    intro Z
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hi]
  have hc := fro_cs (Xᴴ * P) (Y * P)
  have hb := col_bound Y P
  rw [h1, h2, Matrix.mul_assoc P X Y, tr3, Matrix.mul_assoc P X Xᴴ, tr3] at hc
  rw [hs, hi] at hb
  rw [Matrix.mul_assoc P X Y, Matrix.mul_assoc P X Xᴴ]
  have h0 : 0 ≤ (P * (X * Xᴴ)).trace.re := by
    have := (Xᴴ * P)ᴴ * (Xᴴ * P)
    have hpsd : 0 ≤ ((Xᴴ * P)ᴴ * (Xᴴ * P)).trace.re := by
      rw [fro_re]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [h2, Matrix.mul_assoc P X Xᴴ, tr3] at hpsd
    exact hpsd
  exact hc.trans (mul_le_mul_of_nonneg_left hb h0)

lemma tr_nonneg (P X : Matrix I I ℂ) (hP : IsStarProjection P) :
    0 ≤ (P * X * Xᴴ).trace.re := by
  have hi : P * P = P := hP.isIdempotentElem
  have hs : Pᴴ = P := hP.isSelfAdjoint
  have h2 : (Xᴴ * P)ᴴ * (Xᴴ * P) = P * X * Xᴴ * P := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hs]; simp [Matrix.mul_assoc]
  have hpsd : 0 ≤ ((Xᴴ * P)ᴴ * (Xᴴ * P)).trace.re := by
    rw [fro_re]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hi] at hpsd
  exact hpsd

lemma trace_proj (P : Matrix I I ℂ) (hP : IsStarProjection P) :
    P.trace = ((P.trace.re : ℝ) : ℂ) ∧ 0 ≤ P.trace.re ∧ (P ≠ 0 → 0 < P.trace.re) := by
  have hi : P * P = P := hP.isIdempotentElem
  have hs : Pᴴ = P := hP.isSelfAdjoint
  have e : P.trace = (Pᴴ * P).trace := by rw [hs, hi]
  have hsum : (Pᴴ * P).trace = ∑ p : I × I, ((Complex.normSq (P p.1 p.2) : ℝ) : ℂ) := by
    rw [trace_conjT_mul]
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [e, hsum]
  simp only [Complex.re_sum, Complex.ofReal_re]
  refine ⟨by push_cast; rfl, Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _, fun hne => ?_⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
    by_contra h; push Not at h; exact hne (Matrix.ext h)
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hij)
    (Finset.single_le_sum (f := fun p : I × I => Complex.normSq (P p.1 p.2))
      (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ (i, j)))

end X6MQ


/-! Proposition 2.1 of De Roeck–Maes–Netočný: joint noncommutative analytic tests
concentrate under a concentrating normalized projection trace. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

lemma norm_one_le {d : ℕ} : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix (Fin d) (Fin d) ℂ)
  rw [conjTranspose_one, Matrix.one_mul] at h
  rcases eq_or_ne ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ 0 with h0 | h0
  · rw [h0]; norm_num
  · have : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ = 1 := by
      have := congrArg (· / ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖) h
      simp only [mul_div_assoc, div_self h0, mul_one] at this
      exact this.symm
    rw [this]

lemma spec_sq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    spectralFunction (fun z : ℝ => (((z - c) ^ 2 : ℝ) : ℂ)) A =
      (A - (c : ℂ) • 1) * (A - (c : ℂ) • 1) := by
  unfold spectralFunction
  rw [dif_pos hA]
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hsp : A = U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set E : Matrix (Fin d) (Fin d) ℂ := diagonal (fun j => (((hA.eigenvalues j - c) : ℝ) : ℂ))
  have hE : A - (c : ℂ) • 1 = U * E * Uᴴ := by
    have : E = diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) - (c : ℂ) • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [E, diagonal]
      · simp [E, diagonal, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hsp, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU2]
  rw [hE]
  have : U * E * Uᴴ * (U * E * Uᴴ) = U * (E * E) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul]
  rw [this]
  have hEE : E * E = diagonal (fun j => (((hA.eigenvalues j - c) ^ 2 : ℝ) : ℂ)) := by
    simp only [E, diagonal_mul_diagonal]; congr 1; funext j; push_cast; ring
  rw [hEE]

variable {K : Type*}

/-- the normalized projection state -/
def om (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (X : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ) : ℂ :=
  traceExpectation (projectionDensity P n) X

lemma om_eq (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) (X) :
    om S P n X = (((P n).trace.re : ℝ) : ℂ)⁻¹ * (P n * X).trace := by
  have h := (trace_proj (P n) hp).1
  simp only [om, traceExpectation, projectionDensity]
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  conv_lhs => rw [h]

lemma om_one (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) (hne : P n ≠ 0) : om S P n 1 = 1 := by
  obtain ⟨h1, -, h3⟩ := trace_proj (P n) hp
  rw [om_eq S P n hp, Matrix.mul_one, h1]
  have : (((P n).trace.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (h3 hne).ne'
  simp only [Complex.ofReal_re]
  exact inv_mul_cancel₀ this

lemma om_add_smul (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) (X Y) (c : ℂ) :
    om S P n (X + c • Y) = om S P n X + c * om S P n Y := by
  rw [om_eq S P n hp, om_eq S P n hp, om_eq S P n hp, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

lemma om_norm (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) (hne : P n ≠ 0) (Y) : ‖om S P n Y‖ ≤ ‖Y‖ := by
  obtain ⟨h1, h2, h3⟩ := trace_proj (P n) hp
  have ht := h3 hne
  have hk := key (P n) 1 Y hp
  simp only [Matrix.mul_one, conjTranspose_one] at hk
  rw [om_eq S P n hp, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg h2]
  have h' : ‖(P n * Y).trace‖ ≤ ‖Y‖ * (P n).trace.re := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) h2) two_ne_zero,
      ← Complex.normSq_eq_norm_sq]
    nlinarith [hk]
  rw [inv_mul_le_iff₀ ht]
  linarith

lemma om_cs (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) (hne : P n ≠ 0) (D W) :
    ‖om S P n (D * W)‖ ^ 2 ≤ (om S P n (D * Dᴴ)).re * ‖W‖ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := trace_proj (P n) hp
  have ht := h3 hne
  have hk := key (P n) D W hp
  set t := (P n).trace.re
  rw [om_eq S P n hp, om_eq S P n hp, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg h2, ← Complex.ofReal_inv, Complex.re_ofReal_mul, mul_pow,
    ← Complex.normSq_eq_norm_sq, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have e : t⁻¹ ^ 2 * Complex.normSq (P n * D * W).trace ≤
      t⁻¹ ^ 2 * ((P n * D * Dᴴ).trace.re * (‖W‖ ^ 2 * t)) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  refine e.trans (le_of_eq ?_)
  have ht' : t ≠ 0 := ht.ne'
  have key2 : t⁻¹ ^ 2 * ((P n * D * Dᴴ).trace.re * (‖W‖ ^ 2 * t)) =
      t⁻¹ * (P n * D * Dᴴ).trace.re * ‖W‖ ^ 2 := by field_simp
  rw [key2]

lemma om_re_nonneg (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) (X) : 0 ≤ (om S P n (X * Xᴴ)).re := by
  obtain ⟨-, h2, -⟩ := trace_proj (P n) hp
  rw [om_eq S P n hp, ← Complex.ofReal_inv, Complex.re_ofReal_mul, ← Matrix.mul_assoc]
  exact mul_nonneg (inv_nonneg.mpr h2) (tr_nonneg _ _ hp)

end X6MQ


noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

variable {K : Type*}

theorem joint (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (P : OperatorSequence S) (x : K → ℝ)
    (hP : projectionConcentrates S P x) :
    ∀ G : AnalyticTestSeries S,
      Tendsto (fun n => traceExpectation (projectionDensity P n) (operatorEvaluation G n))
        atTop (𝓝 (scalarEvaluation G x)) := by
  intro G
  obtain ⟨hproj, hconc⟩ := hP
  have hp : ∀ n, IsStarProjection (P n) := fun n => (hproj n).1
  have hne : ∀ n, P n ≠ 0 := fun n => (hproj n).2
  have hB : ∀ n k, ‖S.observable n k‖ ≤ S.radius k := by
    intro n k
    obtain ⟨B, -, hBr, hBn⟩ := hS.2.2 k
    exact (show ‖S.observable n k‖ ≤ B from hBn n).trans hBr.le
  have hrad : ∀ k, 0 ≤ S.radius k := fun k => (norm_nonneg _).trans (hB 0 k)
  have hword : ∀ n (w : List K), ‖wordOperator (S := S) n w‖ ≤ (w.map S.radius).prod := by
    intro n w
    induction w with
    | nil => simpa [wordOperator] using norm_one_le
    | cons k w ih =>
      simp only [wordOperator, List.map_cons, List.prod_cons] at ih ⊢
      exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hB n k) ih (norm_nonneg _) (hrad k))
  -- centred observables
  let D : ∀ n, K → Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
    fun n k => S.observable n k - (x k : ℂ) • 1
  have hDh : ∀ n k, (D n k)ᴴ = D n k := by
    intro n k
    simp only [D, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal, (hS.2.1 n k).eq]
  have hD : ∀ k, Tendsto (fun n => om S P n (D n k * D n k)) atTop (𝓝 0) := by
    intro k
    have h := hconc k (fun z : ℝ => (((z - x k) ^ 2 : ℝ) : ℂ)) (by fun_prop)
    have h0 : ((((x k - x k) ^ 2 : ℝ)) : ℂ) = 0 := by simp
    rw [h0] at h
    have e : ∀ n, traceExpectation (projectionDensity P n)
        (spectralFunction (fun z : ℝ => (((z - x k) ^ 2 : ℝ) : ℂ)) (S.observable n k)) =
        om S P n (D n k * D n k) := by
      intro n; rw [spec_sq _ (hS.2.1 n k)]; rfl
    exact h.congr e
  have hW : ∀ w : List K, Tendsto (fun n => om S P n (wordOperator n w)) atTop
      (𝓝 (w.map (fun k => (x k : ℂ))).prod) := by
    intro w
    induction w with
    | nil =>
      simp only [wordOperator, List.map_nil, List.prod_nil]
      exact tendsto_const_nhds.congr fun n => (om_one S P n (hp n) (hne n)).symm
    | cons k w ih =>
      have split : ∀ n, om S P n (wordOperator n (k :: w)) =
          om S P n (D n k * wordOperator n w) + (x k : ℂ) * om S P n (wordOperator n w) := by
        intro n
        rw [← om_add_smul S P n (hp n)]
        congr 1
        simp only [wordOperator, List.map_cons, List.prod_cons, D, Matrix.sub_mul,
          Matrix.smul_mul, Matrix.one_mul, sub_add_cancel]
      have h0 : Tendsto (fun n => om S P n (D n k * wordOperator n w)) atTop (𝓝 0) := by
        set C := (w.map S.radius).prod
        have hre : Tendsto (fun n => Real.sqrt ((om S P n (D n k * D n k)).re * C ^ 2))
            atTop (𝓝 0) := by
          have := ((Complex.continuous_re.tendsto 0).comp (hD k)).mul_const (C ^ 2)
          have := this.sqrt
          rw [Complex.zero_re, zero_mul, Real.sqrt_zero] at this
          exact this
        refine squeeze_zero_norm (fun n => ?_) hre
        have h1 := om_cs S P n (hp n) (hne n) (D n k) (wordOperator n w)
        rw [hDh] at h1
        have h2 : (om S P n (D n k * D n k)).re * ‖wordOperator (S := S) n w‖ ^ 2 ≤
            (om S P n (D n k * D n k)).re * C ^ 2 := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hword n w) 2) ?_
          have := om_re_nonneg S P n (hp n) (D n k)
          rwa [hDh] at this
        exact (le_abs_self _).trans (Real.abs_le_sqrt (h1.trans h2))
      have := h0.add (ih.const_mul (x k : ℂ))
      simp only [zero_add, List.map_cons, List.prod_cons] at this ⊢
      exact this.congr fun n => (split n).symm
  -- the series
  have hsum : ∀ n, Summable (fun w => G.coefficient w • wordOperator (S := S) n w) := fun n =>
    Summable.of_norm_bounded G.summable fun w =>
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hword n w) (norm_nonneg _))
  have hev : ∀ n, traceExpectation (projectionDensity P n) (operatorEvaluation G n) =
      ∑' w, G.coefficient w * om S P n (wordOperator n w) := by
    intro n
    let φ : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (Fin (S.dimension n)) ℂ ℂ) ∘ₗ
          (LinearMap.mulLeft ℂ (projectionDensity P n)))
    have hφ : ∀ X, φ X = traceExpectation (projectionDensity P n) X := fun X => rfl
    rw [← hφ, operatorEvaluation, φ.map_tsum (hsum n)]
    congr 1; funext w
    show φ (G.coefficient w • _) = _
    rw [φ.map_smul, smul_eq_mul]
    rfl
  simp_rw [hev]
  unfold scalarEvaluation
  refine tendsto_tsum_of_dominated_convergence (bound := fun w =>
    ‖G.coefficient w‖ * (w.map S.radius).prod) G.summable (fun w => (hW w).const_mul _)
    (Eventually.of_forall fun n w => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((om_norm S P n (hp n) (hne n) _).trans (hword n w))
    (norm_nonneg _)

end X6MQ


/-! The order microcanonical ≤ canonical ≤ mean-canonical entropy. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

variable {K : Type*}

lemma ent_proj {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (hP : IsStarProjection P) (hne : P ≠ 0) :
    densityEntropyNats ((P.trace)⁻¹ • P) = Real.log P.trace.re := by
  obtain ⟨h1, h2, h3⟩ := trace_proj P hP
  have ht := h3 hne
  set t := P.trace.re
  have hsa : IsSelfAdjoint P := hP.isSelfAdjoint
  have hsm : (P.trace)⁻¹ • P = (t⁻¹ : ℝ) • P := by
    rw [h1, ← Complex.ofReal_inv, Complex.coe_smul]
  have hspec : spectrum ℝ P ⊆ {0, 1} := hP.isIdempotentElem.spectrum_subset ℝ
  have hc : cfc (fun z : ℝ => z * Real.log z) ((t⁻¹ : ℝ) • P) =
      (t⁻¹ * Real.log t⁻¹) • P := by
    rw [← cfc_comp_smul (t⁻¹ : ℝ) (fun z : ℝ => z * Real.log z) P
      (Real.continuous_mul_log.continuousOn) hsa]
    rw [← cfc_const_mul_id (t⁻¹ * Real.log t⁻¹) P hsa]
    refine cfc_congr fun z hz => ?_
    rcases hspec hz with h | h
    · simp [Set.mem_singleton_iff.mp h]
    · simp only [Set.mem_singleton_iff] at h
      simp [h]
  unfold densityEntropyNats
  rw [hsm, hc, Matrix.trace_smul, h1]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [Real.log_inv]
  field_simp

lemma state_proj {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (hP : IsStarProjection P) (hne : P ≠ 0) :
    QAlgorithms.IsDensityMatrix ((P.trace)⁻¹ • P) := by
  obtain ⟨h1, h2, h3⟩ := trace_proj P hP
  have ht := h3 hne
  have hpsd : P.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [show Pᴴ = P from hP.isSelfAdjoint, show P * P = P from hP.isIdempotentElem] at this
  refine ⟨hpsd.smul ?_, ?_⟩
  · rw [h1, ← Complex.ofReal_inv]
    exact_mod_cast (inv_nonneg.mpr h2)
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀]
    rw [h1]; exact_mod_cast ht.ne'

theorem micro_le_canon (S : MacroscopicSystem K) (hS : IsMacroscopic S) (x : K → ℝ) :
    microcanonicalEntropy S x ≤ canonicalEntropy S x := by
  refine sSup_le_sSup ?_
  rintro h ⟨P, hP, rfl⟩
  refine ⟨projectionDensity P, fun n => state_proj _ (hP.1 n).1 (hP.1 n).2,
    joint S hS P x hP, ?_⟩
  unfold projectionDimensionDensity entropyDensity
  congr 1
  funext n
  simp only [projectionDensity]
  rw [ent_proj _ (hP.1 n).1 (hP.1 n).2]

open Classical in
/-- the single-letter test series -/
def single (S : MacroscopicSystem K) (k : K) : AnalyticTestSeries S where
  coefficient w := if w = [k] then 1 else 0
  summable := by
    refine summable_of_ne_finset_zero (s := {[k]}) fun w hw => ?_
    simp only [Finset.mem_singleton] at hw
    simp [hw]

lemma single_op (S : MacroscopicSystem K) (k : K) (n : ℕ) :
    operatorEvaluation (single S k) n = S.observable n k := by
  unfold operatorEvaluation
  rw [tsum_eq_single [k] fun w hw => by simp [single, hw]]
  simp [single, wordOperator]

lemma single_sc (S : MacroscopicSystem K) (k : K) (x : K → ℝ) :
    scalarEvaluation (single S k) x = (x k : ℂ) := by
  unfold scalarEvaluation
  rw [tsum_eq_single [k] fun w hw => by simp [single, hw]]
  simp [single]

theorem canon_le_mean (S : MacroscopicSystem K) (x : K → ℝ) :
    canonicalEntropy S x ≤ meanCanonicalEntropy S x := by
  refine sSup_le_sSup ?_
  rintro h ⟨rho, hrho, hc, rfl⟩
  refine ⟨rho, hrho, fun k => ?_, rfl⟩
  have := hc (single S k)
  simp only [single_op, single_sc] at this
  exact this

end X6MQ


/-! Concentration of a state sequence under all analytic tests implies concentration
under all continuous single-variable tests (Weierstrass approximation). -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

section gen

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_fac (A : Matrix I I ℂ) (hA : A.PosSemidef) : ∃ B : Matrix I I ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  exact ⟨_, hAB⟩

lemma key_st (B X Y : Matrix I I ℂ) :
    Complex.normSq (Bᴴ * B * X * Y).trace ≤
      (Bᴴ * B * X * Xᴴ).trace.re * (‖Y‖ ^ 2 * (Bᴴ * B).trace.re) ∧
    0 ≤ (Bᴴ * B * X * Xᴴ).trace.re := by
  have h1 : (Xᴴ * Bᴴ)ᴴ * (Y * Bᴴ) = B * X * Y * Bᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    simp [Matrix.mul_assoc]
  have h2 : (Xᴴ * Bᴴ)ᴴ * (Xᴴ * Bᴴ) = B * X * Xᴴ * Bᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    simp [Matrix.mul_assoc]
  have tr4 : ∀ Z : Matrix I I ℂ, (B * Z * Bᴴ).trace = (Bᴴ * B * Z).trace := by
    intro Z; rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have hc := fro_cs (Xᴴ * Bᴴ) (Y * Bᴴ)
  have hb := col_bound Y Bᴴ
  rw [h1, h2, Matrix.mul_assoc B X Y, tr4, Matrix.mul_assoc B X Xᴴ, tr4] at hc
  rw [conjTranspose_conjTranspose, Matrix.trace_mul_comm B Bᴴ] at hb
  have h0 : 0 ≤ ((Xᴴ * Bᴴ)ᴴ * (Xᴴ * Bᴴ)).trace.re := by
    rw [fro_re]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h2, Matrix.mul_assoc B X Xᴴ, tr4] at h0
  simp only [Matrix.mul_assoc] at hc h0 ⊢
  exact ⟨hc.trans (mul_le_mul_of_nonneg_left hb h0), h0⟩

lemma st_norm (ρ : Matrix I I ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (Y : Matrix I I ℂ) :
    ‖(ρ * Y).trace‖ ≤ ‖Y‖ := by
  obtain ⟨B, hB⟩ := psd_fac ρ hρ.1
  have htr : (Bᴴ * B).trace.re = 1 := by rw [← hB, hρ.2]; simp
  have hk := (key_st B 1 Y).1
  simp only [Matrix.mul_one, conjTranspose_one, htr] at hk
  rw [← hB] at hk
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    ← Complex.normSq_eq_norm_sq]
  simpa using hk

lemma st_cs (ρ : Matrix I I ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (D W : Matrix I I ℂ) :
    ‖(ρ * (D * W)).trace‖ ^ 2 ≤ (ρ * (D * Dᴴ)).trace.re * ‖W‖ ^ 2 ∧
    0 ≤ (ρ * (D * Dᴴ)).trace.re := by
  obtain ⟨B, hB⟩ := psd_fac ρ hρ.1
  have htr : (Bᴴ * B).trace.re = 1 := by rw [← hB, hρ.2]; simp
  obtain ⟨hk, h0⟩ := key_st B D W
  rw [htr, mul_one, ← hB] at hk
  rw [← hB] at h0
  rw [← Complex.normSq_eq_norm_sq, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact ⟨by linarith, h0⟩

lemma eig_le (A : Matrix I I ℂ) (hA : A.IsHermitian) (j : I) : |hA.eigenvalues j| ≤ ‖A‖ := by
  have hv : ‖hA.eigenvectorBasis j‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 j
  have h := Matrix.l2_opNorm_mulVec A (hA.eigenvectorBasis j)
  have e : (EuclideanSpace.equiv I ℂ).symm (A *ᵥ (hA.eigenvectorBasis j).ofLp) =
      hA.eigenvalues j • hA.eigenvectorBasis j := by
    have := hA.mulVec_eigenvectorBasis j
    rw [this]; rfl
  rw [e, norm_smul, hv, mul_one, mul_one, Real.norm_eq_abs] at h
  exact h

lemma unit_norm (U : Matrix I I ℂ) (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [hU] at h
  have h1 : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    have h' := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix I I ℂ)
    rw [conjTranspose_one, Matrix.one_mul] at h'
    nlinarith [norm_nonneg (1 : Matrix I I ℂ)]
  nlinarith [norm_nonneg U]

end gen

lemma sF_eq {d : ℕ} (f : ℝ → ℂ) (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    spectralFunction f A = (↑hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun j => f (hA.eigenvalues j)) *
        (↑hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  unfold spectralFunction; rw [dif_pos hA]

lemma sF_diff {d : ℕ} (f g : ℝ → ℂ) (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ j, ‖f (hA.eigenvalues j) - g (hA.eigenvalues j)‖ ≤ ε) :
    ‖spectralFunction f A - spectralFunction g A‖ ≤ ε := by
  rw [sF_eq f A hA, sF_eq g A hA, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hu : ‖U‖ ≤ 1 := unit_norm U hU1
  have hu' : ‖Uᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hu
  have hD : ‖diagonal (fun j => f (hA.eigenvalues j) - g (hA.eigenvalues j))‖ ≤ ε := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hε).mpr h
  calc ‖U * diagonal (fun j => f (hA.eigenvalues j) - g (hA.eigenvalues j)) * Uᴴ‖
      ≤ ‖U‖ * ‖diagonal (fun j => f (hA.eigenvalues j) - g (hA.eigenvalues j))‖ * ‖Uᴴ‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ε * 1 := by gcongr
    _ = ε := by ring

lemma sF_poly {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℕ → ℂ) (N : ℕ) :
    spectralFunction (fun z : ℝ => ∑ m ∈ Finset.range N, c m * (z : ℂ) ^ m) A =
      ∑ m ∈ Finset.range N, c m • A ^ m := by
  rw [sF_eq _ A hA]
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hsp : A = U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hpow : ∀ m : ℕ, A ^ m = U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ) ^ m) * Uᴴ := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero]
      rw [show (diagonal fun j => (1 : ℂ)) = 1 from diagonal_one, Matrix.mul_one, hU2]
    | succ m ih =>
      have : U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ) ^ m) * Uᴴ *
          (U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) * Uᴴ) =
          U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ) ^ (m + 1)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul, ← Matrix.mul_assoc
          (diagonal _) (diagonal _), diagonal_mul_diagonal]
        simp only [pow_succ]
      rw [pow_succ, ih, ← this, ← hsp]
  have hdiag : diagonal (fun j => ∑ m ∈ Finset.range N, c m * ((hA.eigenvalues j : ℝ) : ℂ) ^ m) =
      ∑ m ∈ Finset.range N, c m • diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ) ^ m) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [diagonal, Matrix.sum_apply]
    · simp [diagonal, Matrix.sum_apply, h]
  rw [hdiag, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hpow m, Matrix.mul_smul, Matrix.smul_mul]

variable {K : Type*}

open Classical in
/-- the single-word test series -/
def wtest (S : MacroscopicSystem K) (w0 : List K) : AnalyticTestSeries S where
  coefficient w := if w = w0 then 1 else 0
  summable := by
    refine summable_of_ne_finset_zero (s := {w0}) fun w hw => ?_
    simp only [Finset.mem_singleton] at hw
    simp [hw]

lemma wtest_op (S : MacroscopicSystem K) (w0 : List K) (n : ℕ) :
    operatorEvaluation (wtest S w0) n = wordOperator n w0 := by
  unfold operatorEvaluation
  rw [tsum_eq_single w0 fun w hw => by simp [wtest, hw]]
  simp [wtest]

lemma wtest_sc (S : MacroscopicSystem K) (w0 : List K) (x : K → ℝ) :
    scalarEvaluation (wtest S w0) x = (w0.map (fun k => (x k : ℂ))).prod := by
  unfold scalarEvaluation
  rw [tsum_eq_single w0 fun w hw => by simp [wtest, hw]]
  simp [wtest]

theorem to_single (S : MacroscopicSystem K) (hS : IsMacroscopic S) (rho : OperatorSequence S)
    (x : K → ℝ) (hrho : IsStateSequence rho) (hc : stateConcentrates S rho x) :
    singleVariableConcentrates S rho x := by
  intro k F hF
  obtain ⟨B, hB0, -, hBn⟩ := hS.2.2 k
  have hA : ∀ n, ‖S.observable n k‖ ≤ B := fun n => hBn n
  have hmono : ∀ m : ℕ, Tendsto (fun n => traceExpectation (rho n) (S.observable n k ^ m))
      atTop (𝓝 ((x k : ℂ) ^ m)) := by
    intro m
    have := hc (wtest S (List.replicate m k))
    simp only [wtest_op, wtest_sc, wordOperator, List.map_replicate, List.prod_replicate] at this
    exact this
  have hx : |x k| ≤ B := by
    have h1 := hmono 1
    simp only [pow_one] at h1
    have h2 := (continuous_norm.tendsto _).comp h1
    have h3 : ‖(x k : ℂ)‖ ≤ B := le_of_tendsto' h2 fun n =>
      (st_norm _ (hrho n) _).trans (hA n)
    simpa [Complex.norm_real] using h3
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / 8 := by positivity
  obtain ⟨p1, hp1⟩ := exists_polynomial_near_of_continuousOn (-B) B (fun z => (F z).re)
    (Complex.continuous_re.comp hF).continuousOn (ε / 8) hδ
  obtain ⟨p2, hp2⟩ := exists_polynomial_near_of_continuousOn (-B) B (fun z => (F z).im)
    (Complex.continuous_im.comp hF).continuousOn (ε / 8) hδ
  set N := max p1.natDegree p2.natDegree + 1
  let c : ℕ → ℂ := fun m => (p1.coeff m : ℂ) + (p2.coeff m : ℂ) * Complex.I
  let q : ℝ → ℂ := fun z => ∑ m ∈ Finset.range N, c m * (z : ℂ) ^ m
  have hq : ∀ z : ℝ, q z = ((p1.eval z : ℝ) : ℂ) + ((p2.eval z : ℝ) : ℂ) * Complex.I := by
    intro z
    rw [Polynomial.eval_eq_sum_range' (p := p1) (n := N) (by omega),
      Polynomial.eval_eq_sum_range' (p := p2) (n := N) (by omega)]
    simp only [q, c, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    push_cast
    rw [Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  have hFq : ∀ z ∈ Set.Icc (-B) B, ‖F z - q z‖ ≤ ε / 4 := by
    intro z hz
    rw [hq]
    have e1 := hp1 z hz
    have e2 := hp2 z hz
    have : F z - (((p1.eval z : ℝ) : ℂ) + ((p2.eval z : ℝ) : ℂ) * Complex.I) =
        (((F z).re - p1.eval z : ℝ) : ℂ) + (((F z).im - p2.eval z : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm (F z).im]
    linarith
  have hpoly : Tendsto (fun n => traceExpectation (rho n)
      (∑ m ∈ Finset.range N, c m • S.observable n k ^ m)) atTop (𝓝 (q (x k))) := by
    have : ∀ n, traceExpectation (rho n) (∑ m ∈ Finset.range N, c m • S.observable n k ^ m) =
        ∑ m ∈ Finset.range N, c m * traceExpectation (rho n) (S.observable n k ^ m) := by
      intro n
      simp only [traceExpectation, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul]
    simp only [this, q]
    exact tendsto_finset_sum _ fun m _ => (hmono m).const_mul _
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hpoly (ε / 4) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have hherm := hS.2.1 n k
  have hsq : spectralFunction q (S.observable n k) =
      ∑ m ∈ Finset.range N, c m • S.observable n k ^ m := sF_poly _ hherm c N
  have hdiff : ‖spectralFunction F (S.observable n k) - spectralFunction q (S.observable n k)‖ ≤
      ε / 4 := by
    refine sF_diff F q _ hherm (ε / 4) (by positivity) fun j => hFq _ ?_
    have := (eig_le _ hherm j).trans (hA n)
    exact ⟨by linarith [neg_abs_le (hherm.eigenvalues j)], by linarith [le_abs_self (hherm.eigenvalues j)]⟩
  have t1 : ‖traceExpectation (rho n) (spectralFunction F (S.observable n k)) -
      traceExpectation (rho n) (spectralFunction q (S.observable n k))‖ ≤ ε / 4 := by
    simp only [traceExpectation]
    rw [← Matrix.trace_sub, ← Matrix.mul_sub]
    exact (st_norm _ (hrho n) _).trans hdiff
  have t2 := hN0 n hn
  rw [dist_eq_norm, ← hsq] at t2
  have t3 : ‖q (x k) - F (x k)‖ ≤ ε / 4 := by
    rw [norm_sub_rev]; exact hFq _ ⟨by linarith [neg_abs_le (x k)], by linarith [le_abs_self (x k)]⟩
  rw [dist_eq_norm]
  calc ‖traceExpectation (rho n) (spectralFunction F (S.observable n k)) - F (x k)‖
      ≤ ‖traceExpectation (rho n) (spectralFunction F (S.observable n k)) -
          traceExpectation (rho n) (spectralFunction q (S.observable n k))‖ +
        ‖traceExpectation (rho n) (spectralFunction q (S.observable n k)) - q (x k)‖ +
        ‖q (x k) - F (x k)‖ := by
          refine (norm_sub_le_norm_sub_add_norm_sub _ (q (x k)) _).trans ?_
          gcongr
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

end X6MQ


noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

variable {K : Type*}

/-- the state functional of a general density sequence -/
def st (S : MacroscopicSystem K) (rho : OperatorSequence S) (n : ℕ)
    (X : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ) : ℂ :=
  traceExpectation (rho n) X

lemma st_one (S : MacroscopicSystem K) (rho : OperatorSequence S) (n : ℕ)
    (h : QAlgorithms.IsDensityMatrix (rho n)) : st S rho n 1 = 1 := by
  simp [st, traceExpectation, h.2]

lemma st_add_smul (S : MacroscopicSystem K) (rho : OperatorSequence S) (n : ℕ) (X Y) (c : ℂ) :
    st S rho n (X + c • Y) = st S rho n X + c * st S rho n Y := by
  simp [st, traceExpectation, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]

lemma st_norm' (S : MacroscopicSystem K) (rho : OperatorSequence S) (n : ℕ)
    (h : QAlgorithms.IsDensityMatrix (rho n)) (Y) : ‖st S rho n Y‖ ≤ ‖Y‖ :=
  st_norm _ h Y

lemma st_cs' (S : MacroscopicSystem K) (rho : OperatorSequence S) (n : ℕ)
    (h : QAlgorithms.IsDensityMatrix (rho n)) (D W) :
    ‖st S rho n (D * W)‖ ^ 2 ≤ (st S rho n (D * Dᴴ)).re * ‖W‖ ^ 2 :=
  (st_cs _ h D W).1

lemma st_re_nonneg (S : MacroscopicSystem K) (rho : OperatorSequence S) (n : ℕ)
    (h : QAlgorithms.IsDensityMatrix (rho n)) (X) : 0 ≤ (st S rho n (X * Xᴴ)).re :=
  (st_cs _ h X 1).2

theorem from_single (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hrho : IsStateSequence rho) (hconc : singleVariableConcentrates S rho x) :
    stateConcentrates S rho x := by
  intro G
  have hB : ∀ n k, ‖S.observable n k‖ ≤ S.radius k := by
    intro n k
    obtain ⟨B, -, hBr, hBn⟩ := hS.2.2 k
    exact (show ‖S.observable n k‖ ≤ B from hBn n).trans hBr.le
  have hrad : ∀ k, 0 ≤ S.radius k := fun k => (norm_nonneg _).trans (hB 0 k)
  have hword : ∀ n (w : List K), ‖wordOperator (S := S) n w‖ ≤ (w.map S.radius).prod := by
    intro n w
    induction w with
    | nil => simpa [wordOperator] using norm_one_le
    | cons k w ih =>
      simp only [wordOperator, List.map_cons, List.prod_cons] at ih ⊢
      exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hB n k) ih (norm_nonneg _) (hrad k))
  -- centred observables
  let D : ∀ n, K → Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
    fun n k => S.observable n k - (x k : ℂ) • 1
  have hDh : ∀ n k, (D n k)ᴴ = D n k := by
    intro n k
    simp only [D, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal, (hS.2.1 n k).eq]
  have hD : ∀ k, Tendsto (fun n => st S rho n (D n k * D n k)) atTop (𝓝 0) := by
    intro k
    have h := hconc k (fun z : ℝ => (((z - x k) ^ 2 : ℝ) : ℂ)) (by fun_prop)
    have h0 : ((((x k - x k) ^ 2 : ℝ)) : ℂ) = 0 := by simp
    rw [h0] at h
    have e : ∀ n, traceExpectation (rho n)
        (spectralFunction (fun z : ℝ => (((z - x k) ^ 2 : ℝ) : ℂ)) (S.observable n k)) =
        st S rho n (D n k * D n k) := by
      intro n; rw [spec_sq _ (hS.2.1 n k)]; rfl
    exact h.congr e
  have hW : ∀ w : List K, Tendsto (fun n => st S rho n (wordOperator n w)) atTop
      (𝓝 (w.map (fun k => (x k : ℂ))).prod) := by
    intro w
    induction w with
    | nil =>
      simp only [wordOperator, List.map_nil, List.prod_nil]
      exact tendsto_const_nhds.congr fun n => (st_one S rho n (hrho n)).symm
    | cons k w ih =>
      have split : ∀ n, st S rho n (wordOperator n (k :: w)) =
          st S rho n (D n k * wordOperator n w) + (x k : ℂ) * st S rho n (wordOperator n w) := by
        intro n
        rw [← st_add_smul S rho n]
        congr 1
        simp only [wordOperator, List.map_cons, List.prod_cons, D, Matrix.sub_mul,
          Matrix.smul_mul, Matrix.one_mul, sub_add_cancel]
      have h0 : Tendsto (fun n => st S rho n (D n k * wordOperator n w)) atTop (𝓝 0) := by
        set C := (w.map S.radius).prod
        have hre : Tendsto (fun n => Real.sqrt ((st S rho n (D n k * D n k)).re * C ^ 2))
            atTop (𝓝 0) := by
          have := ((Complex.continuous_re.tendsto 0).comp (hD k)).mul_const (C ^ 2)
          have := this.sqrt
          rw [Complex.zero_re, zero_mul, Real.sqrt_zero] at this
          exact this
        refine squeeze_zero_norm (fun n => ?_) hre
        have h1 := st_cs' S rho n (hrho n) (D n k) (wordOperator n w)
        rw [hDh] at h1
        have h2 : (st S rho n (D n k * D n k)).re * ‖wordOperator (S := S) n w‖ ^ 2 ≤
            (st S rho n (D n k * D n k)).re * C ^ 2 := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hword n w) 2) ?_
          have := st_re_nonneg S rho n (hrho n) (D n k)
          rwa [hDh] at this
        exact (le_abs_self _).trans (Real.abs_le_sqrt (h1.trans h2))
      have := h0.add (ih.const_mul (x k : ℂ))
      simp only [zero_add, List.map_cons, List.prod_cons] at this ⊢
      exact this.congr fun n => (split n).symm
  -- the series
  have hsum : ∀ n, Summable (fun w => G.coefficient w • wordOperator (S := S) n w) := fun n =>
    Summable.of_norm_bounded G.summable fun w =>
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hword n w) (norm_nonneg _))
  have hev : ∀ n, traceExpectation (rho n) (operatorEvaluation G n) =
      ∑' w, G.coefficient w * st S rho n (wordOperator n w) := by
    intro n
    let φ : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (Fin (S.dimension n)) ℂ ℂ) ∘ₗ
          (LinearMap.mulLeft ℂ (rho n)))
    have hφ : ∀ X, φ X = traceExpectation (rho n) X := fun X => rfl
    rw [← hφ, operatorEvaluation, φ.map_tsum (hsum n)]
    congr 1; funext w
    show φ (G.coefficient w • _) = _
    rw [φ.map_smul, smul_eq_mul]
    rfl
  simp_rw [hev]
  unfold scalarEvaluation
  refine tendsto_tsum_of_dominated_convergence (bound := fun w =>
    ‖G.coefficient w‖ * (w.map S.radius).prod) G.summable (fun w => (hW w).const_mul _)
    (Eventually.of_forall fun n w => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((st_norm' S rho n (hrho n) _).trans (hword n w))
    (norm_nonneg _)

theorem conc_equiv (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hrho : IsStateSequence rho) :
    stateConcentrates S rho x ↔ singleVariableConcentrates S rho x :=
  ⟨to_single S hS rho x hrho, from_single S hS rho x hrho⟩

end X6MQ


/-! Microcanonical autonomy: entropy at the endpoint dominates the initial entropy,
and the microcanonical H-theorem. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

lemma tr_aut {d : ℕ} (τ : Matrix (Fin d) (Fin d) ℂ ≃⋆ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) : (τ X).trace = X.trace := by
  rcases d with _ | d
  · simp [Matrix.trace]
  have hcomm : ∀ Y Z, (τ (Y * Z)).trace = (τ (Z * Y)).trace := by
    intro Y Z; rw [map_mul, map_mul]; exact Matrix.trace_mul_comm _ _
  have hsm : ∀ i j (c : ℂ), (τ (Matrix.single i j c)).trace =
      c * (τ (Matrix.single i j 1)).trace := by
    intro i j c
    have : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, Matrix.trace_smul, smul_eq_mul]
  have hoff : ∀ i j, i ≠ j → (τ (Matrix.single i j 1)).trace = 0 := by
    intro i j hij
    have e1 : Matrix.single i j (1 : ℂ) = Matrix.single i i 1 * Matrix.single i j 1 := by
      rw [Matrix.single_mul_single_same, one_mul]
    rw [e1, hcomm, Matrix.single_mul_single_of_ne (h := Ne.symm hij)]
    simp
  have hdiag : ∀ i, (τ (Matrix.single i i 1)).trace = (τ (Matrix.single 0 0 1)).trace := by
    intro i
    have e1 : Matrix.single i i (1 : ℂ) = Matrix.single i 0 1 * Matrix.single 0 i 1 := by
      rw [Matrix.single_mul_single_same, one_mul]
    have e2 : Matrix.single 0 i (1 : ℂ) * Matrix.single i 0 1 = Matrix.single 0 0 1 := by
      rw [Matrix.single_mul_single_same, one_mul]
    rw [e1, hcomm, e2]
  have hall : ∀ Y, (τ Y).trace = (τ (Matrix.single 0 0 1)).trace * Y.trace := by
    intro Y
    conv_lhs => rw [matrix_eq_sum_single Y]
    rw [map_sum, Matrix.trace_sum]
    simp only [map_sum, Matrix.trace_sum]
    rw [show Y.trace = ∑ i, Y i i from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [hsm, hdiag]; simp [mul_comm]
    · intro j _ hj; rw [hsm, hoff i j (Ne.symm hj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h1 := hall 1
  rw [map_one] at h1
  have hd : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace ≠ 0 := by
    simp [Matrix.trace]; exact Nat.cast_add_one_ne_zero d
  have he : (τ (Matrix.single 0 0 1)).trace = 1 := (mul_eq_right₀ hd).mp h1.symm
  rw [hall, he, one_mul]

variable {K : Type*}

theorem endpoint (S : MacroscopicSystem K) (hS : IsMacroscopic S) (tau : AutomorphismDynamics S)
    (phi : MacroscopicDynamics K) (haut : microcanonicalAutonomy S tau phi) :
    ∀ x, microcanonicalAdmissible S x → ∀ (t s : ℝ), 0 ≤ s → s ≤ t →
      microcanonicalEntropy S x ≤ microcanonicalEntropy S (phi t s x) := by
  intro x hx t s hs hst
  obtain ⟨P, ⟨hPc, hPd⟩, hconv⟩ := haut.2 x hx
  let σ := fun n => tau n t s
  let P' : OperatorSequence S := fun n => (σ n).symm (P n)
  have hp : ∀ n, IsStarProjection (P n) := fun n => (hPc.1 n).1
  have hne : ∀ n, P n ≠ 0 := fun n => (hPc.1 n).2
  have hσP : ∀ n, σ n (P' n) = P n := fun n => (σ n).apply_symm_apply _
  have hp' : ∀ n, IsStarProjection (P' n) := by
    intro n
    refine ⟨?_, ?_⟩
    · show P' n * P' n = P' n
      simp only [P']
      rw [← map_mul, (hp n).isIdempotentElem.eq]
    · show star (P' n) = P' n
      simp only [P']
      rw [← map_star, (hp n).isSelfAdjoint.star_eq]
  have hne' : ∀ n, P' n ≠ 0 := by
    intro n h
    apply hne n
    rw [← hσP n, h, map_zero]
  have htr : ∀ n, (P' n).trace = (P n).trace := by
    intro n; rw [← tr_aut (σ n) (P' n), hσP]
  have hexp : ∀ n X, traceExpectation (projectionDensity P' n) X =
      traceExpectation (projectionDensity P n) (σ n X) := by
    intro n X
    simp only [traceExpectation, projectionDensity, Matrix.smul_mul, Matrix.trace_smul, htr]
    congr 1
    rw [← tr_aut (σ n) (P' n * X), map_mul, hσP]
  have hstate : stateConcentrates S (projectionDensity P') (phi t s x) := by
    intro G
    have := hconv G t s hs hst
    exact this.congr fun n => (hexp n _).symm
  have hst' : IsStateSequence (projectionDensity P') := fun n => state_proj _ (hp' n) (hne' n)
  have hconc : projectionConcentrates S P' (phi t s x) :=
    ⟨fun n => ⟨hp' n, hne' n⟩, to_single S hS _ _ hst' hstate⟩
  have hdim : projectionDimensionDensity P' = projectionDimensionDensity P := by
    unfold projectionDimensionDensity
    simp only [htr]
  rw [← hPd, ← hdim]
  exact le_sSup ⟨P', hconc, rfl⟩

theorem hTheorem (S : MacroscopicSystem K) (hS : IsMacroscopic S) (tau : AutomorphismDynamics S)
    (phi : MacroscopicDynamics K) (haut : microcanonicalAutonomy S tau phi)
    (hsemigroup : macroscopicSemigroup (microcanonicalAdmissible S) phi) :
    ∀ x, microcanonicalAdmissible S x →
      MonotoneOn (fun t => microcanonicalEntropy S (phi t 0 x)) (Set.Ici 0) := by
  intro x hx a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hadm : microcanonicalAdmissible S (phi a 0 x) := haut.1 x hx a 0 le_rfl ha
  have := endpoint S hS tau phi haut (phi a 0 x) hadm b a ha hab
  rwa [hsemigroup x hx b a 0 le_rfl ha hab] at this

end X6MQ


/-! Remark 2.2: classically equivalent analytic tests have the same limit, and centred
exponential sums / ordered exponential products tend to one. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator Nat

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

/-- the exponential-type constant `∑ Cⁿ/n!` -/
def ec (C : ℝ) : ℝ := ∑' n : ℕ, C ^ n / (n ! : ℝ)

lemma norm_pow_le_d {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  rcases n with _ | n
  · simpa using norm_one_le
  · exact norm_pow_le' a (Nat.succ_pos n)

lemma exp_sub_one {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ) (C : ℝ) (hC : ‖a‖ ≤ C) :
    ∃ Z : Matrix (Fin d) (Fin d) ℂ, NormedSpace.exp a - 1 = a * Z ∧ ‖Z‖ ≤ ec C := by
  have hs : Summable (fun n : ℕ => ((n ! : ℂ)⁻¹) • a ^ n) := NormedSpace.expSeries_summable' a
  let g : ℕ → Matrix (Fin d) (Fin d) ℂ := fun n => (((n + 1)! : ℂ)⁻¹) • a ^ n
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hgb : ∀ n, ‖g n‖ ≤ C ^ n / (n ! : ℝ) := by
    intro n
    refine (norm_smul_le _ _).trans ?_
    rw [norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    have h1 : ((n + 1)! : ℝ)⁻¹ ≤ (n ! : ℝ)⁻¹ :=
      inv_anti₀ (by exact_mod_cast Nat.factorial_pos n)
        (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
    have h2 : ‖a ^ n‖ ≤ C ^ n := (norm_pow_le_d a n).trans (pow_le_pow_left₀ (norm_nonneg _) hC n)
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hsC : Summable (fun n : ℕ => C ^ n / (n ! : ℝ)) := Real.summable_pow_div_factorial C
  have hg : Summable g := Summable.of_norm_bounded hsC hgb
  refine ⟨∑' n, g n, ?_, ?_⟩
  · rw [congrFun (NormedSpace.exp_eq_tsum ℂ) a]
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, add_sub_cancel_left]
    rw [← hg.tsum_mul_left a]
    congr 1; funext n
    simp only [g, Matrix.mul_smul, ← pow_succ']
  · refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hgb hsC)).trans ?_
    exact Summable.tsum_le_tsum hgb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hgb hsC) hsC

lemma ec_nonneg (C : ℝ) (hC : 0 ≤ C) : 0 ≤ ec C := tsum_nonneg fun n => by positivity

variable {K : Type*}

lemma om_sum (S : MacroscopicSystem K) (P : OperatorSequence S) (n : ℕ)
    (hp : IsStarProjection (P n)) {ι : Type*} (R : Finset ι) (c : ι → ℂ) (X : ι → _) :
    om S P n (∑ k ∈ R, c k • X k) = ∑ k ∈ R, c k * om S P n (X k) := by
  simp only [om_eq S P n hp, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- `ω_n(D_k Y_n) → 0` for uniformly bounded `Y_n`. -/
lemma small (S : MacroscopicSystem K) (hS : IsMacroscopic S) (P : OperatorSequence S)
    (x : K → ℝ) (hP : projectionConcentrates S P x) (k : K)
    (Y : ∀ n, Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ) (C : ℝ)
    (hY : ∀ n, ‖Y n‖ ≤ C) :
    Tendsto (fun n => om S P n ((S.observable n k - (x k : ℂ) • 1) * Y n)) atTop (𝓝 0) := by
  obtain ⟨hproj, hconc⟩ := hP
  have hp : ∀ n, IsStarProjection (P n) := fun n => (hproj n).1
  have hne : ∀ n, P n ≠ 0 := fun n => (hproj n).2
  let D : ∀ n, Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
    fun n => S.observable n k - (x k : ℂ) • 1
  have hDh : ∀ n, (D n)ᴴ = D n := by
    intro n
    simp only [D, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal, (hS.2.1 n k).eq]
  have hD : Tendsto (fun n => om S P n (D n * D n)) atTop (𝓝 0) := by
    have h := hconc k (fun z : ℝ => (((z - x k) ^ 2 : ℝ) : ℂ)) (by fun_prop)
    have h0 : ((((x k - x k) ^ 2 : ℝ)) : ℂ) = 0 := by simp
    rw [h0] at h
    have e : ∀ n, traceExpectation (projectionDensity P n)
        (spectralFunction (fun z : ℝ => (((z - x k) ^ 2 : ℝ) : ℂ)) (S.observable n k)) =
        om S P n (D n * D n) := by
      intro n; rw [spec_sq _ (hS.2.1 n k)]; rfl
    exact h.congr e
  have hre : Tendsto (fun n => Real.sqrt ((om S P n (D n * D n)).re * C ^ 2)) atTop (𝓝 0) := by
    have := (((Complex.continuous_re.tendsto 0).comp hD).mul_const (C ^ 2)).sqrt
    rw [Complex.zero_re, zero_mul, Real.sqrt_zero] at this
    exact this
  refine squeeze_zero_norm (fun n => ?_) hre
  have h1 := om_cs S P n (hp n) (hne n) (D n) (Y n)
  rw [hDh] at h1
  have hC : 0 ≤ C := (norm_nonneg _).trans (hY 0)
  have h2 : (om S P n (D n * D n)).re * ‖Y n‖ ^ 2 ≤ (om S P n (D n * D n)).re * C ^ 2 := by
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hY n) 2) ?_
    have := om_re_nonneg S P n (hp n) (D n)
    rwa [hDh] at this
  exact (le_abs_self _).trans (Real.abs_le_sqrt (h1.trans h2))

theorem expTests (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (P : OperatorSequence S) (x : K → ℝ)
    (hP : projectionConcentrates S P x) :
    (∀ G H : AnalyticTestSeries S,
      (∀ y : K → ℝ, (∀ k, |y k| < S.radius k) →
        scalarEvaluation G y = scalarEvaluation H y) →
      ∃ z : ℂ,
        Tendsto (fun n => traceExpectation (projectionDensity P n) (operatorEvaluation G n))
          atTop (𝓝 z) ∧
        Tendsto (fun n => traceExpectation (projectionDensity P n) (operatorEvaluation H n))
          atTop (𝓝 z)) ∧
    ∀ (R : Finset K) (order : List K), order.Nodup →
      (∀ k, k ∈ order ↔ k ∈ R) → ∀ lambda : K → ℂ,
      Tendsto (fun n => traceExpectation (projectionDensity P n)
        (NormedSpace.exp (∑ k ∈ R,
          lambda k • (S.observable n k - (x k : ℂ) • 1)))) atTop (𝓝 (1 : ℂ)) ∧
      Tendsto (fun n => traceExpectation (projectionDensity P n)
        ((order.map (fun k => NormedSpace.exp
          (lambda k • (S.observable n k - (x k : ℂ) • 1)))).prod))
        atTop (𝓝 (1 : ℂ)) := by
  have hp : ∀ n, IsStarProjection (P n) := fun n => (hP.1 n).1
  have hne : ∀ n, P n ≠ 0 := fun n => (hP.1 n).2
  choose B hB0 hBr hBn using hS.2.2
  have hA : ∀ n k, ‖S.observable n k‖ ≤ B k := fun n k => hBn k n
  have hxk : ∀ k, |x k| ≤ B k := by
    intro k
    have h1 := joint S hS P x hP (wtest S [k])
    simp only [wtest_op, wtest_sc, wordOperator, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] at h1
    have h2 := (continuous_norm.tendsto _).comp h1
    have h3 : ‖(x k : ℂ)‖ ≤ B k := le_of_tendsto' h2 fun n =>
      (om_norm S P n (hp n) (hne n) _).trans (hA n k)
    simpa [Complex.norm_real] using h3
  refine ⟨fun G H hGH => ⟨scalarEvaluation G x, joint S hS P x hP G, ?_⟩, ?_⟩
  · rw [hGH x (fun k => (hxk k).trans_lt (hBr k))]
    exact joint S hS P x hP H
  intro R order _ _ lam
  let D : ∀ n, K → Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
    fun n k => S.observable n k - (x k : ℂ) • 1
  have hDn : ∀ n k, ‖D n k‖ ≤ B k + |x k| := by
    intro n k
    refine (norm_sub_le _ _).trans (add_le_add (hA n k) ?_)
    refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) norm_one_le
  have hsmD : ∀ n k, ‖lam k • D n k‖ ≤ ‖lam k‖ * (B k + |x k|) := fun n k =>
    (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hDn n k) (norm_nonneg _))
  have hc0 : ∀ k, 0 ≤ ‖lam k‖ * (B k + |x k|) := fun k =>
    mul_nonneg (norm_nonneg _) (add_nonneg (hB0 k) (abs_nonneg _))
  constructor
  · -- exponential sums
    set C0 := ∑ k ∈ R, ‖lam k‖ * (B k + |x k|)
    have hM : ∀ n, ‖∑ k ∈ R, lam k • D n k‖ ≤ C0 := fun n =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hsmD n k)
    choose Z hZ hZb using fun n => exp_sub_one (∑ k ∈ R, lam k • D n k) C0 (hM n)
    have e : ∀ n, om S P n (NormedSpace.exp (∑ k ∈ R, lam k • D n k)) =
        1 + ∑ k ∈ R, lam k * om S P n (D n k * Z n) := by
      intro n
      have : NormedSpace.exp (∑ k ∈ R, lam k • D n k) = 1 + ∑ k ∈ R, lam k • (D n k * Z n) := by
        rw [← sub_eq_iff_eq_add', hZ n, Finset.sum_mul]
        simp only [Matrix.smul_mul]
      rw [this, show (1 : Matrix _ _ ℂ) + ∑ k ∈ R, lam k • (D n k * Z n) =
        1 + (1 : ℂ) • ∑ k ∈ R, lam k • (D n k * Z n) by rw [one_smul],
        om_add_smul S P n (hp n), om_one S P n (hp n) (hne n), one_mul, om_sum S P n (hp n)]
    have hlim : Tendsto (fun n => 1 + ∑ k ∈ R, lam k * om S P n (D n k * Z n)) atTop
        (𝓝 (1 + ∑ k ∈ R, lam k * 0)) :=
      tendsto_const_nhds.add (tendsto_finset_sum _ fun k _ =>
        (small S hS P x hP k Z (ec C0) hZb).const_mul _)
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at hlim
    exact hlim.congr fun n => (e n).symm
  · -- ordered exponential products
    have hZ1 : ∀ n k, ∃ Z : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ,
        NormedSpace.exp (lam k • D n k) - 1 = (lam k • D n k) * Z ∧
          ‖Z‖ ≤ ec (‖lam k‖ * (B k + |x k|)) := fun n k => exp_sub_one _ _ (hsmD n k)
    choose Z hZ hZb using hZ1
    let β : K → ℝ := fun k => 1 +
      ‖lam k‖ * (B k + |x k|) * ec (‖lam k‖ * (B k + |x k|))
    have hEb : ∀ n k, ‖NormedSpace.exp (lam k • D n k)‖ ≤ β k := by
      intro n k
      have : NormedSpace.exp (lam k • D n k) = 1 + (lam k • D n k) * Z n k := by
        rw [← hZ n k]; abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      have h1 := norm_one_le (d := S.dimension n)
      have h2 := (Matrix.l2_opNorm_mul (lam k • D n k) (Z n k)).trans
        (mul_le_mul (hsmD n k) (hZb n k) (norm_nonneg _) (hc0 k))
      simp only [β]
      linarith
    have hβ : ∀ k, 0 ≤ β k := fun k => by
      simp only [β]
      have := mul_nonneg (hc0 k) (ec_nonneg _ (hc0 k))
      linarith
    have hprod : ∀ n (L : List K), ‖(L.map (fun k => NormedSpace.exp (lam k • D n k))).prod‖ ≤
        (L.map β).prod := by
      intro n L
      induction L with
      | nil => simpa using norm_one_le
      | cons k L ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hEb n k) ih (norm_nonneg _) (hβ k))
    have main : ∀ L : List K, Tendsto (fun n => om S P n
        ((L.map (fun k => NormedSpace.exp (lam k • D n k))).prod)) atTop (𝓝 1) := by
      intro L
      induction L with
      | nil =>
        simp only [List.map_nil, List.prod_nil]
        exact tendsto_const_nhds.congr fun n => (om_one S P n (hp n) (hne n)).symm
      | cons k L ih =>
        have e : ∀ n, om S P n (((k :: L).map (fun k => NormedSpace.exp (lam k • D n k))).prod) =
            om S P n (L.map (fun k => NormedSpace.exp (lam k • D n k))).prod +
              lam k * om S P n (D n k * (Z n k *
                (L.map (fun k => NormedSpace.exp (lam k • D n k))).prod)) := by
          intro n
          rw [← om_add_smul S P n (hp n)]
          congr 1
          simp only [List.map_cons, List.prod_cons]
          have : NormedSpace.exp (lam k • D n k) = 1 + (lam k • D n k) * Z n k := by
            rw [← hZ n k]; abel
          rw [this, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.mul_assoc]
        have hY : ∀ n, ‖Z n k * (L.map (fun k => NormedSpace.exp (lam k • D n k))).prod‖ ≤
            ec (‖lam k‖ * (B k + |x k|)) * (L.map β).prod := fun n =>
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hZb n k) (hprod n L) (norm_nonneg _)
            ((norm_nonneg _).trans (hZb n k)))
        have := ih.add ((small S hS P x hP k _ _ hY).const_mul (lam k))
        rw [mul_zero, add_zero] at this
        exact this.congr fun n => (e n).symm
    exact main order

end X6MQ


/-! (3.4)–(3.5): continuous tests concentrating about the moving mean of the scaled log
density imply the asymptotic equipartition property. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

section gen
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma st_psd (ρ : Matrix I I ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (Y : Matrix I I ℂ)
    (hY : Y.PosSemidef) : 0 ≤ (ρ * Y).trace.re := by
  obtain ⟨B, rfl⟩ := psd_fac Y hY
  have := (st_cs ρ hρ Bᴴ 1).2
  rwa [conjTranspose_conjTranspose] at this

lemma tr_real (ρ L : Matrix I I ℂ) (hρ : ρ.IsHermitian) (hL : L.IsHermitian) :
    (ρ * L).trace = (((ρ * L).trace.re : ℝ) : ℂ) := by
  have h : star (ρ * L).trace = (ρ * L).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hρ.eq, hL.eq, Matrix.trace_mul_comm]
  have him : (ρ * L).trace.im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  exact Complex.ext rfl (by simp [him])

end gen

variable {K : Type*}

theorem aep (S : MacroscopicSystem K) (rho : OperatorSequence S)
    (hrho : IsStateSequence rho)
    (hcontinuous : ∀ F : ℝ → ℂ, Continuous F →
      Tendsto (fun n => traceExpectation (rho n) (spectralFunction F (scaledLogDensity rho n)) -
        F ((traceExpectation (rho n) (scaledLogDensity rho n)).re)) atTop (𝓝 (0 : ℂ))) :
    asymptoticEquipartition rho := by
  intro δ hδ
  set L := scaledLogDensity rho with hLdef
  have hLh : ∀ n, (L n).IsHermitian := by
    intro n
    have h1 : IsSelfAdjoint (cfc Real.log (rho n)) := cfc_predicate _ _
    show ((volume n : ℂ)⁻¹ • cfc Real.log (rho n))ᴴ = _
    rw [conjTranspose_smul, show (cfc Real.log (rho n))ᴴ = cfc Real.log (rho n) from h1]
    congr 1
    simp [Complex.star_def]
  set m : ℕ → ℝ := fun n => (traceExpectation (rho n) (L n)).re with hmdef
  have hm : ∀ n, traceExpectation (rho n) (L n) = (m n : ℂ) := fun n =>
    tr_real _ _ (hrho n).1.isHermitian (hLh n)
  -- variance tends to zero
  have hvar0 := hcontinuous (fun z : ℝ => (((z - 0) ^ 2 : ℝ) : ℂ)) (by fun_prop)
  have e1 : ∀ n, spectralFunction (fun z : ℝ => (((z - 0) ^ 2 : ℝ) : ℂ)) (L n) = L n * L n := by
    intro n; rw [spec_sq _ (hLh n)]; simp
  set X : ∀ n, Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
    fun n => centeredLogDensity rho n with hXdef
  have hX : ∀ n, X n = L n - (m n : ℂ) • 1 := by
    intro n; change L n - traceExpectation (rho n) (L n) • 1 = _; rw [hm]
  have hXh : ∀ n, IsSelfAdjoint (X n) := by
    intro n
    rw [hX]
    refine IsSelfAdjoint.sub (hLh n) ?_
    exact IsSelfAdjoint.smul (show star ((m n : ℝ) : ℂ) = ((m n : ℝ) : ℂ) from
      Complex.conj_ofReal _) (IsSelfAdjoint.one _)
  have hvarE : ∀ n, traceExpectation (rho n) (X n * X n) =
      traceExpectation (rho n) (spectralFunction (fun z : ℝ => (((z - 0) ^ 2 : ℝ) : ℂ)) (L n)) -
        (fun z : ℝ => (((z - 0) ^ 2 : ℝ) : ℂ)) (m n) := by
    intro n
    rw [e1, hX]
    have hone : (rho n * 1).trace = 1 := by simp [(hrho n).2]
    have hmn := hm n
    simp only [traceExpectation] at hmn ⊢
    have hXX : (L n - (m n : ℂ) • 1) * (L n - (m n : ℂ) • 1) =
        L n * L n - (2 * (m n : ℂ)) • L n + ((m n : ℂ) ^ 2) • 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul]
      module
    rw [hXX]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, hmn, hone]
    push_cast; ring
  have hvar : Tendsto (fun n => (traceExpectation (rho n) (X n * X n)).re) atTop (𝓝 0) := by
    have := (Complex.continuous_re.tendsto 0).comp (hvar0.congr fun n => (hvarE n).symm)
    rw [Complex.zero_re] at this
    exact this
  -- window mass
  set W : ∀ n, Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
    fun n => spectralWindow (X n) (-δ) δ with hWdef
  set p : ℕ → ℝ := fun n => (traceExpectation (rho n) (W n)).re with hpdef
  have hfin : ∀ n, (spectrum ℝ (X n)).Finite := fun n => Matrix.finite_real_spectrum
  have hbounds : ∀ n, p n ≤ 1 ∧ 1 - δ⁻¹ ^ 2 * (traceExpectation (rho n) (X n * X n)).re ≤ p n := by
    intro n
    open scoped MatrixOrder in
    have hind : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (X n)) := fun f => (hfin n).continuousOn f
    have hW1 : W n ≤ 1 := by
      simp only [W, spectralWindow]
      rw [← cfc_const_one ℝ (X n) (hXh n)]
      refine cfc_mono (fun z _ => ?_) (hind _) (hind _)
      split_ifs <;> norm_num
    have hW2 : 1 - W n ≤ (δ⁻¹ ^ 2 : ℝ) • (X n * X n) := by
      simp only [W, spectralWindow]
      rw [← cfc_const_one ℝ (X n) (hXh n), ← cfc_sub _ _ (X n) (hind _) (hind _),
        ← sq, ← cfc_pow_id (R := ℝ) (X n) 2 (hXh n),
        ← cfc_const_mul (δ⁻¹ ^ 2 : ℝ) (fun z : ℝ => z ^ 2) (X n) (hind _)]
      refine cfc_mono (fun z _ => ?_) (hind _) (hind _)
      split_ifs with h
      · simp only [sub_self]; positivity
      · simp only [not_and_or, not_le] at h
        have : δ ^ 2 < z ^ 2 := by
          rcases h with h | h
          · nlinarith
          · nlinarith
        rw [sub_zero, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
        linarith
    have h1 := st_psd (rho n) (hrho n) _ (Matrix.le_iff.mp hW1)
    have h2 := st_psd (rho n) (hrho n) _ (Matrix.le_iff.mp hW2)
    have hone : (rho n * 1).trace.re = 1 := by simp [(hrho n).2]
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hone, Matrix.mul_smul,
      Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at h1 h2
    simp only [p, traceExpectation]
    constructor <;> linarith
  have hp1 : Tendsto p atTop (𝓝 1) := by
    have hlow : Tendsto (fun n => 1 - δ⁻¹ ^ 2 * (traceExpectation (rho n) (X n * X n)).re)
        atTop (𝓝 1) := by
      have := (hvar.const_mul (δ⁻¹ ^ 2))
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub this
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hbounds n).2) (fun n => (hbounds n).1)
  have hev : ∀ᶠ n in atTop, 0 < p n := hp1.eventually (lt_mem_nhds one_pos)
  have hlog : Tendsto (fun n => Real.log (p n) / (volume n : ℝ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => Real.log (p n)) atTop (𝓝 0) := by
      have := (Real.continuousAt_log one_ne_zero).tendsto.comp hp1
      rw [Real.log_one] at this
      exact this
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hl.norm)
    rw [norm_div, Real.norm_eq_abs (volume n : ℝ)]
    have hv : (1 : ℝ) ≤ |(volume n : ℝ)| := by
      rw [abs_of_nonneg (by positivity)]; simp [volume]
    exact div_le_self (norm_nonneg _) hv
  have := (continuous_coe_real_ereal.tendsto 0).comp hlog
  simp only [EReal.coe_zero] at this
  refine this.congr' ?_
  filter_upwards [hev] with n hn
  simp only [Function.comp, scaledLogMass]
  rw [if_pos (by simpa [p, W, X] using hn)]
  rfl

end X6MQ


noncomputable section

open Filter
open scoped Topology ComplexOrder Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Renew46.P24
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P10 (pauli)
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S)
    (hrho : IsStateSequence rho) (hpositive : ∀ n, (rho n).PosDef)
    (hcontinuous : ∀ F : ℝ → ℂ, Continuous F →
      Tendsto (fun n => traceExpectation (rho n) (spectralFunction F (scaledLogDensity rho n)) -
        F ((traceExpectation (rho n) (scaledLogDensity rho n)).re)) atTop (𝓝 (0 : ℂ))) :
    asymptoticEquipartition rho :=
  X6MQ.aep S rho hrho hcontinuous

end
