-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P24.entropyHierarchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:39:10.721864+00:00
-- url     : https://prove2.me/submissions/e71c73a4-b356-4a23-9224-52adfaa988cc

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
    (hS : IsMacroscopic S) (x : K → ℝ) :
    microcanonicalEntropy S x ≤ canonicalEntropy S x ∧
      canonicalEntropy S x ≤ meanCanonicalEntropy S x :=
  ⟨X6MQ.micro_le_canon S hS x, X6MQ.canon_le_mean S x⟩

end
