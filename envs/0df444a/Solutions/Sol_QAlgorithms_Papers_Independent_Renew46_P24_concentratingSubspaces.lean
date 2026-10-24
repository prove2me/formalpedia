-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P24.concentratingSubspaces
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T11:42:01.756098+00:00
-- url     : https://prove2.me/submissions/1b01fd10-4f5d-4cf2-8980-7d70d9cea188

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


/-! (3.3): differentiable generating functions give exponential concentration (Chernoff). -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

lemma exp_cfc {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • A) = cfc (fun z : ℝ => Real.exp (s * z)) A := by
  have hsa : IsSelfAdjoint A := hA
  have h1 : (s : ℂ) • A = s • A := Complex.coe_smul s A
  have h2 : IsSelfAdjoint (s • A) := (IsSelfAdjoint.all s).smul hsa
  rw [h1, ← CFC.real_exp_eq_normedSpace_exp h2]
  rw [← cfc_comp_smul s Real.exp A (Real.continuous_exp.continuousOn) hsa]
  rfl

lemma spec_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (z : ℝ)
    (hz : z ∈ spectrum ℝ A) : |z| ≤ ‖A‖ := by
  rw [hA.spectrum_real_eq_range_eigenvalues] at hz
  obtain ⟨j, rfl⟩ := hz
  exact eig_le A hA j

variable {K : Type*}

theorem gfc (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S)
    (hrho : IsStateSequence rho)
    (hexists : ∀ k, ∀ᶠ t : ℝ in 𝓝 0, ∃ z : ℝ,
      Tendsto (generatingSequence S rho k t) atTop (𝓝 z))
    (hdiff : ∀ k, DifferentiableAt ℝ (generatingFunction S rho k) 0) :
    exponentiallyConcentrates S rho
      (fun k => deriv (generatingFunction S rho k) 0) := by
  intro δ hδ k
  set Λ := generatingFunction S rho k with hΛ
  set x := deriv Λ 0 with hx
  obtain ⟨B, hB0, -, hBn⟩ := hS.2.2 k
  have hA : ∀ n, ‖S.observable n k‖ ≤ B := fun n => hBn n
  have hAh : ∀ n, (S.observable n k).IsHermitian := fun n => hS.2.1 n k
  have hsa : ∀ n, IsSelfAdjoint (S.observable n k) := fun n => hAh n
  have hfin : ∀ n, (spectrum ℝ (S.observable n k)).Finite := fun n => Matrix.finite_real_spectrum
  have hind : ∀ n (f : ℝ → ℝ), ContinuousOn f (spectrum ℝ (S.observable n k)) :=
    fun n f => (hfin n).continuousOn f
  set V : ℕ → ℝ := fun n => (volume n : ℝ) with hV
  have hV1 : ∀ n, 1 ≤ V n := fun n => by simp [V, volume]
  have hVpos : ∀ n, 0 < V n := fun n => lt_of_lt_of_le one_pos (hV1 n)
  -- the exponential moments
  let ω : ∀ n, Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ → ℝ :=
    fun n X => (traceExpectation (rho n) X).re
  have hωpsd : ∀ n Y, Y.PosSemidef → 0 ≤ ω n Y := fun n Y hY => st_psd _ (hrho n) Y hY
  have hω1 : ∀ n, ω n 1 = 1 := fun n => by simp [ω, traceExpectation, (hrho n).2]
  have hωlin : ∀ n (a b : ℝ) (X Y), ω n (a • X + b • Y) = a * ω n X + b * ω n Y := by
    intro n a b X Y
    simp only [ω, traceExpectation, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul,
      Matrix.trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hωsub : ∀ n X Y, ω n (X - Y) = ω n X - ω n Y := by
    intro n X Y
    simp [ω, traceExpectation, Matrix.mul_sub, Matrix.trace_sub]
  -- positivity of exponential moments
  have hpos : ∀ n (s : ℝ), Real.exp (-|s| * B) ≤ ω n (cfc (fun z : ℝ => Real.exp (s * z))
      (S.observable n k)) := by
    intro n s
    open scoped MatrixOrder in
    have hle : algebraMap ℝ _ (Real.exp (-|s| * B)) ≤
        cfc (fun z : ℝ => Real.exp (s * z)) (S.observable n k) := by
      rw [← cfc_const (Real.exp (-|s| * B)) (S.observable n k) (hsa n)]
      refine cfc_mono (fun z hz => ?_) (hind n _) (hind n _)
      have hz' := (spec_le _ (hAh n) z hz).trans (hA n)
      apply Real.exp_le_exp.mpr
      have : -(|s| * B) ≤ s * z := by
        have := abs_mul s z
        nlinarith [neg_abs_le (s * z), abs_nonneg s, abs_nonneg z]
      linarith
    have h1 := hωpsd n _ (Matrix.le_iff.mp hle)
    rw [hωsub, Algebra.algebraMap_eq_smul_one] at h1
    have h2 : ω n (Real.exp (-|s| * B) • (1 : Matrix _ _ ℂ)) = Real.exp (-|s| * B) := by
      have := hωlin n (Real.exp (-|s| * B)) 0 1 1
      rw [zero_smul, add_zero, hω1] at this
      simpa using this
    linarith
  -- generating sequence identity
  have hgen : ∀ n (t : ℝ), ω n (cfc (fun z : ℝ => Real.exp ((t * V n) * z)) (S.observable n k)) =
      Real.exp (V n * generatingSequence S rho k t n) := by
    intro n t
    have hp := (Real.exp_pos _).trans_le (hpos n (t * V n))
    have hc : ((t : ℂ) * (((volume n : ℕ) : ℝ) : ℂ)) = ((t * V n : ℝ) : ℂ) := by simp [V]
    have hg : generatingSequence S rho k t n = Real.log (ω n (cfc (fun z : ℝ =>
        Real.exp ((t * V n) * z)) (S.observable n k))) / V n := by
      simp only [generatingSequence, ω]
      rw [hc, exp_cfc _ (hAh n)]
    rw [hg, mul_div_cancel₀ _ (hVpos n).ne', Real.exp_log hp]
  -- Chernoff bound
  set W := fun n => spectralWindow (S.observable n k) (x - δ) (x + δ)
  have hchern : ∀ n (s : ℝ), 0 ≤ s →
      1 - ω n (W n) ≤ Real.exp (-s * (x + δ)) * ω n (cfc (fun z : ℝ => Real.exp (s * z))
        (S.observable n k)) + Real.exp (s * (x - δ)) *
          ω n (cfc (fun z : ℝ => Real.exp ((-s) * z)) (S.observable n k)) := by
    intro n s hs
    open scoped MatrixOrder in
    have hle : 1 - W n ≤ cfc (fun z : ℝ => Real.exp (-s * (x + δ)) * Real.exp (s * z) +
        Real.exp (s * (x - δ)) * Real.exp ((-s) * z)) (S.observable n k) := by
      simp only [W, spectralWindow]
      rw [← cfc_const_one ℝ (S.observable n k) (hsa n), ← cfc_sub _ _ _ (hind n _) (hind n _)]
      refine cfc_mono (fun z _ => ?_) (hind n _) (hind n _)
      have e1 : 0 ≤ Real.exp (-s * (x + δ)) * Real.exp (s * z) := by positivity
      have e2 : 0 ≤ Real.exp (s * (x - δ)) * Real.exp ((-s) * z) := by positivity
      split_ifs with h
      · simp only [sub_self]; linarith
      · simp only [not_and_or, not_le] at h
        rcases h with h | h
        · have : 1 ≤ Real.exp (s * (x - δ)) * Real.exp ((-s) * z) := by
            rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
          linarith
        · have : 1 ≤ Real.exp (-s * (x + δ)) * Real.exp (s * z) := by
            rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
          linarith
    have h1 := hωpsd n _ (Matrix.le_iff.mp hle)
    rw [hωsub, hωsub, hω1] at h1
    rw [cfc_add _ _ _ (hind n _) (hind n _), cfc_const_mul _ _ _ (hind n _),
      cfc_const_mul _ _ _ (hind n _), hωlin] at h1
    linarith
  -- the derivative at zero
  have hΛ0 : Λ 0 = 0 := by
    have hc : ∀ n, generatingSequence S rho k 0 n = 0 := by
      intro n
      simp [generatingSequence, traceExpectation, (hrho n).2]
    have : generatingSequence S rho k 0 = fun _ => 0 := funext hc
    simp only [hΛ, generatingFunction, this]
    exact tendsto_const_nhds.limUnder_eq
  have hder : HasDerivAt Λ x 0 := (hdiff k).hasDerivAt
  have hslope := hder.tendsto_slope_zero
  simp only [zero_add, hΛ0, sub_zero] at hslope
  have hev1 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u⁻¹ • Λ u - x| < δ / 2 ∧
      ∃ z : ℝ, Tendsto (generatingSequence S rho k u) atTop (𝓝 z) := by
    refine ((Metric.tendsto_nhds.mp hslope) (δ / 2) (by positivity)).mono ?_ |>.and
      (nhdsWithin_le_nhds (hexists k))
    intro u hu; simpa [Real.dist_eq] using hu
  have hev2 : ∀ᶠ u in 𝓝[>] (0 : ℝ), (|u⁻¹ • Λ u - x| < δ / 2 ∧
      ∃ z : ℝ, Tendsto (generatingSequence S rho k u) atTop (𝓝 z)) ∧
      (|(-u)⁻¹ • Λ (-u) - x| < δ / 2 ∧
      ∃ z : ℝ, Tendsto (generatingSequence S rho k (-u)) atTop (𝓝 z)) := by
    have hgt : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun u (hu : 0 < u) => hu.ne')
    have hneg : Tendsto (fun u : ℝ => -u) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_neg.tendsto (0 : ℝ)); simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
        exact neg_ne_zero.mpr hu.ne'
    exact Filter.Eventually.and (hgt hev1) (hneg.eventually hev1)
  obtain ⟨t, ⟨⟨ht1, ⟨z1, hz1⟩⟩, ⟨ht2, ⟨z2, hz2⟩⟩⟩, htpos⟩ :=
    (hev2.and self_mem_nhdsWithin).exists
  have htpos' : 0 < t := htpos
  have hL1 : Tendsto (generatingSequence S rho k t) atTop (𝓝 (Λ t)) :=
    tendsto_nhds_limUnder ⟨z1, hz1⟩
  have hL2 : Tendsto (generatingSequence S rho k (-t)) atTop (𝓝 (Λ (-t))) :=
    tendsto_nhds_limUnder ⟨z2, hz2⟩
  have ha : Λ t - t * (x + δ) < -(t * δ / 2) := by
    have h0 := (abs_lt.mp ht1).2
    rw [smul_eq_mul] at h0
    have h4 : t⁻¹ * Λ t < x + δ / 2 := by linarith
    rw [inv_mul_lt_iff₀ htpos'] at h4
    nlinarith
  have hb : Λ (-t) + t * (x - δ) < -(t * δ / 2) := by
    have h0 := (abs_lt.mp ht2).1
    rw [smul_eq_mul, inv_neg, neg_mul] at h0
    have h4 : t⁻¹ * Λ (-t) < -x + δ / 2 := by linarith
    rw [inv_mul_lt_iff₀ htpos'] at h4
    nlinarith
  have hE1 : ∀ᶠ n in atTop, generatingSequence S rho k t n - t * (x + δ) < -(t * δ / 4) := by
    have := (hL1.sub_const (t * (x + δ))).eventually (gt_mem_nhds
      (show Λ t - t * (x + δ) < -(t * δ / 4) by have := mul_pos htpos' hδ; linarith))
    exact this
  have hE2 : ∀ᶠ n in atTop, generatingSequence S rho k (-t) n + t * (x - δ) < -(t * δ / 4) := by
    have := (hL2.add_const (t * (x - δ))).eventually (gt_mem_nhds
      (show Λ (-t) + t * (x - δ) < -(t * δ / 4) by have := mul_pos htpos' hδ; linarith))
    exact this
  have hlarge : ∀ᶠ n in atTop, Real.log 2 ≤ V n * (t * δ / 8) := by
    have hVt : Tendsto V atTop atTop := by
      simp only [V, volume]; push_cast
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (hVt.atTop_mul_const (by positivity : 0 < t * δ / 8)).eventually_ge_atTop _
  refine ⟨t * δ / 8, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hE1.and (hE2.and hlarge))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN n hn.le
  have hc := hchern n (t * V n) (by positivity [hVpos n])
  rw [hgen n t] at hc
  have hneg' : (-(t * V n)) = (-t) * V n := by ring
  rw [hneg', hgen n (-t)] at hc
  have k1 : Real.exp (-t * V n * (x + δ)) * Real.exp (V n * generatingSequence S rho k t n) ≤
      Real.exp (-(V n * (t * δ / 4))) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hVpos n]
  have k2 : Real.exp (t * V n * (x - δ)) * Real.exp (V n * generatingSequence S rho k (-t) n) ≤
      Real.exp (-(V n * (t * δ / 4))) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hVpos n]
  have k3 : 2 * Real.exp (-(V n * (t * δ / 4))) ≤ Real.exp (-(t * δ / 8) * V n) := by
    have e : -(V n * (t * δ / 4)) = -(t * δ / 8) * V n + -(V n * (t * δ / 8)) := by ring
    rw [e, Real.exp_add]
    have : Real.exp (-(V n * (t * δ / 8))) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), one_div, inv_inv]
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ _ := Real.exp_le_exp.mpr h3
    nlinarith [Real.exp_pos (-(t * δ / 8) * V n)]
  show 1 - Real.exp (-(t * δ / 8) * V n) ≤ ω n (W n)
  linarith

end X6MQ


/-! Gibbs variational inequality `S(σ) + tr(σH) ≤ log tr e^H` and the entropy of Gibbs states. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

section gen
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma cfc_U (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix I I ℂ) *
      diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma tr_cfc (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_U A hA f, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    show ((hA.eigenvectorUnitary : Matrix I I ℂ))ᴴ * (hA.eigenvectorUnitary : Matrix I I ℂ) = 1
      from Unitary.coe_star_mul_self hA.eigenvectorUnitary, Matrix.one_mul, trace_diagonal]

lemma tr_cfc_re (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [tr_cfc A hA f, Complex.re_sum]; simp

lemma ent_eig (σ : Matrix I I ℂ) (hσ : σ.IsHermitian) :
    -(cfc (fun z : ℝ => z * Real.log z) σ).trace.re =
      -∑ i, hσ.eigenvalues i * Real.log (hσ.eigenvalues i) := by
  rw [tr_cfc_re σ hσ]

end gen

lemma class_gibbs {ι : Type*} [Fintype ι] (p a : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) :
    -∑ i, p i * Real.log (p i) + ∑ i, p i * a i ≤ Real.log (∑ i, Real.exp (a i)) := by
  have hne : Nonempty ι := by
    by_contra h; rw [not_nonempty_iff] at h; simp at hp1
  set Zs := ∑ i, Real.exp (a i)
  have hZ : 0 < Zs := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have key : ∀ i, p i * (a i - Real.log Zs - Real.log (p i)) ≤ Real.exp (a i) / Zs - p i := by
    intro i
    rcases (hp0 i).eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.exp (a i) / Zs / p i by positivity)
      rw [Real.log_div (by positivity) h.ne', Real.log_div (by positivity) hZ.ne',
        Real.log_exp] at h1
      have := mul_le_mul_of_nonneg_left h1 h.le
      have e2 : p i * (Real.exp (a i) / Zs / p i - 1) = Real.exp (a i) / Zs - p i := by
        field_simp
      linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, div_self hZ.ne', hp1, sub_self] at hs
  have e : ∑ i, p i * (a i - Real.log Zs - Real.log (p i)) =
      ∑ i, p i * a i - Real.log Zs * ∑ i, p i - ∑ i, p i * Real.log (p i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e, hp1] at hs
  linarith

section gen2
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma peierls (H : Matrix I I ℂ) (hH : H.IsHermitian) (U : Matrix I I ℂ) (hU : Uᴴ * U = 1) :
    ∑ i, Real.exp ((Uᴴ * H * U) i i).re ≤ (cfc Real.exp H).trace.re := by
  set W : Matrix I I ℂ := (hH.eigenvectorUnitary : Matrix I I ℂ)
  have hW1 : Wᴴ * W = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hW2 : W * Wᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  set M := Wᴴ * U
  have hM1 : Mᴴ * M = 1 := by
    simp only [M, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, hW2, Matrix.one_mul, hU]
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hM2 : M * Mᴴ = 1 := by
    simp only [M, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, hU2, Matrix.one_mul, hW1]
  set h := hH.eigenvalues
  have hHW : H = W * diagonal (fun j => ((h j : ℝ) : ℂ)) * Wᴴ := by
    have := cfc_U H hH id
    rw [cfc_id ℝ H] at this
    exact this
  have hent : ∀ i, ((Uᴴ * H * U) i i).re = ∑ j, Complex.normSq (M j i) * h j := by
    intro i
    have : Uᴴ * H * U = Mᴴ * diagonal (fun j => ((h j : ℝ) : ℂ)) * M := by
      rw [hHW]; simp only [M, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [this]
    simp only [Matrix.mul_apply, diagonal, of_apply, conjTranspose_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]; ring
  have hns : ∀ z : ℂ, (star z * z).re = Complex.normSq z := by
    intro z; simp [Complex.normSq_apply, Complex.mul_re]
  have hns' : ∀ z : ℂ, (z * star z).re = Complex.normSq z := by
    intro z; rw [mul_comm]; exact hns z
  have hw : ∀ i, ∑ j, Complex.normSq (M j i) = 1 := by
    intro i
    have := congrFun (congrFun hM1 i) i
    simp only [Matrix.mul_apply, conjTranspose_apply, one_apply_eq] at this
    have h2 := congrArg Complex.re this
    rw [Complex.re_sum] at h2
    simp only [hns, Complex.one_re] at h2
    exact h2
  have hw' : ∀ j, ∑ i, Complex.normSq (M j i) = 1 := by
    intro j
    have := congrFun (congrFun hM2 j) j
    simp only [Matrix.mul_apply, conjTranspose_apply, one_apply_eq] at this
    have h2 := congrArg Complex.re this
    rw [Complex.re_sum] at h2
    simp only [hns', Complex.one_re] at h2
    exact h2
  rw [tr_cfc_re H hH]
  calc ∑ i, Real.exp ((Uᴴ * H * U) i i).re
      = ∑ i, Real.exp (∑ j, Complex.normSq (M j i) * h j) := by simp only [hent]
    _ ≤ ∑ i, ∑ j, Complex.normSq (M j i) * Real.exp (h j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun j => Complex.normSq (M j i))
          (p := h) (fun j _ => Complex.normSq_nonneg _) (hw i) (fun j _ => Set.mem_univ _)
        simpa [smul_eq_mul] using this
    _ = ∑ j, Real.exp (h j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, hw' j, one_mul]

lemma gibbs_var (σ : Matrix I I ℂ) (hσ : QAlgorithms.IsDensityMatrix σ) (H : Matrix I I ℂ)
    (hH : H.IsHermitian) :
    -(cfc (fun z : ℝ => z * Real.log z) σ).trace.re + (σ * H).trace.re ≤
      Real.log (cfc Real.exp H).trace.re := by
  have hsh : σ.IsHermitian := hσ.1.isHermitian
  set U : Matrix I I ℂ := (hsh.eigenvectorUnitary : Matrix I I ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hsh.eigenvectorUnitary
  set p := hsh.eigenvalues
  have hp0 : ∀ i, 0 ≤ p i := hσ.1.eigenvalues_nonneg
  have hp1 : ∑ i, p i = 1 := by
    have := hsh.trace_eq_sum_eigenvalues
    rw [hσ.2] at this
    have h2 := congrArg Complex.re this
    simp at h2
    linarith
  have hσU : σ = U * diagonal (fun i => ((p i : ℝ) : ℂ)) * Uᴴ := by
    have := cfc_U σ hsh id
    rw [cfc_id ℝ σ] at this
    exact this
  have htr : (σ * H).trace.re = ∑ i, p i * ((Uᴴ * H * U) i i).re := by
    rw [hσU, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ H U]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, diagonal, of_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re, mul_comm]
  rw [ent_eig σ hsh, htr]
  have h1 := class_gibbs p (fun i => ((Uᴴ * H * U) i i).re) hp0 hp1
  have h2 := peierls H hH U hU1
  have hpos : 0 < ∑ i, Real.exp ((Uᴴ * H * U) i i).re := by
    have hne : Nonempty I := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hp1
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  exact h1.trans (Real.log_le_log hpos h2)

/-- entropy and trace data of a Gibbs state -/
lemma gibbs_data (H : Matrix I I ℂ) (hH : H.IsHermitian) [Nonempty I] :
    let Z := (cfc Real.exp H).trace.re
    0 < Z ∧ QAlgorithms.gibbsState H = cfc (fun z : ℝ => Z⁻¹ * Real.exp z) H ∧
    QAlgorithms.IsDensityMatrix (QAlgorithms.gibbsState H) ∧
    -(cfc (fun z : ℝ => z * Real.log z) (QAlgorithms.gibbsState H)).trace.re =
      Real.log Z - (QAlgorithms.gibbsState H * H).trace.re := by
  intro Z
  have hsa : IsSelfAdjoint H := hH
  have hexp : NormedSpace.exp H = cfc Real.exp H := (CFC.real_exp_eq_normedSpace_exp hsa).symm
  have hZ : 0 < Z := by
    simp only [Z]
    rw [tr_cfc_re H hH]
    have hne : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) hne
  have hZc : (cfc Real.exp H).trace = ((Z : ℝ) : ℂ) := by
    simp only [Z]; rw [tr_cfc H hH]
    apply Complex.ext <;> simp [Complex.re_sum, Complex.im_sum]
  have hfin : (spectrum ℝ H).Finite := Matrix.finite_real_spectrum
  have hg : QAlgorithms.gibbsState H = cfc (fun z : ℝ => Z⁻¹ * Real.exp z) H := by
    unfold QAlgorithms.gibbsState
    rw [hexp, hZc, cfc_const_mul Z⁻¹ Real.exp H (hfin.continuousOn _), ← Complex.ofReal_inv,
      Complex.coe_smul]
  have hsum : ∑ i, Z⁻¹ * Real.exp (hH.eigenvalues i) = 1 := by
    rw [← Finset.mul_sum, ← tr_cfc_re H hH Real.exp]; exact inv_mul_cancel₀ hZ.ne'
  refine ⟨hZ, hg, ⟨?_, ?_⟩, ?_⟩
  · rw [hg]
    open scoped MatrixOrder in
    exact Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun z _ => by positivity)
  · rw [hg]
    simp only [tr_cfc H hH]
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  · rw [hg, ← cfc_comp' (fun z : ℝ => z * Real.log z) (fun z : ℝ => Z⁻¹ * Real.exp z) H
      (Set.Finite.continuousOn (hfin.image _) _) (hfin.continuousOn _)]
    have hm : cfc (fun z : ℝ => Z⁻¹ * Real.exp z) H * H =
        cfc (fun z : ℝ => Z⁻¹ * Real.exp z * z) H := by
      have := cfc_mul (fun z : ℝ => Z⁻¹ * Real.exp z) (fun z : ℝ => z) H
        (hfin.continuousOn _) (hfin.continuousOn _)
      rw [cfc_id' ℝ H] at this
      exact this.symm
    rw [hm, tr_cfc_re H hH, tr_cfc_re H hH]
    have e : ∀ i, Z⁻¹ * Real.exp (hH.eigenvalues i) * Real.log (Z⁻¹ * Real.exp (hH.eigenvalues i)) =
        Z⁻¹ * Real.exp (hH.eigenvalues i) * hH.eigenvalues i -
          Real.log Z * (Z⁻¹ * Real.exp (hH.eigenvalues i)) := by
      intro i
      rw [Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
      ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring

end gen2

end X6MQ


/-! (2.14)–(2.15): Gibbs families are canonical macrostates; mean-canonical entropy equals
`limsup pressure − λ·x`. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

lemma ls (u c : ℕ → ℝ) (c0 : ℝ) (hc : Tendsto c atTop (𝓝 c0)) :
    limsup (fun n => ((u n - c n : ℝ) : EReal)) atTop =
      limsup (fun n => (u n : EReal)) atTop - (c0 : EReal) := by
  have hv : Tendsto (fun n => ((-c n : ℝ) : EReal)) atTop (𝓝 ((-c0 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hc.neg
  have hls : limsup (fun n => ((-c n : ℝ) : EReal)) atTop = ((-c0 : ℝ) : EReal) := hv.limsup_eq
  have hli : liminf (fun n => ((-c n : ℝ) : EReal)) atTop = ((-c0 : ℝ) : EReal) := hv.liminf_eq
  have hf : (fun n => ((u n - c n : ℝ) : EReal)) =
      (fun n => (u n : EReal)) + (fun n => ((-c n : ℝ) : EReal)) := by
    funext n; simp only [Pi.add_apply, sub_eq_add_neg, EReal.coe_add]
  rw [hf, sub_eq_add_neg, ← EReal.coe_neg]
  refine le_antisymm ?_ ?_
  · have := EReal.limsup_add_le (u := fun n => (u n : EReal)) (v := fun n => ((-c n : ℝ) : EReal))
      (f := atTop) (.inr (by rw [hls]; exact EReal.coe_ne_top _))
      (.inr (by rw [hls]; exact EReal.coe_ne_bot _))
    rwa [hls] at this
  · have := EReal.le_limsup_add (u := fun n => (u n : EReal)) (v := fun n => ((-c n : ℝ) : EReal))
      (f := atTop)
    rwa [hli] at this

theorem gibbsCan {q : ℕ} (S : MacroscopicSystem (Fin q))
    (hS : IsMacroscopic S) (lambda : Fin q → ℝ) (x : Fin q → ℝ)
    (hx : meanConcentrates S (gibbsFamily S lambda) x) :
    canonicalMacrostate S (gibbsFamily S lambda) x ∧
    meanCanonicalEntropy S x =
      Filter.limsup (fun n => (pressureSequence S lambda n : EReal)) atTop -
        ((∑ k, lambda k * x k : ℝ) : EReal) := by
  set H := fun n => gibbsExponent S lambda n with hHdef
  have hH : ∀ n, (H n).IsHermitian := by
    intro n
    simp only [H, gibbsExponent]
    refine IsSelfAdjoint.smul (by simp [Complex.star_def]) ?_
    refine isSelfAdjoint_sum _ fun k _ => ?_
    exact IsSelfAdjoint.smul (show star ((lambda k : ℝ) : ℂ) = ((lambda k : ℝ) : ℂ) from
      Complex.conj_ofReal _) (hS.2.1 n k)
  have hne : ∀ n, Nonempty (Fin (S.dimension n)) := fun n => ⟨⟨0, hS.1 n⟩⟩
  set V : ℕ → ℝ := fun n => (volume n : ℝ) with hV
  have hVpos : ∀ n, 0 < V n := fun n => by simp [V, volume]; positivity
  have hZ : ∀ n, gibbsPartitionTrace S lambda n = (cfc Real.exp (H n)).trace.re := by
    intro n
    simp only [gibbsPartitionTrace]
    rw [← CFC.real_exp_eq_normedSpace_exp (hH n : IsSelfAdjoint (H n))]
  have hTr : ∀ n (σ : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ),
      (σ * H n).trace.re = V n * ∑ k, lambda k * (traceExpectation σ (S.observable n k)).re := by
    intro n σ
    simp only [H, gibbsExponent, traceExpectation, Matrix.mul_smul, Matrix.mul_sum,
      Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    rw [show ((volume n : ℕ) : ℂ) = ((V n : ℝ) : ℂ) by simp [V], Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul]
  set c : ℕ → ℝ := fun n =>
    ∑ k, lambda k * (traceExpectation (gibbsFamily S lambda n) (S.observable n k)).re
  set c0 := ∑ k, lambda k * x k
  have hc : Tendsto c atTop (𝓝 c0) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_re.tendsto _).comp (hx k)).const_mul _
  set P := Filter.limsup (fun n => (pressureSequence S lambda n : EReal)) atTop
  have hstate : IsStateSequence (gibbsFamily S lambda) := fun n =>
    (haveI := hne n; gibbs_data (H n) (hH n)).2.2.1
  have hent : ∀ n, densityEntropyNats (gibbsFamily S lambda n) / (volume n : ℝ) =
      pressureSequence S lambda n - c n := by
    intro n
    haveI := hne n
    obtain ⟨hZp, -, -, he⟩ := gibbs_data (H n) (hH n)
    simp only [densityEntropyNats]
    change -(cfc (fun z : ℝ => z * Real.log z) (QAlgorithms.gibbsState (H n))).trace.re / V n = _
    rw [he, hTr, pressureSequence, hZ]
    change _ = Real.log (cfc Real.exp (H n)).trace.re / V n - c n
    field_simp [(hVpos n).ne']
    simp only [c, gibbsFamily]
    ring
  have hgib : entropyDensity (gibbsFamily S lambda) = P - (c0 : EReal) := by
    unfold entropyDensity
    have : (fun n => (densityEntropyNats (gibbsFamily S lambda n) : EReal) /
        (((volume n : ℕ) : ℝ) : EReal)) = fun n => ((pressureSequence S lambda n - c n : ℝ) : EReal) := by
      funext n; rw [← EReal.coe_div, hent]
    rw [this]
    exact ls _ c c0 hc
  have hup : ∀ σ : OperatorSequence S, IsStateSequence σ → meanConcentrates S σ x →
      entropyDensity σ ≤ P - (c0 : EReal) := by
    intro σ hσ hσx
    set c' : ℕ → ℝ := fun n => ∑ k, lambda k * (traceExpectation (σ n) (S.observable n k)).re
    have hc' : Tendsto c' atTop (𝓝 c0) := by
      refine tendsto_finsetSum _ fun k _ => ?_
      exact ((Complex.continuous_re.tendsto _).comp (hσx k)).const_mul _
    rw [← ls _ c' c0 hc']
    unfold entropyDensity
    refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    have hv := gibbs_var (σ n) (hσ n) (H n) (hH n)
    rw [hTr] at hv
    simp only [densityEntropyNats]
    refine EReal.coe_le_coe_iff.mpr ?_
    rw [pressureSequence, hZ]
    have hVn : (0 : ℝ) < (volume n : ℝ) := hVpos n
    rw [← div_eq_mul_inv, div_le_iff₀ hVn, sub_mul, div_mul_cancel₀ _ hVn.ne']
    simp only [c']
    have e : V n = (volume n : ℝ) := rfl
    rw [e] at hv
    linarith
  have hmean : meanCanonicalEntropy S x = P - (c0 : EReal) := by
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro h ⟨σ, hσ, hσx, rfl⟩
      exact hup σ hσ hσx
    · rw [← hgib]
      exact le_sSup ⟨_, hstate, hx, rfl⟩
  exact ⟨⟨hstate, hx, hgib.trans hmean.symm⟩, hmean⟩

end X6MQ


/-! (3.6): locally existing, continuously differentiable pressure implies the AEP for the
Gibbs family. Proof: apply `gfc` to the one-observable system `B_n = Σ λ_k A_{n,k}`. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

attribute [local instance] Classical.propDecidable Classical.decEq

variable {q : ℕ}

/-- the observable `Σ λ_k A_k` -/
def Bop (S : MacroscopicSystem (Fin q)) (lam : Fin q → ℝ) (n : ℕ) :
    Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ :=
  ∑ k, (lam k : ℂ) • S.observable n k

lemma Bop_herm (S : MacroscopicSystem (Fin q)) (hS : IsMacroscopic S) (lam : Fin q → ℝ) (n : ℕ) :
    (Bop S lam n).IsHermitian := by
  refine isSelfAdjoint_sum _ fun k _ => ?_
  exact IsSelfAdjoint.smul (show star ((lam k : ℝ) : ℂ) = ((lam k : ℝ) : ℂ) from
    Complex.conj_ofReal _) (hS.2.1 n k)

lemma Bop_smul (S : MacroscopicSystem (Fin q)) (lam : Fin q → ℝ) (n : ℕ) (c : ℝ) :
    Bop S (c • lam) n = c • Bop S lam n := by
  simp only [Bop, Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.coe_smul, smul_smul]; push_cast; rfl

lemma gexp (S : MacroscopicSystem (Fin q)) (lam : Fin q → ℝ) (n : ℕ) :
    gibbsExponent S lam n = ((volume n : ℕ) : ℝ) • Bop S lam n := by
  simp only [gibbsExponent, Bop]
  rw [← Complex.coe_smul]; push_cast; rfl

lemma exp_cfc_r {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    NormedSpace.exp (s • A) = cfc (fun z : ℝ => Real.exp (s * z)) A := by
  rw [← Complex.coe_smul]; exact exp_cfc A hA s

/-- spectral data of the Gibbs family in the eigenbasis of `B_n`. -/
lemma gdata (S : MacroscopicSystem (Fin q)) (hS : IsMacroscopic S) (lam : Fin q → ℝ) (n : ℕ) :
    let B := Bop S lam n
    let hB := Bop_herm S hS lam n
    let V : ℝ := ((volume n : ℕ) : ℝ)
    let Zn : ℝ := ∑ i, Real.exp (V * hB.eigenvalues i)
    0 < Zn ∧
    (∀ c : ℝ, gibbsPartitionTrace S (c • lam) n = ∑ i, Real.exp (c * V * hB.eigenvalues i)) ∧
    gibbsFamily S lam n = cfc (fun z : ℝ => Zn⁻¹ * Real.exp (V * z)) B ∧
    (∀ f : ℝ → ℝ, (traceExpectation (gibbsFamily S lam n) (cfc f B)).re =
      ∑ i, Zn⁻¹ * Real.exp (V * hB.eigenvalues i) * f (hB.eigenvalues i)) ∧
    (∀ f : ℝ → ℝ, traceExpectation (gibbsFamily S lam n) (cfc f B) =
      ((∑ i, Zn⁻¹ * Real.exp (V * hB.eigenvalues i) * f (hB.eigenvalues i) : ℝ) : ℂ)) := by
  intro B hB V Zn
  have hne : Nonempty (Fin (S.dimension n)) := ⟨⟨0, hS.1 n⟩⟩
  have hfin : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum
  have hZ : 0 < Zn := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hexpc : ∀ c : ℝ, NormedSpace.exp (gibbsExponent S (c • lam) n) =
      cfc (fun z : ℝ => Real.exp (c * V * z)) B := by
    intro c
    rw [gexp, Bop_smul, smul_smul, exp_cfc_r _ hB]
    simp only [V, B]; congr 1; funext z; ring_nf
  have hZc : ∀ c : ℝ, gibbsPartitionTrace S (c • lam) n = ∑ i, Real.exp (c * V * hB.eigenvalues i) := by
    intro c; simp only [gibbsPartitionTrace]; rw [hexpc, tr_cfc_re B hB]
  have hρ : gibbsFamily S lam n = cfc (fun z : ℝ => Zn⁻¹ * Real.exp (V * z)) B := by
    have h1 : gibbsExponent S lam n = gibbsExponent S ((1 : ℝ) • lam) n := by rw [one_smul]
    simp only [gibbsFamily, QAlgorithms.gibbsState]
    rw [h1, hexpc 1, tr_cfc B hB, cfc_const_mul Zn⁻¹ _ B (hfin.continuousOn _)]
    have : (∑ i, (((fun z : ℝ => Real.exp (1 * V * z)) (hB.eigenvalues i) : ℝ) : ℂ)) =
        ((Zn : ℝ) : ℂ) := by
      simp only [Zn, one_mul]; push_cast; rfl
    rw [this, ← Complex.ofReal_inv, Complex.coe_smul]
    congr 1; congr 1; funext z; rw [one_mul]
  have hom : ∀ f : ℝ → ℝ, traceExpectation (gibbsFamily S lam n) (cfc f B) =
      ((∑ i, Zn⁻¹ * Real.exp (V * hB.eigenvalues i) * f (hB.eigenvalues i) : ℝ) : ℂ) := by
    intro f
    simp only [traceExpectation]
    rw [hρ, ← cfc_mul _ _ B (hfin.continuousOn _) (hfin.continuousOn _), tr_cfc B hB]
    push_cast; rfl
  refine ⟨hZ, hZc, hρ, fun f => ?_, hom⟩
  rw [hom f, Complex.ofReal_re]

/-- the auxiliary one-observable system -/
def Saux (S : MacroscopicSystem (Fin q)) (lam : Fin q → ℝ) (R : ℝ) : MacroscopicSystem Unit where
  dimension := S.dimension
  observable n _ := Bop S lam n
  radius _ := R

lemma slm_of_tendsto_one (p : ℕ → ℝ) (hp1 : Tendsto p atTop (𝓝 1)) :
    Tendsto (fun n => scaledLogMass n (p n)) atTop (𝓝 (0 : EReal)) := by
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
  rw [if_pos hn]
  rfl

theorem pressAEP (S : MacroscopicSystem (Fin q))
    (hS : IsMacroscopic S) (lambda : Fin q → ℝ)
    (hexists : ∀ᶠ theta : (Fin q → ℝ) in 𝓝 lambda, ∃ z : ℝ,
      Tendsto (pressureSequence S theta) atTop (𝓝 z))
    (hdiff : ContDiffAt ℝ 1 (pressure S) lambda) :
    asymptoticEquipartition (gibbsFamily S lambda) := by
  choose Bk hBk0 hBkr hBkn using hS.2.2
  set R0 := ∑ k, |lambda k| * Bk k with hR0
  have hR0nn : 0 ≤ R0 := Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (hBk0 k)
  have hBn : ∀ n, ‖Bop S lambda n‖ ≤ R0 := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hBkn k n) (abs_nonneg _)
  set S' := Saux S lambda (R0 + 1)
  have hS' : IsMacroscopic S' := by
    refine ⟨hS.1, fun n _ => Bop_herm S hS lambda n, fun _ => ⟨R0, hR0nn, by simp [S', Saux],
      fun n => hBn n⟩⟩
  set ρ := gibbsFamily S lambda
  have hρ : IsStateSequence ρ := fun n => by
    haveI : Nonempty (Fin (S.dimension n)) := ⟨⟨0, hS.1 n⟩⟩
    have hH : (gibbsExponent S lambda n).IsHermitian := by
      rw [gexp]
      exact (IsSelfAdjoint.all ((volume n : ℕ) : ℝ)).smul (Bop_herm S hS lambda n)
    exact (gibbs_data (gibbsExponent S lambda n) hH).2.2.1
  -- generating sequence of the auxiliary system
  set g : ℝ → (Fin q → ℝ) := fun t => (1 + t) • lambda
  have hgen : ∀ t n, generatingSequence S' ρ Unit.unit t n =
      pressureSequence S (g t) n - pressureSequence S lambda n := by
    intro t n
    obtain ⟨hZ, hZc, -, hom, -⟩ := gdata S hS lambda n
    set hB := Bop_herm S hS lambda n
    set V : ℝ := ((volume n : ℕ) : ℝ)
    have hV : 0 < V := by simp [V, volume]; positivity
    have h1 : ((t : ℂ) * ((V : ℝ) : ℂ)) • (S'.observable n Unit.unit) = (t * V) • Bop S lambda n := by
      rw [← Complex.coe_smul]; push_cast; rfl
    simp only [generatingSequence, pressureSequence]
    rw [h1]
    erw [exp_cfc_r _ hB, hom]
    have e2 : gibbsPartitionTrace S (g t) n = ∑ i, Real.exp ((1 + t) * V * hB.eigenvalues i) :=
      hZc (1 + t)
    have e3 : gibbsPartitionTrace S lambda n = ∑ i, Real.exp (1 * V * hB.eigenvalues i) := by
      rw [← hZc 1, one_smul]
    rw [e2, e3]
    simp only [one_mul]
    have e4 : ∑ i, (∑ j, Real.exp (V * hB.eigenvalues j))⁻¹ * Real.exp (V * hB.eigenvalues i) *
        Real.exp (t * V * hB.eigenvalues i) = (∑ j, Real.exp (V * hB.eigenvalues j))⁻¹ *
        ∑ i, Real.exp ((1 + t) * V * hB.eigenvalues i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    have hpos : 0 < ∑ i, Real.exp ((1 + t) * V * hB.eigenvalues i) := by
      haveI : Nonempty (Fin (S.dimension n)) := ⟨⟨0, hS.1 n⟩⟩
      exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    rw [e4, Real.log_mul (inv_ne_zero hZ.ne') hpos.ne', Real.log_inv]
    ring
  -- hypotheses for `gfc`
  have hg0 : g 0 = lambda := by simp [g]
  have hgc : Tendsto g (𝓝 0) (𝓝 lambda) := by
    have : Continuous g := (continuous_const.add continuous_id).smul continuous_const
    have h := this.tendsto 0
    rwa [hg0] at h
  obtain ⟨zl, hzl⟩ := hexists.self_of_nhds
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∃ z, Tendsto (pressureSequence S (g t)) atTop (𝓝 z) :=
    hgc.eventually hexists
  have hex' : ∀ k : Unit, ∀ᶠ t : ℝ in 𝓝 0, ∃ z : ℝ,
      Tendsto (generatingSequence S' ρ k t) atTop (𝓝 z) := by
    intro k
    filter_upwards [hev] with t ⟨z, hz⟩
    exact ⟨z - zl, (hz.sub hzl).congr fun n => (hgen t n).symm⟩
  set phiF := fun t => pressure S (g t) - pressure S lambda
  have heq : generatingFunction S' ρ Unit.unit =ᶠ[𝓝 0] phiF := by
    filter_upwards [hev] with t ⟨z, hz⟩
    have h1 : Tendsto (generatingSequence S' ρ Unit.unit t) atTop (𝓝 (z - zl)) :=
      (hz.sub hzl).congr fun n => (hgen t n).symm
    simp only [generatingFunction, phiF, pressure]
    rw [h1.limUnder_eq, hz.limUnder_eq, hzl.limUnder_eq]
  have hphiFd : DifferentiableAt ℝ phiF 0 := by
    have hp : DifferentiableAt ℝ (pressure S) (g 0) := by
      rw [hg0]; exact hdiff.differentiableAt (by norm_num)
    have hgd : DifferentiableAt ℝ g 0 :=
      ((differentiableAt_const _).add differentiableAt_id).smul_const lambda
    exact (hp.comp 0 hgd).sub_const _
  have hdiff' : ∀ k : Unit, DifferentiableAt ℝ (generatingFunction S' ρ k) 0 := by
    intro k; cases k; exact hphiFd.congr_of_eventuallyEq heq
  have hconc := gfc S' hS' ρ hρ hex' hdiff'
  set m := deriv (generatingFunction S' ρ Unit.unit) 0
  -- spectral data
  have hfinB : ∀ n, (spectrum ℝ (Bop S lambda n)).Finite := fun n => Matrix.finite_real_spectrum
  set w : ∀ n, Fin (S.dimension n) → ℝ := fun n i =>
    (∑ j, Real.exp (((volume n : ℕ) : ℝ) * (Bop_herm S hS lambda n).eigenvalues j))⁻¹ *
      Real.exp (((volume n : ℕ) : ℝ) * (Bop_herm S hS lambda n).eigenvalues i)
  set lam : ∀ n, Fin (S.dimension n) → ℝ := fun n i => (Bop_herm S hS lambda n).eigenvalues i
  have hw0 : ∀ n i, 0 ≤ w n i := fun n i => by
    obtain ⟨hZ, -⟩ := gdata S hS lambda n
    exact mul_nonneg (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le
  have hw1 : ∀ n, ∑ i, w n i = 1 := fun n => by
    obtain ⟨hZ, -⟩ := gdata S hS lambda n
    simp only [w]; rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hZ.ne'
  have hom : ∀ n (f : ℝ → ℝ), (traceExpectation (ρ n) (cfc f (Bop S lambda n))).re =
      ∑ i, w n i * f (lam n i) := fun n f => (gdata S hS lambda n).2.2.2.1 f
  have hlam : ∀ n i, |lam n i| ≤ R0 := fun n i =>
    (eig_le _ (Bop_herm S hS lambda n) i).trans (hBn n)
  set b : ℕ → ℝ := fun n => ∑ i, w n i * lam n i
  -- the auxiliary window
  have hwin : ∀ n (η : ℝ), (traceExpectation (ρ n) (spectralWindow (S'.observable n Unit.unit)
      (m - η) (m + η))).re = ∑ i, w n i * (if m - η ≤ lam n i ∧ lam n i ≤ m + η then 1 else 0) := by
    intro n η
    exact hom n _
  -- the moving mean converges
  have hb : Tendsto b atTop (𝓝 m) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨C, hC, n0, hn0⟩ := hconc (ε / 2) (by positivity) Unit.unit
    set K := R0 + |m| + 1
    have hK : 0 < K := by positivity
    have hsmall : Tendsto (fun n : ℕ => K * Real.exp (-C * (volume n : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => -C * (volume n : ℝ)) atTop atBot := by
        have : Tendsto (fun n : ℕ => (volume n : ℝ)) atTop atTop := by
          simp only [volume]; push_cast
          exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        exact this.const_mul_atTop_of_neg (by linarith)
      have := (Real.tendsto_exp_atBot.comp h1).const_mul K
      simpa using this
    obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.mp hsmall (ε / 2) (by positivity)
    refine ⟨max (n0 + 1) n1, fun n hn => ?_⟩
    have hA := hn0 n (by omega)
    have hB := hn1 n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hB
    replace hA := hA.trans_eq (hwin n (ε / 2))
    have hdev : |b n - m| ≤ ε / 2 + K * (1 - ∑ i, w n i *
        (if m - ε / 2 ≤ lam n i ∧ lam n i ≤ m + ε / 2 then 1 else 0)) := by
      have e : b n - m = ∑ i, w n i * (lam n i - m) := by
        simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      rw [e]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have e2 : ε / 2 + K * (1 - ∑ i, w n i *
          (if m - ε / 2 ≤ lam n i ∧ lam n i ≤ m + ε / 2 then 1 else 0)) =
          ∑ i, w n i * (ε / 2 + K * (1 - (if m - ε / 2 ≤ lam n i ∧ lam n i ≤ m + ε / 2
            then 1 else 0))) := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hw1, mul_one, one_mul, Finset.mul_sum]
        congr 1
        refine congrArg (K - ·) (Finset.sum_congr rfl fun i _ => by ring)
      rw [e2]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hw0 n i)]
      refine mul_le_mul_of_nonneg_left ?_ (hw0 n i)
      split_ifs with h
      · simp only [sub_self, mul_zero, add_zero]
        exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
      · simp only [sub_zero, mul_one]
        have := hlam n i
        have : |lam n i - m| ≤ |lam n i| + |m| := by
          have := abs_sub (lam n i) m; linarith
        linarith [abs_nonneg (lam n i), (by positivity : 0 ≤ ε / 2)]
    rw [Real.dist_eq]
    calc |b n - m| ≤ ε / 2 + K * (1 - ∑ i, w n i *
        (if m - ε / 2 ≤ lam n i ∧ lam n i ≤ m + ε / 2 then 1 else 0)) := hdev
      _ ≤ ε / 2 + K * Real.exp (-C * (volume n : ℝ)) := by
          gcongr; linarith
      _ < ε := by linarith
  -- the centred log density
  have hcent : ∀ n, centeredLogDensity ρ n = cfc (fun z => z - b n) (Bop S lambda n) := by
    intro n
    obtain ⟨hZ, -, hρn, -, homc⟩ := gdata S hS lambda n
    have hfin := hfinB n
    have hV : 0 < ((volume n : ℕ) : ℝ) := by simp [volume]; positivity
    set c := ((volume n : ℕ) : ℝ)⁻¹ * Real.log (∑ i, Real.exp (((volume n : ℕ) : ℝ) *
      (Bop_herm S hS lambda n).eigenvalues i)) with hcdef
    have hsl : scaledLogDensity ρ n = cfc (fun z => z - c) (Bop S lambda n) := by
      simp only [scaledLogDensity]
      rw [show ρ n = _ from hρn, ← cfc_comp' Real.log _ (Bop S lambda n)
        ((hfin.image _).continuousOn _) (hfin.continuousOn _)
        (show IsSelfAdjoint (Bop S lambda n) from Bop_herm S hS lambda n)]
      rw [show ((volume n : ℕ) : ℂ)⁻¹ = ((((volume n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.coe_smul, ← cfc_const_mul _ _ (Bop S lambda n) (hfin.continuousOn _)]
      refine cfc_congr fun z _ => ?_
      simp only [Function.comp, hcdef]
      rw [Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
      field_simp
      ring
    have hmean : traceExpectation (ρ n) (scaledLogDensity ρ n) = (((b n - c) : ℝ) : ℂ) := by
      rw [hsl, homc]
      congr 1
      have := hw1 n
      simp only [w, lam] at this
      simp only [b, w, lam, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, this, one_mul]
    simp only [centeredLogDensity]
    rw [hmean, hsl]
    have e : cfc (fun z => z - b n) (Bop S lambda n) =
        cfc (fun z => (z - c) - (b n - c)) (Bop S lambda n) := cfc_congr fun z _ => by ring
    have hk : cfc (fun _ : ℝ => b n - c) (Bop S lambda n) = ((b n - c : ℝ) : ℂ) • 1 := by
      rw [cfc_const (b n - c) (Bop S lambda n)
        (show IsSelfAdjoint (Bop S lambda n) from Bop_herm S hS lambda n),
        Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    rw [e, cfc_sub (fun z => z - c) (fun _ => b n - c) _ (hfin.continuousOn _)
      (hfin.continuousOn _)]
    erw [hk]
  intro δ hδ
  set pm : ℕ → ℝ := fun n =>
    (traceExpectation (ρ n) (spectralWindow (centeredLogDensity ρ n) (-δ) δ)).re
  have hpm : ∀ n, pm n = ∑ i, w n i *
      (if -δ ≤ lam n i - b n ∧ lam n i - b n ≤ δ then 1 else 0) := by
    intro n
    simp only [pm, spectralWindow]
    rw [hcent n, ← cfc_comp' _ _ _ (((hfinB n).image _).continuousOn _)
      ((hfinB n).continuousOn _)
      (show IsSelfAdjoint (Bop S lambda n) from Bop_herm S hS lambda n)]
    exact hom n _
  show Tendsto (fun n => scaledLogMass n (pm n)) atTop (𝓝 0)
  apply slm_of_tendsto_one
  have hle1 : ∀ n, pm n ≤ 1 := by
    intro n
    rw [hpm]
    calc _ ≤ ∑ i, w n i := Finset.sum_le_sum fun i _ =>
          mul_le_of_le_one_right (hw0 n i) (by split_ifs <;> norm_num)
      _ = 1 := hw1 n
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC, n0, hn0⟩ := hconc (δ / 2) (by positivity) Unit.unit
  have hsmall : Tendsto (fun n : ℕ => Real.exp (-C * (volume n : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => -C * (volume n : ℝ)) atTop atBot := by
      have : Tendsto (fun n : ℕ => (volume n : ℝ)) atTop atTop := by
        simp only [volume]; push_cast
        exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact this.const_mul_atTop_of_neg (by linarith)
    exact Real.tendsto_exp_atBot.comp h1
  obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.mp hsmall ε hε
  obtain ⟨n2, hn2⟩ := Metric.tendsto_atTop.mp hb (δ / 2) (by positivity)
  refine ⟨max (max (n0 + 1) n1) n2, fun n hn => ?_⟩
  have hA := (hn0 n (by omega)).trans_eq (hwin n (δ / 2))
  have hE := hn1 n (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] at hE
  have hbm := hn2 n (by omega)
  rw [Real.dist_eq] at hbm
  have hlow : ∑ i, w n i * (if m - δ / 2 ≤ lam n i ∧ lam n i ≤ m + δ / 2 then 1 else 0) ≤
      pm n := by
    rw [hpm]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw0 n i)
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2
      have := abs_lt.mp hbm
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    · norm_num
    · exact le_rfl
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [hle1 n]

end X6MQ


/-! Lemma 3.2: exponentially concentrating subspaces realizing the entropy. -/

noncomputable section

open Filter Matrix
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

namespace X6MQ

open QAlgorithms.Papers.Independent.Renew46.P24

attribute [local instance] Classical.propDecidable Classical.decEq

section gen
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma om_cfc_self (ρ : Matrix I I ℂ) (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    (ρ * cfc f ρ).trace.re = ∑ i, hρ.eigenvalues i * f (hρ.eigenvalues i) := by
  have hfin : (spectrum ℝ ρ).Finite := Matrix.finite_real_spectrum
  have hsa : IsSelfAdjoint ρ := hρ
  conv_lhs => rw [show ρ * cfc f ρ = cfc (fun z => z * f z) ρ by
    rw [cfc_mul (fun z => z) f ρ (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ ρ hsa]]
  rw [tr_cfc_re ρ hρ]

lemma tr_psd_mul (A Y : Matrix I I ℂ) (hA : A.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (A * Y).trace.re := by
  obtain ⟨B, rfl⟩ := psd_fac A hA
  have h1 : (Bᴴ * B * Y).trace = (B * Y * Bᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h1]
  have := (hY.mul_mul_conjTranspose_same B).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma proj_cfc (A : Matrix I I ℂ) (hA : IsSelfAdjoint A) (χ : ℝ → ℝ)
    (hχ : ∀ z, χ z = 0 ∨ χ z = 1) : IsStarProjection (cfc χ A) := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  refine ⟨?_, cfc_predicate _ _⟩
  show cfc χ A * cfc χ A = cfc χ A
  rw [← cfc_mul χ χ A (hfin.continuousOn _) (hfin.continuousOn _)]
  refine cfc_congr fun z _ => ?_
  rcases hχ z with h | h <;> simp [h]

end gen

variable {K : Type*}

theorem csub (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hrho : IsStateSequence rho) (hpositive : ∀ n, (rho n).PosDef)
    (hexponential : exponentiallyConcentrates S rho x)
    (hequipartition : asymptoticEquipartition rho) :
    ∃ P : OperatorSequence S, IsProjectionSequence P ∧
      exponentiallyConcentrates S (projectionDensity P) x ∧
      Tendsto (fun n => (Real.log (P n).trace.re - densityEntropyNats (rho n)) /
        (volume n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  set V : ℕ → ℝ := fun n => ((volume n : ℕ) : ℝ) with hVdef
  have hV1 : ∀ n, 1 ≤ V n := fun n => by simp [V, volume]
  have hVpos : ∀ n, 0 < V n := fun n => lt_of_lt_of_le one_pos (hV1 n)
  have hh : ∀ n, (rho n).IsHermitian := fun n => (hrho n).1.isHermitian
  have hsa : ∀ n, IsSelfAdjoint (rho n) := fun n => hh n
  have hfin : ∀ n, (spectrum ℝ (rho n)).Finite := fun n => Matrix.finite_real_spectrum
  set r : ∀ n, Fin (S.dimension n) → ℝ := fun n i => (hh n).eigenvalues i
  have hr0 : ∀ n i, 0 < r n i := fun n i => (hpositive n).eigenvalues_pos i
  have hr1 : ∀ n, ∑ i, r n i = 1 := by
    intro n
    have := (hh n).trace_eq_sum_eigenvalues
    rw [(hrho n).2] at this
    have h2 := congrArg Complex.re this
    simp at h2
    simp only [r]; linarith
  set Sn : ℕ → ℝ := fun n => densityEntropyNats (rho n)
  have hSn : ∀ n, Sn n = -∑ i, r n i * Real.log (r n i) := fun n => by
    simp only [Sn, densityEntropyNats]; rw [tr_cfc_re _ (hh n)]
  -- the windows
  let χ : ℝ → ℕ → ℝ → ℝ := fun δ n z =>
    if -δ ≤ (V n)⁻¹ * Real.log z + Sn n / V n ∧ (V n)⁻¹ * Real.log z + Sn n / V n ≤ δ then 1 else 0
  have hχ01 : ∀ δ n z, χ δ n z = 0 ∨ χ δ n z = 1 := fun δ n z => by
    simp only [χ]; split_ifs <;> simp
  set mass : ℕ → ℝ → ℝ := fun n δ => ∑ i, r n i * χ δ n (r n i)
  have hwin : ∀ n δ, spectralWindow (centeredLogDensity rho n) (-δ) δ = cfc (χ δ n) (rho n) := by
    intro n δ
    have hlog : scaledLogDensity rho n = cfc (fun z => (V n)⁻¹ * Real.log z) (rho n) := by
      simp only [scaledLogDensity]
      rw [show ((volume n : ℕ) : ℂ)⁻¹ = (((V n)⁻¹ : ℝ) : ℂ) by simp [V], Complex.coe_smul,
        ← cfc_const_mul _ _ (rho n) ((hfin n).continuousOn _)]
    have hmean : traceExpectation (rho n) (scaledLogDensity rho n) =
        ((-(Sn n / V n) : ℝ) : ℂ) := by
      rw [hlog]
      apply Complex.ext
      · simp only [traceExpectation]
        rw [om_cfc_self _ (hh n), Complex.ofReal_re, hSn]
        simp only [r]
        rw [neg_div, neg_neg, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => by ring
      · simp only [traceExpectation, Complex.ofReal_im]
        have hL : (cfc (fun z => (V n)⁻¹ * Real.log z) (rho n)).IsHermitian := cfc_predicate _ _
        rw [tr_real _ _ (hh n) hL, Complex.ofReal_im]
    have hcent : centeredLogDensity rho n =
        cfc (fun z => (V n)⁻¹ * Real.log z + Sn n / V n) (rho n) := by
      simp only [centeredLogDensity]
      rw [hmean, hlog, cfc_add (a := rho n) (f := fun z => (V n)⁻¹ * Real.log z)
        (g := fun _ => Sn n / V n) ((hfin n).continuousOn _) ((hfin n).continuousOn _),
        cfc_const (Sn n / V n) (rho n) (hsa n), Algebra.algebraMap_eq_smul_one,
        Complex.coe_smul, neg_smul, sub_neg_eq_add]
    simp only [spectralWindow]
    rw [hcent, ← cfc_comp' _ _ _ (((hfin n).image _).continuousOn _) ((hfin n).continuousOn _)
      (hsa n)]
  have hmass : ∀ n δ, (traceExpectation (rho n) (spectralWindow (centeredLogDensity rho n) (-δ) δ)).re
      = mass n δ := by
    intro n δ
    rw [hwin, traceExpectation, om_cfc_self _ (hh n)]
  -- AEP in real form
  have haep : ∀ δ, 0 < δ → ∀ ε, 0 < ε → ∀ᶠ n in atTop, 0 < mass n δ ∧
      -ε ≤ Real.log (mass n δ) / V n := by
    intro δ hδ ε hε
    have h := hequipartition δ hδ
    have hI : Set.Ioi ((-ε : ℝ) : EReal) ∈ 𝓝 (0 : EReal) :=
      Ioi_mem_nhds (by exact_mod_cast (neg_neg_iff_pos.mpr hε))
    filter_upwards [h hI] with n hn
    simp only [Set.mem_preimage, Set.mem_Ioi, scaledLogMass, hmass] at hn
    split_ifs at hn with hp
    · refine ⟨hp, ?_⟩
      have := EReal.coe_lt_coe_iff.mp hn
      exact this.le
    · exact absurd hn (by simp)
  -- diagonal choice of window widths
  have hN : ∀ j : ℕ, ∃ N, ∀ n ≥ N, 0 < mass n (1 / ((j : ℝ) + 1)) ∧
      -(1 / ((j : ℝ) + 1)) ≤ Real.log (mass n (1 / ((j : ℝ) + 1))) / V n :=
    fun j => Filter.eventually_atTop.mp (haep _ (by positivity) _ (by positivity))
  choose N hNspec using hN
  let J : ℕ → ℕ := fun n => Nat.findGreatest (fun j => ∀ i ≤ j, N i ≤ n) n
  have hJspec : ∀ n, N 0 ≤ n → N (J n) ≤ n := by
    intro n hn
    have : (fun j => ∀ i ≤ j, N i ≤ n) (J n) :=
      Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, N i ≤ n) (m := 0) (Nat.zero_le _) (fun i hi => by
        obtain rfl := Nat.le_zero.mp hi; exact hn)
    exact this (J n) le_rfl
  have hJtop : Tendsto J atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro j0
    refine ⟨max j0 (∑ i ∈ Finset.range (j0 + 1), N i), fun n hn => ?_⟩
    apply Nat.le_findGreatest (le_of_max_le_left hn)
    intro i hi
    have : N i ≤ ∑ i ∈ Finset.range (j0 + 1), N i :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have := le_of_max_le_right hn
    omega
  set δ : ℕ → ℝ := fun n => 1 / ((J n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have : Tendsto (fun n => ((J n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hJtop)
    have := this.inv_tendsto_atTop
    exact this.congr fun n => (one_div _).symm
  have hgood : ∀ n, N 0 ≤ n → 0 < mass n (δ n) ∧ -δ n ≤ Real.log (mass n (δ n)) / V n :=
    fun n hn => hNspec (J n) n (hJspec n hn)
  -- spectral bounds
  have hχ0 : ∀ δ n z, 0 ≤ χ δ n z := fun δ n z => by rcases hχ01 δ n z with h | h <;> simp [h]
  have hmass1 : ∀ n δ, mass n δ ≤ 1 := by
    intro n δ
    calc mass n δ ≤ ∑ i, r n i := Finset.sum_le_sum fun i _ =>
          mul_le_of_le_one_right (hr0 n i).le (by rcases hχ01 δ n (r n i) with h | h <;> simp [h])
      _ = 1 := hr1 n
  set tP : ℕ → ℝ := fun n => ∑ i, χ (δ n) n (r n i)
  have hb1 : ∀ n, mass n (δ n) ≤ Real.exp (-Sn n + δ n * V n) * tP n := by
    intro n
    simp only [mass, tP, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases hχ01 (δ n) n (r n i) with h | h
    · rw [h]; simp
    · rw [h, mul_one, mul_one]
      have h2 : (V n)⁻¹ * Real.log (r n i) + Sn n / V n ≤ δ n := by
        simp only [χ] at h; split_ifs at h with h3; exact h3.2; simp at h
      have h3 : Real.log (r n i) ≤ -Sn n + δ n * V n := by
        have := hVpos n
        rw [inv_mul_eq_div, ← add_div, div_le_iff₀ this] at h2
        linarith
      calc r n i = Real.exp (Real.log (r n i)) := (Real.exp_log (hr0 n i)).symm
        _ ≤ _ := Real.exp_le_exp.mpr h3
  have hlow : ∀ n z, 0 < z → χ (δ n) n z ≤ Real.exp (Sn n + δ n * V n) * z := by
    intro n z hz
    rcases hχ01 (δ n) n z with h | h
    · rw [h]; positivity
    · rw [h]
      have h2 : -δ n ≤ (V n)⁻¹ * Real.log z + Sn n / V n := by
        simp only [χ] at h; split_ifs at h with h3; exact h3.1; simp at h
      have h3 : -Sn n - δ n * V n ≤ Real.log z := by
        have := hVpos n
        rw [inv_mul_eq_div, ← add_div, le_div_iff₀ this] at h2
        linarith
      calc (1 : ℝ) = Real.exp (Sn n + δ n * V n) * Real.exp (-Sn n - δ n * V n) := by
            rw [← Real.exp_add]; simp
        _ ≤ Real.exp (Sn n + δ n * V n) * Real.exp (Real.log z) := by gcongr
        _ = _ := by rw [Real.exp_log hz]
  have hb2 : ∀ n, tP n ≤ Real.exp (Sn n + δ n * V n) := by
    intro n
    calc tP n ≤ ∑ i, Real.exp (Sn n + δ n * V n) * r n i :=
          Finset.sum_le_sum fun i _ => hlow n _ (hr0 n i)
      _ = _ := by rw [← Finset.mul_sum, hr1, mul_one]
  have hb3 : ∀ n (Y : Matrix (Fin (S.dimension n)) (Fin (S.dimension n)) ℂ), Y.PosSemidef →
      (cfc (χ (δ n) n) (rho n) * Y).trace.re ≤
        Real.exp (Sn n + δ n * V n) * (rho n * Y).trace.re := by
    intro n Y hY
    open scoped MatrixOrder in
    have hD : 0 ≤ cfc (fun z => Real.exp (Sn n + δ n * V n) * z - χ (δ n) n z) (rho n) := by
      refine cfc_nonneg fun z hz => ?_
      rw [(hh n).spectrum_real_eq_range_eigenvalues] at hz
      obtain ⟨i, rfl⟩ := hz
      linarith [hlow n _ (hr0 n i)]
    have hD' := tr_psd_mul _ Y (Matrix.nonneg_iff_posSemidef.mp hD) hY
    rw [cfc_sub _ _ (rho n) ((hfin n).continuousOn _) ((hfin n).continuousOn _),
      cfc_const_mul _ _ (rho n) ((hfin n).continuousOn _), cfc_id' ℝ (rho n) (hsa n),
      Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.trace_smul,
      Complex.real_smul, Complex.re_ofReal_mul] at hD'
    linarith
  have htrP : ∀ n, (cfc (χ (δ n) n) (rho n)).trace = ((tP n : ℝ) : ℂ) := by
    intro n; rw [tr_cfc _ (hh n)]; simp only [tP, Complex.ofReal_sum]; rfl
  -- the projections
  have hne : ∀ n, Nonempty (Fin (S.dimension n)) := fun n => ⟨⟨0, hS.1 n⟩⟩
  set P : OperatorSequence S := fun n =>
    if 0 < mass n (δ n) then cfc (χ (δ n) n) (rho n) else 1
  have htP : ∀ n, 0 < mass n (δ n) → 0 < tP n := by
    intro n hm
    by_contra h
    push Not at h
    have hz : ∀ i, χ (δ n) n (r n i) = 0 := by
      intro i
      have := Finset.single_le_sum (f := fun i => χ (δ n) n (r n i)) (fun j _ => hχ0 _ _ _)
        (Finset.mem_univ i)
      linarith [hχ0 (δ n) n (r n i)]
    have : mass n (δ n) = 0 := by simp [mass, hz]
    linarith
  have hPproj : IsProjectionSequence P := by
    intro n
    by_cases hm : 0 < mass n (δ n)
    · simp only [P, if_pos hm]
      refine ⟨proj_cfc _ (hsa n) _ (hχ01 _ n), fun h0 => ?_⟩
      have := htrP n
      rw [h0, Matrix.trace_zero] at this
      have h2 := congrArg Complex.re this
      simp at h2
      linarith [htP n hm]
    · simp only [P, if_neg hm]
      haveI := hne n
      exact ⟨IsStarProjection.one _, one_ne_zero⟩
  refine ⟨P, hPproj, ?_, ?_⟩
  · -- exponential concentration
    intro dA hdA k
    obtain ⟨C, hC, n0, hn0⟩ := hexponential dA hdA k
    refine ⟨C / 2, by positivity, ?_⟩
    obtain ⟨n3, hn3⟩ := Metric.tendsto_atTop.mp hδ0 (C / 6) (by positivity)
    refine ⟨max (max n0 (N 0)) n3, fun n hn => ?_⟩
    obtain ⟨hm, hlm⟩ := hgood n (by omega)
    have hδn : δ n < C / 6 := by
      have := hn3 n (by omega); rw [Real.dist_eq, sub_zero, abs_of_pos (hδpos n)] at this
      exact this
    have hρW := hn0 n (by omega)
    set A := S.observable n k
    set W := spectralWindow A (x k - dA) (x k + dA)
    have hAsa : IsSelfAdjoint A := hS.2.1 n k
    have hfinA : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
    open scoped MatrixOrder in
    have hW1 : W ≤ 1 := by
      simp only [W, spectralWindow]
      rw [← cfc_const_one ℝ A hAsa]
      refine cfc_mono (fun z _ => ?_) (hfinA.continuousOn _) (hfinA.continuousOn _)
      split_ifs <;> norm_num
    have hY : (1 - W).PosSemidef := Matrix.le_iff.mp hW1
    have hPn : P n = cfc (χ (δ n) n) (rho n) := by simp only [P, if_pos hm]
    have hkey := hb3 n (1 - W) hY
    have hρ1 : (rho n * (1 - W)).trace.re = 1 - (traceExpectation (rho n) W).re := by
      simp [traceExpectation, Matrix.mul_sub, Matrix.trace_sub, (hrho n).2]
    have hP1 : (cfc (χ (δ n) n) (rho n) * (1 - W)).trace.re =
        tP n - (cfc (χ (δ n) n) (rho n) * W).trace.re := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, htrP,
        Complex.ofReal_re]
    have hωP : (traceExpectation (projectionDensity P n) W).re =
        (tP n)⁻¹ * (cfc (χ (δ n) n) (rho n) * W).trace.re := by
      simp only [traceExpectation, projectionDensity, hPn, Matrix.smul_mul, Matrix.trace_smul,
        htrP, smul_eq_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    have htPpos := htP n hm
    -- lower bound on tP
    have hmlow : Real.exp (-(δ n * V n)) ≤ mass n (δ n) := by
      have := (le_div_iff₀ (hVpos n)).mp (by linarith [hlm] : -δ n ≤ Real.log (mass n (δ n)) / V n)
      calc Real.exp (-(δ n * V n)) ≤ Real.exp (Real.log (mass n (δ n))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = _ := Real.exp_log hm
    have htPlow : Real.exp (Sn n - 2 * (δ n * V n)) ≤ tP n := by
      have h1 := hb1 n
      have h2 : Real.exp (-(δ n * V n)) ≤ Real.exp (-Sn n + δ n * V n) * tP n := hmlow.trans h1
      have h3 : Real.exp (Sn n - 2 * (δ n * V n)) =
          Real.exp (-(δ n * V n)) * Real.exp (Sn n - δ n * V n) := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp (-Sn n + δ n * V n) * Real.exp (Sn n - δ n * V n) = 1 := by
        rw [← Real.exp_add]; simp
      rw [h3]
      calc Real.exp (-(δ n * V n)) * Real.exp (Sn n - δ n * V n)
          ≤ Real.exp (-Sn n + δ n * V n) * tP n * Real.exp (Sn n - δ n * V n) := by gcongr
        _ = tP n := by rw [mul_comm (Real.exp _) (tP n), mul_assoc, h4, mul_one]
    -- conclude
    rw [hωP]
    have hnum : (cfc (χ (δ n) n) (rho n) * (1 - W)).trace.re ≤
        Real.exp (Sn n + δ n * V n) * Real.exp (-C * V n) := by
      refine hkey.trans ?_
      rw [hρ1]
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have hfrac : (cfc (χ (δ n) n) (rho n) * (1 - W)).trace.re / tP n ≤
        Real.exp (-(C / 2) * V n) := by
      rw [div_le_iff₀ htPpos]
      refine hnum.trans ?_
      calc Real.exp (Sn n + δ n * V n) * Real.exp (-C * V n)
          = Real.exp (-(C / 2) * V n) * Real.exp (Sn n - 2 * (δ n * V n)) *
              Real.exp (3 * (δ n * V n) - C / 2 * V n) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(C / 2) * V n) * tP n * 1 := by
            gcongr
            rw [Real.exp_le_one_iff]
            nlinarith [hVpos n]
        _ = _ := by ring
    have : (tP n)⁻¹ * (cfc (χ (δ n) n) (rho n) * W).trace.re =
        1 - (cfc (χ (δ n) n) (rho n) * (1 - W)).trace.re / tP n := by
      rw [hP1]; field_simp; ring
    rw [this]
    linarith
  · -- entropy matching
    have hev : ∀ᶠ n in atTop, |(Real.log (P n).trace.re - densityEntropyNats (rho n)) / V n| ≤
        2 * δ n := by
      filter_upwards [eventually_ge_atTop (N 0)] with n hn
      obtain ⟨hm, hlm⟩ := hgood n hn
      have hPn : P n = cfc (χ (δ n) n) (rho n) := by simp only [P, if_pos hm]
      have htPpos := htP n hm
      rw [hPn, htrP, Complex.ofReal_re]
      change |(Real.log (tP n) - Sn n) / V n| ≤ 2 * δ n
      have hup : Real.log (tP n) ≤ Sn n + δ n * V n := by
        calc Real.log (tP n) ≤ Real.log (Real.exp (Sn n + δ n * V n)) :=
              Real.log_le_log htPpos (hb2 n)
          _ = _ := Real.log_exp _
      have hlo : Real.log (mass n (δ n)) + Sn n - δ n * V n ≤ Real.log (tP n) := by
        have h1 := hb1 n
        have h2 : Real.log (mass n (δ n)) ≤ Real.log (Real.exp (-Sn n + δ n * V n) * tP n) :=
          Real.log_le_log hm h1
        rw [Real.log_mul (Real.exp_pos _).ne' htPpos.ne', Real.log_exp] at h2
        linarith
      have hlm2 : Real.log (mass n (δ n)) ≤ 0 := Real.log_nonpos hm.le (hmass1 n _)
      have hV := hVpos n
      have hlm' := (le_div_iff₀ hV).mp hlm
      rw [abs_le, le_div_iff₀ hV, div_le_iff₀ hV]
      constructor <;> nlinarith [hδpos n]
    have h2δ : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by simpa using hδ0.const_mul 2
    exact squeeze_zero_norm' (hev.mono fun n h => by rwa [Real.norm_eq_abs]) h2δ

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
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hrho : IsStateSequence rho) (hpositive : ∀ n, (rho n).PosDef)
    (hexponential : exponentiallyConcentrates S rho x)
    (hequipartition : asymptoticEquipartition rho) :
    ∃ P : OperatorSequence S, IsProjectionSequence P ∧
      exponentiallyConcentrates S (projectionDensity P) x ∧
      Tendsto (fun n => (Real.log (P n).trace.re - densityEntropyNats (rho n)) /
        (volume n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
  X6MQ.csub S hS rho x hrho hpositive hexponential hequipartition

end
