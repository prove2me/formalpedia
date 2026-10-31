-- Prove2me | solution 1 for QAlgorithms.Nannicini.adiabatic_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @Alien60
-- created : 2026-10-30T12:58:15.203532+00:00
-- url     : https://prove2.me/submissions/1d798e09-c33f-4cda-97b1-6a36bf1e29e1

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open QAlgorithms
open scoped Matrix

namespace QAlgorithms.Nannicini.AdiabaticCx

noncomputable section

/-! ## Generic lemmas -/

/-- A `2 × 2` complex matrix with entries bounded by `b` has operator norm at most `2b`. -/
theorem sum_two_of_equiv {ι M : Type*} [Fintype ι] [AddCommMonoid M] (e : ι ≃ Fin 2)
    (f : ι → M) : ∑ i, f i = f (e.symm 0) + f (e.symm 1) := by
  rw [← e.symm.sum_comp, Fin.sum_univ_two]

/-- A complex matrix on a two-element index type with entries bounded by `b` has operator norm
at most `2b`. -/
theorem specNorm_le_two_mul_of_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 2)
    (A : Matrix ι ι ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, ‖A i j‖ ≤ b) : specNorm A ≤ 2 * b := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  simp only [LinearEquiv.trans_apply, Matrix.toLpLin_apply,
    LinearMap.coe_toContinuousLinearMap']
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [sum_two_of_equiv e, Matrix.mulVec, dotProduct]
  set i0 := e.symm 0
  set i1 := e.symm 1
  set x0 := ‖x i0‖
  set x1 := ‖x i1‖
  have hrow : ∀ i, ‖A i i0 * x i0 + A i i1 * x i1‖ ≤ b * x0 + b * x1 := fun i => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (h i i0) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (h i i1) (norm_nonneg _))
  have hx0 : 0 ≤ x0 := norm_nonneg _
  have hx1 : 0 ≤ x1 := norm_nonneg _
  have h0 := hrow i0
  have h1 := hrow i1
  have n0 := norm_nonneg (A i0 i0 * x i0 + A i0 i1 * x i1)
  have n1 := norm_nonneg (A i1 i0 * x i0 + A i1 i1 * x i1)
  rw [show 2 * b * √(x0 ^ 2 + x1 ^ 2) = √((2 * b) ^ 2 * (x0 ^ 2 + x1 ^ 2)) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  simp only [Fin.isValue, WithLp.ofLp_toLp] at *
  nlinarith [mul_le_mul h0 h0 n0 (by positivity), mul_le_mul h1 h1 n1 (by positivity),
    sq_nonneg (x0 - x1), mul_nonneg hb hb]

/-- Helper: two values in `{0,1}` on a two-element index summing to `1`. -/
theorem gap_of_zero_one {n : ℕ} (f : Fin n → ℝ) (hn : n = 2) (h01 : ∀ k, f k = 0 ∨ f k = 1)
    (hsum : ∑ k, f k = 1) :
    (∃! k, f k = 0) ∧ ∀ k, f k ≠ 0 → (1 : ℝ) ≤ |f k - 0| := by
  subst hn
  refine ⟨?_, fun k hk => by rcases h01 k with h | h <;> simp_all⟩
  rw [Fin.sum_univ_two] at hsum
  rcases h01 0 with h0 | h0 <;> rcases h01 1 with h1 | h1
  · rw [h0, h1] at hsum; norm_num at hsum
  · refine ⟨0, h0, fun k hk => ?_⟩
    fin_cases k
    · rfl
    · simp_all
  · refine ⟨1, h1, fun k hk => ?_⟩
    fin_cases k
    · simp_all
    · rfl
  · rw [h0, h1] at hsum; norm_num at hsum

/-- A Hermitian idempotent `2 × 2` matrix of trace `1` (a rank-one projector) has a gap `1`
around the eigenvalue `0`. -/
theorem hasGapAround_of_proj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hidem : A * A = A) (htr : A.trace = 1) : HasGapAround A 0 1 := by
  have eig01 : ∀ j, hA.eigenvalues j = 0 ∨ hA.eigenvalues j = 1 := by
    intro j
    have hv := hA.mulVec_eigenvectorBasis j
    set μ := hA.eigenvalues j
    set v := ⇑(hA.eigenvectorBasis j)
    have h2 : A *ᵥ (A *ᵥ v) = A *ᵥ v := by rw [Matrix.mulVec_mulVec, hidem]
    rw [hv, Matrix.mulVec_smul, hv, smul_smul] at h2
    have h3 : (μ * μ - μ) • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · have : μ * (μ - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · exact absurd (by simpa [v] using h) ((hA.eigenvectorBasis).orthonormal.ne_zero j)
  have hasc : ∀ k, ascEigenvalues A k = hA.eigenvalues
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.rev k)) := by
    intro k
    simp [ascEigenvalues, dif_pos hA, Matrix.IsHermitian.eigenvalues]
  have hsum : ∑ k, ascEigenvalues A k = 1 := by
    have htr' := hA.trace_eq_sum_eigenvalues
    rw [htr] at htr'
    have hr : ∑ i, hA.eigenvalues i = 1 := by
      have := congrArg Complex.re htr'.symm
      simpa using this
    simp_rw [hasc]
    rw [← hr]
    exact (Equiv.sum_comp (Fin.revPerm.trans (Fintype.equivOfCardEq (Fintype.card_fin _)))
      hA.eigenvalues)
  obtain ⟨h1, h2⟩ := gap_of_zero_one (ascEigenvalues A) hcard
    (fun k => by rw [hasc]; exact eig01 _) hsum
  exact ⟨hA, h1, h2⟩

/-! ## The counterexample -/

/-- Rotation speed `a = 2m/(m²+1)` and `τ = (m²-1)/(m²+1)`, `m = 10⁶`; `a² + τ² = 1`. -/
def a : ℝ := 2 * 10 ^ 6 / (10 ^ 12 + 1)
def τ : ℝ := (10 ^ 12 - 1) / (10 ^ 12 + 1)

theorem a_pos : 0 < a := by norm_num [a]
theorem a_sq_add_τ_sq : a ^ 2 + τ ^ 2 = 1 := by norm_num [a, τ]

/-- `p s = sin(a s)`, `q s = cos(a s)`. -/
def p (s : ℝ) : ℝ := Real.sin (a * s)
def q (s : ℝ) : ℝ := Real.cos (a * s)

theorem hp (s : ℝ) : HasDerivAt p (a * q s) s :=
  (((hasDerivAt_id' s).const_mul a).sin).congr_deriv (by simp [q]; ring)

theorem hq (s : ℝ) : HasDerivAt q (-(a * p s)) s :=
  (((hasDerivAt_id' s).const_mul a).cos).congr_deriv (by simp [p]; ring)

theorem pq_sq (s : ℝ) : p s ^ 2 + q s ^ 2 = 1 := by simp [p, q, Real.sin_sq_add_cos_sq]

/-- `H(s) = |v(s)⟩⟨v(s)|`, `v(s) = (-sin(as), cos(as))`: the projector rotated by angle `as`. -/
def Hc (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((p s ^ 2 : ℝ) : ℂ), ((-(p s * q s) : ℝ) : ℂ); ((-(p s * q s) : ℝ) : ℂ), ((q s ^ 2 : ℝ) : ℂ)]

def H1 (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((a * (2 * p s * q s) : ℝ) : ℂ), ((a * (p s ^ 2 - q s ^ 2) : ℝ) : ℂ);
    ((a * (p s ^ 2 - q s ^ 2) : ℝ) : ℂ), ((-(a * (2 * p s * q s)) : ℝ) : ℂ)]

def H2 (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((2 * a ^ 2 * (q s ^ 2 - p s ^ 2) : ℝ) : ℂ), ((4 * a ^ 2 * (p s * q s) : ℝ) : ℂ);
    ((4 * a ^ 2 * (p s * q s) : ℝ) : ℂ), ((-(2 * a ^ 2 * (q s ^ 2 - p s ^ 2)) : ℝ) : ℂ)]

theorem hHc (s : ℝ) (_ : s ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    HasDerivWithinAt (fun t => Hc t i j) (H1 s i j) (Set.Icc 0 1) s := by
  fin_cases i <;> fin_cases j
  · exact (((hp s).pow 2).congr_deriv (by simp; ring)).ofReal_comp.hasDerivWithinAt
  · exact ((((hp s).mul (hq s)).neg).congr_deriv (by ring)).ofReal_comp.hasDerivWithinAt
  · exact ((((hp s).mul (hq s)).neg).congr_deriv (by ring)).ofReal_comp.hasDerivWithinAt
  · exact (((hq s).pow 2).congr_deriv (by simp; ring)).ofReal_comp.hasDerivWithinAt

theorem hH1 (s : ℝ) (_ : s ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    HasDerivWithinAt (fun t => H1 t i j) (H2 s i j) (Set.Icc 0 1) s := by
  fin_cases i <;> fin_cases j
  · exact (((((hp s).const_mul 2).mul (hq s)).const_mul a).congr_deriv
      (by ring)).ofReal_comp.hasDerivWithinAt
  · exact (((((hp s).pow 2).sub ((hq s).pow 2)).const_mul a).congr_deriv
      (by simp; ring)).ofReal_comp.hasDerivWithinAt
  · exact (((((hp s).pow 2).sub ((hq s).pow 2)).const_mul a).congr_deriv
      (by simp; ring)).ofReal_comp.hasDerivWithinAt
  · exact ((((((hp s).const_mul 2).mul (hq s)).const_mul a).neg).congr_deriv
      (by ring)).ofReal_comp.hasDerivWithinAt

theorem abs_two_pq_le (s : ℝ) : |2 * p s * q s| ≤ 1 := by
  have := pq_sq s
  exact abs_le.2 ⟨by nlinarith [sq_nonneg (p s + q s)], by nlinarith [sq_nonneg (p s - q s)]⟩

theorem abs_sq_sub_le (s : ℝ) : |p s ^ 2 - q s ^ 2| ≤ 1 := by
  have := pq_sq s
  exact abs_le.2 ⟨by nlinarith [sq_nonneg (p s)], by nlinarith [sq_nonneg (q s)]⟩

theorem hN1 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 2) (s : ℝ) :
    specNorm ((H1 s).submatrix e e) ≤ 2 * a := by
  have ha := a_pos
  have e1 : |a * (2 * p s * q s)| ≤ a := by
    rw [abs_mul, abs_of_pos ha]; nlinarith [abs_two_pq_le s]
  have e2 : |a * (p s ^ 2 - q s ^ 2)| ≤ a := by
    rw [abs_mul, abs_of_pos ha]; nlinarith [abs_sq_sub_le s]
  have hb : ∀ k l, ‖H1 s k l‖ ≤ a := fun k l => by
    fin_cases k <;> fin_cases l <;> simp only [H1] <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Complex.norm_real, Real.norm_eq_abs, abs_neg] <;> assumption
  exact specNorm_le_two_mul_of_entry_le e _ a ha.le fun i j => hb (e i) (e j)

theorem hN2 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 2) (s : ℝ) :
    specNorm ((H2 s).submatrix e e) ≤ 4 * a ^ 2 := by
  have ha : 0 < a ^ 2 := by have := a_pos; positivity
  have e1 : |2 * a ^ 2 * (q s ^ 2 - p s ^ 2)| ≤ 2 * a ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * a ^ 2), abs_sub_comm]
    nlinarith [abs_sq_sub_le s]
  have e2 : |4 * a ^ 2 * (p s * q s)| ≤ 2 * a ^ 2 := by
    rw [show 4 * a ^ 2 * (p s * q s) = 2 * a ^ 2 * (2 * p s * q s) by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * a ^ 2)]
    nlinarith [abs_two_pq_le s]
  rw [show 4 * a ^ 2 = 2 * (2 * a ^ 2) by ring]
  have hb : ∀ k l, ‖H2 s k l‖ ≤ 2 * a ^ 2 := fun k l => by
    fin_cases k <;> fin_cases l <;> simp only [H2] <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Complex.norm_real, Real.norm_eq_abs, abs_neg] <;> assumption
  exact specNorm_le_two_mul_of_entry_le e _ _ (by positivity) fun i j => hb (e i) (e j)

theorem pq_sq_C (s : ℝ) : ((p s : ℂ)) ^ 2 + (q s : ℂ) ^ 2 = 1 := by
  exact_mod_cast pq_sq s

theorem hgap {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 2) (s : ℝ) :
    HasGapAround ((Hc s).submatrix e e) 0 1 := by
  have r := pq_sq_C s
  have hH : (Hc s).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Hc, Matrix.conjTranspose_apply]
  have hI : Hc s * Hc s = Hc s := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Hc, Matrix.mul_apply, Fin.sum_univ_two] <;>
      push_cast
    · linear_combination (p s : ℂ) ^ 2 * r
    · linear_combination (-((p s : ℂ) * q s)) * r
    · linear_combination (-((p s : ℂ) * q s)) * r
    · linear_combination (q s : ℂ) ^ 2 * r
  have hT : (Hc s).trace = 1 := by
    simp [Hc, Matrix.trace, Fin.sum_univ_two]
    push_cast
    linear_combination r
  refine hasGapAround_of_proj (by rw [Fintype.card_congr e, Fintype.card_fin]) _
    (hH.submatrix e) ?_ ?_
  · rw [Matrix.submatrix_mul_equiv, hI]
  · rw [← hT]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact e.sum_comp (fun k => Hc s k k)

/-- The instantaneous eigenstate `φ(s) = (cos(as), sin(as))`, eigenvalue `0`. -/
def φc (s : ℝ) : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(q s : ℂ), (p s : ℂ)]

theorem hφc (s : ℝ) : IsState (φc s) ∧ act (Hc s) (φc s) = ((0 : ℝ) : ℂ) • φc s := by
  constructor
  · unfold IsState
    rw [EuclideanSpace.norm_eq]
    simp [φc, Fin.sum_univ_two, Complex.norm_real, sq_abs, add_comm, pq_sq s]
  · ext i
    fin_cases i <;> simp [act, Hc, φc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Explicit solution of `ψ' = i T H(s) ψ`, `T = 2τ`, in the rotating frame. -/
def Ec (s : ℝ) : ℂ := Complex.exp (((τ * s : ℝ) : ℂ) * Complex.I)
def u1 (s : ℝ) : ℂ := Ec s * ((Real.cos s : ℂ) - (τ : ℂ) * Complex.I * (Real.sin s : ℂ))
def u2 (s : ℝ) : ℂ := Ec s * (-(a : ℂ) * (Real.sin s : ℂ))

def ψc (s : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(q s : ℂ) * u1 s - (p s : ℂ) * u2 s, (p s : ℂ) * u1 s + (q s : ℂ) * u2 s]

theorem hEc (s : ℝ) : HasDerivAt Ec (Ec s * ((τ : ℂ) * Complex.I)) s :=
  ((((hasDerivAt_id' s).const_mul τ).ofReal_comp).mul_const Complex.I).cexp.congr_deriv
    (by simp [Ec])

theorem hcos (s : ℝ) : HasDerivAt (fun t => (Real.cos t : ℂ)) (-(Real.sin s : ℂ)) s :=
  (Real.hasDerivAt_cos s).ofReal_comp.congr_deriv (by push_cast; ring)

theorem hsin (s : ℝ) : HasDerivAt (fun t => (Real.sin t : ℂ)) ((Real.cos s : ℂ)) s :=
  (Real.hasDerivAt_sin s).ofReal_comp

theorem hu1 (s : ℝ) : HasDerivAt u1 (Ec s * ((τ : ℂ) * Complex.I) *
    ((Real.cos s : ℂ) - (τ : ℂ) * Complex.I * (Real.sin s : ℂ)) +
    Ec s * (-(Real.sin s : ℂ) - (τ : ℂ) * Complex.I * (Real.cos s : ℂ))) s :=
  (hEc s).mul ((hcos s).sub ((hsin s).const_mul ((τ : ℂ) * Complex.I)))

theorem hu2 (s : ℝ) : HasDerivAt u2 (Ec s * ((τ : ℂ) * Complex.I) *
    (-(a : ℂ) * (Real.sin s : ℂ)) + Ec s * (-(a : ℂ) * (Real.cos s : ℂ))) s :=
  (hEc s).mul ((hsin s).const_mul (-(a : ℂ)))

theorem hpC (s : ℝ) : HasDerivAt (fun t => (p t : ℂ)) ((a : ℂ) * q s) s :=
  (hp s).ofReal_comp.congr_deriv (by push_cast; ring)

theorem hqC (s : ℝ) : HasDerivAt (fun t => (q t : ℂ)) (-((a : ℂ) * p s)) s :=
  (hq s).ofReal_comp.congr_deriv (by push_cast; ring)

theorem hψc (s : ℝ) : HasDerivAt ψc (Complex.I • ((2 * τ : ℝ) : ℂ) • act (Hc s) (ψc s)) s := by
  have g0 := ((hqC s).mul (hu1 s)).sub ((hpC s).mul (hu2 s))
  have g1 := ((hpC s).mul (hu1 s)).add ((hqC s).mul (hu2 s))
  have hg : HasDerivAt (fun t => ![(q t : ℂ) * u1 t - (p t : ℂ) * u2 t,
      (p t : ℂ) * u1 t + (q t : ℂ) * u2 t])
      ![-((a : ℂ) * p s) * u1 s + (q s : ℂ) * (Ec s * ((τ : ℂ) * Complex.I) * ((Real.cos s : ℂ) - (τ : ℂ) * Complex.I * (Real.sin s : ℂ)) + Ec s * (-(Real.sin s : ℂ) - (τ : ℂ) * Complex.I * (Real.cos s : ℂ))) - ((a : ℂ) * q s * u2 s + (p s : ℂ) * (Ec s * ((τ : ℂ) * Complex.I) * (-(a : ℂ) * (Real.sin s : ℂ)) + Ec s * (-(a : ℂ) * (Real.cos s : ℂ)))),
        (a : ℂ) * q s * u1 s + (p s : ℂ) * (Ec s * ((τ : ℂ) * Complex.I) * ((Real.cos s : ℂ) - (τ : ℂ) * Complex.I * (Real.sin s : ℂ)) + Ec s * (-(Real.sin s : ℂ) - (τ : ℂ) * Complex.I * (Real.cos s : ℂ))) + (-((a : ℂ) * p s) * u2 s + (q s : ℂ) * (Ec s * ((τ : ℂ) * Complex.I) * (-(a : ℂ) * (Real.sin s : ℂ)) + Ec s * (-(a : ℂ) * (Real.cos s : ℂ))))] s := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact g0
    · exact g1
  have hL : HasFDerivAt (𝕜 := ℝ) (WithLp.toLp 2 : (Fin 2 → ℂ) → EuclideanSpace ℂ (Fin 2))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm :
        (Fin 2 → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin 2))
      ![(q s : ℂ) * u1 s - (p s : ℂ) * u2 s, (p s : ℂ) * u1 s + (q s : ℂ) * u2 s] :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.hasFDerivAt
  have := hL.comp_hasDerivAt s hg
  refine this.congr_deriv ?_
  have r1 := pq_sq_C s
  have r2 : (a : ℂ) ^ 2 + (τ : ℂ) ^ 2 = 1 := by exact_mod_cast a_sq_add_τ_sq
  have r3 := Complex.I_sq
  ext i
  fin_cases i <;>
    simp [act, Hc, ψc, u1, u2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> push_cast
  · linear_combination (-2 * Ec s * Complex.I * Complex.sin (s : ℂ) * a * p s * τ) * r1 +
      (Ec s * Complex.sin (s : ℂ) * q s) * r2 + (-Ec s * Complex.sin (s : ℂ) * q s * τ ^ 2) * r3
  · linear_combination (2 * Ec s * Complex.I * Complex.sin (s : ℂ) * a * q s * τ) * r1 +
      (Ec s * Complex.sin (s : ℂ) * p s) * r2 + (-Ec s * Complex.sin (s : ℂ) * p s * τ ^ 2) * r3

theorem hψ0 : ψc 0 = φc 0 := by
  ext i
  fin_cases i <;> simp [ψc, φc, u1, u2, Ec, p, q]

/-- The final state is at distance at least `a sin 1 > a / 2` from every phase of `φ(1)`. -/
theorem far (θ : ℝ) : a / 2 < ‖Complex.exp ((θ : ℂ) * Complex.I) • ψc 1 - φc 1‖ := by
  set v := Complex.exp ((θ : ℂ) * Complex.I) • ψc 1 - φc 1
  set w : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![-(p 1 : ℂ), (q 1 : ℂ)]
  have hw : ‖w‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [w, Fin.sum_univ_two, Complex.norm_real, sq_abs, pq_sq 1]
  have r1 := pq_sq_C 1
  have hin : inner ℂ w v = Complex.exp ((θ : ℂ) * Complex.I) *
      (Ec 1 * (-(a : ℂ) * (Real.sin 1 : ℂ))) := by
    simp [v, w, ψc, φc, u2, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (Complex.exp ((θ : ℂ) * Complex.I) * (-(Ec 1 * a * Complex.sin 1))) * r1
  have hle := norm_inner_le_norm (𝕜 := ℂ) w v
  rw [hin, hw, one_mul] at hle
  have hs : 5 / 6 < Real.sin 1 := by
    have := Real.sin_gt_sub_cube (x := 1) one_pos; norm_num at this; linarith
  have hE : ‖Ec 1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have ha := a_pos
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, hE, norm_mul, norm_neg,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha, abs_of_pos (by linarith)] at hle
  nlinarith

/-! ## Transport to an arbitrary two-element index type (for universe polymorphism) -/

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 2) 

/-- Transport of a vector along `e`. -/
def tv (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => v (e i))

theorem tv_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) : tv e (c • v) = c • tv e v := by
  ext i; simp [tv]

theorem tv_sub (v w : EuclideanSpace ℂ (Fin 2)) : tv e (v - w) = tv e v - tv e w := by
  ext i; simp [tv]

theorem tv_norm (v : EuclideanSpace ℂ (Fin 2)) : ‖tv e v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [tv, WithLp.ofLp_toLp]
  exact e.sum_comp (fun k => ‖v k‖ ^ 2)

theorem act_tv (A : Matrix (Fin 2) (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    act (A.submatrix e e) (tv e v) = tv e (act A v) := by
  ext i
  simp only [act, tv, WithLp.ofLp_toLp, Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

/-- `tv` as a continuous `ℝ`-linear map. -/
def tvL : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := tv e
      map_add' := fun v w => by ext i; simp [tv]
      map_smul' := fun c v => by ext i; simp [tv] }

theorem hψT (s : ℝ) : HasDerivWithinAt (fun t => tv e (ψc t))
    (Complex.I • ((2 * τ : ℝ) : ℂ) • act ((Hc s).submatrix e e) (tv e (ψc s)))
    (Set.Icc 0 1) s := by
  have := ((tvL e).hasFDerivAt.comp_hasDerivAt s (hψc s)).hasDerivWithinAt (s := Set.Icc 0 1)
  rw [act_tv, ← tv_smul, ← tv_smul]
  exact this

end Transport

end

end QAlgorithms.Nannicini.AdiabaticCx

open QAlgorithms QAlgorithms.Nannicini.AdiabaticCx

theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (lam : ℝ → ℝ) (hlam : ContinuousOn lam (Set.Icc 0 1)) (φ : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = (lam s : ℂ) • φ s)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) (lam s) γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 4 / δ ^ 2 * (N1 ^ 3 / γ ^ 4 + N1 * N2 / γ ^ 3) ≤ T)
    (ψ : ℝ → EuclideanSpace ℂ ι) (hψ : SolvesAdiabaticPlus H T ψ) (hψ0 : ψ 0 = φ 0),
    ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ) := by
  intro h
  have hT : (10 : ℝ) ^ 4 / (a / 2) ^ 2 * ((2 * a) ^ 3 / 1 ^ 4 + 2 * a * (4 * a ^ 2) / 1 ^ 3)
      ≤ 2 * τ := by norm_num [a, τ]
  let e : ULift.{0} (Fin 2) ≃ Fin 2 := Equiv.ulift
  obtain ⟨θ, hθ⟩ := h (ι := ULift.{0} (Fin 2)) (fun s => (Hc s).submatrix e e)
    (fun s => (H1 s).submatrix e e) (fun s => (H2 s).submatrix e e)
    (fun s hs i j => hHc s hs (e i) (e j)) (fun s hs i j => hH1 s hs (e i) (e j))
    (fun _ => 0) continuousOn_const (fun s => tv e (φc s))
    (fun s _ => ⟨(tv_norm e _).trans (hφc s).1,
      by rw [act_tv, (hφc s).2, tv_smul]⟩) 1 one_pos (fun s _ => hgap e s) (2 * a) (4 * a ^ 2)
    (fun s _ => hN1 e s) (fun s _ => hN2 e s) (a / 2) (by have := a_pos; positivity) (2 * τ) hT
    (fun s => tv e (ψc s)) (fun s _ => hψT e s) (by rw [hψ0])
  rw [← tv_smul, ← tv_sub, tv_norm] at hθ
  exact absurd hθ (not_le.2 (far θ))
