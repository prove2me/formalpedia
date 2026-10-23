-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.dephasingStage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:56:00.69087+00:00
-- url     : https://prove2.me/submissions/71bddb39-80f9-41c2-a294-f8e624001ae9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

def X7_th (w j t : ℝ) : Bool × Bool → ℝ := fun x =>
  match x with
  | (false, false) => t * (w - j)
  | (false, true) => t * j
  | (true, false) => t * j
  | (true, true) => -(t * (w + j))

theorem X7_gen (w j t : ℝ) :
    (-(t : ℂ) * Complex.I) • (freeEnergy w + (j : ℂ) • Matrix.kronecker pauliZ pauliZ) =
      Matrix.diagonal (fun x => Complex.I * (X7_th w j t x : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_th, freeEnergy, localEnergy, Matrix.kronecker, Matrix.kroneckerMap_apply,
      QAlgorithms.pauliZ, Matrix.one_apply, Matrix.diagonal_apply] <;> ring

theorem X7_evol (w j t : ℝ) :
    evolution (freeEnergy w + (j : ℂ) • Matrix.kronecker pauliZ pauliZ) t =
      Matrix.diagonal (fun x => Complex.exp (Complex.I * (X7_th w j t x : ℂ))) := by
  unfold evolution
  rw [X7_gen, Matrix.exp_diagonal, Pi.exp_def]
  congr 1; funext x; rw [← Complex.exp_eq_exp_ℂ]

theorem X7_ee (a b : ℝ) :
    Complex.exp (Complex.I * (a : ℂ)) * conj (Complex.exp (Complex.I * (b : ℂ))) =
      Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal]; ring

theorem X7_red_diag (u : Bool × Bool → ℂ) (pA p : ℝ) (cA c : ℂ)
    (h1 : ∀ x, u x * conj (u x) = 1) :
    reduced (Matrix.diagonal u) (rho pA cA) (rho p c) =
      rho p (c * ((pA : ℂ) * (u (false, false) * conj (u (true, false))) +
        ((1 - pA : ℝ) : ℂ) * (u (false, true) * conj (u (true, true))))) := by
  have a := h1 (false, false)
  have b := h1 (false, true)
  have c' := h1 (true, false)
  have d := h1 (true, true)
  ext i j
  cases i <;> cases j <;>
    simp [reduced, rho, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · linear_combination ((p : ℂ) * pA) * a + (p * (1 - pA)) * b
  · ring
  · ring
  · linear_combination ((1 - (p : ℂ)) * pA) * c' + ((1 - p) * (1 - pA)) * d

theorem X7_deph_rho (m : Model) (jzz p : ℝ) (c : ℂ) :
    dephasingCollision m jzz (rho p c) = rho p (c * dephasingFactor m jzz) := by
  unfold dephasingCollision
  rw [X7_evol, X7_red_diag]
  · congr 2
    unfold dephasingFactor
    rw [X7_ee, X7_ee]
    simp only [X7_th]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  · intro x
    rw [X7_ee, sub_self]; simp

theorem X7_density_rho (r : Op Bool) (hr : IsDensityMatrix r) :
    r = rho (population r) (coherence r) := by
  have hH := hr.1.1
  have h1 : r true false = conj (r false true) := by
    have := congrFun (congrFun hH true) false
    simp [Matrix.conjTranspose_apply] at this
    rw [← this]
  have h2 : ((r false false).re : ℂ) = r false false := by
    have := congrFun (congrFun hH false) false
    simp [Matrix.conjTranspose_apply] at this
    apply Complex.ext
    · simp
    · simp
      have := congrArg Complex.im this
      simp at this
      linarith
  have h3 : r true true = 1 - r false false := by
    have := hr.2
    simp [Matrix.trace] at this
    linear_combination this
  ext i j
  cases i <;> cases j <;> simp [rho, population, coherence, h1, h2, h3]

theorem X7_normSq_exp (x : ℝ) : Complex.normSq (Complex.exp (Complex.I * (x : ℂ))) = 1 := by
  rw [Complex.normSq_eq_norm_sq, mul_comm, Complex.norm_exp_ofReal_mul_I]; norm_num

theorem X7_rho_cont (p : ℝ) : Continuous (fun c : ℂ => rho p c) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  cases i <;> cases j <;> simp only [rho, Bool.false_eq_true, if_true, if_false]
  · exact continuous_const
  · exact continuous_id
  · exact Complex.continuous_conj
  · exact continuous_const

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (jzz : ℝ) (r : Op Bool) (hr : IsDensityMatrix r)
    (hp : 0 < m.pA) (hp1 : m.pA < 1) (hS : Real.sin (2 * jzz * m.duration) ≠ 0) :
    (∀ n : ℕ, (dephasingCollision m jzz)^[n] r =
      rho (population r) (coherence r * dephasingFactor m jzz ^ n)) ∧
    Complex.normSq (dephasingFactor m jzz) =
      1 - 4 * m.pA * (1 - m.pA) * Real.sin (2 * jzz * m.duration) ^ 2 ∧
    Complex.normSq (dephasingFactor m jzz) < 1 ∧
    Tendsto (fun n : ℕ => (dephasingCollision m jzz)^[n] r) atTop
      (𝓝 (rho (population r) 0)) := by
  have hit : ∀ n : ℕ, (dephasingCollision m jzz)^[n] r =
      rho (population r) (coherence r * dephasingFactor m jzz ^ n) := by
    intro n
    induction n with
    | zero => simpa using X7_density_rho r hr
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, X7_deph_rho, pow_succ, mul_assoc]
  set t := m.duration
  set w := m.frequency
  have hf : dephasingFactor m jzz =
      (m.pA : ℂ) * Complex.exp (Complex.I * ((-((2 * jzz - w) * t)) : ℝ)) +
      ((1 - m.pA : ℝ) : ℂ) * Complex.exp (Complex.I * (((2 * jzz + w) * t) : ℝ)) := by
    unfold dephasingFactor; congr 2 <;> push_cast <;> ring_nf <;> rfl
  have hnorm : Complex.normSq (dephasingFactor m jzz) =
      1 - 4 * m.pA * (1 - m.pA) * Real.sin (2 * jzz * t) ^ 2 := by
    rw [hf, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul, X7_normSq_exp,
      X7_normSq_exp, Complex.normSq_ofReal, Complex.normSq_ofReal]
    have hc : (((m.pA : ℂ) * Complex.exp (Complex.I * ((-((2 * jzz - w) * t)) : ℝ))) *
        conj (((1 - m.pA : ℝ) : ℂ) * Complex.exp (Complex.I * (((2 * jzz + w) * t) : ℝ)))).re =
        m.pA * (1 - m.pA) * Real.cos (4 * jzz * t) := by
      rw [map_mul, Complex.conj_ofReal, show ∀ a b c d : ℂ, a * b * (c * d) = (a * c) * (b * d)
        from fun a b c d => by ring, X7_ee, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
        mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
      congr 1; rw [← Real.cos_neg]; congr 1; ring
    rw [hc]
    have h2 : Real.cos (4 * jzz * t) = 1 - 2 * Real.sin (2 * jzz * t) ^ 2 := by
      rw [show 4 * jzz * t = 2 * (2 * jzz * t) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    rw [h2]; ring
  have hlt : Complex.normSq (dephasingFactor m jzz) < 1 := by
    rw [hnorm]
    have : 0 < Real.sin (2 * jzz * t) ^ 2 := by positivity
    have : 0 < m.pA * (1 - m.pA) := mul_pos hp (by linarith)
    nlinarith
  refine ⟨hit, hnorm, hlt, ?_⟩
  have hn : ‖dephasingFactor m jzz‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hlt
    nlinarith [norm_nonneg (dephasingFactor m jzz)]
  have h0 : Tendsto (fun n : ℕ => coherence r * dephasingFactor m jzz ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).const_mul (coherence r)
    simpa using this
  have := ((X7_rho_cont (population r)).tendsto 0).comp h0
  simp only [funext hit]
  exact this
