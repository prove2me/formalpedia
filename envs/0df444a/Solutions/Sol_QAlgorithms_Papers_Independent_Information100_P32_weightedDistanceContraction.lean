-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.weightedDistanceContraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:43:12.129109+00:00
-- url     : https://prove2.me/submissions/f290fa6c-d37d-4444-877a-b8f1b9cc297f

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- explicit collision unitary -/
def X7_Umat (e C S : ℂ) : Op (Bool × Bool) := fun x y =>
  match x, y with
  | (false, false), (false, false) => e
  | (false, true), (false, true) => C
  | (false, true), (true, false) => -Complex.I * S
  | (true, false), (false, true) => -Complex.I * S
  | (true, false), (true, false) => C
  | (true, true), (true, true) => conj e
  | _, _ => 0

def X7_V : Op (Bool × Bool) := fun x y =>
  match x, y with
  | (false, false), (false, false) => 1
  | (false, true), (false, true) => 1
  | (false, true), (true, false) => 1
  | (true, false), (false, true) => 1
  | (true, false), (true, false) => -1
  | (true, true), (true, true) => 1
  | _, _ => 0

def X7_W : Op (Bool × Bool) := fun x y =>
  match x, y with
  | (false, false), (false, false) => 1
  | (false, true), (false, true) => 1/2
  | (false, true), (true, false) => 1/2
  | (true, false), (false, true) => 1/2
  | (true, false), (true, false) => -1/2
  | (true, true), (true, true) => 1
  | _, _ => 0

def X7_d (w j t : ℝ) : Bool × Bool → ℂ := fun x =>
  match x with
  | (false, false) => Complex.I * ((w * t : ℝ) : ℂ)
  | (false, true) => ((-(2 * j * t) : ℝ) : ℂ) * Complex.I
  | (true, false) => ((2 * j * t : ℝ) : ℂ) * Complex.I
  | (true, true) => -(Complex.I * ((w * t : ℝ) : ℂ))

theorem X7_VW : X7_V * X7_W = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] <;> norm_num

theorem X7_WV : X7_W * X7_V = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] <;> norm_num

theorem X7_gen_eq (w j t : ℝ) :
    (-(t : ℂ) * Complex.I) • (freeEnergy w + interaction j) =
      X7_V * Matrix.diagonal (X7_d w j t) * X7_W := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_W, X7_d, freeEnergy, interaction, localEnergy, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.pauliX,
      QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.one_apply, Matrix.diagonal_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem X7_evolution_eq (w j t : ℝ) :
    evolution (freeEnergy w + interaction j) t =
      X7_Umat (Complex.exp (Complex.I * ((w * t : ℝ) : ℂ)))
        (Real.cos (2 * j * t) : ℂ) (Real.sin (2 * j * t) : ℂ) := by
  unfold evolution
  rw [X7_gen_eq]
  let u : (Op (Bool × Bool))ˣ := ⟨X7_V, X7_W, X7_VW, X7_WV⟩
  have h := Matrix.exp_units_conj u (Matrix.diagonal (X7_d w j t))
  simp only [u, Units.inv_mk] at h
  change NormedSpace.exp (X7_V * Matrix.diagonal (X7_d w j t) * X7_W) = _
  rw [h, Matrix.exp_diagonal, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  have hed : (fun i => Complex.exp (X7_d w j t i)) = fun x =>
      match x with
      | (false, false) => Complex.exp (Complex.I * ((w * t : ℝ) : ℂ))
      | (false, true) => (Real.cos (2 * j * t) : ℂ) - (Real.sin (2 * j * t) : ℂ) * Complex.I
      | (true, false) => (Real.cos (2 * j * t) : ℂ) + (Real.sin (2 * j * t) : ℂ) * Complex.I
      | (true, true) => conj (Complex.exp (Complex.I * ((w * t : ℝ) : ℂ))) := by
    funext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b
    · rfl
    · simp only [X7_d]
      rw [Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos_neg, Complex.sin_neg]
      ring
    · simp only [X7_d]
      rw [Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    · simp only [X7_d]
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_ofReal]
  rw [hed]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_W, X7_Umat, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.diagonal_apply] <;>
    ring_nf

theorem X7_im_eq (z : ℂ) : (z.im : ℂ) = -Complex.I * (z - conj z) / 2 := by
  apply Complex.ext <;> simp

theorem X7_econj (r : ℝ) :
    Complex.exp (Complex.I * (r : ℂ)) * conj (Complex.exp (Complex.I * (r : ℂ))) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : Complex.I * (r : ℂ) + conj (Complex.I * (r : ℂ)) = 0 := by
    apply Complex.ext <;> simp
  rw [this, Complex.exp_zero]

theorem X7_CS (x : ℝ) : ((Real.cos x : ℝ) : ℂ) ^ 2 + ((Real.sin x : ℝ) : ℂ) ^ 2 = 1 := by
  have := Real.cos_sq_add_sin_sq x
  exact_mod_cast this

/-- next population -/
def X7_pn (m : Model) (p : ℝ) (c : ℂ) : ℝ :=
  m.pA + angleC m ^ 2 * (p - m.pA) -
      Real.sin (4 * m.coupling * m.duration) * (c * conj m.cA).im

/-- next coherence -/
def X7_cn (m : Model) (p : ℝ) (c : ℂ) : ℂ :=
  Complex.exp (Complex.I * (m.frequency * m.duration : ℝ)) *
        ((c * (angleC m : ℂ)) + Complex.I * (2 * p - 1 : ℝ) * m.cA * (angleS m : ℂ))

theorem X7_red_rho_q (e : ℂ) (C S pA p q : ℝ) (cA c : ℂ) (hE : e * conj e = 1)
    (hCS : (C : ℂ) ^ 2 + (S : ℂ) ^ 2 = 1)
    (hq : (q : ℂ) = -Complex.I * (c * conj cA - conj c * cA) / 2) :
    reduced (X7_Umat e C S) (rho pA cA) (rho p c) =
      rho (pA + C ^ 2 * (p - pA) - 2 * S * C * q)
        (e * (c * C + Complex.I * (2 * p - 1 : ℝ) * cA * S)) := by
  ext i j
  cases i <;> cases j
  · simp [reduced, rho, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, X7_Umat, Matrix.conjTranspose_apply, hq]
    linear_combination ((p : ℂ) * pA) * hE + (pA - p * pA) * hCS +
      ((S : ℂ) ^ 2 * p * pA - (S : ℂ) ^ 2 * pA) * Complex.I_sq
  · simp [reduced, rho, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, X7_Umat, Matrix.conjTranspose_apply]
    ring
  · simp [reduced, rho, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, X7_Umat, Matrix.conjTranspose_apply, map_ofNat]
    ring
  · simp [reduced, rho, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, X7_Umat, Matrix.conjTranspose_apply, hq]
    linear_combination (1 - (p : ℂ) - pA + p * pA) * hE + (p - p * pA) * hCS +
      ((p : ℂ) * pA * (S : ℂ) ^ 2 - p * (S : ℂ) ^ 2) * Complex.I_sq

theorem X7_red_rho (e : ℂ) (C S pA p : ℝ) (cA c : ℂ) (hE : e * conj e = 1)
    (hCS : (C : ℂ) ^ 2 + (S : ℂ) ^ 2 = 1) :
    reduced (X7_Umat e C S) (rho pA cA) (rho p c) =
      rho (pA + C ^ 2 * (p - pA) - 2 * S * C * (c * conj cA).im)
        (e * (c * C + Complex.I * (2 * p - 1 : ℝ) * cA * S)) := by
  apply X7_red_rho_q _ _ _ _ _ _ _ _ hE hCS
  rw [X7_im_eq]; simp

theorem X7_pop_rho (p : ℝ) (c : ℂ) : population (rho p c) = p := by
  simp [population, rho]

theorem X7_coh_rho (p : ℝ) (c : ℂ) : coherence (rho p c) = c := rfl

theorem X7_collision_rho (m : Model) (p : ℝ) (c : ℂ) :
    collision m (rho p c) = rho (X7_pn m p c) (X7_cn m p c) := by
  have hE := X7_econj (m.frequency * m.duration)
  have hCS := X7_CS (2 * m.coupling * m.duration)
  have h4 : Real.sin (4 * m.coupling * m.duration) =
      2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) := by
    rw [← Real.sin_two_mul]; ring_nf
  unfold collision
  rw [X7_evolution_eq, X7_red_rho _ _ _ _ _ _ _ hE hCS]
  unfold X7_pn X7_cn angleC angleS
  rw [h4]

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

theorem X7_trajectory_rho (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) (n : ℕ) :
    trajectory m r n = rho (population (trajectory m r n)) (coherence (trajectory m r n)) := by
  induction n with
  | zero => exact X7_density_rho r hr
  | succ n ih =>
    have hs : trajectory m r (n + 1) = collision m (trajectory m r n) := by
      simp only [trajectory]
      rw [Function.iterate_succ_apply']
    rw [hs, ih, X7_collision_rho]
    simp [population, coherence, rho]

theorem X7_recurrence (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) (n : ℕ) :
    trajectory m r (n + 1) =
      rho (X7_pn m (population (trajectory m r n)) (coherence (trajectory m r n)))
        (X7_cn m (population (trajectory m r n)) (coherence (trajectory m r n))) := by
  have hs : trajectory m r (n + 1) = collision m (trajectory m r n) := by
    simp only [trajectory]
    rw [Function.iterate_succ_apply']
  rw [hs]
  conv_lhs => rw [X7_trajectory_rho m r hr n]
  rw [X7_collision_rho]

theorem X7_affine_rho (m : Model) (p : ℝ) (c : ℂ) :
    coordinates (rho (X7_pn m p c) (X7_cn m p c)) =
      (affineMatrix m).mulVec (coordinates (rho p c)) + affineOffset m := by
  have hCS := X7_CS (2 * m.coupling * m.duration)
  have h4 : Real.sin (4 * m.coupling * m.duration) =
      2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hq := X7_im_eq (c * conj m.cA)
  unfold coordinates affineMatrix affineOffset X7_pn X7_cn angleC angleS
  rw [X7_pop_rho, X7_coh_rho, X7_pop_rho, X7_coh_rho, h4]
  generalize Real.cos (2 * m.coupling * m.duration) = C at *
  generalize Real.sin (2 * m.coupling * m.duration) = S at *
  generalize Complex.exp (Complex.I * ((m.frequency * m.duration : ℝ) : ℂ)) = e
  generalize (c * conj m.cA).im = q at *
  funext k
  fin_cases k
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hq]
    linear_combination (-(m.pA : ℂ)) * hCS
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, map_ofNat]
    ring


theorem X7_rho_sub_DD (p q : ℝ) (c d : ℂ) :
    (rho p c - rho q d)ᴴ * (rho p c - rho q d) =
      algebraMap ℝ (Op Bool) ((p - q) ^ 2 + Complex.normSq (c - d)) := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  cases i <;> cases j <;>
    apply Complex.ext <;>
    simp [rho, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.normSq_apply, pow_two,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem X7_TD_rho (p q : ℝ) (c d : ℂ) :
    QAlgorithms.traceDistance (rho p c) (rho q d) =
      Real.sqrt ((p - q) ^ 2 + Complex.normSq (c - d)) := by
  unfold QAlgorithms.traceDistance QAlgorithms.traceNorm
  rw [X7_rho_sub_DD, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul,
    Matrix.trace_one]
  simp
  ring

theorem X7_coord_sub (a b : Op Bool) :
    coordinates (a - b) = coordinates a - coordinates b := by
  funext k
  fin_cases k <;> simp [coordinates, population, coherence]

theorem X7_wN_rho_sub (p q : ℝ) (c d : ℂ) :
    weightedNorm (coordinates (rho p c - rho q d)) =
      Real.sqrt ((p - q) ^ 2 + Complex.normSq (c - d)) := by
  rw [X7_coord_sub]
  unfold weightedNorm
  congr 1
  simp [coordinates, X7_pop_rho, X7_coh_rho, Complex.normSq_apply]
  ring

def X7_G (v : Fin 3 → ℂ) : ℝ :=
  Complex.normSq (v 0) + Complex.normSq (v 1) / 2 + Complex.normSq (v 2) / 2

theorem X7_G_nonneg (v : Fin 3 → ℂ) : 0 ≤ X7_G v := by
  unfold X7_G
  have := Complex.normSq_nonneg (v 0)
  have := Complex.normSq_nonneg (v 1)
  have := Complex.normSq_nonneg (v 2)
  linarith

theorem X7_poly (C S : ℝ) (a v0 v1 v2 : ℂ) :
    Complex.normSq ((C : ℂ) ^ 2 * v0 + Complex.I * S * C * (conj a * v1 - a * v2)) +
      Complex.normSq (2 * Complex.I * a * S * v0 + C * v1) / 2 +
      Complex.normSq (-2 * Complex.I * conj a * S * v0 + C * v2) / 2 =
    (1 - S ^ 2 * (1 - 4 * Complex.normSq a)) *
        (Complex.normSq v0 + Complex.normSq v1 / 2 + Complex.normSq v2 / 2) -
      (S ^ 2 * Complex.normSq (C * v0 - Complex.I * S * (a * v2 - conj a * v1)) +
        S ^ 2 * Complex.normSq (a * v2 + conj a * v1)) -
      (1 - C ^ 2 - S ^ 2) * ((Complex.normSq v0 + Complex.normSq v1 / 2 + Complex.normSq v2 / 2) +
        Complex.normSq (C * v0 - Complex.I * S * (a * v2 - conj a * v1))) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
    pow_two]
  norm_num
  ring

theorem X7_quad (m : Model) (v : Fin 3 → ℂ) :
    X7_G ((affineMatrix m).mulVec v) =
      (1 - angleS m ^ 2 * (1 - 4 * Complex.normSq m.cA)) * X7_G v -
      (angleS m ^ 2 * Complex.normSq (angleC m * v 0 -
          Complex.I * angleS m * (m.cA * v 2 - conj m.cA * v 1)) +
        angleS m ^ 2 * Complex.normSq (m.cA * v 2 + conj m.cA * v 1)) := by
  have hCS := Real.cos_sq_add_sin_sq (2 * m.coupling * m.duration)
  have h4 : Real.sin (4 * m.coupling * m.duration) =
      2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) := by
    rw [← Real.sin_two_mul]; ring_nf
  set e := Complex.exp (Complex.I * ((m.frequency * m.duration : ℝ) : ℂ)) with he
  have hne : Complex.normSq e = 1 := by
    rw [he, Complex.normSq_eq_norm_sq, mul_comm, Complex.norm_exp_ofReal_mul_I]; simp
  have hne' : Complex.normSq (conj e) = 1 := by rw [Complex.normSq_conj, hne]
  have r0 : (affineMatrix m).mulVec v 0 = ((angleC m : ℝ) : ℂ) ^ 2 * v 0 +
      Complex.I * (angleS m : ℂ) * (angleC m : ℂ) * (conj m.cA * v 1 - m.cA * v 2) := by
    simp [affineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h4, angleC, angleS]
    ring
  have r1 : (affineMatrix m).mulVec v 1 = e * (2 * Complex.I * m.cA * (angleS m : ℂ) * v 0 +
      (angleC m : ℂ) * v 1) := by
    simp [affineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, he]
    ring
  have r2 : (affineMatrix m).mulVec v 2 = conj e * (-2 * Complex.I * conj m.cA *
      (angleS m : ℂ) * v 0 + (angleC m : ℂ) * v 2) := by
    simp [affineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, he]
    ring
  unfold X7_G
  rw [r0, r1, r2, Complex.normSq_mul, Complex.normSq_mul, hne, hne', one_mul, one_mul,
    X7_poly]
  have hE : 1 - angleC m ^ 2 - angleS m ^ 2 = 0 := by
    unfold angleC angleS; linarith
  rw [hE, zero_mul, sub_zero]

theorem X7_R_nonneg (m : Model) : 0 ≤ 1 - angleS m ^ 2 * (1 - 4 * Complex.normSq m.cA) := by
  have hS : angleS m ^ 2 ≤ 1 := by
    unfold angleS; nlinarith [Real.sin_sq_add_cos_sq (2 * m.coupling * m.duration)]
  have := Complex.normSq_nonneg m.cA
  nlinarith

theorem X7_wN_le (m : Model) (v : Fin 3 → ℂ) :
    weightedNorm ((affineMatrix m).mulVec v) ≤ contractionRate m * weightedNorm v := by
  have hq := X7_quad m v
  have hle : X7_G ((affineMatrix m).mulVec v) ≤
      (1 - angleS m ^ 2 * (1 - 4 * Complex.normSq m.cA)) * X7_G v := by
    rw [hq]
    have : 0 ≤ angleS m ^ 2 * Complex.normSq (angleC m * v 0 -
          Complex.I * angleS m * (m.cA * v 2 - conj m.cA * v 1)) +
        angleS m ^ 2 * Complex.normSq (m.cA * v 2 + conj m.cA * v 1) :=
      add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
        (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
    linarith
  unfold weightedNorm contractionRate
  rw [← Real.sqrt_mul (X7_R_nonneg m)]
  exact Real.sqrt_le_sqrt hle

theorem X7_induced (m : Model) : weightedInducedNorm (affineMatrix m) = contractionRate m := by
  have hr0 : 0 ≤ contractionRate m := Real.sqrt_nonneg _
  have hub : ∀ x : Fin 3 → ℂ,
      weightedNorm ((affineMatrix m).mulVec x) / weightedNorm x ≤ contractionRate m := by
    intro x
    change Real.sqrt (X7_G _) / Real.sqrt (X7_G x) ≤ _
    rcases (Real.sqrt_nonneg (X7_G x)).lt_or_eq with h | h
    · rw [div_le_iff₀ h]
      exact X7_wN_le m x
    · rw [← h, div_zero]; exact hr0
  -- witness
  have hwit : ∃ x : Fin 3 → ℂ, 0 < X7_G x ∧
      angleS m ^ 2 * Complex.normSq (angleC m * x 0 -
          Complex.I * angleS m * (m.cA * x 2 - conj m.cA * x 1)) +
        angleS m ^ 2 * Complex.normSq (m.cA * x 2 + conj m.cA * x 1) = 0 := by
    by_cases ha : m.cA = 0
    · refine ⟨![0, 1, 0], ?_, ?_⟩
      · simp [X7_G]
      · simp [ha]
    · have hq : 0 < Complex.normSq m.cA := Complex.normSq_pos.2 ha
      have hconj : conj m.cA * m.cA = (Complex.normSq m.cA : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]
      refine ⟨![2 * (angleS m : ℂ) * (Complex.normSq m.cA : ℂ),
        Complex.I * (angleC m : ℂ) * m.cA, -Complex.I * (angleC m : ℂ) * conj m.cA], ?_, ?_⟩
      · have hCS : angleC m ^ 2 + angleS m ^ 2 = 1 := by
          unfold angleC angleS; exact Real.cos_sq_add_sin_sq _
        simp only [X7_G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, Complex.normSq_mul, Complex.normSq_ofReal,
          Complex.normSq_I, Complex.normSq_neg, Complex.normSq_conj, Complex.normSq_ofNat]
        have hpos : 0 < 4 * angleS m ^ 2 * Complex.normSq m.cA + angleC m ^ 2 := by
          rcases le_or_gt (4 * Complex.normSq m.cA) 1 with h | h
          · nlinarith [sq_nonneg (angleC m), sq_nonneg (angleS m)]
          · nlinarith [sq_nonneg (angleC m), sq_nonneg (angleS m)]
        nlinarith [mul_pos hq hpos]
      · have e1 : (angleC m : ℂ) * (2 * (angleS m : ℂ) * (Complex.normSq m.cA : ℂ)) -
            Complex.I * (angleS m : ℂ) * (m.cA * (-Complex.I * (angleC m : ℂ) * conj m.cA) -
              conj m.cA * (Complex.I * (angleC m : ℂ) * m.cA)) = 0 := by
          linear_combination (-2 * (angleS m : ℂ) * (angleC m : ℂ)) * hconj +
            (2 * (angleS m : ℂ) * (angleC m : ℂ) * conj m.cA * m.cA) * Complex.I_sq
        have e2 : m.cA * (-Complex.I * (angleC m : ℂ) * conj m.cA) +
            conj m.cA * (Complex.I * (angleC m : ℂ) * m.cA) = 0 := by ring
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [e1, e2]; simp
  obtain ⟨x, hx, hx0⟩ := hwit
  have hval : weightedNorm ((affineMatrix m).mulVec x) / weightedNorm x = contractionRate m := by
    unfold weightedNorm contractionRate
    have := X7_quad m x
    rw [hx0, sub_zero] at this
    change Real.sqrt (X7_G _) / Real.sqrt (X7_G x) = _
    rw [this, Real.sqrt_mul (X7_R_nonneg m)]
    field_simp [(Real.sqrt_pos.2 hx).ne']
  unfold weightedInducedNorm
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hval⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hub y

theorem X7_coords_traj (m : Model) (s r : Op Bool) (hs : IsDensityMatrix s)
    (hr : IsDensityMatrix r) (hfix : collision m s = s) (n : ℕ) :
    coordinates (trajectory m r n - s) = ((affineMatrix m) ^ n).mulVec (coordinates (r - s)) := by
  have hsc : coordinates s = (affineMatrix m).mulVec (coordinates s) + affineOffset m := by
    have h := X7_density_rho s hs
    conv_lhs => rw [← hfix, h, X7_collision_rho]
    rw [X7_affine_rho, ← h]
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    have hstep : coordinates (trajectory m r (n + 1)) =
        (affineMatrix m).mulVec (coordinates (trajectory m r n)) + affineOffset m := by
      rw [X7_recurrence m r hr n]
      conv_rhs => rw [X7_trajectory_rho m r hr n]
      exact X7_affine_rho m _ _
    rw [X7_coord_sub] at ih ⊢
    rw [hstep, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
    conv_lhs => rw [hsc]
    rw [Matrix.mulVec_sub]
    abel

theorem X7_TD_traj (m : Model) (s r : Op Bool) (hs : IsDensityMatrix s)
    (hr : IsDensityMatrix r) (n : ℕ) :
    QAlgorithms.traceDistance s (trajectory m r n) =
      weightedNorm (coordinates (trajectory m r n - s)) := by
  rw [X7_density_rho s hs, X7_trajectory_rho m r hr n, X7_TD_rho, X7_wN_rho_sub]
  congr 1
  rw [← Complex.normSq_neg (coherence s - _), neg_sub]
  ring

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (s r : Op Bool)
    (hs : IsDensityMatrix s) (hr : IsDensityMatrix r) (hfix : collision m s = s) :
    weightedInducedNorm (affineMatrix m) = contractionRate m ∧
    (∀ n : ℕ,
      traceDistance s (trajectory m r n) =
        Real.sqrt ((population (trajectory m r n) - population s) ^ 2 +
          Complex.normSq (coherence (trajectory m r n) - coherence s)) ∧
      traceDistance s (trajectory m r n) =
        weightedNorm (((affineMatrix m) ^ n).mulVec (coordinates (r - s))) ∧
      traceDistance s (trajectory m r n) ≤ contractionRate m ^ n * traceDistance s r) := by
  refine ⟨X7_induced m, fun n => ⟨?_, ?_, ?_⟩⟩
  · rw [X7_density_rho s hs, X7_trajectory_rho m r hr n, X7_TD_rho, X7_pop_rho, X7_pop_rho,
      X7_coh_rho, X7_coh_rho]
    congr 1
    rw [← Complex.normSq_neg (coherence s - _), neg_sub]
    ring
  · rw [X7_TD_traj m s r hs hr n, X7_coords_traj m s r hs hr hfix n]
  · rw [X7_TD_traj m s r hs hr n, X7_coords_traj m s r hs hr hfix n]
    have h0 : traceDistance s r = weightedNorm (coordinates (r - s)) := by
      have := X7_TD_traj m s r hs hr 0
      simpa [trajectory] using this
    rw [h0]
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      calc weightedNorm ((affineMatrix m).mulVec (((affineMatrix m) ^ k).mulVec _))
          ≤ contractionRate m * weightedNorm (((affineMatrix m) ^ k).mulVec _) := X7_wN_le m _
        _ ≤ contractionRate m * (contractionRate m ^ k * weightedNorm (coordinates (r - s))) :=
            mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _)
        _ = contractionRate m ^ (k + 1) * weightedNorm (coordinates (r - s)) := by ring

end
