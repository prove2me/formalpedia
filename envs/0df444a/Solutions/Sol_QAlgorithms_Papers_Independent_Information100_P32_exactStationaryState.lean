-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.exactStationaryState
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:43:38.234417+00:00
-- url     : https://prove2.me/submissions/c6b316ef-fc79-4009-83bc-cbad5f800929

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

open ComplexOrder in
theorem X7_rho_density' (p : ℝ) (c : ℂ) (hp : 0 < p) (hph : Physical p c) :
    IsDensityMatrix (rho p c) := by
  obtain ⟨-, -, hq⟩ := hph
  set d := p * (1 - p) - Complex.normSq c with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  let A : Op Bool := Matrix.of fun i j => if i then (if j then ((Real.sqrt (d / p) : ℝ) : ℂ) else 0)
    else (if j then c / ((Real.sqrt p : ℝ) : ℂ) else ((Real.sqrt p : ℝ) : ℂ))
  have hsp : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hp).ne'
  have hs2 : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
  have hs3 : ((Real.sqrt (d / p) : ℝ) : ℂ) * ((Real.sqrt (d / p) : ℝ) : ℂ) = ((d / p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hd0 hp.le)]
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hnc : conj c * c = (Complex.normSq c : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
  have hA : Aᴴ * A = rho p c := by
    ext i j
    cases i <;> cases j <;>
      simp only [A, rho, Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply,
        Matrix.of_apply, if_true, if_false, Bool.false_eq_true, star_zero, zero_mul, add_zero,
        mul_zero, zero_add, RCLike.star_def, Complex.conj_ofReal, map_div₀, map_zero]
    · exact hs2
    · field_simp
    · field_simp
    · rw [hs3]
      have e : conj c / ((Real.sqrt p : ℝ) : ℂ) * (c / ((Real.sqrt p : ℝ) : ℂ)) =
          (Complex.normSq c : ℂ) / p := by
        rw [← hnc, ← hs2]; field_simp
      rw [e, hd]; push_cast; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [← hA]; exact Matrix.posSemidef_conjTranspose_mul_self A
  · simp [rho, Matrix.trace]


open ComplexOrder in
theorem X7_phys_density (p : ℝ) (c : ℂ) (hph : Physical p c) : IsDensityMatrix (rho p c) := by
  rcases hph.1.lt_or_eq with hp | hp
  · exact X7_rho_density' p c hp hph
  · subst hp
    have hc : c = 0 := by
      have h := hph.2.2
      simp at h
      exact Complex.normSq_eq_zero.1 (le_antisymm h (Complex.normSq_nonneg c))
    subst hc
    let A : Op Bool := Matrix.of fun i j => if i ∧ j then 1 else 0
    have hA : Aᴴ * A = rho 0 0 := by
      ext i j
      cases i <;> cases j <;>
        simp [A, rho, Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply]
    refine ⟨?_, ?_⟩
    · rw [← hA]; exact Matrix.posSemidef_conjTranspose_mul_self A
    · simp [rho, Matrix.trace]

theorem X7_coords_traj' (m : Model) (ps : ℝ) (cs : ℂ) (r : Op Bool)
    (hr : IsDensityMatrix r) (hfix : collision m (rho ps cs) = rho ps cs) (n : ℕ) :
    coordinates (trajectory m r n - rho ps cs) =
      ((affineMatrix m) ^ n).mulVec (coordinates (r - rho ps cs)) := by
  have hsc : coordinates (rho ps cs) =
      (affineMatrix m).mulVec (coordinates (rho ps cs)) + affineOffset m := by
    conv_lhs => rw [← hfix, X7_collision_rho]
    rw [X7_affine_rho]
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

theorem X7_G_smul (c : ℂ) (v : Fin 3 → ℂ) : X7_G (c • v) = Complex.normSq c * X7_G v := by
  simp [X7_G, Complex.normSq_mul]; ring

def X7_Δ (m : Model) (v : Fin 3 → ℂ) : ℝ :=
  angleS m ^ 2 * Complex.normSq (angleC m * v 0 -
          Complex.I * angleS m * (m.cA * v 2 - conj m.cA * v 1)) +
        angleS m ^ 2 * Complex.normSq (m.cA * v 2 + conj m.cA * v 1)

theorem X7_Δ_nonneg (m : Model) (v : Fin 3 → ℂ) : 0 ≤ X7_Δ m v :=
  add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))

def X7_R (m : Model) : ℝ := 1 - angleS m ^ 2 * (1 - 4 * Complex.normSq m.cA)

theorem X7_R_le (m : Model) : X7_R m ≤ 1 := by
  have hq : Complex.normSq m.cA ≤ 1 / 4 := by
    have h := m.ancilla_physical.2.2
    nlinarith [sq_nonneg (m.pA - 1 / 2)]
  unfold X7_R; nlinarith [sq_nonneg (angleS m)]

theorem X7_quad' (m : Model) (v : Fin 3 → ℂ) :
    X7_G ((affineMatrix m).mulVec v) = X7_R m * X7_G v - X7_Δ m v := X7_quad m v

theorem X7_step_le (m : Model) (v : Fin 3 → ℂ) : X7_G ((affineMatrix m).mulVec v) ≤ X7_G v := by
  rw [X7_quad']
  have := X7_Δ_nonneg m v
  have := X7_R_le m
  have := X7_G_nonneg v
  nlinarith

theorem X7_two_lt (m : Model) (hS : angleS m ≠ 0) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    X7_G ((affineMatrix m).mulVec ((affineMatrix m).mulVec v)) < X7_G v := by
  have hGpos : 0 < X7_G v := by
    by_contra hcon
    push_neg at hcon
    have h0 := le_antisymm hcon (X7_G_nonneg v)
    apply hv
    unfold X7_G at h0
    have a0 := Complex.normSq_nonneg (v 0)
    have a1 := Complex.normSq_nonneg (v 1)
    have a2 := Complex.normSq_nonneg (v 2)
    have e0 : v 0 = 0 := Complex.normSq_eq_zero.1 (by linarith)
    have e1 : v 1 = 0 := Complex.normSq_eq_zero.1 (by linarith)
    have e2 : v 2 = 0 := Complex.normSq_eq_zero.1 (by linarith)
    funext k; fin_cases k <;> simp [e0, e1, e2]
  have h2 : X7_G ((affineMatrix m).mulVec ((affineMatrix m).mulVec v)) =
      X7_R m * (X7_R m * X7_G v - X7_Δ m v) - X7_Δ m ((affineMatrix m).mulVec v) := by
    rw [X7_quad', X7_quad']
  have hR0 : 0 ≤ X7_R m := X7_R_nonneg m
  have hR1 := X7_R_le m
  have hd1 := X7_Δ_nonneg m v
  have hd2 := X7_Δ_nonneg m ((affineMatrix m).mulVec v)
  rcases hR1.lt_or_eq with hlt | heq
  · rw [h2]
    nlinarith [mul_nonneg hR0 hd1, mul_nonneg (mul_nonneg hR0 (sub_nonneg.2 hR1)) hGpos.le,
      mul_pos (sub_pos.2 hlt) hGpos]
  · -- the pure-ancilla case q = 1/4
    rw [h2, heq]
    have hS2 : 0 < angleS m ^ 2 := by positivity
    have hq : Complex.normSq m.cA = 1 / 4 := by
      unfold X7_R at heq
      have : angleS m ^ 2 * (1 - 4 * Complex.normSq m.cA) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hS2.ne'
      · linarith
    suffices hpos : 0 < X7_Δ m v + X7_Δ m ((affineMatrix m).mulVec v) by linarith
    by_contra hcon
    push_neg at hcon
    have z1 : X7_Δ m v = 0 := by linarith
    have z2 : X7_Δ m ((affineMatrix m).mulVec v) = 0 := by linarith
    unfold X7_Δ at z1 z2
    have n1 := Complex.normSq_nonneg (angleC m * v 0 -
          Complex.I * angleS m * (m.cA * v 2 - conj m.cA * v 1))
    have n2 := Complex.normSq_nonneg (m.cA * v 2 + conj m.cA * v 1)
    set w := (affineMatrix m).mulVec v with hw
    have n3 := Complex.normSq_nonneg (angleC m * w 0 -
          Complex.I * angleS m * (m.cA * w 2 - conj m.cA * w 1))
    have n4 := Complex.normSq_nonneg (m.cA * w 2 + conj m.cA * w 1)
    have q1 : angleC m * v 0 - Complex.I * angleS m * (m.cA * v 2 - conj m.cA * v 1) = 0 :=
      Complex.normSq_eq_zero.1 (by nlinarith)
    have q2 : m.cA * v 2 + conj m.cA * v 1 = 0 := Complex.normSq_eq_zero.1 (by nlinarith)
    have q3 : angleC m * w 0 - Complex.I * angleS m * (m.cA * w 2 - conj m.cA * w 1) = 0 :=
      Complex.normSq_eq_zero.1 (by nlinarith)
    have q4 : m.cA * w 2 + conj m.cA * w 1 = 0 := Complex.normSq_eq_zero.1 (by nlinarith)
    have h4 : Real.sin (4 * m.coupling * m.duration) =
        2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) := by
      rw [← Real.sin_two_mul]; ring_nf
    set e := Complex.exp (Complex.I * ((m.frequency * m.duration : ℝ) : ℂ)) with he
    have hne : e ≠ 0 := Complex.exp_ne_zero _
    have hcne : conj e ≠ 0 := by rw [map_ne_zero]; exact hne
    have w0 : w 0 = ((angleC m : ℝ) : ℂ) ^ 2 * v 0 +
        Complex.I * (angleS m : ℂ) * (angleC m : ℂ) * (conj m.cA * v 1 - m.cA * v 2) := by
      simp [w, affineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h4, angleC, angleS]
      ring
    have w1 : w 1 = e * (2 * Complex.I * m.cA * (angleS m : ℂ) * v 0 +
        (angleC m : ℂ) * v 1) := by
      simp [w, affineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, he]
      ring
    have w2 : w 2 = conj e * (-2 * Complex.I * conj m.cA *
        (angleS m : ℂ) * v 0 + (angleC m : ℂ) * v 2) := by
      simp [w, affineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, he]
      ring
    have hSc : (angleS m : ℂ) ≠ 0 := by exact_mod_cast hS
    have ha : m.cA ≠ 0 := by
      intro h; rw [h] at hq; simp at hq
    have hac : conj m.cA ≠ 0 := by rw [map_ne_zero]; exact ha
    have hqc : conj m.cA * m.cA = 1 / 4 := by
      rw [← Complex.normSq_eq_conj_mul_self, hq]; push_cast; ring
    have hCS : ((angleC m : ℝ) : ℂ) ^ 2 + ((angleS m : ℝ) : ℂ) ^ 2 = 1 := by
      unfold angleC angleS; exact X7_CS _
    -- w0 = 0
    have hw0 : w 0 = 0 := by
      rw [w0]
      have : m.cA * v 2 = -(conj m.cA * v 1) := by linear_combination q2
      linear_combination (angleC m : ℂ) * q1
    rw [hw0] at q3
    have hd : m.cA * w 2 - conj m.cA * w 1 = 0 := by
      have : Complex.I * (angleS m : ℂ) * (m.cA * w 2 - conj m.cA * w 1) = 0 := by
        linear_combination -q3
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero Complex.I_ne_zero hSc)
      · exact h
    have hw1z : conj m.cA * w 1 = 0 := by linear_combination (q4 - hd) / 2
    have hw1 : w 1 = 0 := by
      rcases mul_eq_zero.1 hw1z with h | h
      · exact absurd h hac
      · exact h
    have hA : 2 * Complex.I * m.cA * (angleS m : ℂ) * v 0 + (angleC m : ℂ) * v 1 = 0 := by
      rw [w1] at hw1
      rcases mul_eq_zero.1 hw1 with h | h
      · exact absurd h hne
      · exact h
    -- set u := conj cA * v1
    have hB : (angleC m : ℂ) * v 0 = -2 * Complex.I * (angleS m : ℂ) * (conj m.cA * v 1) := by
      have : m.cA * v 2 = -(conj m.cA * v 1) := by linear_combination q2
      linear_combination q1 + Complex.I * (angleS m : ℂ) * this
    have hA' : (angleC m : ℂ) * (conj m.cA * v 1) =
        -2 * Complex.I * (angleS m : ℂ) * (1 / 4) * v 0 := by
      linear_combination conj m.cA * hA - (2 * Complex.I * (angleS m : ℂ) * v 0) * hqc
    have hv0 : v 0 = 0 := by
      have : v 0 * (((angleC m : ℝ) : ℂ) ^ 2 + ((angleS m : ℝ) : ℂ) ^ 2) = 0 := by
        linear_combination (angleC m : ℂ) * hB -
          (2 * Complex.I * (angleS m : ℂ)) * hA' + ((angleS m : ℂ) ^ 2 * v 0) * Complex.I_sq
      rw [hCS, mul_one] at this; exact this
    have hu : conj m.cA * v 1 = 0 := by
      rw [hv0, mul_zero] at hB
      have : (-2 * Complex.I * (angleS m : ℂ)) * (conj m.cA * v 1) = 0 := by
        linear_combination -hB
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by
          refine mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hSc)
      · exact h
    have hv1 : v 1 = 0 := by
      rcases mul_eq_zero.1 hu with h | h
      · exact absurd h hac
      · exact h
    have hv2 : v 2 = 0 := by
      have : m.cA * v 2 = 0 := by rw [hv1] at q2; simpa using q2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha
      · exact h
    exact absurd (by funext k; fin_cases k <;> simp [hv0, hv1, hv2]) hv

theorem X7_lambda (m : Model) (hS : angleS m ≠ 0) : ∃ l : ℝ, 0 ≤ l ∧ l < 1 ∧
    ∀ v, X7_G ((affineMatrix m).mulVec ((affineMatrix m).mulVec v)) ≤ l * X7_G v := by
  set Ksph : Set (Fin 3 → ℂ) := {v | X7_G v = 1}
  have hcontG : Continuous X7_G := by
    unfold X7_G; fun_prop
  have hcont2 : Continuous fun v : Fin 3 → ℂ =>
      X7_G ((affineMatrix m).mulVec ((affineMatrix m).mulVec v)) :=
    hcontG.comp ((Matrix.mulVecLin (affineMatrix m)).continuous_of_finiteDimensional.comp
      (Matrix.mulVecLin (affineMatrix m)).continuous_of_finiteDimensional)
  have hclosed : IsClosed Ksph := isClosed_eq hcontG continuous_const
  have hbdd : Bornology.IsBounded Ksph := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2, fun v hv => ?_⟩
    simp only [Ksph, Set.mem_setOf_eq] at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    have hi : Complex.normSq (v i) ≤ 2 := by
      unfold X7_G at hv
      have a0 := Complex.normSq_nonneg (v 0)
      have a1 := Complex.normSq_nonneg (v 1)
      have a2 := Complex.normSq_nonneg (v 2)
      fin_cases i <;> simp <;> linarith
    have : ‖v i‖ ^ 2 ≤ 2 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; linarith
    nlinarith [norm_nonneg (v i), this]
  have hcpt : IsCompact Ksph := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : Ksph.Nonempty := ⟨![1, 0, 0], by simp [Ksph, X7_G]⟩
  obtain ⟨v0, hv0K, hmax⟩ := hcpt.exists_isMaxOn hne hcont2.continuousOn
  set l := X7_G ((affineMatrix m).mulVec ((affineMatrix m).mulVec v0))
  have hv0ne : v0 ≠ 0 := by
    intro h; simp [Ksph, h, X7_G] at hv0K
  have hl1 : l < 1 := by
    have := X7_two_lt m hS v0 hv0ne
    simp only [Ksph, Set.mem_setOf_eq] at hv0K
    rw [hv0K] at this; exact this
  refine ⟨l, X7_G_nonneg _, hl1, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp [X7_G]
  · have hGpos : 0 < X7_G v := by
      have := X7_two_lt m hS v hv
      have := X7_G_nonneg ((affineMatrix m).mulVec ((affineMatrix m).mulVec v))
      linarith
    set t := Real.sqrt (X7_G v)
    have ht : 0 < t := Real.sqrt_pos.2 hGpos
    have ht2 : t ^ 2 = X7_G v := Real.sq_sqrt hGpos.le
    set w := ((t⁻¹ : ℝ) : ℂ) • v
    have hwK : w ∈ Ksph := by
      simp only [Ksph, Set.mem_setOf_eq, w, X7_G_smul, Complex.normSq_ofReal]
      rw [← ht2]; field_simp
    have := hmax hwK
    simp only [Set.mem_setOf_eq] at this
    simp only [w, Matrix.mulVec_smul, X7_G_smul, Complex.normSq_ofReal] at this
    have hinv : 0 < t⁻¹ * t⁻¹ := by positivity
    have : X7_G ((affineMatrix m).mulVec ((affineMatrix m).mulVec v)) ≤ l * t ^ 2 := by
      have e : t⁻¹ * t⁻¹ * (l * t ^ 2) = l := by field_simp
      nlinarith
    rw [ht2] at this; exact this

theorem X7_G_tendsto (m : Model) (hS : angleS m ≠ 0) (v : Fin 3 → ℂ) :
    Tendsto (fun n => X7_G (((affineMatrix m) ^ n).mulVec v)) atTop (𝓝 0) := by
  obtain ⟨l, hl0, hl1, hl⟩ := X7_lambda m hS
  have hbound : ∀ n, X7_G (((affineMatrix m) ^ n).mulVec v) ≤ l ^ (n / 2) * X7_G v := by
    have hk : ∀ k, X7_G (((affineMatrix m) ^ (2 * k)).mulVec v) ≤ l ^ k * X7_G v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ', pow_succ', ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec]
        calc _ ≤ l * X7_G (((affineMatrix m) ^ (2 * k)).mulVec v) := hl _
          _ ≤ l * (l ^ k * X7_G v) := mul_le_mul_of_nonneg_left ih hl0
          _ = l ^ (k + 1) * X7_G v := by ring
    intro n
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [show 2 * k / 2 = k by omega]; exact hk k
    · rw [show (2 * k + 1) / 2 = k by omega, pow_succ', ← Matrix.mulVec_mulVec]
      exact (X7_step_le m _).trans (hk k)
  have hlim : Tendsto (fun n : ℕ => l ^ (n / 2) * X7_G v) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hl1).comp
      (Nat.tendsto_div_const_atTop (n := 2) (by norm_num))
    simpa using this.mul_const (X7_G v)
  exact squeeze_zero (fun n => X7_G_nonneg _) hbound hlim

theorem X7_G_rho_sub (p q : ℝ) (c d : ℂ) :
    X7_G (coordinates (rho p c - rho q d)) = (p - q) ^ 2 + Complex.normSq (c - d) := by
  rw [X7_coord_sub]
  simp [X7_G, coordinates, X7_pop_rho, X7_coh_rho, Complex.normSq_apply]
  ring

theorem X7_rho_tendsto {ι : Type*} {F : Filter ι} (p : ι → ℝ) (c : ι → ℂ) (p0 : ℝ) (c0 : ℂ)
    (hp : Tendsto p F (𝓝 p0)) (hc : Tendsto c F (𝓝 c0)) :
    Tendsto (fun i => rho (p i) (c i)) F (𝓝 (rho p0 c0)) := by
  have hp' : Tendsto (fun i => ((p i : ℝ) : ℂ)) F (𝓝 (p0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hp
  have hp'' : Tendsto (fun i => ((1 - p i : ℝ) : ℂ)) F (𝓝 ((1 - p0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hp)
  have hc' : Tendsto (fun i => conj (c i)) F (𝓝 (conj c0)) :=
    (Complex.continuous_conj.tendsto _).comp hc
  refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
  cases a <;> cases b
  · exact hp'
  · exact hc
  · exact hc'
  · exact hp''

theorem X7_starCoh_mul (m : Model) :
    starCoherence m * conj m.cA =
      ((-(Complex.normSq m.cA) / denominatorK m * (2 * m.pA - 1) * angleS m *
          Real.sin (m.frequency * m.duration) : ℝ) : ℂ) +
      ((-(Complex.normSq m.cA) / denominatorK m * (2 * m.pA - 1) * angleS m *
          differenceL m : ℝ) : ℂ) * Complex.I := by
  unfold starCoherence
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  ring

theorem X7_star_fixed (m : Model) (hK : 0 < denominatorK m) (hS : angleS m ≠ 0) :
    collision m (starState m) = starState m := by
  unfold starState
  rw [X7_collision_rho]
  have hKne : denominatorK m ≠ 0 := hK.ne'
  have hKc : (denominatorK m : ℂ) ≠ 0 := by exact_mod_cast hKne
  have hCS := Real.cos_sq_add_sin_sq (2 * m.coupling * m.duration)
  have hcs2 := Real.cos_sq_add_sin_sq (m.frequency * m.duration)
  congr 1
  · -- population
    unfold X7_pn
    have h4 : Real.sin (4 * m.coupling * m.duration) =
        2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) := by
      rw [← Real.sin_two_mul]; ring_nf
    have hm : (starCoherence m * conj m.cA).im =
        -(Complex.normSq m.cA) / denominatorK m * (2 * m.pA - 1) * angleS m * differenceL m := by
      rw [X7_starCoh_mul]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      ring
    rw [hm, h4]
    unfold starPopulation angleC angleS at *
    linear_combination (2 * Complex.normSq m.cA / denominatorK m * (2 * m.pA - 1) *
      Real.cos (2 * m.coupling * m.duration) * differenceL m) * hCS
  · -- coherence
    have hx : Complex.ofReal (2 * starPopulation m - 1) =
        Complex.ofReal (2 * m.pA - 1) * (Complex.ofReal (differenceL m) ^ 2 +
          Complex.ofReal (Real.sin (m.frequency * m.duration)) ^ 2) /
          Complex.ofReal (denominatorK m) := by
      have hK2 : denominatorK m + 4 * Complex.normSq m.cA * angleC m * differenceL m =
          differenceL m ^ 2 + Real.sin (m.frequency * m.duration) ^ 2 := by
        unfold denominatorK denominatorD; ring
      have hxr : (2 * starPopulation m - 1) =
          (2 * m.pA - 1) * (differenceL m ^ 2 + Real.sin (m.frequency * m.duration) ^ 2) /
            denominatorK m := by
        rw [← hK2, eq_div_iff hKne]
        unfold starPopulation
        field_simp
        ring
      rw [hxr]
      push_cast
      ring
    unfold X7_cn starCoherence
    rw [hx]
    have he' : Complex.exp (Complex.I * Complex.ofReal (m.frequency * m.duration)) =
        Complex.ofReal (Real.cos (m.frequency * m.duration)) +
        Complex.ofReal (Real.sin (m.frequency * m.duration)) * Complex.I := by
      rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [he']
    have hL : Complex.ofReal (differenceL m) =
        Complex.ofReal (angleC m) - Complex.ofReal (Real.cos (m.frequency * m.duration)) := by
      unfold differenceL; push_cast; ring
    rw [hL]
    have hcs2c : Complex.ofReal (Real.cos (m.frequency * m.duration)) ^ 2 +
        Complex.ofReal (Real.sin (m.frequency * m.duration)) ^ 2 = 1 := X7_CS _
    generalize Complex.ofReal (Real.cos (m.frequency * m.duration)) = co at *
    generalize Complex.ofReal (Real.sin (m.frequency * m.duration)) = si at *
    generalize Complex.ofReal (angleC m) = C at *
    generalize Complex.ofReal (angleS m) = S at *
    generalize Complex.ofReal (2 * m.pA - 1) = x at *
    generalize hKdef : Complex.ofReal (denominatorK m) = K at *
    linear_combination (-(m.cA / K * x * S) * (si + Complex.I * (C - co))) * hcs2c +
      (-co * si * m.cA / K * x * S * C + co ^ 2 * si * m.cA / K * x * S +
        si ^ 3 * m.cA / K * x * S) * Complex.I_sq

theorem X7_phys_alg (C S co si q x : ℝ) (hCS : C ^ 2 + S ^ 2 = 1) (hcs : co ^ 2 + si ^ 2 = 1)
    (hq0 : 0 ≤ q) (hx : x ^ 2 ≤ 1 - 4 * q) :
    x ^ 2 * ((C - co) ^ 2 + si ^ 2) * (((C - co) ^ 2 + si ^ 2) + 4 * q * S ^ 2) ≤
      (((C - co) ^ 2 + si ^ 2) - 4 * q * C * (C - co)) ^ 2 := by
  set D := (C - co) ^ 2 + si ^ 2 with hD
  have hid : (D - 4 * q * C * (C - co)) ^ 2 - (1 - 4 * q) * D * (D + 4 * q * S ^ 2) =
      16 * q ^ 2 * (C ^ 2 * (C - co) ^ 2 + S ^ 2 * D) := by
    rw [hD]
    linear_combination (4 * q * ((C - co) ^ 2 + si ^ 2)) * hcs -
      (4 * q * ((C - co) ^ 2 + si ^ 2)) * hCS
  have hD0 : 0 ≤ D := by positivity
  have hDD : 0 ≤ D * (D + 4 * q * S ^ 2) := by positivity
  have h16 : 0 ≤ 16 * q ^ 2 * (C ^ 2 * (C - co) ^ 2 + S ^ 2 * D) := by positivity
  nlinarith

theorem X7_star_phys (m : Model) (hK : 0 < denominatorK m) :
    Physical (starPopulation m) (starCoherence m) := by
  have hKne : denominatorK m ≠ 0 := hK.ne'
  set q := Complex.normSq m.cA
  set x := 2 * m.pA - 1
  set D := differenceL m ^ 2 + Real.sin (m.frequency * m.duration) ^ 2 with hD
  have hK2 : denominatorK m = D - 4 * q * angleC m * differenceL m := by
    unfold denominatorK denominatorD; rfl
  have hxs : 2 * starPopulation m - 1 = x * D / denominatorK m := by
    rw [eq_div_iff hKne]
    unfold starPopulation
    field_simp
    rw [hK2]
    ring
  have hc : starCoherence m = -(m.cA * ((x * angleS m / denominatorK m : ℝ) : ℂ)) *
      ((Real.sin (m.frequency * m.duration) : ℂ) + (differenceL m : ℂ) * Complex.I) := by
    unfold starCoherence
    simp only [x]
    push_cast
    ring
  have hnc : Complex.normSq (starCoherence m) =
      q * (x * angleS m / denominatorK m) ^ 2 * D := by
    rw [hc, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_add_mul_I]
    rw [hD]; ring
  have hqx : x ^ 2 ≤ 1 - 4 * q := by
    have h := m.ancilla_physical.2.2
    simp only [x, q] at *
    nlinarith
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have halg := X7_phys_alg (angleC m) (angleS m) (Real.cos (m.frequency * m.duration))
    (Real.sin (m.frequency * m.duration)) q x
    (by unfold angleC angleS; exact Real.cos_sq_add_sin_sq _)
    (Real.cos_sq_add_sin_sq _) hq0 hqx
  have hL : differenceL m = angleC m - Real.cos (m.frequency * m.duration) := rfl
  rw [← hL] at halg
  rw [← hD, ← hK2] at halg
  -- key: 4 * normSq c* ≤ 1 - (2p*-1)^2
  have hK2pos : 0 < denominatorK m ^ 2 := by positivity
  have key : 4 * Complex.normSq (starCoherence m) ≤ 1 - (2 * starPopulation m - 1) ^ 2 := by
    rw [hnc, hxs]
    have e1 : 4 * (q * (x * angleS m / denominatorK m) ^ 2 * D) =
        (4 * q * x ^ 2 * angleS m ^ 2 * D) / denominatorK m ^ 2 := by
      field_simp
    have e2 : 1 - (x * D / denominatorK m) ^ 2 =
        (denominatorK m ^ 2 - x ^ 2 * D ^ 2) / denominatorK m ^ 2 := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hK2pos.le
    nlinarith
  have hn0 := Complex.normSq_nonneg (starCoherence m)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hK : 0 < denominatorK m) (hS : angleS m ≠ 0) :
    IsDensityMatrix (starState m) ∧ collision m (starState m) = starState m ∧
    (∀ r, IsDensityMatrix r → collision m r = r → r = starState m) ∧
    (∀ r, IsDensityMatrix r → Tendsto (trajectory m r) atTop (𝓝 (starState m))) := by
  have hfix := X7_star_fixed m hK hS
  have hdens : IsDensityMatrix (starState m) := X7_phys_density _ _ (X7_star_phys m hK)
  have hconv : ∀ r, IsDensityMatrix r → Tendsto (trajectory m r) atTop (𝓝 (starState m)) := by
    intro r hr
    set ps := starPopulation m
    set cs := starCoherence m
    have hst : starState m = rho ps cs := rfl
    rw [hst] at hfix ⊢
    have hG := X7_G_tendsto m hS (coordinates (r - rho ps cs))
    have hGn : Tendsto (fun n => (population (trajectory m r n) - ps) ^ 2 +
        Complex.normSq (coherence (trajectory m r n) - cs)) atTop (𝓝 0) := by
      refine hG.congr fun n => ?_
      rw [← X7_coords_traj' m ps cs r hr hfix n]
      conv_lhs => rw [X7_trajectory_rho m r hr n]
      rw [X7_G_rho_sub]
    have hsq : Tendsto (fun n => Real.sqrt ((population (trajectory m r n) - ps) ^ 2 +
        Complex.normSq (coherence (trajectory m r n) - cs))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hGn
      rw [Real.sqrt_zero] at this
      exact this
    have hp : Tendsto (fun n => population (trajectory m r n)) atTop (𝓝 ps) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hsq
      rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      have := Complex.normSq_nonneg (coherence (trajectory m r n) - cs)
      linarith
    have hc : Tendsto (fun n => coherence (trajectory m r n)) atTop (𝓝 cs) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hsq
      rw [Complex.dist_eq, Complex.norm_def]
      apply Real.sqrt_le_sqrt
      have := sq_nonneg (population (trajectory m r n) - ps)
      linarith
    have := X7_rho_tendsto _ _ ps cs hp hc
    refine this.congr fun n => ?_
    exact (X7_trajectory_rho m r hr n).symm
  refine ⟨hdens, hfix, ?_, hconv⟩
  intro r hr hrfix
  have hconst : trajectory m r = fun _ => r := by
    funext n
    exact Function.iterate_fixed hrfix n
  have h1 := hconv r hr
  rw [hconst] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

end
