-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.heatDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:21:52.513054+00:00
-- url     : https://prove2.me/submissions/f50243f3-8934-43f5-9ab5-2077e552a7bc

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

theorem X7_kronB (w : ℝ) : Matrix.kronecker (1 : Op Bool) (localEnergy w) =
      Matrix.of fun x y => if x = y then (if x.2 then (w : ℂ) / 2 else -(w : ℂ) / 2) else 0 := by
  ext ⟨a1, b1⟩ ⟨a2, b2⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;>
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, localEnergy, QAlgorithms.pauliZ,
      Matrix.one_apply] <;> ring

theorem X7_heat_trace (e : ℂ) (C S w p : ℝ) (c : ℂ) (a : Op Bool) (hE : e * conj e = 1)
    (hCS : (C : ℂ) ^ 2 + (S : ℂ) ^ 2 = 1) :
    (((X7_Umat e C S)ᴴ * Matrix.kronecker 1 (localEnergy w) * X7_Umat e C S -
        Matrix.kronecker 1 (localEnergy w)) * Matrix.kronecker (rho p c) a).trace =
      w * S ^ 2 * ((1 - p) * a false false - p * a true true) +
        Complex.I * S * C * w * (c * a true false - conj c * a false true) := by
  rw [X7_kronB]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fintype.sum_bool,
    Matrix.mul_apply, Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.of_apply, Matrix.conjTranspose_apply, X7_Umat, rho]
  simp
  linear_combination ((w : ℂ) * (-(p : ℂ) * a true true / 2 - p * a false false / 2 +
      a true true / 2)) * hE +
    ((w : ℂ) * p * a true true * (S : ℂ) ^ 2 / 2 + w * p * (S : ℂ) ^ 2 * a false false / 2 -
      w * (S : ℂ) ^ 2 * a false false / 2) * Complex.I_sq +
    ((w : ℂ) * (p * a true true + p * a false false - a false false) / 2) * hCS

theorem X7_heat_rr (m : Model) (p q : ℝ) (c d : ℂ) :
    heat m (rho p c) (rho q d) =
      m.frequency * Real.sin (2 * m.coupling * m.duration) ^ 2 * (q - p) -
        2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) *
          m.frequency * (c * conj d).im := by
  have hE := X7_econj (m.frequency * m.duration)
  have hCS := X7_CS (2 * m.coupling * m.duration)
  unfold heat observableChange
  simp only []
  rw [X7_evolution_eq, X7_heat_trace _ _ _ _ _ _ _ hE hCS]
  generalize Real.cos (2 * m.coupling * m.duration) = C at *
  generalize Real.sin (2 * m.coupling * m.duration) = S at *
  simp [rho, ← Complex.ofReal_pow]
  ring

theorem X7_heat_add (m : Model) (r a b : Op Bool) :
    heat m r (a + b) = heat m r a + heat m r b := by
  unfold heat observableChange
  simp only []
  rw [show Matrix.kronecker r (a + b) = Matrix.kronecker r a + Matrix.kronecker r b from
    Matrix.kronecker_add _ _ _, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

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

theorem X7_rho_ff (p : ℝ) (c : ℂ) : rho p c false false = ((p : ℝ) : ℂ) := rfl

theorem X7_rho_tt (p : ℝ) (c : ℂ) : rho p c true true = ((1 - p : ℝ) : ℂ) := rfl

theorem X7_trace_L (w : ℝ) (X : Op Bool) :
    (localEnergy w * X).trace.re = (-w / 2) * (X false false).re + (w / 2) * (X true true).re := by
  simp [localEnergy, QAlgorithms.pauliZ, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  ring

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) :
    heat m r (rho m.pA m.cA) = heat m r (diagonalAncilla m) + heat m r (offDiagonalAncilla m) ∧
    heat m r (diagonalAncilla m) = m.frequency * (m.pA - population r) * angleS m ^ 2 ∧
    heat m r (offDiagonalAncilla m) =
      -m.frequency * Real.sin (4 * m.coupling * m.duration) * (coherence r * conj m.cA).im ∧
    heat m r (rho m.pA m.cA) =
      -((localEnergy m.frequency * (collision m r - r)).trace.re) ∧
    (0 < denominatorK m → heat m (starState m) (rho m.pA m.cA) = 0) := by
  have h4 : Real.sin (4 * m.coupling * m.duration) =
      2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hCSr := Real.cos_sq_add_sin_sq (2 * m.coupling * m.duration)
  have hsplit : rho m.pA m.cA = diagonalAncilla m + offDiagonalAncilla m := by
    unfold offDiagonalAncilla; abel
  have hadd : heat m r (rho m.pA m.cA) =
      heat m r (diagonalAncilla m) + heat m r (offDiagonalAncilla m) := by
    conv_lhs => rw [hsplit]
    exact X7_heat_add m r _ _
  have hrr := X7_density_rho r hr
  have hdiag : heat m r (diagonalAncilla m) =
      m.frequency * (m.pA - population r) * angleS m ^ 2 := by
    rw [hrr, diagonalAncilla, X7_heat_rr]
    simp [X7_pop_rho, angleS]
    ring
  have hfull : heat m r (rho m.pA m.cA) =
      m.frequency * Real.sin (2 * m.coupling * m.duration) ^ 2 * (m.pA - population r) -
        2 * Real.sin (2 * m.coupling * m.duration) * Real.cos (2 * m.coupling * m.duration) *
          m.frequency * (coherence r * conj m.cA).im := by
    rw [hrr, X7_heat_rr, X7_pop_rho, X7_coh_rho]
  refine ⟨hadd, hdiag, ?_, ?_, ?_⟩
  · have := hadd
    rw [hfull, hdiag] at this
    rw [h4]
    unfold angleS at this
    linarith
  · rw [hfull, X7_trace_L]
    conv_rhs => rw [hrr, X7_collision_rho]
    simp only [Matrix.sub_apply]
    rw [X7_rho_ff, X7_rho_ff, X7_rho_tt, X7_rho_tt]
    simp only [← Complex.ofReal_sub, Complex.ofReal_re]
    unfold X7_pn angleC
    rw [h4]
    linear_combination (m.frequency * (m.pA - population r)) * hCSr
  · intro _
    unfold starState
    rw [X7_heat_rr]
    have hm : (starCoherence m * conj m.cA).im =
        -(Complex.normSq m.cA) / denominatorK m * (2 * m.pA - 1) * angleS m * differenceL m := by
      rw [X7_starCoh_mul]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      ring
    rw [hm]
    unfold starPopulation angleC angleS
    ring

end
