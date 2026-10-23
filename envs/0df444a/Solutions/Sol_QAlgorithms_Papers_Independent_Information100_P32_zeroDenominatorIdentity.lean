-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.zeroDenominatorIdentity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:15:30.219746+00:00
-- url     : https://prove2.me/submissions/1234e1c2-105c-4105-9a46-da58a502c8b6

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

theorem X7_K_zero (m : Model) (hK : denominatorK m = 0) :
    (angleC m = 1 ∧ Real.cos (m.frequency * m.duration) = 1) ∨
     (angleC m = -1 ∧ Real.cos (m.frequency * m.duration) = -1) := by
  have hph := m.ancilla_physical
  obtain ⟨h0, h1, hq⟩ := hph
  set q := Complex.normSq m.cA
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hq4 : 4 * q ≤ 1 := by nlinarith [sq_nonneg (2 * m.pA - 1)]
  set C := angleC m
  set k := Real.cos (m.frequency * m.duration)
  have hs : Real.sin (m.frequency * m.duration) ^ 2 = 1 - k ^ 2 := by
    rw [Real.sin_sq]
  have hC1 : C ≤ 1 := Real.cos_le_one _
  have hC2 : -1 ≤ C := Real.neg_one_le_cos _
  have hk1 : k ≤ 1 := Real.cos_le_one _
  have hk2 : -1 ≤ k := Real.neg_one_le_cos _
  have hKe : (1 - 4 * q) * C ^ 2 - (2 - 4 * q) * C * k + 1 = 0 := by
    have : denominatorK m = (1 - 4 * q) * C ^ 2 - (2 - 4 * q) * C * k + 1 := by
      unfold denominatorK denominatorD differenceL
      rw [hs]; ring
    linarith
  -- K ≥ (1-|C|)(1-(1-a)|C|) + (2-a)(|C| - C k)
  have hab : |C| ≤ 1 := abs_le.mpr ⟨hC2, hC1⟩
  have hCk : C * k ≤ |C| := by
    calc C * k ≤ |C * k| := le_abs_self _
      _ = |C| * |k| := abs_mul _ _
      _ ≤ |C| * 1 := by
          apply mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hk2, hk1⟩) (abs_nonneg _)
      _ = |C| := mul_one _
  have hsq : C ^ 2 = |C| ^ 2 := (sq_abs C).symm
  have e1 : (1 - |C|) * (1 - (1 - 4 * q) * |C|) + (2 - 4 * q) * (|C| - C * k) = 0 := by
    rw [hsq] at hKe; linarith
  have t1 : 0 ≤ (1 - |C|) * (1 - (1 - 4 * q) * |C|) := by
    apply mul_nonneg <;> nlinarith [abs_nonneg C]
  have t2 : 0 ≤ (2 - 4 * q) * (|C| - C * k) := by
    apply mul_nonneg <;> linarith
  have t2' : |C| = C * k := by
    have : (2 - 4 * q) * (|C| - C * k) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have t1' : (1 - |C|) * (1 - (1 - 4 * q) * |C|) = 0 := by linarith
  have hCa : |C| = 1 := by
    rcases mul_eq_zero.mp t1' with h | h
    · linarith
    · nlinarith [mul_nonneg hq0 (abs_nonneg C)]
  rcases abs_eq (zero_le_one) |>.mp hCa with h | h
  · left; refine ⟨h, ?_⟩; rw [h, abs_one] at t2'; linarith
  · right; refine ⟨h, ?_⟩; rw [h, abs_neg, abs_one] at t2'; linarith

open ComplexOrder in
theorem X7_rho_density (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsDensityMatrix (rho p 0) := by
  have he : rho p 0 = Matrix.diagonal (fun i : Bool => if i then ((1 - p : ℝ) : ℂ) else (p : ℂ)) := by
    ext i j; cases i <;> cases j <;> simp [rho, Matrix.diagonal]
  refine ⟨?_, ?_⟩
  · rw [he, Matrix.posSemidef_diagonal_iff]
    intro i; cases i <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
      exact_mod_cast (by linarith : (0:ℝ) ≤ _)
  · simp [rho, Matrix.trace]

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hK : denominatorK m = 0) :
    ((angleC m = 1 ∧ Real.cos (m.frequency * m.duration) = 1) ∨
     (angleC m = -1 ∧ Real.cos (m.frequency * m.duration) = -1)) ∧
    (∀ r : Op Bool, collision m r = r) ∧
    ¬(∃ r : Op Bool, IsDensityMatrix r ∧
      ∀ s : Op Bool, IsDensityMatrix s → collision m s = s → s = r) := by
  have hc := X7_K_zero m hK
  have hid : ∀ r : Op Bool, collision m r = r := by
    intro r
    have hS : Real.sin (2 * m.coupling * m.duration) = 0 := by
      have := Real.sin_sq_add_cos_sq (2 * m.coupling * m.duration)
      have hC2 : Real.cos (2 * m.coupling * m.duration) ^ 2 = 1 := by
        rcases hc with h | h <;> (unfold angleC at h; rw [h.1]; norm_num)
      nlinarith
    have hsw : Real.sin (m.frequency * m.duration) = 0 := by
      have := Real.sin_sq_add_cos_sq (m.frequency * m.duration)
      have hC2 : Real.cos (m.frequency * m.duration) ^ 2 = 1 := by
        rcases hc with h | h <;> (rw [h.2]; norm_num)
      nlinarith
    have hE : Complex.exp (Complex.I * ((m.frequency * m.duration : ℝ) : ℂ)) =
        (Real.cos (2 * m.coupling * m.duration) : ℂ) := by
      rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsw]
      have : Real.cos (m.frequency * m.duration) = Real.cos (2 * m.coupling * m.duration) := by
        rcases hc with h | h <;> (unfold angleC at h; rw [h.1, h.2])
      rw [this]; simp
    have hc2 : (Real.cos (2 * m.coupling * m.duration) : ℂ) * (Real.cos (2 * m.coupling * m.duration) : ℂ) = 1 := by
      rcases hc with h | h <;> (unfold angleC at h; rw [h.1]; norm_num)
    have htr : (rho m.pA m.cA) false false + (rho m.pA m.cA) true true = 1 := by
      simp [rho]
    unfold collision
    rw [X7_evolution_eq, hE, hS]
    set c : ℂ := (Real.cos (2 * m.coupling * m.duration) : ℂ)
    have hcc : conj c = c := Complex.conj_ofReal _
    ext i j
    cases i <;> cases j <;>
      simp [reduced, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
        Matrix.kroneckerMap_apply, X7_Umat, Matrix.conjTranspose_apply, hcc] <;>
      linear_combination (r _ _ * (rho m.pA m.cA false false + rho m.pA m.cA true true)) * hc2 +
        r _ _ * htr
  refine ⟨hc, hid, ?_⟩
  rintro ⟨r, _, hu⟩
  have h1 := hu (rho 1 0) (X7_rho_density 1 (by norm_num) (by norm_num)) (hid _)
  have h0 := hu (rho 0 0) (X7_rho_density 0 (by norm_num) (by norm_num)) (hid _)
  have := congrFun (congrFun (h1.trans h0.symm) false) false
  simp [rho] at this
