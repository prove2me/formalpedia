-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P20.classical_symplectic_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:41:27.829443+00:00
-- url     : https://prove2.me/submissions/d48d53b4-330a-4185-b5d2-ab1a92da0b8f

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20
noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

lemma g62h_ds {n : ℕ} (z w : DoublePhase n) : doubleSigma z w =
    ∑ j, (z 2 j * w 0 j - z 0 j * w 2 j + z 3 j * w 1 j - z 1 j * w 3 j) := by
  simp only [doubleSigma, coordinateDot, Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma g62h_R_symp {n : ℕ} (θ : ℝ) (z w : DoublePhase n) :
    doubleSigma (classicalR θ z) (classicalR θ w) = doubleSigma z w := by
  rw [g62h_ds, g62h_ds]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [classicalR]
  linear_combination (z 2 j * w 0 j - z 0 j * w 2 j + z 3 j * w 1 j - z 1 j * w 3 j) *
    Real.sin_sq_add_cos_sq θ

lemma g62h_D_symp {n : ℕ} (s : ℝ) (z w : DoublePhase n) :
    doubleSigma (doublePhaseDilation s z) (doublePhaseDilation s w) = doubleSigma z w := by
  rw [g62h_ds, g62h_ds]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  simp [doublePhaseDilation]
  linear_combination (z 2 j * w 0 j - z 0 j * w 2 j + z 3 j * w 1 j - z 1 j * w 3 j) * h

lemma g62h_R_inv {n : ℕ} (θ : ℝ) (z : DoublePhase n) : classicalR θ (classicalR (-θ) z) = z := by
  funext a j
  have h := Real.sin_sq_add_cos_sq θ
  fin_cases a <;> simp [classicalR] <;>
    first | linear_combination (z 0 j) * h | linear_combination (z 1 j) * h | linear_combination (z 2 j) * h | linear_combination (z 3 j) * h

lemma g62h_D_inv {n : ℕ} (s : ℝ) (z : DoublePhase n) :
    doublePhaseDilation s (doublePhaseDilation (-s) z) = z := by
  have h : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  have h' : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  funext a j
  fin_cases a <;> simp [doublePhaseDilation, smul_smul] <;>
    first | linear_combination (z _ j) * h

lemma g62h_R_bij {n : ℕ} (θ : ℝ) : Function.Bijective (classicalR (n := n) θ) :=
  Function.bijective_iff_has_inverse.mpr ⟨classicalR (-θ), fun z => by
    simpa using g62h_R_inv (-θ) z, fun z => g62h_R_inv θ z⟩

lemma g62h_D_bij {n : ℕ} (s : ℝ) : Function.Bijective (doublePhaseDilation (n := n) s) :=
  Function.bijective_iff_has_inverse.mpr ⟨doublePhaseDilation (-s), fun z => by
    simpa using g62h_D_inv (-s) z, fun z => g62h_D_inv s z⟩

lemma g62h_decomp {n : ℕ} (z : DoublePhase n) :
    classicalS z = classicalR (Real.pi / 4) (doublePhaseDilation (Real.log (Real.sqrt 2)) z) := by
  have h2 : Real.exp (Real.log (Real.sqrt 2)) = Real.sqrt 2 :=
    Real.exp_log (by positivity)
  have h3 : Real.exp (-Real.log (Real.sqrt 2)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.exp_neg, h2]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  funext a j
  fin_cases a <;> simp [classicalS, classicalR, doublePhaseDilation, h2, h3, smul_smul,
    Real.cos_pi_div_four, Real.sin_pi_div_four] <;> field_simp <;>
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring

/-- directional derivative via a line -/
lemma g62h_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E → ℝ) (z v : E)
    (hH : DifferentiableAt ℝ H z) (c : ℝ) (h : HasDerivAt (fun t : ℝ => H (z + t • v)) c 0) :
    fderiv ℝ H z v = c := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have h2 : HasFDerivAt H (fderiv ℝ H z) (z + (0:ℝ) • v) := by simpa using hH.hasFDerivAt
  exact (h2.comp_hasDerivAt 0 h1).unique h

lemma g62h_Q_line {n : ℕ} (a b : Fin 4) (z v : DoublePhase n) :
    HasDerivAt (fun t : ℝ => coordinateDot ((z + t • v) a) ((z + t • v) b))
      (coordinateDot (v a) (z b) + coordinateDot (z a) (v b)) 0 := by
  simp only [coordinateDot, ← Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum
  intro j _
  have ha : HasDerivAt (fun t : ℝ => (z + t • v) a j) (v a j) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v a j)).const_add (z a j)
  have hb : HasDerivAt (fun t : ℝ => (z + t • v) b j) (v b j) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v b j)).const_add (z b j)
  have := ha.mul hb
  simp only [zero_smul, add_zero] at this
  exact this

lemma g62h_Q_diff {n : ℕ} (a b : Fin 4) (z : DoublePhase n) :
    DifferentiableAt ℝ (fun w : DoublePhase n => coordinateDot (w a) (w b)) z := by
  unfold coordinateDot
  fun_prop

@[simp] lemma g62h_dot_single {n : ℕ} (j : Fin n) (u : Configuration n) :
    coordinateDot (Pi.single j 1) u = u j := by
  simp [coordinateDot, Pi.single_apply]

@[simp] lemma g62h_dot_single' {n : ℕ} (j : Fin n) (u : Configuration n) :
    coordinateDot u (Pi.single j 1) = u j := by
  simp [coordinateDot, Pi.single_apply]

@[simp] lemma g62h_dot_zero {n : ℕ} (u : Configuration n) :
    coordinateDot u 0 = 0 ∧ coordinateDot 0 u = 0 := by
  simp [coordinateDot]

lemma g62h_field_D {n : ℕ} (w : DoublePhase n) :
    hamiltonField dilationHamiltonian w = ![w 0, w 1, -w 2, -w 3] := by
  have hd : DifferentiableAt ℝ (dilationHamiltonian (n := n)) w := by
    unfold dilationHamiltonian
    exact (g62h_Q_diff 0 2 w).add (g62h_Q_diff 1 3 w)
  have key : ∀ v : DoublePhase n, fderiv ℝ dilationHamiltonian w v =
      (coordinateDot (v 0) (w 2) + coordinateDot (w 0) (v 2)) +
      (coordinateDot (v 1) (w 3) + coordinateDot (w 1) (v 3)) := fun v =>
    g62h_fd _ w v hd _ ((g62h_Q_line 0 2 w v).add (g62h_Q_line 1 3 w v))
  funext a j
  fin_cases a <;> simp [hamiltonField, key]

lemma g62h_field_R {n : ℕ} (w : DoublePhase n) :
    hamiltonField rotationHamiltonian w = ![-w 3, -w 2, w 1, w 0] := by
  have hd : DifferentiableAt ℝ (rotationHamiltonian (n := n)) w := by
    unfold rotationHamiltonian
    exact ((g62h_Q_diff 2 3 w).neg).sub (g62h_Q_diff 0 1 w)
  have key : ∀ v : DoublePhase n, fderiv ℝ rotationHamiltonian w v =
      -(coordinateDot (v 2) (w 3) + coordinateDot (w 2) (v 3)) -
      (coordinateDot (v 0) (w 1) + coordinateDot (w 0) (v 1)) := fun v =>
    g62h_fd _ w v hd _ ((g62h_Q_line 2 3 w v).neg.sub (g62h_Q_line 0 1 w v))
  funext a j
  fin_cases a <;> simp [hamiltonField, key]

theorem solution {n : ℕ} (hn : 0 < n) :
    Function.Bijective (classicalS (n := n)) ∧
    (∀ z w : DoublePhase n, doubleSigma (classicalS z) (classicalS w) = doubleSigma z w) ∧
    (∀ z : DoublePhase n,
      classicalS z = classicalR (Real.pi / 4) (doublePhaseDilation (Real.log (Real.sqrt 2)) z)) ∧
    (∀ s : ℝ, Function.Bijective (doublePhaseDilation (n := n) s) ∧
      ∀ z w : DoublePhase n, doubleSigma (doublePhaseDilation s z) (doublePhaseDilation s w) = doubleSigma z w) ∧
    (∀ theta : ℝ, Function.Bijective (classicalR (n := n) theta) ∧
      ∀ z w : DoublePhase n, doubleSigma (classicalR theta z) (classicalR theta w) = doubleSigma z w) ∧
    (∀ (s : ℝ) (z : DoublePhase n), HasDerivAt (fun t => doublePhaseDilation t z)
      (hamiltonField dilationHamiltonian (doublePhaseDilation s z)) s) ∧
    (∀ (theta : ℝ) (z : DoublePhase n), HasDerivAt (fun t => classicalR t z)
      (hamiltonField rotationHamiltonian (classicalR theta z)) theta) := by
  have hS : classicalS (n := n) = classicalR (Real.pi / 4) ∘
      doublePhaseDilation (Real.log (Real.sqrt 2)) := funext g62h_decomp
  refine ⟨?_, ?_, g62h_decomp, fun s => ⟨g62h_D_bij s, g62h_D_symp s⟩,
    fun θ => ⟨g62h_R_bij θ, g62h_R_symp θ⟩, ?_, ?_⟩
  · rw [hS]; exact (g62h_R_bij _).comp (g62h_D_bij _)
  · intro z w; rw [g62h_decomp, g62h_decomp, g62h_R_symp, g62h_D_symp]
  · intro s z
    rw [g62h_field_D]
    refine hasDerivAt_pi.2 (fun a => hasDerivAt_pi.2 (fun j => ?_))
    fin_cases a
    · simpa [doublePhaseDilation] using (Real.hasDerivAt_exp s).mul_const (z 0 j)
    · simpa [doublePhaseDilation] using (Real.hasDerivAt_exp s).mul_const (z 1 j)
    · simpa [doublePhaseDilation] using
        (((hasDerivAt_neg s).exp).mul_const (z 2 j))
    · simpa [doublePhaseDilation] using
        (((hasDerivAt_neg s).exp).mul_const (z 3 j))
  · intro θ z
    rw [g62h_field_R]
    refine hasDerivAt_pi.2 (fun a => hasDerivAt_pi.2 (fun j => ?_))
    fin_cases a
    · have := ((Real.hasDerivAt_cos θ).mul_const (z 0 j)).sub ((Real.hasDerivAt_sin θ).mul_const (z 3 j))
      convert this using 1
      · ext x; simp only [classicalR, Pi.sub_apply, Pi.add_apply]; simp; try ring
      · simp [classicalR]; try ring
    · have := ((Real.hasDerivAt_cos θ).mul_const (z 1 j)).sub ((Real.hasDerivAt_sin θ).mul_const (z 2 j))
      convert this using 1
      · ext x; simp only [classicalR, Pi.sub_apply, Pi.add_apply]; simp; try ring
      · simp [classicalR]; try ring
    · have := ((Real.hasDerivAt_sin θ).mul_const (z 1 j)).add ((Real.hasDerivAt_cos θ).mul_const (z 2 j))
      convert this using 1
      · ext x; simp only [classicalR, Pi.sub_apply, Pi.add_apply]; simp; try ring
      · simp [classicalR]; try ring
    · have := ((Real.hasDerivAt_sin θ).mul_const (z 0 j)).add ((Real.hasDerivAt_cos θ).mul_const (z 3 j))
      convert this using 1
      · ext x; simp only [classicalR, Pi.sub_apply, Pi.add_apply]; simp; try ring
      · simp [classicalR]; try ring
