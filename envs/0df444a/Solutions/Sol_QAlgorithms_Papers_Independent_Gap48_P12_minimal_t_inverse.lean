-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.minimal_t_inverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:56:35.605163+00:00
-- url     : https://prove2.me/submissions/9bfec0db-1c6c-4f3d-8f82-043abe051e31

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P12

theorem g73v_expT : Complex.exp (Complex.I * Real.pi / 4) =
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ + ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hp : Real.sqrt 2 ≠ 0 := by positivity
    field_simp; linarith
  rw [h2]; push_cast; ring

theorem g73v_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

theorem g73v_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact_mod_cast this

theorem g73v_conjs : (starRingEnd ℂ) ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := Complex.conj_ofReal _


theorem g73v_act_mul (A B : Matrix Bool Bool ℂ) (ψ : EuclideanSpace ℂ Bool) :
    act (A * B) ψ = act A (act B ψ) := by
  simp [act, Matrix.mulVec_mulVec]

theorem g73v_stab_of_comm (x y z x' y' z' : ℝ) (U : Matrix Bool Bool ℂ) (ψ : EuclideanSpace ℂ Bool)
    (hc : blochMatrix x' y' z' * U = U * blochMatrix x y z) (h : PauliStabilizes x y z ψ) :
    PauliStabilizes x' y' z' (act U ψ) := by
  unfold PauliStabilizes at *
  rw [← g73v_act_mul, hc, g73v_act_mul, h]

theorem g73v_commT (x y z : ℝ) :
    blochMatrix ((x - y) / Real.sqrt 2) ((x + y) / Real.sqrt 2) z * gateT =
      gateT * blochMatrix x y z := by
  have hs := g73v_sq
  have hn := g73v_ne
  ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, blochMatrix, pauliX, pauliY, pauliZ, gateT, g73v_expT] <;>
    field_simp <;> ring_nf <;> simp [hs] <;> ring_nf

theorem g73v_commH (x y z : ℝ) :
    blochMatrix z (-y) x * hadamard = hadamard * blochMatrix x y z := by
  have hs := g73v_sq
  have hn := g73v_ne
  ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, blochMatrix, pauliX, pauliY, pauliZ, hadamard] <;>
    field_simp <;> ring_nf <;> simp [hs] <;> ring_nf

theorem g73v_commS (x y z : ℝ) :
    blochMatrix (-y) x z * phaseS = phaseS * blochMatrix x y z := by
  ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, blochMatrix, pauliX, pauliY, pauliZ, phaseS] <;> ring_nf <;>
    simp <;> ring_nf

theorem g73v_zero (x y z : ℝ) (h : PauliStabilizes x y z (ket false)) :
    x = 0 ∧ y = 0 ∧ z = 1 := by
  unfold PauliStabilizes at h
  have h0 := congrArg (fun v : EuclideanSpace ℂ Bool => v false) h
  have h1 := congrArg (fun v : EuclideanSpace ℂ Bool => v true) h
  simp [act, ket, blochMatrix, pauliX, pauliY, pauliZ, Matrix.mulVec, dotProduct] at h0 h1
  have a := congrArg Complex.re h1
  have b := congrArg Complex.im h1
  simp at a b
  exact ⟨a, b, by exact_mod_cast h0⟩

theorem g73v_wm_cons (a : CircuitLetter) (w : CircuitWord) :
    QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp (a :: w)) =
      gateMatrix .hp a *
        QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w) := by
  cases a <;>
    simp [chronologicalInstructions, QAlgorithms.Papers.Independent.Next46.P21.wordMatrix,
      QAlgorithms.Papers.Independent.Next46.P21.letterMatrix, gateMatrix]

theorem g73v_tc_cons (a : CircuitLetter) (w : CircuitWord) :
    wordTCount (a :: w) = wordTCount w + (if a = .t then 1 else 0) := by
  cases a <;> simp [wordTCount, List.count_cons]

theorem g73v_sqrt_mul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem g73v_ccT (n : ℕ) (q : StabilizerCoefficients) :
    let q' : StabilizerCoefficients := ![q 0 - q 2, q 1 - q 3, q 0 + q 2, q 1 + q 3, 2 * q 5, q 4]
    coefficientCoordinate (n+1) q' 0 =
        (coefficientCoordinate n q 0 - coefficientCoordinate n q 1) / Real.sqrt 2 ∧
    coefficientCoordinate (n+1) q' 1 =
        (coefficientCoordinate n q 0 + coefficientCoordinate n q 1) / Real.sqrt 2 ∧
    coefficientCoordinate (n+1) q' 2 = coefficientCoordinate n q 2 := by
  have hs := g73v_sqrt_mul
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> simp [coefficientCoordinate, pow_succ] <;> field_simp <;> push_cast <;>
    ring_nf <;> simp [hs] <;> ring_nf

theorem g73v_stabT (n : ℕ) (q : StabilizerCoefficients) (ψ : EuclideanSpace ℂ Bool)
    (h : PauliStabilizes (coefficientCoordinate n q 0) (coefficientCoordinate n q 1)
      (coefficientCoordinate n q 2) ψ) :
    PauliStabilizes
      (coefficientCoordinate (n+1) ![q 0 - q 2, q 1 - q 3, q 0 + q 2, q 1 + q 3, 2 * q 5, q 4] 0)
      (coefficientCoordinate (n+1) ![q 0 - q 2, q 1 - q 3, q 0 + q 2, q 1 + q 3, 2 * q 5, q 4] 1)
      (coefficientCoordinate (n+1) ![q 0 - q 2, q 1 - q 3, q 0 + q 2, q 1 + q 3, 2 * q 5, q 4] 2)
      (act gateT ψ) := by
  obtain ⟨e0, e1, e2⟩ := g73v_ccT n q
  rw [e0, e1, e2]
  exact g73v_stab_of_comm _ _ _ _ _ _ gateT ψ (g73v_commT _ _ _) h

theorem g73v_stabH (n : ℕ) (q : StabilizerCoefficients) (ψ : EuclideanSpace ℂ Bool)
    (h : PauliStabilizes (coefficientCoordinate n q 0) (coefficientCoordinate n q 1)
      (coefficientCoordinate n q 2) ψ) :
    PauliStabilizes
      (coefficientCoordinate n ![q 4, q 5, -q 2, -q 3, q 0, q 1] 0)
      (coefficientCoordinate n ![q 4, q 5, -q 2, -q 3, q 0, q 1] 1)
      (coefficientCoordinate n ![q 4, q 5, -q 2, -q 3, q 0, q 1] 2)
      (act hadamard ψ) := by
  have e1 : coefficientCoordinate n ![q 4, q 5, -q 2, -q 3, q 0, q 1] 1 =
      -coefficientCoordinate n q 1 := by
    simp [coefficientCoordinate]; ring
  have e0 : coefficientCoordinate n ![q 4, q 5, -q 2, -q 3, q 0, q 1] 0 =
      coefficientCoordinate n q 2 := by simp [coefficientCoordinate]
  have e2 : coefficientCoordinate n ![q 4, q 5, -q 2, -q 3, q 0, q 1] 2 =
      coefficientCoordinate n q 0 := by simp [coefficientCoordinate]
  rw [e0, e1, e2]
  exact g73v_stab_of_comm _ _ _ _ _ _ hadamard ψ (g73v_commH _ _ _) h

theorem g73v_stabS (n : ℕ) (q : StabilizerCoefficients) (ψ : EuclideanSpace ℂ Bool)
    (h : PauliStabilizes (coefficientCoordinate n q 0) (coefficientCoordinate n q 1)
      (coefficientCoordinate n q 2) ψ) :
    PauliStabilizes
      (coefficientCoordinate n ![-q 2, -q 3, q 0, q 1, q 4, q 5] 0)
      (coefficientCoordinate n ![-q 2, -q 3, q 0, q 1, q 4, q 5] 1)
      (coefficientCoordinate n ![-q 2, -q 3, q 0, q 1, q 4, q 5] 2)
      (act phaseS ψ) := by
  have e0 : coefficientCoordinate n ![-q 2, -q 3, q 0, q 1, q 4, q 5] 0 =
      -coefficientCoordinate n q 1 := by
    simp [coefficientCoordinate]; ring
  have e1 : coefficientCoordinate n ![-q 2, -q 3, q 0, q 1, q 4, q 5] 1 =
      coefficientCoordinate n q 0 := by simp [coefficientCoordinate]
  have e2 : coefficientCoordinate n ![-q 2, -q 3, q 0, q 1, q 4, q 5] 2 =
      coefficientCoordinate n q 2 := by simp [coefficientCoordinate]
  rw [e0, e1, e2]
  exact g73v_stab_of_comm _ _ _ _ _ _ phaseS ψ (g73v_commS _ _ _) h

theorem g73v_wT (k k' : Fin 9) (C : CircuitWord)
    (hp : ∀ q : StabilizerCoefficients, HasParity k q →
      HasParity k' ![q 0 - q 2, q 1 - q 3, q 0 + q 2, q 1 + q 3, 2 * q 5, q 4])
    (h : InParityClass k C) : InParityClass k' (.t :: C) := by
  obtain ⟨q, hq, hs⟩ := h
  refine ⟨_, hp q hq, ?_⟩
  beta_reduce at hs ⊢
  have := g73v_stabT _ q _ hs
  simp only [g73v_tc_cons, g73v_wm_cons, g73v_act_mul, gateMatrix, if_pos rfl]
  exact this

theorem g73v_wHT (k k' : Fin 9) (C : CircuitWord)
    (hp : ∀ q : StabilizerCoefficients, HasParity k q →
      HasParity k' ![2 * q 5, q 4, -(q 0 + q 2), -(q 1 + q 3), q 0 - q 2, q 1 - q 3])
    (h : InParityClass k C) : InParityClass k' (.h :: .t :: C) := by
  obtain ⟨q, hq, hs⟩ := h
  refine ⟨_, hp q hq, ?_⟩
  beta_reduce at hs ⊢
  have := g73v_stabH _ _ _ (g73v_stabT _ q _ hs)
  simp only [g73v_tc_cons, g73v_wm_cons, g73v_act_mul, gateMatrix, if_pos rfl] at this ⊢
  simpa using this

theorem g73v_wPHT (k k' : Fin 9) (C : CircuitWord)
    (hp : ∀ q : StabilizerCoefficients, HasParity k q →
      HasParity k' ![q 0 + q 2, q 1 + q 3, 2 * q 5, q 4, q 0 - q 2, q 1 - q 3])
    (h : InParityClass k C) : InParityClass k' (.p :: .h :: .t :: C) := by
  obtain ⟨q, hq, hs⟩ := h
  refine ⟨_, hp q hq, ?_⟩
  beta_reduce at hs ⊢
  have := g73v_stabS _ _ _ (g73v_stabH _ _ _ (g73v_stabT _ q _ hs))
  simp only [g73v_tc_cons, g73v_wm_cons, g73v_act_mul, gateMatrix, if_pos rfl] at this ⊢
  simpa using this

theorem g73v_par_iff (k : Fin 9) (q : StabilizerCoefficients) :
    HasParity k q ↔ ∀ j, q j % 2 = if parityPattern k j then 1 else 0 := by
  unfold HasParity
  refine forall_congr' fun j => ?_
  split_ifs <;> simp [Int.odd_iff, Int.even_iff]


theorem g73v_chron_append (w1 w2 : CircuitWord) :
    chronologicalInstructions .hp (w1 ++ w2) =
      chronologicalInstructions .hp w2 ++ chronologicalInstructions .hp w1 := by
  simp [chronologicalInstructions, List.reverse_append, List.flatMap_append]

theorem g73v_wm_append (w1 w2 : CircuitWord) :
    QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp (w1 ++ w2)) =
      QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w1) *
      QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w2) := by
  rw [g73v_chron_append]
  simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, List.reverse_append, List.prod_append]

theorem g73v_cl_mul (A B : Matrix Bool Bool ℂ) (hA : A ∈ cliffordSet .hp) (hB : B ∈ cliffordSet .hp) :
    A * B ∈ cliffordSet .hp := by
  obtain ⟨w1, h1, rfl⟩ := hA
  obtain ⟨w2, h2, rfl⟩ := hB
  refine ⟨w1 ++ w2, ?_, ?_⟩
  · simp only [IsCliffordWord, List.mem_append, not_or] at *; exact ⟨h1, h2⟩
  · exact g73v_wm_append w1 w2

theorem g73v_cl_letter (a : CircuitLetter) (ha : a ≠ .t) : gateMatrix .hp a ∈ cliffordSet .hp := by
  refine ⟨[a], ?_, ?_⟩
  · simp [IsCliffordWord]; exact fun h => ha h.symm
  · have := g73v_wm_cons a []
    beta_reduce; rw [this]; exact mul_one _

theorem g73v_S_mem : phaseS ∈ cliffordSet .hp := g73v_cl_letter .p (by decide)
theorem g73v_H_mem : hadamard ∈ cliffordSet .hp := g73v_cl_letter .h (by decide)

theorem g73v_Sstar : star phaseS = phaseS * phaseS * phaseS := by
  ext i j; cases i <;> cases j <;> simp [phaseS, Matrix.star_apply, Matrix.mul_apply]

theorem g73v_Sstar_mem : star phaseS ∈ cliffordSet .hp := by
  rw [g73v_Sstar]; exact g73v_cl_mul _ _ (g73v_cl_mul _ _ g73v_S_mem g73v_S_mem) g73v_S_mem

theorem g73v_TT : gateT * gateT = phaseS := by
  ext i j; cases i <;> cases j <;> simp [phaseS, gateT, Matrix.mul_apply]
  rw [← Complex.exp_add]
  have : Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 = (Real.pi / 2 : ℝ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; simp

theorem g73v_TsT : star gateT * gateT = 1 := by
  ext i j; cases i <;> cases j <;> simp [gateT, Matrix.star_apply, Matrix.mul_apply]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : (starRingEnd ℂ) (Complex.I * Real.pi / 4) + Complex.I * Real.pi / 4 = 0 := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
  rw [this, Complex.exp_zero]

theorem g73v_TTs : gateT * star gateT = 1 := by
  ext i j; cases i <;> cases j <;> simp [gateT, Matrix.star_apply, Matrix.mul_apply]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : Complex.I * Real.pi / 4 + (starRingEnd ℂ) (Complex.I * Real.pi / 4) = 0 := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
  rw [this, Complex.exp_zero]

theorem g73v_TsTs : star gateT * star gateT = star phaseS := by
  rw [← g73v_TT, star_mul]

theorem g73v_cancel1 (M : Matrix Bool Bool ℂ) : star gateT * (gateT * M * star gateT) * gateT = M := by
  rw [show star gateT * (gateT * M * star gateT) * gateT =
    (star gateT * gateT) * M * (star gateT * gateT) by simp only [mul_assoc], g73v_TsT, one_mul, mul_one]

theorem g73v_cancel2 (M : Matrix Bool Bool ℂ) : gateT * (star gateT * M * gateT) * star gateT = M := by
  rw [show gateT * (star gateT * M * gateT) * star gateT =
    (gateT * star gateT) * M * (gateT * star gateT) by simp only [mul_assoc], g73v_TTs, one_mul, mul_one]

theorem g73v_TsT_assoc (M : Matrix Bool Bool ℂ) : star gateT * (gateT * M) = M := by
  rw [← mul_assoc, g73v_TsT, one_mul]

theorem g73v_TTs_assoc (M : Matrix Bool Bool ℂ) : gateT * (star gateT * M) = M := by
  rw [← mul_assoc, g73v_TTs, one_mul]

theorem g73v_idA : hadamard * (phaseS * hadamard) * gateT =
    phaseS * hadamard * gateT * (hadamard * phaseS * phaseS * hadamard) := by
  have hs := g73v_sq
  have hn := g73v_ne
  have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
    linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * hs
  have h4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    linear_combination (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 + 2) * hs
  ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, hadamard, phaseS, gateT, g73v_expT] <;>
    field_simp <;> ring_nf <;> simp [hs, h3, h4] <;> ring_nf

theorem g73v_idB : phaseS * (phaseS * hadamard) * gateT =
    hadamard * gateT * (hadamard * phaseS * hadamard * phaseS * phaseS * phaseS * hadamard) := by
  have hs := g73v_sq
  have hn := g73v_ne
  have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
    linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * hs
  have h4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    linear_combination (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 + 2) * hs
  ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, hadamard, phaseS, gateT, g73v_expT] <;>
    field_simp <;> ring_nf <;> simp [hs, h3, h4] <;> ring_nf

theorem g73v_idC : phaseS * gateT = gateT * phaseS := by
  ext i j <;> cases i <;> cases j <;> simp [Matrix.mul_apply, phaseS, gateT] <;> ring

theorem g73v_one_mem : (1 : Matrix Bool Bool ℂ) ∈ cliffordSet .hp :=
  ⟨[], by simp [IsCliffordWord], rfl⟩

theorem g73v_coset (w : CircuitWord) (hw : IsCliffordWord w) :
    ∃ S : Matrix Bool Bool ℂ, S ∈ ({1, hadamard, phaseS * hadamard} : Set (Matrix Bool Bool ℂ)) ∧
      ∃ U : Matrix Bool Bool ℂ, U ∈ cliffordSet .hp ∧
        QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w) * gateT =
          S * gateT * U := by
  induction w with
  | nil => exact ⟨1, by simp, 1, g73v_one_mem, by simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, chronologicalInstructions]⟩
  | cons a w ih =>
    simp only [IsCliffordWord, List.mem_cons, not_or] at hw
    obtain ⟨ha, hw⟩ := hw
    obtain ⟨S, hS, U, hU, he⟩ := ih hw
    rw [g73v_wm_cons, mul_assoc, he]
    have hH := g73v_H_mem
    have hSm := g73v_S_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS ⊢
    rcases hS with rfl | rfl | rfl <;> cases a
    · exact ⟨hadamard, by simp, U, hU, by simp [gateMatrix, mul_assoc]⟩
    · exact ⟨1, by simp, phaseS * U, g73v_cl_mul _ _ hSm hU, by
        simp only [gateMatrix, one_mul, ← mul_assoc, g73v_idC]⟩
    · exact absurd rfl ha
    · exact ⟨1, by simp, U, hU, by
        simp only [gateMatrix, ← mul_assoc, hadamard_mul_self, one_mul]⟩
    · exact ⟨phaseS * hadamard, by simp, U, hU, by simp [gateMatrix, mul_assoc]⟩
    · exact absurd rfl ha
    · refine ⟨phaseS * hadamard, by simp, (hadamard * phaseS * phaseS * hadamard) * U,
        g73v_cl_mul _ _ (g73v_cl_mul _ _ (g73v_cl_mul _ _ (g73v_cl_mul _ _ hH hSm) hSm) hH) hU, ?_⟩
      simp only [gateMatrix]
      rw [← mul_assoc, ← mul_assoc, g73v_idA]; simp only [mul_assoc]
    · refine ⟨hadamard, by simp,
        (hadamard * phaseS * hadamard * phaseS * phaseS * phaseS * hadamard) * U, ?_, ?_⟩
      · refine g73v_cl_mul _ _ ?_ hU
        repeat' apply g73v_cl_mul
        all_goals assumption
      simp only [gateMatrix]
      rw [← mul_assoc, ← mul_assoc, g73v_idB]; simp only [mul_assoc]
    · exact absurd rfl ha

theorem g73v_expTn : Complex.exp (-(Complex.I * Real.pi / 4)) =
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ - ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I := by
  have : -(Complex.I * Real.pi / 4) = ((-(Real.pi / 4)) : ℝ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hp : Real.sqrt 2 ≠ 0 := by positivity
    field_simp; linarith
  rw [h2]; push_cast; ring

theorem g73v_Tstar : star gateT = phaseS * phaseS * phaseS * gateT := by
  ext i j; cases i <;> cases j <;> simp [phaseS, gateT, Matrix.star_apply, Matrix.mul_apply]
  rw [← Complex.exp_conj]
  have : (starRingEnd ℂ) (Complex.I * Real.pi / 4) = -(Complex.I * Real.pi / 4) := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
  rw [this, g73v_expTn, g73v_expT]
  ring_nf; rw [Complex.I_sq]; ring

theorem g73v_Hstar : star hadamard = hadamard := by
  ext i j; cases i <;> cases j <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]

def g73v_invL : CircuitLetter → CircuitWord
  | .h => [.h]
  | .p => [.p, .p, .p]
  | .t => [.p, .p, .p, .t]

theorem g73v_invL_mat (a : CircuitLetter) :
    QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp (g73v_invL a)) =
      star (gateMatrix .hp a) := by
  cases a <;> simp only [g73v_invL, g73v_wm_cons, gateMatrix] <;>
    simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, chronologicalInstructions,
      g73v_Hstar, g73v_Sstar, g73v_Tstar, mul_assoc]

theorem g73v_invL_tc (a : CircuitLetter) : wordTCount (g73v_invL a) = if a = .t then 1 else 0 := by
  cases a <;> rfl

theorem g73v_inv_word (w : CircuitWord) :
    ∃ v : CircuitWord, wordTCount v = wordTCount w ∧
      QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp v) =
        star (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w)) := by
  induction w with
  | nil => exact ⟨[], rfl, by simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, chronologicalInstructions]⟩
  | cons a w ih =>
    obtain ⟨v, hv, hm⟩ := ih
    refine ⟨v ++ g73v_invL a, ?_, ?_⟩
    · simp only [wordTCount, List.count_append] at hv ⊢
      rw [hv]
      cases a <;> simp [g73v_invL, List.count_cons]
    · rw [g73v_wm_append, hm, g73v_invL_mat, g73v_wm_cons, star_mul]

theorem g73v_atMost_star (n : ℕ) (U : Matrix Bool Bool ℂ) (h : U ∈ atMostT n) : star U ∈ atMostT n := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨v, hv, hm⟩ := g73v_inv_word w
  exact ⟨v, hv ▸ hw, hm⟩


local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.8, Lemma 1: preserve both the normal-word and minimal-layer
premises. Inversion of the evaluated unitary is its adjoint.
The zero layer is M₀, as required by the source proof's n=0 case. -/
theorem solution (reps : Representatives .hp) (n : ℕ)
    (C : CircuitWord) (hC : IsNormalWord .hp reps C) (ht : wordTCount C = n)
    (hminimal : wordMatrix .hp C ∈ minimalT n) :
    star (wordMatrix .hp C) ∈ minimalT n := by
  cases n with
  | zero => exact g73v_atMost_star 0 _ hminimal
  | succ m =>
    obtain ⟨h1, h2⟩ := hminimal
    refine ⟨g73v_atMost_star _ _ h1, fun h3 => h2 ?_⟩
    have := g73v_atMost_star _ _ h3
    rwa [star_star] at this


end
