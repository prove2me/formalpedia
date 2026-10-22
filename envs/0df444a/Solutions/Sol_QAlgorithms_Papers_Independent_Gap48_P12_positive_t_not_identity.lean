-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.positive_t_not_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:11:22.787054+00:00
-- url     : https://prove2.me/submissions/3dc321ea-2331-40d0-b272-dbcec924ca10

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

def g73v_qT (q : StabilizerCoefficients) : StabilizerCoefficients :=
  ![q 0 - q 2, q 1 - q 3, q 0 + q 2, q 1 + q 3, 2 * q 5, q 4]
def g73v_qHT (q : StabilizerCoefficients) : StabilizerCoefficients :=
  ![2 * q 5, q 4, -(q 0 + q 2), -(q 1 + q 3), q 0 - q 2, q 1 - q 3]
def g73v_qPHT (q : StabilizerCoefficients) : StabilizerCoefficients :=
  ![q 0 + q 2, q 1 + q 3, 2 * q 5, q 4, q 0 - q 2, q 1 - q 3]

def g73v_St (n : ℕ) (q : StabilizerCoefficients) (ψ : EuclideanSpace ℂ Bool) : Prop :=
  PauliStabilizes (coefficientCoordinate n q 0) (coefficientCoordinate n q 1)
    (coefficientCoordinate n q 2) ψ

theorem g73v_sT (C : CircuitWord) (q : StabilizerCoefficients)
    (hs : g73v_St (wordTCount C) q (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp C)) (ket false))) :
    g73v_St (wordTCount (.t :: C)) (g73v_qT q) (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp (.t :: C))) (ket false)) := by
  have := g73v_stabT _ q _ hs
  simp only [g73v_St, g73v_tc_cons, g73v_wm_cons, g73v_act_mul, gateMatrix, if_pos rfl]
  exact this

theorem g73v_sHT (C : CircuitWord) (q : StabilizerCoefficients)
    (hs : g73v_St (wordTCount C) q (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp C)) (ket false))) :
    g73v_St (wordTCount (.h :: .t :: C)) (g73v_qHT q) (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp (.h :: .t :: C))) (ket false)) := by
  have := g73v_stabH _ _ _ (g73v_stabT _ q _ hs)
  simp only [g73v_St, g73v_tc_cons, g73v_wm_cons, g73v_act_mul, gateMatrix, if_pos rfl] at this ⊢
  simpa [g73v_qHT] using this

theorem g73v_sPHT (C : CircuitWord) (q : StabilizerCoefficients)
    (hs : g73v_St (wordTCount C) q (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp C)) (ket false))) :
    g73v_St (wordTCount (.p :: .h :: .t :: C)) (g73v_qPHT q)
      (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp (.p :: .h :: .t :: C))) (ket false)) := by
  have := g73v_stabS _ _ _ (g73v_stabH _ _ _ (g73v_stabT _ q _ hs))
  simp only [g73v_St, g73v_tc_cons, g73v_wm_cons, g73v_act_mul, gateMatrix, if_pos rfl] at this ⊢
  simpa [g73v_qPHT] using this

def g73v_P (p : Fin 6 → ℤ) (q : StabilizerCoefficients) : Prop := ∀ j, q j % 2 = p j

/-- class invariant of block words -/
def g73v_Inv (bw : CircuitWord) : Prop :=
  (bw = [] ∨ bw = [.t] ∨ bw = [.h, .t] ∨ bw = [.p, .h, .t] ∨ 2 ≤ wordTCount bw) ∧
  ∃ q : StabilizerCoefficients, g73v_St (wordTCount bw) q (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) (ket false)) ∧
    ((wordTCount bw = 0 ∧ g73v_P ![0,0,0,0,1,0] q) ∨
     (wordTCount bw = 1 ∧ bw.head? = some .t ∧ g73v_P ![0,0,0,0,0,1] q) ∨
     (wordTCount bw = 1 ∧ bw.head? ≠ some .t ∧
        (g73v_P ![0,1,0,0,0,0] q ∨ g73v_P ![0,0,0,1,0,0] q)) ∨
     (2 ≤ wordTCount bw ∧ bw.head? = some .t ∧ g73v_P ![0,1,0,1,0,0] q) ∨
     (2 ≤ wordTCount bw ∧ bw.head? ≠ some .t ∧
        (g73v_P ![0,1,0,0,0,1] q ∨ g73v_P ![0,0,0,1,0,1] q)))

theorem g73v_Z0 : PauliStabilizes 0 0 1 (ket false) := by
  unfold PauliStabilizes
  ext i; cases i <;> simp [act, ket, blochMatrix, pauliX, pauliY, pauliZ, Matrix.mulVec, dotProduct]

theorem g73v_inv_nil : g73v_Inv [] := by
  refine ⟨Or.inl rfl, ![0,0,0,0,1,0], ?_, Or.inl ⟨rfl, ?_⟩⟩
  · have : coefficientCoordinate 0 ![0,0,0,0,1,0] 0 = 0 ∧ coefficientCoordinate 0 ![0,0,0,0,1,0] 1 = 0 ∧
        coefficientCoordinate 0 ![0,0,0,0,1,0] 2 = 1 := by
      refine ⟨?_, ?_, ?_⟩ <;> simp [coefficientCoordinate]
    simp only [g73v_St, wordTCount, List.count_nil]
    rw [this.1, this.2.1, this.2.2]
    have : act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp [])) (ket false) = ket false := by
      simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, chronologicalInstructions, act]
    rw [this]; exact g73v_Z0
  · intro j; fin_cases j <;> rfl

theorem g73v_tcT (bw : CircuitWord) : wordTCount (.t :: bw) = wordTCount bw + 1 := by
  simp [g73v_tc_cons]
theorem g73v_tcHT (bw : CircuitWord) : wordTCount (.h :: .t :: bw) = wordTCount bw + 1 := by
  simp [g73v_tc_cons]
theorem g73v_tcPHT (bw : CircuitWord) : wordTCount (.p :: .h :: .t :: bw) = wordTCount bw + 1 := by
  simp [g73v_tc_cons]

theorem g73v_shape_tc (bw : CircuitWord)
    (h : bw = [] ∨ bw = [.t] ∨ bw = [.h, .t] ∨ bw = [.p, .h, .t] ∨ 2 ≤ wordTCount bw) :
    bw = [] ∨ 1 ≤ wordTCount bw := by
  rcases h with rfl | rfl | rfl | rfl | h
  · exact Or.inl rfl
  all_goals first | (right; decide) | (right; omega)

theorem g73v_inv_T (bw : CircuitWord) (h : g73v_Inv bw) (hh : bw.head? ≠ some .t) :
    g73v_Inv (.t :: bw) := by
  obtain ⟨hsh, q, hs, hc⟩ := h
  have htc := g73v_tcT bw
  refine ⟨?_, g73v_qT q, g73v_sT bw q hs, ?_⟩
  · rcases g73v_shape_tc bw hsh with rfl | h1
    · exact Or.inr (Or.inl rfl)
    · right; right; right; right; omega
  · rw [htc]
    rcases hc with ⟨h0, hp⟩ | ⟨h1, hht, _⟩ | ⟨h1, _, hp | hp⟩ | ⟨h2, hht, _⟩ | ⟨h2, _, hp | hp⟩
    · right; left; exact ⟨by omega, rfl, (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · exact absurd hht hh
    · right; right; right; left; exact ⟨by omega, rfl, (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · right; right; right; left; exact ⟨by omega, rfl, (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · exact absurd hht hh
    · right; right; right; left; exact ⟨by omega, rfl, (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · right; right; right; left; exact ⟨by omega, rfl, (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩

theorem g73v_inv_HT (bw : CircuitWord) (h : g73v_Inv bw) (hh : bw.head? ≠ some .t) :
    g73v_Inv (.h :: .t :: bw) := by
  obtain ⟨hsh, q, hs, hc⟩ := h
  have htc := g73v_tcHT bw
  refine ⟨?_, g73v_qHT q, g73v_sHT bw q hs, ?_⟩
  · rcases g73v_shape_tc bw hsh with rfl | h1
    · exact Or.inr (Or.inr (Or.inl rfl))
    · right; right; right; right; omega
  · rw [htc]
    rcases hc with ⟨h0, hp⟩ | ⟨h1, hht, _⟩ | ⟨h1, _, hp | hp⟩ | ⟨h2, hht, _⟩ | ⟨h2, _, hp | hp⟩
    · right; right; left; exact ⟨by omega, by simp, Or.inl (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · exact absurd hht hh
    · right; right; right; right; exact ⟨by omega, by simp, Or.inr (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · right; right; right; right; exact ⟨by omega, by simp, Or.inr (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · exact absurd hht hh
    · right; right; right; right; exact ⟨by omega, by simp, Or.inr (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · right; right; right; right; exact ⟨by omega, by simp, Or.inr (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩

theorem g73v_inv_PHT (bw : CircuitWord) (h : g73v_Inv bw) (hh : bw.head? ≠ some .t) :
    g73v_Inv (.p :: .h :: .t :: bw) := by
  obtain ⟨hsh, q, hs, hc⟩ := h
  have htc := g73v_tcPHT bw
  refine ⟨?_, g73v_qPHT q, g73v_sPHT bw q hs, ?_⟩
  · rcases g73v_shape_tc bw hsh with rfl | h1
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · right; right; right; right; omega
  · rw [htc]
    rcases hc with ⟨h0, hp⟩ | ⟨h1, hht, _⟩ | ⟨h1, _, hp | hp⟩ | ⟨h2, hht, _⟩ | ⟨h2, _, hp | hp⟩
    · right; right; left; exact ⟨by omega, by simp, Or.inr (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · exact absurd hht hh
    · right; right; right; right; exact ⟨by omega, by simp, Or.inl (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · right; right; right; right; exact ⟨by omega, by simp, Or.inl (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · exact absurd hht hh
    · right; right; right; right; exact ⟨by omega, by simp, Or.inl (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩
    · right; right; right; right; exact ⟨by omega, by simp, Or.inl (by
        intro j; have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
        have h4 := hp 4; have h5 := hp 5
        simp [g73v_P, g73v_qT, g73v_qHT, g73v_qPHT] at h0 h1 h2 h3 h4 h5 ⊢
        fin_cases j <;> simp <;> omega)⟩

theorem g73v_head_app (bw x : CircuitWord) (h : (bw ++ x).head? ≠ some .t) (hx : x.head? ≠ some .t) :
    bw.head? ≠ some .t := by
  cases bw with
  | nil => simp
  | cons a l => simpa using h

theorem g73v_cliff_head (w : CircuitWord) (hw : IsCliffordWord w) : w.head? ≠ some .t := by
  cases w with
  | nil => simp
  | cons a l =>
    simp only [IsCliffordWord, List.mem_cons, not_or] at hw
    simpa using fun h => hw.1 h.symm

theorem g73v_nf (reps : Representatives .hp) (C : CircuitWord) (hC : IsNormalWord .hp reps C) :
    ∃ bw : CircuitWord, ∃ U : Matrix Bool Bool ℂ, U ∈ cliffordSet .hp ∧
      C = bw ++ reps.word U ∧ g73v_Inv bw := by
  induction hC with
  | tail U hU => exact ⟨[], U, hU, rfl, g73v_inv_nil⟩
  | withT w hw hhead ih =>
    obtain ⟨bw, U, hU, rfl, hi⟩ := ih
    exact ⟨_, U, hU, rfl, g73v_inv_T bw hi
      (g73v_head_app bw _ hhead (g73v_cliff_head _ (reps.clifford U hU)))⟩
  | withHT w hw hhead ih =>
    obtain ⟨bw, U, hU, rfl, hi⟩ := ih
    exact ⟨.h :: .t :: bw, U, hU, rfl, g73v_inv_HT bw hi
      (g73v_head_app bw _ hhead (g73v_cliff_head _ (reps.clifford U hU)))⟩
  | withPHT w hw hhead ih =>
    obtain ⟨bw, U, hU, rfl, hi⟩ := ih
    exact ⟨.p :: .h :: .t :: bw, U, hU, rfl, g73v_inv_PHT bw hi
      (g73v_head_app bw _ hhead (g73v_cliff_head _ (reps.clifford U hU)))⟩

theorem g73v_act_sub (A B : Matrix Bool Bool ℂ) (ψ : EuclideanSpace ℂ Bool) :
    act (A - B) ψ = act A ψ - act B ψ := by
  simp [act, Matrix.sub_mulVec]

theorem g73v_act_smul_one (c : ℂ) (ψ : EuclideanSpace ℂ Bool) :
    act (c • (1 : Matrix Bool Bool ℂ)) ψ = c • ψ := by
  ext i; simp [act, Matrix.smul_mulVec]

theorem g73v_bloch_sub (x y z x' y' z' : ℝ) :
    blochMatrix x y z - blochMatrix x' y' z' = blochMatrix (x - x') (y - y') (z - z') := by
  simp only [blochMatrix]; push_cast; module

theorem g73v_bloch_sq (a b c : ℝ) :
    blochMatrix a b c * blochMatrix a b c = ((a^2 + b^2 + c^2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  ext i j; cases i <;> cases j <;>
    simp [Matrix.mul_apply, blochMatrix, pauliX, pauliY, pauliZ] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem g73v_uniq (ψ : EuclideanSpace ℂ Bool) (hψ : ψ ≠ 0) (x y z x' y' z' : ℝ)
    (h1 : PauliStabilizes x y z ψ) (h2 : PauliStabilizes x' y' z' ψ) :
    x = x' ∧ y = y' ∧ z = z' := by
  unfold PauliStabilizes at h1 h2
  have hd : act (blochMatrix (x - x') (y - y') (z - z')) ψ = 0 := by
    rw [← g73v_bloch_sub, g73v_act_sub, h1, h2, sub_self]
  have hdd : act (blochMatrix (x - x') (y - y') (z - z') * blochMatrix (x - x') (y - y') (z - z')) ψ = 0 := by
    rw [g73v_act_mul, hd]; simp [act]
  rw [g73v_bloch_sq, g73v_act_smul_one, smul_eq_zero] at hdd
  rcases hdd with h | h
  · have h' : (x - x')^2 + (y - y')^2 + (z - z')^2 = 0 := by exact_mod_cast h
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x - x'), sq_nonneg (y - y'), sq_nonneg (z - z')]
  · exact absurd h hψ

theorem g73v_irr (u v : ℤ) (h : (u : ℝ) + v * Real.sqrt 2 = 0) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have : Real.sqrt 2 = ((-u / v : ℚ) : ℝ) := by
      push_cast; field_simp; linarith
    exact irrational_sqrt_two ⟨_, this.symm⟩

theorem g73v_even (n : ℕ) (hn : 2 ≤ n) (u v a : ℤ)
    (h : ((u : ℝ) + v * Real.sqrt 2) / Real.sqrt 2 ^ n = a) : u % 2 = 0 ∧ v % 2 = 0 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 2 ^ n ≠ 0 := by positivity
  rw [div_eq_iff hpos] at h
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 1 ≤ m := by omega
    rw [pow_mul, hs] at h
    have := g73v_irr (u - a * 2 ^ m) v (by push_cast; linarith)
    have hu : u = a * 2 ^ m := by linarith [this.1]
    refine ⟨?_, by rw [this.2]; rfl⟩
    rw [hu, show m = (m - 1) + 1 by omega, pow_succ]; simp [← mul_assoc]
  · have hm : 1 ≤ m := by omega
    rw [pow_succ, pow_mul, hs] at h
    have := g73v_irr u (v - a * 2 ^ m) (by push_cast; linarith)
    have hv : v = a * 2 ^ m := by linarith [this.2]
    refine ⟨by rw [this.1]; rfl, ?_⟩
    rw [hv, show m = (m - 1) + 1 by omega, pow_succ]; simp [← mul_assoc]

theorem g73v_cliff_int (w : CircuitWord) (hw : IsCliffordWord w) :
    ∃ a b c : ℤ, PauliStabilizes a b c (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w)) (ket false)) := by
  induction w with
  | nil =>
    refine ⟨0, 0, 1, ?_⟩
    have : act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp [])) (ket false) = ket false := by
      simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, chronologicalInstructions, act]
    rw [this]; simpa using g73v_Z0
  | cons l w ih =>
    simp only [IsCliffordWord, List.mem_cons, not_or] at hw
    obtain ⟨a, b, c, h⟩ := ih hw.2
    rw [g73v_wm_cons, g73v_act_mul]
    cases l
    · refine ⟨c, -b, a, ?_⟩
      have := g73v_stab_of_comm _ _ _ _ _ _ hadamard _ (g73v_commH _ _ _) h
      simpa [gateMatrix] using this
    · refine ⟨-b, a, c, ?_⟩
      have := g73v_stab_of_comm _ _ _ _ _ _ phaseS _ (g73v_commS _ _ _) h
      simpa [gateMatrix] using this
    · exact absurd rfl hw.1

theorem g73v_cl_unitary (U : Matrix Bool Bool ℂ) (hU : U ∈ cliffordSet .hp) : star U * U = 1 := by
  obtain ⟨w, hw, rfl⟩ := hU
  induction w with
  | nil => simp [QAlgorithms.Papers.Independent.Next46.P21.wordMatrix, chronologicalInstructions]
  | cons l w ih =>
    simp only [IsCliffordWord, List.mem_cons, not_or] at hw
    beta_reduce at ih ⊢
    rw [g73v_wm_cons, star_mul]
    have hl : star (gateMatrix .hp l) * gateMatrix .hp l = 1 := by
      cases l
      · simp only [gateMatrix, g73v_Hstar, hadamard_mul_self]
      · ext i j; cases i <;> cases j <;> simp [gateMatrix, phaseS, Matrix.star_apply, Matrix.mul_apply]
      · exact absurd rfl hw.1
    rw [show star (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w)) * star (gateMatrix .hp l) * (gateMatrix .hp l * (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w))) =
      star (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w)) * (star (gateMatrix .hp l) * gateMatrix .hp l) * (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp w)) by simp only [mul_assoc],
      hl, mul_one, ih hw.2]

theorem g73v_cl_star (U : Matrix Bool Bool ℂ) (hU : U ∈ cliffordSet .hp) : star U ∈ cliffordSet .hp := by
  obtain ⟨w, hw, rfl⟩ := hU
  obtain ⟨v, hv, hm⟩ := g73v_inv_word w
  refine ⟨v, ?_, hm⟩
  have h0 : wordTCount w = 0 := List.count_eq_zero.2 hw
  exact List.count_eq_zero.1 (hv.trans h0)

theorem g73v_T_not_cl : gateT ∉ cliffordSet .hp := by
  intro hT
  obtain ⟨w, hw, he⟩ := g73v_cl_mul _ _ hT g73v_H_mem
  obtain ⟨a, b, c, h⟩ := g73v_cliff_int w hw
  beta_reduce at he
  rw [he] at h
  have h1 := g73v_stab_of_comm _ _ _ _ _ _ hadamard _ (g73v_commH _ _ _) g73v_Z0
  have h2 := g73v_stab_of_comm _ _ _ _ _ _ gateT _ (g73v_commT _ _ _) h1
  rw [← g73v_act_mul] at h2
  have hne : act (gateT * hadamard) (ket false) ≠ 0 := by
    intro h0
    have := congrArg (fun v : EuclideanSpace ℂ Bool => v false) h0
    simp [act, ket, gateT, hadamard, Matrix.mulVec, dotProduct, Matrix.mul_apply] at this
  obtain ⟨ha, -, -⟩ := g73v_uniq _ hne _ _ _ _ _ _ h h2
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : Real.sqrt 2 ≠ 0 := by positivity
  have : (a : ℝ) * Real.sqrt 2 = 1 := by rw [ha]; field_simp; ring
  have h3 : ((2 * a ^ 2 : ℤ) : ℝ) = 1 := by
    push_cast; nlinarith [this]
  have h4 : (2 * a ^ 2 : ℤ) = 1 := by exact_mod_cast h3
  omega

theorem g73v_even2 (n : ℕ) (hn : 2 ≤ n) (q : StabilizerCoefficients) (j : Fin 3) (a : ℤ)
    (h : coefficientCoordinate n q j = a) :
    q ⟨2 * j.val, by omega⟩ % 2 = 0 ∧ q ⟨2 * j.val + 1, by omega⟩ % 2 = 0 :=
  g73v_even n hn _ _ a h

theorem g73v_S4 : phaseS * phaseS * phaseS * phaseS = 1 := by
  ext i j; cases i <;> cases j <;> simp [phaseS, Matrix.mul_apply]

theorem g73v_ptni (reps : Representatives .hp)
    (C : CircuitWord) (hC : IsNormalWord .hp reps C) (ht : 0 < wordTCount C) :
    (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp C)) ≠ 1 := by
  intro hE
  obtain ⟨bw, U, hU, rfl, ⟨hsh, q, hs, hc⟩⟩ := g73v_nf reps C hC
  have hUw := reps.clifford U hU
  have htc0 : wordTCount (reps.word U) = 0 := List.count_eq_zero.2 hUw
  have htc : wordTCount (bw ++ reps.word U) = wordTCount bw := by
    simp only [wordTCount, List.count_append] at htc0 ⊢; omega
  rw [htc] at ht
  have hcU := reps.computes U hU
  beta_reduce at hcU
  rw [g73v_wm_append, hcU] at hE
  have hUM : U * (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) = 1 := mul_eq_one_comm.1 hE
  have hMcl : (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) ∈ cliffordSet .hp := by
    have hsu := g73v_cl_unitary U hU
    have : (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) = star U := by
      calc (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) = (star U * U) * (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) := by rw [hsu, one_mul]
        _ = star U * (U * (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw))) := by rw [mul_assoc]
        _ = star U := by rw [hUM, mul_one]
    rw [this]; exact g73v_cl_star U hU
  have hnil : (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp [])) = 1 := rfl
  rcases hsh with rfl | rfl | rfl | rfl | h2
  · simp [wordTCount] at ht
  · apply g73v_T_not_cl
    rw [g73v_wm_cons, hnil, mul_one] at hMcl; exact hMcl
  · apply g73v_T_not_cl
    rw [g73v_wm_cons, g73v_wm_cons, hnil, mul_one] at hMcl
    have := g73v_cl_mul _ _ g73v_H_mem hMcl
    simpa [gateMatrix, ← mul_assoc, hadamard_mul_self] using this
  · apply g73v_T_not_cl
    rw [g73v_wm_cons, g73v_wm_cons, g73v_wm_cons, hnil, mul_one] at hMcl
    have h3 : phaseS * phaseS * phaseS ∈ cliffordSet .hp :=
      g73v_cl_mul _ _ (g73v_cl_mul _ _ g73v_S_mem g73v_S_mem) g73v_S_mem
    have := g73v_cl_mul _ _ (g73v_cl_mul _ _ g73v_H_mem h3) hMcl
    have e : hadamard * (phaseS * phaseS * phaseS) *
        (gateMatrix .hp .p * (gateMatrix .hp .h * gateMatrix .hp .t)) = gateT := by
      simp only [gateMatrix]
      rw [show hadamard * (phaseS * phaseS * phaseS) * (phaseS * (hadamard * gateT)) =
        hadamard * (phaseS * phaseS * phaseS * phaseS) * hadamard * gateT by simp only [mul_assoc],
        g73v_S4, mul_one, hadamard_mul_self, one_mul]
    rwa [e] at this
  · obtain ⟨w, hw, hwe⟩ := hMcl
    obtain ⟨a, b, c, hint⟩ := g73v_cliff_int w hw
    beta_reduce at hwe
    rw [hwe] at hint
    have hne : act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) (ket false) ≠ 0 := by
      intro h0
      have : act U (act (QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions .hp bw)) (ket false)) = ket false := by
        rw [← g73v_act_mul, hUM]; simp [act]
      rw [h0] at this
      have h1 := congrArg (fun v : EuclideanSpace ℂ Bool => v false) this
      simp [act, ket] at h1
    obtain ⟨e0, e1, e2⟩ := g73v_uniq _ hne _ _ _ _ _ _ hs hint
    have k0 := g73v_even2 _ h2 q 0 a e0
    have k1 := g73v_even2 _ h2 q 1 b e1
    have k2 := g73v_even2 _ h2 q 2 c e2
    have q0 : q 0 % 2 = 0 := k0.1
    have q1 : q 1 % 2 = 0 := k0.2
    have q2 : q 2 % 2 = 0 := k1.1
    have q3 : q 3 % 2 = 0 := k1.2
    have q4 : q 4 % 2 = 0 := k2.1
    have q5 : q 5 % 2 = 0 := k2.2
    rcases hc with ⟨h0, hp⟩ | ⟨h1, _, hp⟩ | ⟨h1, _, hp | hp⟩ | ⟨_, _, hp⟩ | ⟨_, _, hp | hp⟩
    · omega
    · omega
    · omega
    · omega
    all_goals
      have p1 := hp 1
      have p3 := hp 3
      simp at p1 p3
      omega


local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.8, Statement (II-B), proved pp.10–13: positive-T normal
words are not the identity matrix. In particular this is not the false
claim that all such words move |0>: the normal word T fixes |0>. -/
theorem solution (reps : Representatives .hp)
    (C : CircuitWord) (hC : IsNormalWord .hp reps C) (ht : 0 < wordTCount C) :
    wordMatrix .hp C ≠ 1 := by
  exact g73v_ptni reps C hC ht


end
