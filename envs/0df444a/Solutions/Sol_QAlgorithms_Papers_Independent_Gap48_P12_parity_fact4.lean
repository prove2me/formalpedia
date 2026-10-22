-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.parity_fact4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:40:27.70346+00:00
-- url     : https://prove2.me/submissions/646ed606-08b6-42e3-a326-0c85c795f92b

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



local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.12, Fact 4: T1/T2 --HT--> T2 and --PHT--> T1.
Membership uses actual circuit stabilization at its actual T-count. -/
theorem solution (C : CircuitWord) (h : InParityClass 0 C ∨ InParityClass 1 C) :
    InParityClass 1 (.h :: .t :: C) ∧ InParityClass 0 (.p :: .h :: .t :: C) := by
  constructor
  · rcases h with h | h
    · exact g73v_wHT 0 1 C (fun q h => by
      rw [g73v_par_iff] at h ⊢
      have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
      simp [parityPattern] at h0 h1 h2 h3 h4 h5
      intro j; fin_cases j <;> simp [parityPattern] <;> omega) h
    · exact g73v_wHT 1 1 C (fun q h => by
      rw [g73v_par_iff] at h ⊢
      have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
      simp [parityPattern] at h0 h1 h2 h3 h4 h5
      intro j; fin_cases j <;> simp [parityPattern] <;> omega) h
  · rcases h with h | h
    · exact g73v_wPHT 0 0 C (fun q h => by
      rw [g73v_par_iff] at h ⊢
      have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
      simp [parityPattern] at h0 h1 h2 h3 h4 h5
      intro j; fin_cases j <;> simp [parityPattern] <;> omega) h
    · exact g73v_wPHT 1 0 C (fun q h => by
      rw [g73v_par_iff] at h ⊢
      have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
      simp [parityPattern] at h0 h1 h2 h3 h4 h5
      intro j; fin_cases j <;> simp [parityPattern] <;> omega) h


end
