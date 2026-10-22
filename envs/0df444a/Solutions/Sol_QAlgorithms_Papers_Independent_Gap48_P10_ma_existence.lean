-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.ma_existence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:53:02.877297+00:00
-- url     : https://prove2.me/submissions/f7aa678b-1d7f-4ab2-8924-82532c42426a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

open scoped MatrixOrder


lemma g73q_p2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
lemma g73q_p3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [pow_succ, g73q_p2]
lemma g73q_p4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, g73q_p2]; norm_num
lemma g73q_i3 : Complex.I ^ 3 = - Complex.I := by
  rw [pow_succ, Complex.I_sq]; ring
lemma g73q_i4 : Complex.I ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, Complex.I_sq]; norm_num

lemma g73q_w_eq : QAlgorithms.gateT true true =
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 + Complex.I) := by
  have h : QAlgorithms.gateT true true = Complex.exp (Complex.I * Real.pi / 4) := rfl
  rw [h, show Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  push_cast
  ring_nf
  simp only [g73q_p2, g73q_p3, g73q_p4, Complex.I_sq, g73q_i3, g73q_i4]
  ring_nf

lemma g73q_s2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma g73q_HH : QAlgorithms.hadamard * QAlgorithms.hadamard = (1 : Mat) := by
  have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (Real.sqrt 2 : ℝ) ≠ 0)
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.hadamard, Matrix.mul_apply, Fintype.sum_bool] <;>
    field_simp <;> ring_nf <;> simp only [g73q_p2, g73q_p3, g73q_p4, Complex.I_sq, g73q_i3, g73q_i4] <;> ring_nf

lemma g73q_HX : QAlgorithms.hadamard * QAlgorithms.pauliX =
    QAlgorithms.phaseS * QAlgorithms.phaseS * QAlgorithms.hadamard := by
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.hadamard, QAlgorithms.pauliX, QAlgorithms.phaseS,
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal]

lemma g73q_TT : QAlgorithms.gateT * QAlgorithms.gateT = QAlgorithms.phaseS := by
  have h : Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) = Complex.I := by
    rw [← Complex.exp_add, show Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 = Real.pi / 2 * Complex.I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.gateT, QAlgorithms.phaseS, Matrix.mul_apply,
    Fintype.sum_bool, Matrix.diagonal, h]

lemma g73q_ST : QAlgorithms.phaseS * QAlgorithms.gateT = QAlgorithms.gateT * QAlgorithms.phaseS := by
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.gateT, QAlgorithms.phaseS, Matrix.mul_apply,
    Fintype.sum_bool, Matrix.diagonal, mul_comm]

lemma g73q_XT : QAlgorithms.pauliX * QAlgorithms.gateT = QAlgorithms.gateT *
    (scalarOmega * (QAlgorithms.phaseS * (QAlgorithms.phaseS * (QAlgorithms.phaseS * QAlgorithms.pauliX)))) := by
  have hw := g73q_w_eq
  have h : QAlgorithms.gateT true true = Complex.exp (Complex.I * Real.pi / 4) := rfl
  rw [h] at hw
  have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (Real.sqrt 2 : ℝ) ≠ 0)
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.gateT, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega,
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal, hw] <;> field_simp <;>
    ring_nf <;> simp only [g73q_p2, g73q_p3, g73q_p4, Complex.I_sq, g73q_i3, g73q_i4] <;> ring_nf

lemma g73q_HSH : QAlgorithms.hadamard * (QAlgorithms.phaseS * QAlgorithms.hadamard) =
    (QAlgorithms.phaseS * QAlgorithms.hadamard) *
      (scalarOmega ^ 7 * (QAlgorithms.phaseS * QAlgorithms.pauliX)) := by
  have hw := g73q_w_eq
  have hsc : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (Real.sqrt 2 : ℝ) ≠ 0)
  have hw2 : (QAlgorithms.gateT true true) ^ 2 = Complex.I := by
    have := congrFun (congrFun g73q_TT true) true
    simpa [QAlgorithms.gateT, QAlgorithms.phaseS, Matrix.mul_apply, Matrix.diagonal, sq] using this
  have h7 : scalarOmega ^ 7 = (-Complex.I * QAlgorithms.gateT true true) • (1 : Mat) := by
    simp only [scalarOmega, smul_pow, one_pow]
    congr 1
    rw [show 7 = 2 * 3 + 1 by rfl, pow_succ, pow_mul, hw2, g73q_i3]
  rw [h7, hw]
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.hadamard, QAlgorithms.phaseS, QAlgorithms.pauliX,
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal] <;> field_simp <;>
    ring_nf <;> simp only [g73q_p2, g73q_p3, g73q_p4, Complex.I_sq, g73q_i3, g73q_i4] <;> ring_nf

lemma g73q_cw_append (w1 w2 : List CliffordLetter) :
    cliffordWordMatrix (w1 ++ w2) = cliffordWordMatrix w1 * cliffordWordMatrix w2 := by
  simp [cliffordWordMatrix, List.prod_append]

lemma g73q_cw_cons (l : CliffordLetter) (w : List CliffordLetter) :
    cliffordWordMatrix (l :: w) = cliffordLetterMatrix l * cliffordWordMatrix w := by
  simp [cliffordWordMatrix]

lemma g73q_cl_mul {A B : Mat} (hA : A ∈ cliffordSet) (hB : B ∈ cliffordSet) : A * B ∈ cliffordSet := by
  obtain ⟨w1, rfl⟩ := hA; obtain ⟨w2, rfl⟩ := hB
  exact ⟨w1 ++ w2, g73q_cw_append w1 w2⟩

lemma g73q_cl_H : QAlgorithms.hadamard ∈ cliffordSet := ⟨[.h], by simp [cliffordWordMatrix, cliffordLetterMatrix]⟩
lemma g73q_cl_S : QAlgorithms.phaseS ∈ cliffordSet := ⟨[.s], by simp [cliffordWordMatrix, cliffordLetterMatrix]⟩
lemma g73q_cl_W : scalarOmega ∈ cliffordSet := ⟨[.«omega»], by simp [cliffordWordMatrix, cliffordLetterMatrix]⟩
lemma g73q_cl_X : QAlgorithms.pauliX ∈ cliffordSet := by
  have : QAlgorithms.pauliX = QAlgorithms.hadamard * (QAlgorithms.phaseS * QAlgorithms.phaseS * QAlgorithms.hadamard) := by
    rw [← g73q_HX, ← Matrix.mul_assoc, g73q_HH, Matrix.one_mul]
  rw [this]
  exact g73q_cl_mul g73q_cl_H (g73q_cl_mul (g73q_cl_mul g73q_cl_S g73q_cl_S) g73q_cl_H)

lemma g73q_sm_cons {s : Mat} (hs : s ∈ smallSet) (l : SmallLetter) : smallLetterMatrix l * s ∈ smallSet := by
  obtain ⟨w, rfl⟩ := hs
  exact ⟨l :: w, by simp⟩

lemma g73q_sm_one : (1 : Mat) ∈ smallSet := ⟨[], by simp⟩

lemma g73q_omega_comm (A : Mat) : scalarOmega * A = A * scalarOmega := by
  simp [scalarOmega]

lemma g73q_small_T {s : Mat} (hs : s ∈ smallSet) :
    ∃ C ∈ cliffordSet, s * QAlgorithms.gateT = QAlgorithms.gateT * C := by
  obtain ⟨w, rfl⟩ := hs
  induction w with
  | nil => exact ⟨1, ⟨[], rfl⟩, by simp⟩
  | cons l w ih =>
    obtain ⟨C, hC, hCe⟩ := ih
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.mul_assoc, hCe, ← Matrix.mul_assoc]
    cases l with
    | s => exact ⟨QAlgorithms.phaseS * C, g73q_cl_mul g73q_cl_S hC, by
        simp only [smallLetterMatrix]; rw [g73q_ST, Matrix.mul_assoc]⟩
    | «omega» => exact ⟨scalarOmega * C, g73q_cl_mul g73q_cl_W hC, by
        simp only [smallLetterMatrix]; rw [g73q_omega_comm, Matrix.mul_assoc]⟩
    | x =>
      refine ⟨(scalarOmega * (QAlgorithms.phaseS * (QAlgorithms.phaseS * (QAlgorithms.phaseS * QAlgorithms.pauliX)))) * C,
        g73q_cl_mul (g73q_cl_mul g73q_cl_W (g73q_cl_mul g73q_cl_S (g73q_cl_mul g73q_cl_S
          (g73q_cl_mul g73q_cl_S g73q_cl_X)))) hC, ?_⟩
      simp only [smallLetterMatrix]; rw [g73q_XT, Matrix.mul_assoc]

lemma g73q_coset {C : Mat} (hC : C ∈ cliffordSet) :
    ∃ s ∈ smallSet, C = s ∨ C = QAlgorithms.hadamard * s ∨
      C = QAlgorithms.phaseS * QAlgorithms.hadamard * s := by
  obtain ⟨w, rfl⟩ := hC
  induction w with
  | nil => exact ⟨1, g73q_sm_one, Or.inl rfl⟩
  | cons l w ih =>
    obtain ⟨s, hs, h⟩ := ih
    rw [g73q_cw_cons]
    cases l with
    | «omega» =>
      refine ⟨scalarOmega * s, g73q_sm_cons hs .«omega», ?_⟩
      simp only [cliffordLetterMatrix]
      rcases h with h | h | h <;> rw [h]
      · exact Or.inl rfl
      · right; left; rw [← Matrix.mul_assoc, g73q_omega_comm, Matrix.mul_assoc]
      · right; right
        rw [← Matrix.mul_assoc, g73q_omega_comm]; simp only [Matrix.mul_assoc]
    | s =>
      simp only [cliffordLetterMatrix]
      rcases h with h | h | h <;> rw [h]
      · exact ⟨QAlgorithms.phaseS * s, g73q_sm_cons hs .s, Or.inl rfl⟩
      · exact ⟨s, hs, Or.inr (Or.inr (by rw [Matrix.mul_assoc]))⟩
      · refine ⟨QAlgorithms.pauliX * s, g73q_sm_cons hs .x, Or.inr (Or.inl ?_)⟩
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← g73q_HX]
    | h =>
      simp only [cliffordLetterMatrix]
      rcases h with h | h | h <;> rw [h]
      · exact ⟨s, hs, Or.inr (Or.inl rfl)⟩
      · exact ⟨s, hs, Or.inl (by rw [← Matrix.mul_assoc, g73q_HH, Matrix.one_mul])⟩
      · refine ⟨scalarOmega ^ 7 * (QAlgorithms.phaseS * QAlgorithms.pauliX) * s, ?_, Or.inr (Or.inr ?_)⟩
        · have h1 := g73q_sm_cons (g73q_sm_cons hs .x) .s
          have h2 : ∀ n : ℕ, ∀ t ∈ smallSet, scalarOmega ^ n * t ∈ smallSet := by
            intro n; induction n with
            | zero => intro t ht; simpa using ht
            | succ n ihn => intro t ht; rw [pow_succ, Matrix.mul_assoc]; exact ihn _ (g73q_sm_cons ht .«omega»)
          have := h2 7 _ h1
          simp only [smallLetterMatrix] at this
          rwa [Matrix.mul_assoc, Matrix.mul_assoc]
        · rw [show QAlgorithms.hadamard * (QAlgorithms.phaseS * QAlgorithms.hadamard * s) =
              (QAlgorithms.hadamard * (QAlgorithms.phaseS * QAlgorithms.hadamard)) * s by
                simp only [Matrix.mul_assoc], g73q_HSH]
          simp only [Matrix.mul_assoc]

lemma g73q_key {C : Mat} (hC : C ∈ cliffordSet) :
    ∃ C' ∈ cliffordSet, C * QAlgorithms.gateT = QAlgorithms.gateT * C' ∨
      C * QAlgorithms.gateT = QAlgorithms.hadamard * QAlgorithms.gateT * C' ∨
      C * QAlgorithms.gateT = QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.gateT * C' := by
  obtain ⟨s, hs, h⟩ := g73q_coset hC
  obtain ⟨C', hC', e⟩ := g73q_small_T hs
  refine ⟨C', hC', ?_⟩
  rcases h with h | h | h <;> rw [h]
  · exact Or.inl e
  · right; left; rw [Matrix.mul_assoc, e, Matrix.mul_assoc]
  · right; right; rw [Matrix.mul_assoc, e]; simp only [Matrix.mul_assoc]

lemma g73q_Hval : cliffordH.val = QAlgorithms.hadamard := by
  simp [cliffordH, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix]

lemma g73q_SHval : cliffordSH.val = QAlgorithms.phaseS * QAlgorithms.hadamard := by
  simp [cliffordSH, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix]

def g73q_syl (q : Bool) : Mat :=
  (if q then QAlgorithms.phaseS * QAlgorithms.hadamard else QAlgorithms.hadamard) * QAlgorithms.gateT

lemma g73q_fm (body : List Bool) :
    ((body.flatMap (fun q => [Token.clifford (if q then cliffordSH else cliffordH), Token.t])).map
      tokenMatrix).prod = (body.map g73q_syl).prod := by
  induction body with
  | nil => simp
  | cons q b ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih]
    cases q <;> simp [tokenMatrix, g73q_syl, g73q_Hval, g73q_SHval, Matrix.mul_assoc]

lemma g73q_val (M : NormalForm) :
    maValue M = (if M.leadingT then QAlgorithms.gateT else 1) * (M.body.map g73q_syl).prod *
      M.terminal.val := by
  unfold maValue normalValue normalTokens
  rw [List.map_append, List.map_append, List.prod_append, List.prod_append, g73q_fm]
  cases M.leadingT <;> simp [tokenMatrix]

lemma g73q_syl_mem (q : Bool) {C : Mat} (hC : C ∈ cliffordSet) :
    (if q then QAlgorithms.phaseS * QAlgorithms.hadamard else QAlgorithms.hadamard) *
      QAlgorithms.phaseS * C ∈ cliffordSet := by
  cases q
  · exact g73q_cl_mul (g73q_cl_mul g73q_cl_H g73q_cl_S) hC
  · exact g73q_cl_mul (g73q_cl_mul (g73q_cl_mul g73q_cl_S g73q_cl_H) g73q_cl_S) hC

lemma g73q_TT' (X : Mat) : QAlgorithms.gateT * (QAlgorithms.gateT * X) = QAlgorithms.phaseS * X := by
  rw [← Matrix.mul_assoc, g73q_TT]

lemma g73q_exists (w : List Input) :
    ∃ M : NormalForm, maValue M = inputWordMatrix w ∧ normalTCount M ≤ inputTCount w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨⟨false, [], cliffordI⟩, by simp [g73q_val, cliffordI, cliffordOfWord, cliffordWordMatrix, inputWordMatrix],
      by simp [normalTCount]⟩
  | append_singleton w a ih =>
    obtain ⟨⟨lt, body, C⟩, hv, hc⟩ := ih
    have hW : inputWordMatrix (w ++ [a]) = inputWordMatrix w * inputMatrix a := by
      simp [inputWordMatrix, List.prod_append]
    rw [hW, ← hv, g73q_val]
    simp only [normalTCount] at hc ⊢
    have hTC : inputTCount (w ++ [a]) = inputTCount w +
        (match a with | .t => 1 | .clifford _ => 0) := by
      cases a <;> simp [inputTCount, List.filter_append]
    rw [hTC]
    cases a with
    | clifford C2 =>
      refine ⟨⟨lt, body, ⟨C.val * C2.val, g73q_cl_mul C.2 C2.2⟩⟩, ?_, ?_⟩
      · rw [g73q_val]; simp [inputMatrix, Matrix.mul_assoc]
      · simpa using hc
    | t =>
      obtain ⟨C', hC', h | h | h⟩ := g73q_key C.2
      · rcases List.eq_nil_or_concat body with hb | ⟨b', q, hb⟩
        · subst hb
          cases lt
          · refine ⟨⟨true, [], ⟨C', hC'⟩⟩, ?_, ?_⟩
            · rw [g73q_val]; simp [inputMatrix, h]
            · simp
          · refine ⟨⟨false, [], ⟨QAlgorithms.phaseS * C', g73q_cl_mul g73q_cl_S hC'⟩⟩, ?_, ?_⟩
            · rw [g73q_val]
              simp only [inputMatrix, if_true, List.map_nil, List.prod_nil, Matrix.mul_one,
                Bool.false_eq_true, if_false, Matrix.one_mul]
              rw [Matrix.mul_assoc _ C.val, h, g73q_TT']
            · simp
        · subst hb
          rw [List.concat_eq_append] at hc ⊢
          refine ⟨⟨lt, b', ⟨_, g73q_syl_mem q hC'⟩⟩, ?_, ?_⟩
          · rw [g73q_val]
            simp only [inputMatrix, List.map_append, List.prod_append, List.map_cons, List.map_nil,
              List.prod_cons, List.prod_nil, mul_one, g73q_syl]
            rw [Matrix.mul_assoc _ C.val, h]
            simp only [Matrix.mul_assoc, g73q_TT']
          · simp at hc ⊢; omega
      · refine ⟨⟨lt, body ++ [false], ⟨C', hC'⟩⟩, ?_, ?_⟩
        · rw [g73q_val]
          simp only [inputMatrix, List.map_append, List.prod_append, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one, g73q_syl]
          rw [Matrix.mul_assoc _ C.val, h]
          simp [Matrix.mul_assoc]
        · simp; omega
      · refine ⟨⟨lt, body ++ [true], ⟨C', hC'⟩⟩, ?_, ?_⟩
        · rw [g73q_val]
          simp only [inputMatrix, List.map_append, List.prod_append, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one, g73q_syl]
          rw [Matrix.mul_assoc _ C.val, h]
          simp [Matrix.mul_assoc]
        · simp; omega

lemma g73q_chrono_append (l1 l2 : List Letter) :
    chronologicalValue (l1 ++ l2) = chronologicalValue l2 * chronologicalValue l1 := by
  simp [chronologicalValue, List.prod_append]

lemma g73q_ltc_append (l1 l2 : List Letter) :
    letterTCount (l1 ++ l2) = letterTCount l1 + letterTCount l2 := by
  simp [letterTCount, List.filter_append]

lemma g73q_chrono_toks (toks : List Token) :
    chronologicalValue (toks.reverse.flatMap expandToken) =
      (toks.map (fun t => chronologicalValue (expandToken t))).prod := by
  induction toks with
  | nil => rfl
  | cons t ts ih =>
    rw [List.reverse_cons, List.flatMap_append, g73q_chrono_append, ih]
    simp

lemma g73q_ltc_toks (toks : List Token) :
    letterTCount (toks.reverse.flatMap expandToken) =
      (toks.map (fun t => letterTCount (expandToken t))).sum := by
  induction toks with
  | nil => rfl
  | cons t ts ih =>
    rw [List.reverse_cons, List.flatMap_append, g73q_ltc_append, ih]
    simp [add_comm]

lemma g73q_expC (C : Clifford) :
    chronologicalValue (expandClifford C) = C.val ∧ letterTCount (expandClifford C) = 0 := by
  constructor
  · have := Classical.choose_spec C.property
    simp only [chronologicalValue, expandClifford, List.map_reverse, List.reverse_reverse, List.map_map]
    conv_rhs => rw [← this]
    unfold cliffordWordMatrix
    congr 1
    apply List.map_congr_left
    intro a _
    cases a <;> rfl
  · unfold letterTCount expandClifford
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_map, List.mem_reverse] at ha
    obtain ⟨b, _, rfl⟩ := ha
    cases b <;> simp

lemma g73q_word (a b : Clifford) (M : NormalForm) :
    chronologicalValue (normalWord a b M) = normalValue a b M ∧
      letterTCount (normalWord a b M) = normalTCount M := by
  have hmem : ∀ tok ∈ normalTokens a b M, chronologicalValue (expandToken tok) = tokenMatrix tok ∧
      letterTCount (expandToken tok) = (match tok with | .t => 1 | _ => 0) := by
    intro tok htok
    cases tok with
    | clifford C => exact ⟨(g73q_expC C).1, (g73q_expC C).2⟩
    | t => exact ⟨by simp [chronologicalValue, expandToken, tokenMatrix, letterMatrix], by
        simp [letterTCount, expandToken]⟩
    | axis r =>
      exfalso
      simp [normalTokens] at htok
  constructor
  · unfold normalWord normalValue
    rw [g73q_chrono_toks]
    congr 1
    exact List.map_congr_left (fun tok h => (hmem tok h).1)
  · unfold normalWord
    rw [g73q_ltc_toks, List.map_congr_left (fun tok h => (hmem tok h).2)]
    unfold normalTokens normalTCount
    rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
    have : ∀ l : List Bool, ((l.flatMap (fun q => [Token.clifford (if q then b else a), Token.t])).map
        (fun tok => match tok with | .t => 1 | _ => 0)).sum = l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons q l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp; ring
    rw [this]
    cases M.leadingT <;> simp

/-- Theorem 2.3, PDF p.2: exact MA existence, including the actual chronological
H/S/T/omega expansion and its actual T-letter count. These extra representation
clauses unpack the source's circuit output; no global phase is discarded. -/
theorem solution (U : Mat) (hU : CliffordT U) :
    ∃ M : NormalForm, maValue M = U ∧
      chronologicalValue (normalWord cliffordH cliffordSH M) = U ∧
      letterTCount (normalWord cliffordH cliffordSH M) = normalTCount M := by
  obtain ⟨w, hw⟩ := hU
  obtain ⟨M, hM, -⟩ := g73q_exists w
  have hw2 := g73q_word cliffordH cliffordSH M
  refine ⟨M, hM.trans hw, ?_, hw2.2⟩
  rw [hw2.1]; exact hM.trans hw



end
