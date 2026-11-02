-- Prove2me | solution 1 for QAlgorithms.GottesmanThesis.stabEncoder_encodes
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:25:25.258905+00:00
-- url     : https://prove2.me/submissions/3154f1bc-1187-4b47-9db1-e561d84fd06f

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
set_option autoImplicit false

open QAlgorithms
open scoped Matrix ComplexConjugate

namespace StabEncoderProof

lemma zmod2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  simp [act]

lemma act_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext z
  simp [act, Matrix.mulVec_mulVec]

lemma act_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A + B) ψ = act A ψ + act B ψ := by
  ext z
  simp [act, Matrix.add_mulVec]

lemma act_add_right {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act A (ψ + φ) = act A ψ + act A φ := by
  ext z
  simp [act, Matrix.mulVec_add]

lemma act_smul_right {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (a : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act A (a • ψ) = a • act A ψ := by
  ext z
  simp [act, Matrix.mulVec_smul]

lemma act_smul_left {ι : Type*} [Fintype ι] (a : ℂ) (A : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (a • A) ψ = a • act A ψ := by
  ext z
  simp [act, Matrix.smul_mulVec]

lemma act_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (L : List (Matrix ι ι ℂ))
    (ψ : EuclideanSpace ℂ ι) :
    act L.reverse.prod ψ = L.foldl (fun φ A => act A φ) ψ := by
  induction L generalizing ψ with
  | nil => simp [act_one]
  | cons A tl ih =>
    simp only [List.reverse_cons, List.prod_append, List.prod_singleton, List.foldl_cons]
    rw [act_mul, ih]

lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    (c₁ ++ c₂).unitary = c₂.unitary * c₁.unitary := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma act_circuit_unitary {S : Set Gate} {n : ℕ} (c : Circuit S n) (ψ : EuclideanSpace ℂ (Qubits n)) :
    act c.unitary ψ = c.foldl (fun φ g => act (embedOp g.gate.mat g.wires) φ) ψ := by
  unfold Circuit.unitary
  rw [act_list_prod, List.foldl_map]

lemma ket_apply {ι : Type*} [DecidableEq ι] (z y : ι) :
    ket z y = if y = z then 1 else 0 := by
  simp [ket]

lemma act_ket_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (z y : ι) :
    act A (ket z) y = A y z := by
  simp [act, ket, EuclideanSpace.single, WithLp.ofLp_toLp]

lemma matrix_eq_of_act_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (h : ∀ z : ι, act A (ket z) = act B (ket z)) : A = B := by
  ext y z
  rw [← act_ket_apply A z y, ← act_ket_apply B z y, h z]

def flipBy {n : ℕ} (a : Fin n → ZMod 2) (z : Qubits n) : Qubits n :=
  fun q => xor (z q) (decide (a q = 1))

def phaseFactor (b : ZMod 2) (y : Bool) : ℂ :=
  if b = 1 ∧ y = true then -1 else 1

def phaseOf {n : ℕ} (b : Fin n → ZMod 2) (y : Qubits n) : ℂ :=
  ∏ q : Fin n, phaseFactor (b q) (y q)

lemma singlePauli_apply (aq bq : ZMod 2) (yq zq : Bool) :
    ((if bq = 1 then pauliZ else 1) * (if aq = 1 then pauliX else 1)) yq zq =
      if yq = xor zq (decide (aq = 1)) then phaseFactor bq yq else 0 := by
  by_cases ha : aq = 1 <;> by_cases hb : bq = 1 <;> cases yq <;> cases zq <;>
    simp [ha, hb, pauliX, pauliZ, phaseFactor, Matrix.mul_apply]

lemma rowPauli_apply {n : ℕ} (a b : Fin n → ZMod 2) (y z : Qubits n) :
    rowPauli a b y z = if y = flipBy a z then phaseOf b y else 0 := by
  simp only [rowPauli, kronAll, Matrix.of_apply, singlePauli_apply]
  by_cases hy : y = flipBy a z
  · rw [if_pos hy]
    unfold phaseOf
    refine Finset.prod_congr rfl fun q _ => ?_
    have hq : y q = xor (z q) (decide (a q = 1)) := congrFun hy q
    rw [if_pos hq]
  · rw [if_neg hy]
    have hex : ∃ q : Fin n, y q ≠ xor (z q) (decide (a q = 1)) := by
      by_contra hall
      exact hy (funext fun q => not_ne_iff.mp ( fun h => hall ⟨q, h⟩ ))
    rcases hex with ⟨q, hq⟩
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

lemma act_rowPauli_ket {n : ℕ} (a b : Fin n → ZMod 2) (z : Qubits n) :
    act (rowPauli a b) (ket z) = phaseOf b (flipBy a z) • ket (flipBy a z) := by
  ext y
  rw [act_ket_apply, rowPauli_apply, PiLp.smul_apply, ket_apply, smul_eq_mul]
  by_cases hy : y = flipBy a z
  · subst hy; simp
  · simp [hy]

lemma flipBy_comm {n : ℕ} (a₁ a₂ : Fin n → ZMod 2) (z : Qubits n) :
    flipBy a₁ (flipBy a₂ z) = flipBy a₂ (flipBy a₁ z) := by
  ext q
  simp only [flipBy]
  cases z q <;> cases decide (a₁ q = 1) <;> cases decide (a₂ q = 1) <;> rfl

lemma phaseFactor_xor (b a : ZMod 2) (z : Bool) :
    phaseFactor b (xor z (decide (a = 1))) =
      phaseFactor b z * (if a * b = 1 then (-1 : ℂ) else 1) := by
  rcases zmod2_cases b with rfl | rfl <;> rcases zmod2_cases a with rfl | rfl <;> cases z <;>
    simp [phaseFactor, (by decide : (0 : ZMod 2) ≠ 1)]

lemma zmod2_sign_add (u v : ZMod 2) :
    (if u = 1 then (-1 : ℂ) else 1) * (if v = 1 then (-1 : ℂ) else 1) =
      if u + v = 1 then (-1 : ℂ) else 1 := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;>
    simp [(by decide : (0 : ZMod 2) ≠ 1), (by decide : (1 : ZMod 2) + 1 ≠ 1)]

lemma prod_zmod2_sign {α : Type*} (s : Finset α) (f : α → ZMod 2) :
    (∏ x ∈ s, (if f x = 1 then (-1 : ℂ) else 1)) =
      if (∑ x ∈ s, f x) = 1 then (-1 : ℂ) else 1 := by
  induction s using Finset.cons_induction with
  | empty => simp [(by decide : (0 : ZMod 2) ≠ 1)]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ih, zmod2_sign_add]

lemma phaseOf_flipBy {n : ℕ} (a b : Fin n → ZMod 2) (z : Qubits n) :
    phaseOf b (flipBy a z) =
      phaseOf b z * (if (∑ q : Fin n, a q * b q) = 1 then (-1 : ℂ) else 1) := by
  unfold phaseOf flipBy
  simp only [phaseFactor_xor, Finset.prod_mul_distrib, prod_zmod2_sign]

lemma zmod2_eq_of_add_eq_zero (u v : ZMod 2) (h : u + v = 0) : u = v := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;>
    revert h <;> decide

lemma rowPauli_comm_of_symp {n : ℕ} (a₁ b₁ a₂ b₂ : Fin n → ZMod 2)
    (h : ∑ q : Fin n, (a₁ q * b₂ q + b₁ q * a₂ q) = 0) :
    rowPauli a₁ b₁ * rowPauli a₂ b₂ = rowPauli a₂ b₂ * rowPauli a₁ b₁ := by
  have hsum : (∑ q : Fin n, a₁ q * b₂ q) = ∑ q : Fin n, a₂ q * b₁ q := by
    rw [Finset.sum_add_distrib] at h
    have h' := zmod2_eq_of_add_eq_zero _ _ h
    rw [h']
    refine Finset.sum_congr rfl fun q _ => mul_comm (b₁ q) (a₂ q)
  apply matrix_eq_of_act_ket
  intro z
  rw [act_mul, act_mul, act_rowPauli_ket, act_rowPauli_ket, act_smul_right, act_smul_right,
    act_rowPauli_ket, act_rowPauli_ket, smul_smul, smul_smul, flipBy_comm a₁ a₂ z]
  congr 1
  have h1 := phaseOf_flipBy a₂ b₂ z
  have h2 := phaseOf_flipBy a₁ b₁ (flipBy a₂ z)
  rw [flipBy_comm a₁ a₂ z] at h2
  have h3 := phaseOf_flipBy a₂ b₁ z
  have h4 := phaseOf_flipBy a₁ b₁ z
  have h5 := phaseOf_flipBy a₂ b₂ (flipBy a₁ z)
  have h6 := phaseOf_flipBy a₁ b₂ z
  rw [h2, h1, h3, h5, h4, h6, hsum]
  ring

lemma wire1_apply {N : ℕ} (w : Fin N) (i : Fin 1) : Stabilizer.wire1 w i = w := rfl

lemma mem_range_wire1 {N : ℕ} (w a : Fin N) :
    a ∈ Set.range (Stabilizer.wire1 w) ↔ a = w := by
  constructor
  · rintro ⟨i, rfl⟩; rfl
  · rintro rfl; exact ⟨0, rfl⟩

lemma embedOp_ofMatrix1_apply {N : ℕ} (M : Matrix Bool Bool ℂ) (w : Fin N) (y z : Qubits N) :
    embedOp (Gate.ofMatrix1 M).mat (Stabilizer.wire1 w) y z =
      if ∀ a : Fin N, a ≠ w → y a = z a then M (y w) (z w) else 0 := by
  change (if ∀ a : Fin N, a ∉ Set.range (Stabilizer.wire1 w) → y a = z a then
    M (y (Stabilizer.wire1 w 0)) (z (Stabilizer.wire1 w 0)) else 0) = _
  simp only [mem_range_wire1, wire1_apply]

lemma mem_range_wire2 {N : ℕ} (c t : Fin N) (hct : c ≠ t) (a : Fin N) :
    a ∈ Set.range (Stabilizer.wire2 c t hct) ↔ a = c ∨ a = t := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [Stabilizer.wire2]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [Stabilizer.wire2]⟩
    · exact ⟨1, by simp [Stabilizer.wire2]⟩

lemma stabCtrlApp_embedOp_apply {N : ℕ} (a b : Bool) (hab : (a, b) ≠ (false, false))
    (ctrl tgt : Fin N) (h : ctrl ≠ tgt) (y z : Qubits N) :
    embedOp (stabCtrlApp a b hab ctrl tgt h).gate.mat (stabCtrlApp a b hab ctrl tgt h).wires y z =
      if ∀ q : Fin N, ¬(q = ctrl ∨ q = tgt) → y q = z q then
        controlled ((if b then pauliZ else 1) * (if a then pauliX else 1))
          (y ctrl, y tgt) (z ctrl, z tgt)
      else 0 := by
  change (if ∀ q : Fin N, q ∉ Set.range (Stabilizer.wire2 ctrl tgt h) → y q = z q then
    controlled ((if b then pauliZ else 1) * (if a then pauliX else 1))
      (y (Stabilizer.wire2 ctrl tgt h 0), y (Stabilizer.wire2 ctrl tgt h 1))
      (z (Stabilizer.wire2 ctrl tgt h 0), z (Stabilizer.wire2 ctrl tgt h 1)) else 0) = _
  have hw0 : Stabilizer.wire2 ctrl tgt h 0 = ctrl := rfl
  have hw1 : Stabilizer.wire2 ctrl tgt h 1 = tgt := rfl
  simp only [mem_range_wire2 ctrl tgt h, hw0, hw1]

lemma eq_or_eq_update_of_eq_off {N : ℕ} (w : Fin N) (y z : Qubits N) (hzw : z w = false) :
    (∀ a : Fin N, a ≠ w → y a = z a) ↔ y = z ∨ y = Function.update z w true := by
  constructor
  · intro h
    cases hyw : y w
    · left; ext a
      by_cases haw : a = w
      · subst haw; rw [hyw, hzw]
      · exact h a haw
    · right; ext a
      by_cases haw : a = w
      · subst haw; simp [hyw]
      · simp [haw, h a haw]
  · rintro (rfl | rfl) a ha
    · rfl
    · simp [ha]

lemma act_hadamard_ket {N : ℕ} (w : Fin N) (z : Qubits N) (hzw : z w = false) :
    act (embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 w)) (ket z) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (ket z + ket (Function.update z w true)) := by
  ext y
  rw [act_ket_apply, embedOp_ofMatrix1_apply, PiLp.smul_apply, PiLp.add_apply,
    ket_apply, ket_apply, smul_eq_mul]
  simp only [hadamard, Matrix.of_apply, hzw, Bool.and_false, eq_or_eq_update_of_eq_off w y z hzw]
  have hne : z ≠ Function.update z w true := by
    intro h
    have := congrFun h w
    simp [hzw] at this
  by_cases hyz : y = z
  · subst hyz
    simp [hne]
  · by_cases hyu : y = Function.update z w true
    · subst hyu
      simp [hyz]
    · simp [hyz, hyu]

lemma act_pauliZ_ket {N : ℕ} (w : Fin N) (z : Qubits N) :
    act (embedOp (Gate.ofMatrix1 pauliZ).mat (Stabilizer.wire1 w)) (ket z) =
      (if z w then (-1 : ℂ) else 1) • ket z := by
  ext y
  rw [act_ket_apply, embedOp_ofMatrix1_apply, PiLp.smul_apply, ket_apply, smul_eq_mul]
  simp only [pauliZ, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz, mul_zero]
    by_cases h : ∀ a : Fin N, a ≠ w → y a = z a
    · rw [if_pos h]
      have hyw : y w ≠ z w := by
        intro heq; apply hyz; ext a
        by_cases haw : a = w
        · subst haw; exact heq
        · exact h a haw
      exact if_neg hyw
    · exact if_neg h

lemma controlled_pauli_apply (a b yc yt zc zt : Bool) :
    controlled ((if b then pauliZ else 1) * (if a then pauliX else 1)) (yc, yt) (zc, zt) =
      if yc = zc then
        if zc then
          if yt = xor zt a then (if b ∧ yt then -1 else 1) else 0
        else
          if yt = zt then 1 else 0
      else 0 := by
  cases a <;> cases b <;> cases yc <;> cases yt <;> cases zc <;> cases zt <;>
    simp [controlled, pauliX, pauliZ, Matrix.mul_apply]

lemma act_stabCtrlApp_ket {N : ℕ} (a b : Bool) (hab : (a, b) ≠ (false, false))
    (ctrl tgt : Fin N) (h : ctrl ≠ tgt) (z : Qubits N) :
    act (embedOp (stabCtrlApp a b hab ctrl tgt h).gate.mat (stabCtrlApp a b hab ctrl tgt h).wires) (ket z) =
      if z ctrl then
        (if b ∧ xor (z tgt) a then (-1 : ℂ) else 1) • ket (Function.update z tgt (xor (z tgt) a))
      else ket z := by
  by_cases hzc : z ctrl = true
  · rw [if_pos hzc]
    ext y
    rw [act_ket_apply, stabCtrlApp_embedOp_apply, controlled_pauli_apply,
      PiLp.smul_apply, ket_apply, smul_eq_mul]
    let z' := Function.update z tgt (xor (z tgt) a)
    by_cases hy : y = z'
    · subst hy
      have hout : ∀ q : Fin N, ¬(q = ctrl ∨ q = tgt) → z' q = z q := by
        intro q hq
        exact Function.update_of_ne (fun hqt => hq (Or.inr hqt)) (xor (z tgt) a) z
      have hzc' : z' ctrl = z ctrl := Function.update_of_ne h (xor (z tgt) a) z
      have hzt' : z' tgt = xor (z tgt) a := Function.update_self tgt (xor (z tgt) a) z
      rw [if_pos hout, if_pos hzc', if_pos hzc, if_pos hzt', if_pos rfl, mul_one, hzt']
    · rw [if_neg hy, mul_zero]
      by_cases hout : ∀ q : Fin N, ¬(q = ctrl ∨ q = tgt) → y q = z q
      · rw [if_pos hout]
        by_cases hyc : y ctrl = z ctrl
        · rw [if_pos hyc, if_pos hzc]
          have hyt : y tgt ≠ xor (z tgt) a := by
            intro hyt
            apply hy
            ext q
            dsimp only [z']
            by_cases hqc : q = ctrl
            · subst hqc; rw [hyc, Function.update_of_ne h]
            · by_cases hqt : q = tgt
              · subst hqt; rw [hyt, Function.update_self]
              · rw [hout q (not_or.mpr ⟨hqc, hqt⟩), Function.update_of_ne hqt]
          exact if_neg hyt
        · exact if_neg hyc
      · exact if_neg hout
  · rw [if_neg hzc]
    ext y
    rw [act_ket_apply, stabCtrlApp_embedOp_apply, controlled_pauli_apply, ket_apply]
    by_cases hy : y = z
    · subst hy
      have hout : ∀ q : Fin N, ¬(q = ctrl ∨ q = tgt) → y q = y q := fun _ _ => rfl
      rw [if_pos hout, if_pos rfl, if_neg hzc, if_pos rfl, if_pos rfl]
    · rw [if_neg hy]
      by_cases hout : ∀ q : Fin N, ¬(q = ctrl ∨ q = tgt) → y q = z q
      · rw [if_pos hout]
        by_cases hyc : y ctrl = z ctrl
        · rw [if_pos hyc, if_neg hzc]
          have hyt : y tgt ≠ z tgt := by
            intro hyt
            apply hy
            ext q
            by_cases hqc : q = ctrl
            · subst hqc; exact hyc
            · by_cases hqt : q = tgt
              · subst hqt; exact hyt
              · exact hout q (not_or.mpr ⟨hqc, hqt⟩)
          exact if_neg hyt
        · exact if_neg hyc
      · exact if_neg hout

lemma flipBy_involutive {n : ℕ} (a : Fin n → ZMod 2) (z : Qubits n) :
    flipBy a (flipBy a z) = z := by
  ext q
  simp only [flipBy]
  cases z q <;> cases decide (a q = 1) <;> rfl

lemma flipBy_eq_iff {n : ℕ} (a : Fin n → ZMod 2) (y z : Qubits n) :
    y = flipBy a z ↔ z = flipBy a y := by
  constructor <;> (rintro rfl; rw [flipBy_involutive])

lemma act_rowPauli_apply {n : ℕ} (a b : Fin n → ZMod 2) (ψ : EuclideanSpace ℂ (Qubits n))
    (y : Qubits n) :
    act (rowPauli a b) ψ y = phaseOf b y * ψ (flipBy a y) := by
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, rowPauli_apply]
  have : ∀ z : Qubits n, (if y = flipBy a z then phaseOf b y else 0) * ψ z =
      if z = flipBy a y then phaseOf b y * ψ (flipBy a y) else 0 := by
    intro z
    simp only [flipBy_eq_iff a y z]
    by_cases hz : z = flipBy a y
    · subst hz; simp
    · simp [hz]
  simp [this]

lemma norm_phaseFactor (b : ZMod 2) (y : Bool) : ‖phaseFactor b y‖ = 1 := by
  unfold phaseFactor
  split_ifs <;> simp

lemma norm_phaseOf {n : ℕ} (b : Fin n → ZMod 2) (y : Qubits n) : ‖phaseOf b y‖ = 1 := by
  unfold phaseOf
  rw [norm_prod]
  simp [norm_phaseFactor]

lemma support_false_one_add_rowPauli {n : ℕ} (w : Fin n) (a b : Fin n → ZMod 2)
    (ψ : EuclideanSpace ℂ (Qubits n)) (haw : a w = 0)
    (hψ : ∀ y : Qubits n, y w = true → ψ y = 0) :
    ∀ y : Qubits n, y w = true → act (1 + rowPauli a b) ψ y = 0 := by
  intro y hyw
  rw [act_add, act_one, PiLp.add_apply, act_rowPauli_apply, hψ y hyw, zero_add]
  have hfw : flipBy a y w = true := by
    simp [flipBy, hyw, haw, (by decide : (0 : ZMod 2) ≠ 1)]
  rw [hψ (flipBy a y) hfw, mul_zero]

lemma norm_one_add_rowPauli {n : ℕ} (w : Fin n) (a b : Fin n → ZMod 2)
    (ψ : EuclideanSpace ℂ (Qubits n)) (haw : a w = 1)
    (hψ : ∀ y : Qubits n, y w = true → ψ y = 0) :
    ‖act (1 + rowPauli a b) ψ‖ = Real.sqrt 2 * ‖ψ‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  have hterm : ∀ y : Qubits n,
      ‖(act (1 + rowPauli a b) ψ) y‖ ^ 2 = ‖ψ y‖ ^ 2 + ‖ψ (flipBy a y)‖ ^ 2 := by
    intro y
    rw [act_add, act_one, PiLp.add_apply, act_rowPauli_apply]
    cases hyw : y w
    · have hfw : flipBy a y w = true := by simp [flipBy, hyw, haw]
      rw [hψ (flipBy a y) hfw]
      simp
    · rw [hψ y hyw]
      simp [norm_phaseOf]
  simp_rw [hterm, Finset.sum_add_distrib]
  have hperm : (∑ y : Qubits n, ‖ψ (flipBy a y)‖ ^ 2) = ∑ y : Qubits n, ‖ψ y‖ ^ 2 := by
    let e : Equiv.Perm (Qubits n) := Function.Involutive.toPerm (flipBy a) (flipBy_involutive a)
    exact Equiv.Perm.sum_comp e Finset.univ (fun y => ‖ψ y‖ ^ 2) (by simp)
  rw [hperm, ← two_mul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

lemma eq_sum_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    ψ = ∑ z : ι, ψ z • ket z := by
  ext y
  simp [ket_apply]

lemma act_sum {ι α : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (s : Finset α)
    (f : α → EuclideanSpace ℂ ι) :
    act A (∑ x ∈ s, f x) = ∑ x ∈ s, act A (f x) := by
  induction s using Finset.cons_induction with
  | empty => ext y; simp [act]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, act_add_right, ih]

lemma act_eq_of_act_ket_false {N : ℕ} (w : Fin N) (A B : Matrix (Qubits N) (Qubits N) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits N))
    (hψ : ∀ z : Qubits N, z w = true → ψ z = 0)
    (hAB : ∀ z : Qubits N, z w = false → act A (ket z) = act B (ket z)) :
    act A ψ = act B ψ := by
  rw [eq_sum_ket ψ, act_sum, act_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  cases hzw : z w
  · rw [act_smul_right, act_smul_right, hAB z hzw]
  · rw [hψ z hzw]
    ext y; simp [act]

lemma foldl_finset {α β : Type*} [DecidableEq α]
    (step : β → α → β) (stateOf : Finset α → β)
    (hstep : ∀ (a : α) (S : Finset α), a ∉ S → step (stateOf S) a = stateOf (insert a S))
    (L : List α) (hnd : L.Nodup) (S : Finset α) (hdisj : ∀ x ∈ L, x ∉ S) :
    L.foldl step (stateOf S) = stateOf (L.toFinset ∪ S) := by
  induction L generalizing S with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    have haS : a ∉ S := hdisj a List.mem_cons_self
    simp only [List.foldl_cons, List.toFinset_cons]
    rw [hstep a S haS, ih hnd.2 (insert a S)]
    · rw [Finset.insert_union, Finset.union_insert]
    · intro x hx
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hxa => hnd.1 (hxa ▸ hx), hdisj x (List.mem_cons_of_mem a hx)⟩

lemma foldl_finRange_univ {n : ℕ} {β : Type*}
    (step : β → Fin n → β) (stateOf : Finset (Fin n) → β)
    (hstep : ∀ (a : Fin n) (S : Finset (Fin n)), a ∉ S → step (stateOf S) a = stateOf (insert a S)) :
    (List.finRange n).foldl step (stateOf ∅) = stateOf Finset.univ := by
  rw [foldl_finset step stateOf hstep (List.finRange n) (List.nodup_finRange n) ∅ (by simp)]
  simp

lemma foldl_filterMap_ite {α β γ : Type*} (p : α → Prop) [DecidablePred p]
    (x : α → β) (g : γ → β → γ) (L : List α) (init : γ) :
    (L.filterMap fun a => if p a then some (x a) else none).foldl g init =
      L.foldl (fun acc a => if p a then g acc (x a) else acc) init := by
  induction L generalizing init with
  | nil => rfl
  | cons a tl ih =>
    by_cases ha : p a <;> simp [ha, List.foldl_cons, ih]

lemma foldl_filterMap_dite {α β γ : Type*} (p : α → Prop) [DecidablePred p]
    (x : (a : α) → p a → β) (g : γ → β → γ) (L : List α) (init : γ) :
    (L.filterMap fun a => if h : p a then some (x a h) else none).foldl g init =
      L.foldl (fun acc a => if h : p a then g acc (x a h) else acc) init := by
  induction L generalizing init with
  | nil => rfl
  | cons a tl ih =>
    by_cases ha : p a <;> simp [ha, List.foldl_cons, ih]

lemma foldl_dite_GateApp_smul {S : Set Gate} {N : ℕ} {α : Type*}
    (p : α → Prop) [DecidablePred p] (x : (a : α) → p a → GateApp S N)
    (L : List α) (c : ℂ) (φ : EuclideanSpace ℂ (Qubits N)) :
    L.foldl (fun ψ a => if h : p a then act (embedOp (x a h).gate.mat (x a h).wires) ψ else ψ) (c • φ) =
      c • L.foldl (fun ψ a => if h : p a then act (embedOp (x a h).gate.mat (x a h).wires) ψ else ψ) φ := by
  induction L generalizing φ with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.foldl_cons]
    split_ifs
    · rw [act_smul_right, ih]
    · rw [ih]

lemma act_orderedProd {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (U : Fin t → Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (orderedProd U) ψ = (List.finRange t).foldl (fun φ i => act (U i) φ) ψ := by
  unfold orderedProd
  rw [List.ofFn_eq_map, act_list_prod, List.foldl_map]

lemma xor_decide_zmod2 (u v : ZMod 2) :
    xor (decide (u = 1)) (decide (v = 1)) = decide (u + v = 1) := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;> decide

lemma xor_decide_zmod2_comm (u v : ZMod 2) :
    xor (decide (u = 1)) (decide (v = 1)) = decide (v + u = 1) := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;> decide

lemma qubits_ext_add {m k : ℕ} {u v : Qubits (m + k)}
    (h1 : ∀ j : Fin m, u (Fin.castAdd k j) = v (Fin.castAdd k j))
    (h2 : ∀ i : Fin k, u (Fin.natAdd m i) = v (Fin.natAdd m i)) : u = v := by
  ext q
  by_cases h : (q : ℕ) < m
  · exact h1 ⟨q, h⟩
  · have hq : q = Fin.natAdd m ⟨(q : ℕ) - m, by omega⟩ := by ext; simp; omega
    rw [hq, h2]

def xSum {m k : ℕ} (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (c : Qubits k)
    (S : Finset (Fin k)) (j : Fin m) : ZMod 2 :=
  ∑ i ∈ S, if c i then Hz j (Fin.natAdd m i) else 0

def initStab1 {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (c : Qubits k)
    (S : Finset (Fin k)) : Qubits (m + k) :=
  Fin.append (fun j : Fin m => decide (r ≤ (j : ℕ)) && decide (xSum Hz c S j = 1)) c

def initLogX {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (c : Qubits k)
    (S : Finset (Fin k)) : Qubits (m + k) :=
  Fin.append (fun j : Fin m => decide (r ≤ (j : ℕ)) && decide (xSum Hz c S j = 1))
    (fun i : Fin k => decide (i ∈ S) && c i)

lemma logicalXRow_fst_castAdd {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (i : Fin k) (j : Fin m) :
    (logicalXRow r Hz i).1 (Fin.castAdd k j) =
      if r ≤ (j : ℕ) then Hz j (Fin.natAdd m i) else 0 := by
  simp [logicalXRow]

lemma logicalXRow_fst_natAdd {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (i i' : Fin k) :
    (logicalXRow r Hz i).1 (Fin.natAdd m i') = if i' = i then 1 else 0 := by
  have hlt : ¬ (m + (i' : ℕ) < m) := by omega
  simp [logicalXRow, hlt, Fin.ext_iff]

lemma logicalXRow_snd_castAdd_ge {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (i : Fin k) (j : Fin m) (hj : r ≤ (j : ℕ)) :
    (logicalXRow r Hz i).2 (Fin.castAdd k j) = 0 := by
  have hlt : ¬ ((j : ℕ) < r) := not_lt.mpr hj
  simp [logicalXRow, hlt]

lemma logicalXRow_snd_natAdd {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (i i' : Fin k) :
    (logicalXRow r Hz i).2 (Fin.natAdd m i') = 0 := by
  have hlt : ¬ (m + (i' : ℕ) < m) := by omega
  simp [logicalXRow, hlt]

lemma flipBy_logicalX_initLogX {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (c : Qubits k) (S : Finset (Fin k)) (i : Fin k) (hiS : i ∉ S) (hci : c i = true) :
    flipBy (logicalXRow r Hz i).1 (initLogX r Hz c S) = initLogX r Hz c (insert i S) := by
  apply qubits_ext_add
  · intro j
    simp only [flipBy, initLogX, Fin.append_left, logicalXRow_fst_castAdd,
      xSum, Finset.sum_insert hiS, hci, ↓reduceIte]
    by_cases hj : r ≤ (j : ℕ)
    · simp only [hj, ↓reduceIte, decide_true, Bool.true_and]
      exact xor_decide_zmod2_comm _ _
    · simp [hj, (by decide : (0 : ZMod 2) ≠ 1)]
  · intro i'
    simp only [flipBy, initLogX, Fin.append_right, logicalXRow_fst_natAdd, Finset.mem_insert]
    by_cases hii : i' = i
    · subst hii; simp [hiS, hci]
    · simp [hii, (by decide : (0 : ZMod 2) ≠ 1)]

lemma phaseOf_logicalX_initLogX {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (c : Qubits k) (T : Finset (Fin k)) (i : Fin k) :
    phaseOf (logicalXRow r Hz i).2 (initLogX r Hz c T) = 1 := by
  unfold phaseOf
  rw [Fin.prod_univ_add]
  have h1 : (∏ j : Fin m, phaseFactor ((logicalXRow r Hz i).2 (Fin.castAdd k j))
      (initLogX r Hz c T (Fin.castAdd k j))) = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    by_cases hj : r ≤ (j : ℕ)
    · rw [logicalXRow_snd_castAdd_ge r Hz i j hj]
      simp [phaseFactor, (by decide : (0 : ZMod 2) ≠ 1)]
    · simp [initLogX, Fin.append_left, hj, phaseFactor]
  have h2 : (∏ i' : Fin k, phaseFactor ((logicalXRow r Hz i).2 (Fin.natAdd m i'))
      (initLogX r Hz c T (Fin.natAdd m i'))) = 1 := by
    refine Finset.prod_eq_one fun i' _ => ?_
    rw [logicalXRow_snd_natAdd]
    simp [phaseFactor, (by decide : (0 : ZMod 2) ≠ 1)]
  rw [h1, h2, mul_one]

lemma act_logicalX_step {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (c : Qubits k) (i : Fin k) (S : Finset (Fin k)) (hiS : i ∉ S) :
    act (if c i then logicalX r Hz i else 1) (ket (initLogX r Hz c S)) =
      ket (initLogX r Hz c (insert i S)) := by
  cases hci : c i
  · simp only [Bool.false_eq_true, ↓reduceIte, act_one]
    congr 1
    apply qubits_ext_add
    · intro j
      simp only [initLogX, Fin.append_left, xSum, Finset.sum_insert hiS, hci, Bool.false_eq_true,
        ↓reduceIte, zero_add]
      rfl
    · intro i'
      simp only [initLogX, Fin.append_right, Finset.mem_insert]
      by_cases hii : i' = i
      · subst hii; simp [hci]
      · simp [hii]
  · simp only [↓reduceIte, logicalX, act_rowPauli_ket,
      flipBy_logicalX_initLogX r Hz c S i hiS hci,
      phaseOf_logicalX_initLogX, one_smul]

lemma act_orderedProd_logicalX {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (c : Qubits k) :
    act (orderedProd fun i : Fin k => if c i then logicalX r Hz i else 1) (zeroKet (m + k)) =
      ket (initStab1 r Hz c Finset.univ) := by
  have h0 : zeroKet (m + k) = ket (initLogX r Hz c ∅) := by
    unfold zeroKet
    congr 1
    apply qubits_ext_add <;> intro x <;> simp [initLogX, xSum, (by decide : (0 : ZMod 2) ≠ 1)]
  have huniv : initLogX r Hz c Finset.univ = initStab1 r Hz c Finset.univ := by
    apply qubits_ext_add <;> intro x <;> simp [initLogX, initStab1]
  rw [h0, act_orderedProd,
    foldl_finRange_univ (fun φ i => act (if c i then logicalX r Hz i else 1) φ)
      (fun S => ket (initLogX r Hz c S)) (act_logicalX_step r Hz c),
    huniv]

def initStab1Inner {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (c : Qubits k)
    (S : Finset (Fin k)) (i : Fin k) (T : Finset (Fin m)) : Qubits (m + k) :=
  Fin.append
    (fun j : Fin m =>
      decide (r ≤ (j : ℕ)) &&
        decide ((xSum Hz c S j + if j ∈ T ∧ c i then Hz j (Fin.natAdd m i) else 0) = 1))
    c

lemma act_stabEncoderPart1_inner_step {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hab : (true, false) ≠ (false, false))
    (c : Qubits k) (S : Finset (Fin k)) (i : Fin k) (j : Fin m) (T : Finset (Fin m)) (hjT : j ∉ T) :
    (if r ≤ (j : ℕ) ∧ Hz j (Fin.natAdd m i) = 1 then
      act (embedOp (stabCtrlApp true false hab (Fin.natAdd m i) (Fin.castAdd k j)
        (castAdd_ne_natAdd j i)).gate.mat
        (stabCtrlApp true false hab (Fin.natAdd m i) (Fin.castAdd k j)
          (castAdd_ne_natAdd j i)).wires) (ket (initStab1Inner r Hz c S i T))
    else ket (initStab1Inner r Hz c S i T)) =
      ket (initStab1Inner r Hz c S i (insert j T)) := by
  by_cases hcond : r ≤ (j : ℕ) ∧ Hz j (Fin.natAdd m i) = 1
  · rw [if_pos hcond, act_stabCtrlApp_ket]
    have hctrl : initStab1Inner r Hz c S i T (Fin.natAdd m i) = c i := by
      simp [initStab1Inner]
    rw [hctrl]
    cases hci : c i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      apply qubits_ext_add
      · intro j'; simp [initStab1Inner, hci]
      · intro i'; simp [initStab1Inner]
    · simp only [Bool.false_eq_true, false_and, ↓reduceIte, one_smul, Bool.xor_true]
      congr 1
      apply qubits_ext_add
      · intro j'
        by_cases hjj : j' = j
        · subst hjj
          simp only [Function.update_self, initStab1Inner, Fin.append_left, hcond.1,
            decide_true, Bool.true_and, hjT, hci, false_and, ↓reduceIte, add_zero,
            Finset.mem_insert_self, and_self, hcond.2]
          have := xor_decide_zmod2 (xSum Hz c S j') 1
          simpa using this
        · have hne : Fin.castAdd k j' ≠ Fin.castAdd k j := fun h => hjj (Fin.castAdd_injective m k h)
          rw [Function.update_of_ne hne]
          simp [initStab1Inner, Fin.append_left, hjj]
      · intro i'
        have hne : Fin.natAdd m i' ≠ Fin.castAdd k j := castAdd_ne_natAdd j i'
        simp [Function.update_of_ne hne, initStab1Inner]
  · rw [if_neg hcond]
    congr 1
    apply qubits_ext_add
    · intro j'
      by_cases hjj : j' = j
      · subst hjj
        simp only [initStab1Inner, Fin.append_left, hjT, false_and, ↓reduceIte, add_zero,
          Finset.mem_insert_self, true_and]
        by_cases hr : r ≤ (j' : ℕ)
        · have hHz : Hz j' (Fin.natAdd m i) = 0 := by
            rcases zmod2_cases (Hz j' (Fin.natAdd m i)) with h0 | h1
            · exact h0
            · exact False.elim (hcond ⟨hr, h1⟩)
          simp [hr, hHz]
        · simp [hr]
      · simp [initStab1Inner, Fin.append_left, hjj]
    · intro i'; simp [initStab1Inner]

lemma act_stabEncoderPart1 {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hab : (true, false) ≠ (false, false)) (c : Qubits k) :
    act (Circuit.unitary
      ((List.finRange k).flatMap fun (i : Fin k) => (List.finRange m).filterMap fun (j : Fin m) =>
        if r ≤ (j : ℕ) ∧ Hz j (Fin.natAdd m i) = 1 then
          some (stabCtrlApp true false hab (Fin.natAdd m i) (Fin.castAdd k j)
            (castAdd_ne_natAdd j i))
        else none))
      (ket (Fin.append (fun _ => false) c)) = ket (initStab1 r Hz c Finset.univ) := by
  rw [act_circuit_unitary, List.foldl_flatMap]
  have h0 : ket (Fin.append (fun _ : Fin m => false) c) = ket (initStab1 r Hz c ∅) := by
    congr 1
    apply qubits_ext_add <;> intro x <;> simp [initStab1, xSum, (by decide : (0 : ZMod 2) ≠ 1)]
  rw [h0]
  refine foldl_finRange_univ _ (fun S => ket (initStab1 r Hz c S)) ?_
  intro i S hiS
  rw [foldl_filterMap_ite]
  have hstart : ket (initStab1 r Hz c S) = ket (initStab1Inner r Hz c S i ∅) := by
    congr 1
    apply qubits_ext_add <;> intro x <;> simp [initStab1, initStab1Inner]
  have hend : ket (initStab1Inner r Hz c S i Finset.univ) = ket (initStab1 r Hz c (insert i S)) := by
    congr 1
    apply qubits_ext_add
    · intro j
      simp [initStab1Inner, initStab1, xSum, Finset.sum_insert hiS, add_comm]
    · intro i'; simp [initStab1Inner, initStab1]
  rw [hstart, ← hend]
  exact foldl_finRange_univ _ (fun T => ket (initStab1Inner r Hz c S i T))
    (act_stabEncoderPart1_inner_step r Hz hab c S i)

def partialFlip {m k : ℕ} (Hx : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (i : Fin m)
    (z : Qubits (m + k)) (S : Finset (Fin (m + k))) : Qubits (m + k) :=
  fun q => if q = Fin.castAdd k i ∨ q ∈ S then flipBy (Hx i) z q else z q

noncomputable def partialVec {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (i : Fin m) (z : Qubits (m + k)) (S : Finset (Fin (m + k))) :
    EuclideanSpace ℂ (Qubits (m + k)) :=
  ket z + (∏ q' ∈ insert (Fin.castAdd k i) S, phaseFactor (Hz i q') (flipBy (Hx i) z q')) •
    ket (partialFlip Hx i z S)

lemma partialVec_inner_step {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (i : Fin m) (z : Qubits (m + k)) (hHx : Hx i (Fin.castAdd k i) = 1)
    (hzw : z (Fin.castAdd k i) = false) (q : Fin (m + k)) (S : Finset (Fin (m + k))) (hqS : q ∉ S) :
    (if h : q ≠ Fin.castAdd k i ∧
          (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false) then
      act (embedOp (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
        (Fin.castAdd k i) q (Ne.symm h.1)).gate.mat
        (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
          (Fin.castAdd k i) q (Ne.symm h.1)).wires) (partialVec Hx Hz i z S)
    else partialVec Hx Hz i z S) = partialVec Hx Hz i z (insert q S) := by
  let w := Fin.castAdd k i
  have hfw : flipBy (Hx i) z w = true := by simp [w, flipBy, hzw, hHx]
  by_cases hcond : q ≠ Fin.castAdd k i ∧ (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false)
  · rw [dif_pos hcond]
    unfold partialVec
    rw [act_add_right, act_smul_right, act_stabCtrlApp_ket, act_stabCtrlApp_ket,
      if_neg (by simp [hzw])]
    have hctrl : partialFlip Hx i z S w = true := by simp [w, partialFlip, hfw]
    have htgt : partialFlip Hx i z S q = z q := by simp [partialFlip, hcond.1, hqS]
    rw [if_pos hctrl, htgt]
    have hupd : Function.update (partialFlip Hx i z S) q (xor (z q) (decide (Hx i q = 1))) =
        partialFlip Hx i z (insert q S) := by
      ext q'
      by_cases hqq : q' = q
      · subst hqq; simp [partialFlip, flipBy]
      · rw [Function.update_of_ne hqq]
        simp [partialFlip, hqq]
    have hph : (if decide (Hz i q = 1) = true ∧ xor (z q) (decide (Hx i q = 1)) = true then (-1 : ℂ) else 1) =
        phaseFactor (Hz i q) (flipBy (Hx i) z q) := by
      simp [phaseFactor, flipBy]
    have hq_not_mem : q ∉ insert w S := by
      simp [w, hcond.1, hqS]
    rw [hupd, hph, smul_smul, mul_comm, Finset.insert_comm, Finset.prod_insert hq_not_mem]
  · rw [dif_neg hcond]
    unfold partialVec
    congr 1
    by_cases hqw : q = w
    · subst hqw
      have hins : insert w (insert w S) = insert w S := by ext x; simp
      have hp : partialFlip Hx i z (insert w S) = partialFlip Hx i z S := by
        ext x; simp [w, partialFlip]
      rw [hins, hp]
    · have hfalse : decide (Hx i q = 1) = false ∧ decide (Hz i q = 1) = false := by
        by_contra hnf
        apply hcond
        refine ⟨hqw, ?_⟩
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact hnf heq
      have hHxq : Hx i q ≠ 1 := of_decide_eq_false hfalse.1
      have hHzq : Hz i q ≠ 1 := of_decide_eq_false hfalse.2
      have hq_not_mem : q ∉ insert w S := by simp [w, hqw, hqS]
      have hpf : phaseFactor (Hz i q) (flipBy (Hx i) z q) = 1 := by simp [phaseFactor, hHzq]
      have hflip : flipBy (Hx i) z q = z q := by simp [flipBy, hHxq]
      have hp : partialFlip Hx i z (insert q S) = partialFlip Hx i z S := by
        ext q'
        by_cases hqq : q' = q
        · subst hqq; simp [w, partialFlip, hqw, hqS, hflip]
        · simp [partialFlip, hqq]
      rw [Finset.insert_comm, Finset.prod_insert hq_not_mem, hpf, one_mul, hp]

lemma act_stabGenCircuit_lt_ket {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (h1 : Gate.ofMatrix1 hadamard ∈ stabEncoderGateSet)
    (h2 : Gate.ofMatrix1 pauliZ ∈ stabEncoderGateSet)
    (i : Fin m) (hHx : Hx i (Fin.castAdd k i) = 1) (z : Qubits (m + k))
    (hzw : z (Fin.castAdd k i) = false) :
    (([⟨Gate.ofMatrix1 hadamard, h1, Stabilizer.wire1 (Fin.castAdd k i)⟩] :
        Circuit stabEncoderGateSet (m + k)) ++
      (if Hz i (Fin.castAdd k i) = 1 then
        ([⟨Gate.ofMatrix1 pauliZ, h2, Stabilizer.wire1 (Fin.castAdd k i)⟩] :
          Circuit stabEncoderGateSet (m + k)) else []) ++
      (List.finRange (m + k)).filterMap fun (q : Fin (m + k)) =>
        if h : q ≠ Fin.castAdd k i ∧
            (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false) then
          some (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
            (Fin.castAdd k i) q (Ne.symm h.1))
        else none).foldl (fun φ (g : GateApp stabEncoderGateSet (m + k)) =>
          act (embedOp g.gate.mat g.wires) φ) (ket z) =
      ((Real.sqrt 2)⁻¹ : ℂ) • act (1 + rowPauli (Hx i) (Hz i)) (ket z) := by
  let w := Fin.castAdd k i
  have hfw : flipBy (Hx i) z w = true := by simp [w, flipBy, hzw, hHx]
  have hp0 : Function.update z w true = partialFlip Hx i z ∅ := by
    ext q
    by_cases hqw : q = w
    · subst hqw; simp [w, partialFlip, hfw]
    · rw [Function.update_of_ne hqw]
      simp [w, partialFlip, hqw]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
    act_hadamard_ket w z hzw]
  have hz_step :
      (if Hz i w = 1 then
        ([⟨Gate.ofMatrix1 pauliZ, h2, Stabilizer.wire1 w⟩] :
          Circuit stabEncoderGateSet (m + k)) else []).foldl
        (fun φ (g : GateApp stabEncoderGateSet (m + k)) => act (embedOp g.gate.mat g.wires) φ)
        (((Real.sqrt 2)⁻¹ : ℂ) • (ket z + ket (Function.update z w true))) =
      ((Real.sqrt 2)⁻¹ : ℂ) • partialVec Hx Hz i z ∅ := by
    by_cases hHz : Hz i w = 1
    · rw [if_pos hHz, List.foldl_cons, List.foldl_nil, act_smul_right, act_add_right,
        act_pauliZ_ket, act_pauliZ_ket]
      simp [w, partialVec, hzw, hHz, phaseFactor, hfw, hp0]
    · rw [if_neg hHz, List.foldl_nil]
      simp [w, partialVec, hHz, phaseFactor, hp0]
  rw [hz_step, foldl_filterMap_dite, foldl_dite_GateApp_smul,
    foldl_finRange_univ _ (fun S => partialVec Hx Hz i z S)
      (partialVec_inner_step Hx Hz i z hHx hzw)]
  congr 1
  unfold partialVec
  have huniv : insert w Finset.univ = (Finset.univ : Finset (Fin (m + k))) := by ext x; simp
  have hp_univ : partialFlip Hx i z Finset.univ = flipBy (Hx i) z := by ext x; simp [partialFlip]
  rw [huniv, hp_univ, act_add, act_one, act_rowPauli_ket]
  rfl

lemma act_stabGenCircuit_lt {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (h1 : Gate.ofMatrix1 hadamard ∈ stabEncoderGateSet)
    (h2 : Gate.ofMatrix1 pauliZ ∈ stabEncoderGateSet)
    (i : Fin m) (hHx : Hx i (Fin.castAdd k i) = 1) (ψ : EuclideanSpace ℂ (Qubits (m + k)))
    (hψ : ∀ z : Qubits (m + k), z (Fin.castAdd k i) = true → ψ z = 0) :
    (([⟨Gate.ofMatrix1 hadamard, h1, Stabilizer.wire1 (Fin.castAdd k i)⟩] :
        Circuit stabEncoderGateSet (m + k)) ++
      (if Hz i (Fin.castAdd k i) = 1 then
        ([⟨Gate.ofMatrix1 pauliZ, h2, Stabilizer.wire1 (Fin.castAdd k i)⟩] :
          Circuit stabEncoderGateSet (m + k)) else []) ++
      (List.finRange (m + k)).filterMap fun (q : Fin (m + k)) =>
        if h : q ≠ Fin.castAdd k i ∧
            (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false) then
          some (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
            (Fin.castAdd k i) q (Ne.symm h.1))
        else none).foldl (fun φ (g : GateApp stabEncoderGateSet (m + k)) =>
          act (embedOp g.gate.mat g.wires) φ) ψ =
      ((Real.sqrt 2)⁻¹ : ℂ) • act (1 + rowPauli (Hx i) (Hz i)) ψ := by
  rw [← act_circuit_unitary, ← act_smul_left]
  refine act_eq_of_act_ket_false (Fin.castAdd k i) _ _ ψ hψ fun z hzw => ?_
  rw [act_circuit_unitary, act_smul_left, act_stabGenCircuit_lt_ket Hx Hz h1 h2 i hHx z hzw]

lemma symp_row_sum_eq_zero {m n : ℕ} {Hx Hz : Matrix (Fin m) (Fin n) (ZMod 2)}
    (hcomm : SymplecticCommuting Hx Hz) (i j : Fin m) :
    ∑ q : Fin n, (Hx i q * Hz j q + Hz i q * Hx j q) = 0 := by
  have h := congrFun (congrFun hcomm i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    ← Finset.sum_add_distrib] at h
  exact h

lemma act_rowPauli_ge_initStab1 {m k r : ℕ} {Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)}
    (hstd : IsStandardForm r Hx Hz) (c : Qubits k) (i : Fin m) (hi : r ≤ (i : ℕ)) :
    act (rowPauli (Hx i) (Hz i)) (ket (initStab1 r Hz c Finset.univ)) =
      ket (initStab1 r Hz c Finset.univ) := by
  rw [act_rowPauli_ket]
  have hflip : flipBy (Hx i) (initStab1 r Hz c Finset.univ) = initStab1 r Hz c Finset.univ := by
    ext q
    rw [flipBy, hstd.2.2.1 i q hi]
    simp [(by decide : (0 : ZMod 2) ≠ 1)]
  rw [hflip]
  have hph : phaseOf (Hz i) (initStab1 r Hz c Finset.univ) = 1 := by
    unfold phaseOf
    rw [Fin.prod_univ_add]
    have h1 : (∏ j : Fin m, phaseFactor (Hz i (Fin.castAdd k j))
        (initStab1 r Hz c Finset.univ (Fin.castAdd k j))) =
        if xSum Hz c Finset.univ i = 1 then (-1 : ℂ) else 1 := by
      rw [Finset.prod_eq_single i]
      · have hHzi : Hz i (Fin.castAdd k i) = 1 := by
          rw [hstd.2.2.2 i (Fin.castAdd k i) hi hi i.isLt, Fin.val_castAdd, if_pos rfl]
        simp [initStab1, Fin.append_left, hi, hHzi, phaseFactor]
      · intro j _ hji
        by_cases hj : r ≤ (j : ℕ)
        · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
          have hHzj : Hz i (Fin.castAdd k j) = 0 := by
            rw [hstd.2.2.2 i (Fin.castAdd k j) hi hj j.isLt, Fin.val_castAdd, if_neg hne]
          simp [hHzj, phaseFactor, (by decide : (0 : ZMod 2) ≠ 1)]
        · simp [initStab1, Fin.append_left, hj, phaseFactor]
      · intro hi_mem; exact False.elim (hi_mem (Finset.mem_univ i))
    have h2 : (∏ i' : Fin k, phaseFactor (Hz i (Fin.natAdd m i'))
        (initStab1 r Hz c Finset.univ (Fin.natAdd m i'))) =
        if xSum Hz c Finset.univ i = 1 then (-1 : ℂ) else 1 := by
      have hterm : ∀ i' : Fin k,
          phaseFactor (Hz i (Fin.natAdd m i')) (initStab1 r Hz c Finset.univ (Fin.natAdd m i')) =
            if (if c i' then Hz i (Fin.natAdd m i') else 0) = 1 then (-1 : ℂ) else 1 := by
        intro i'
        simp only [initStab1, Fin.append_right, phaseFactor]
        cases c i' <;> simp [(by decide : (0 : ZMod 2) ≠ 1)]
      simp_rw [hterm, prod_zmod2_sign, xSum]
      rfl
    rw [h1, h2]
    rcases zmod2_cases (xSum Hz c Finset.univ i) with h0 | h0 <;>
      simp [h0, (by decide : (0 : ZMod 2) ≠ 1)]
  rw [hph, one_smul]

lemma stabEncoderPart2_invariant {m k r : ℕ} {Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)}
    (h1 : Gate.ofMatrix1 hadamard ∈ stabEncoderGateSet)
    (h2 : Gate.ofMatrix1 pauliZ ∈ stabEncoderGateSet)
    (hstd : IsStandardForm r Hx Hz) (hcomm : SymplecticCommuting Hx Hz)
    (L : List (Fin m)) (hnd : L.Nodup)
    (ψ_enc ψ_stab : EuclideanSpace ℂ (Qubits (m + k)))
    (hnorm : ‖ψ_enc‖ = 1)
    (hsupp : ∀ i ∈ L, (i : ℕ) < r → ∀ z : Qubits (m + k), z (Fin.castAdd k i) = true → ψ_enc z = 0)
    (hstab : ∀ i : Fin m, r ≤ (i : ℕ) → act (rowPauli (Hx i) (Hz i)) ψ_enc = ψ_enc)
    (hprop : ∃ C : ℝ, 0 < C ∧ ψ_stab = (C : ℂ) • ψ_enc) :
    let ψ_enc_end := L.foldl (fun φ (i : Fin m) =>
      (if (i : ℕ) < r then
        ([⟨Gate.ofMatrix1 hadamard, h1, Stabilizer.wire1 (Fin.castAdd k i)⟩] :
          Circuit stabEncoderGateSet (m + k)) ++
        (if Hz i (Fin.castAdd k i) = 1 then
          ([⟨Gate.ofMatrix1 pauliZ, h2, Stabilizer.wire1 (Fin.castAdd k i)⟩] :
            Circuit stabEncoderGateSet (m + k)) else []) ++
        (List.finRange (m + k)).filterMap fun (q : Fin (m + k)) =>
          if h : q ≠ Fin.castAdd k i ∧
              (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false) then
            some (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
              (Fin.castAdd k i) q (Ne.symm h.1))
          else none
      else []).foldl (fun χ (g : GateApp stabEncoderGateSet (m + k)) =>
        act (embedOp g.gate.mat g.wires) χ) φ) ψ_enc
    let ψ_stab_end := L.foldl (fun φ (i : Fin m) => act (1 + rowPauli (Hx i) (Hz i)) φ) ψ_stab
    ‖ψ_enc_end‖ = 1 ∧ ∃ C : ℝ, 0 < C ∧ ψ_stab_end = (C : ℂ) • ψ_enc_end := by
  induction L generalizing ψ_enc ψ_stab with
  | nil => exact ⟨hnorm, hprop⟩
  | cons i tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    by_cases hir : (i : ℕ) < r
    · rw [if_pos hir]
      have hHxi : Hx i (Fin.castAdd k i) = 1 := by
        rw [hstd.2.1 i (Fin.castAdd k i) hir (by simpa using hir), Fin.val_castAdd, if_pos rfl]
      have hsuppi : ∀ z : Qubits (m + k), z (Fin.castAdd k i) = true → ψ_enc z = 0 :=
        hsupp i List.mem_cons_self hir
      rw [act_stabGenCircuit_lt Hx Hz h1 h2 i hHxi ψ_enc hsuppi]
      let ψ_enc' := ((Real.sqrt 2)⁻¹ : ℂ) • act (1 + rowPauli (Hx i) (Hz i)) ψ_enc
      have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hnorm' : ‖ψ_enc'‖ = 1 := by
        dsimp only [ψ_enc']
        rw [norm_smul, norm_one_add_rowPauli (Fin.castAdd k i) (Hx i) (Hz i) ψ_enc hHxi hsuppi,
          hnorm, mul_one, ← Complex.ofReal_inv, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.mpr hsqrt_pos.le), inv_mul_cancel₀ hsqrt_pos.ne']
      have hsupp' : ∀ i' ∈ tl, (i' : ℕ) < r →
          ∀ z : Qubits (m + k), z (Fin.castAdd k i') = true → ψ_enc' z = 0 := by
        intro i' hi' hi'r z hz
        dsimp only [ψ_enc']
        rw [PiLp.smul_apply, smul_eq_mul]
        have hne : (i : ℕ) ≠ (i' : ℕ) := fun h => hnd.1 (Fin.ext h ▸ hi')
        have hHx_zero : Hx i (Fin.castAdd k i') = 0 := by
          rw [hstd.2.1 i (Fin.castAdd k i') hir (by simpa using hi'r), Fin.val_castAdd, if_neg hne]
        rw [support_false_one_add_rowPauli (Fin.castAdd k i') (Hx i) (Hz i) ψ_enc hHx_zero
          (hsupp i' (List.mem_cons_of_mem i hi') hi'r) z hz, mul_zero]
      have hstab' : ∀ i'' : Fin m, r ≤ (i'' : ℕ) → act (rowPauli (Hx i'') (Hz i'')) ψ_enc' = ψ_enc' := by
        intro i'' hi''
        dsimp only [ψ_enc']
        rw [act_smul_right, act_add, act_one, act_add_right, ← act_mul,
          rowPauli_comm_of_symp _ _ _ _ (symp_row_sum_eq_zero hcomm i'' i),
          act_mul, hstab i'' hi'']
      have hprop' : ∃ C : ℝ, 0 < C ∧
          act (1 + rowPauli (Hx i) (Hz i)) ψ_stab = (C : ℂ) • ψ_enc' := by
        rcases hprop with ⟨C, hC, rfl⟩
        refine ⟨C * Real.sqrt 2, mul_pos hC hsqrt_pos, ?_⟩
        dsimp only [ψ_enc']
        rw [act_smul_right, smul_smul, Complex.ofReal_mul, mul_assoc,
          ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hsqrt_pos.ne',
          Complex.ofReal_one, mul_one]
      exact ih hnd.2 ψ_enc' (act (1 + rowPauli (Hx i) (Hz i)) ψ_stab) hnorm' hsupp' hstab' hprop'
    · rw [if_neg hir, List.foldl_nil]
      have hir' : r ≤ (i : ℕ) := not_lt.mp hir
      have hsupp' : ∀ i' ∈ tl, (i' : ℕ) < r →
          ∀ z : Qubits (m + k), z (Fin.castAdd k i') = true → ψ_enc z = 0 :=
        fun i' hi' => hsupp i' (List.mem_cons_of_mem i hi')
      have hprop' : ∃ C : ℝ, 0 < C ∧
          act (1 + rowPauli (Hx i) (Hz i)) ψ_stab = (C : ℂ) • ψ_enc := by
        rcases hprop with ⟨C, hC, rfl⟩
        refine ⟨C * 2, by linarith, ?_⟩
        rw [act_smul_right, act_add, act_one, hstab i hir', ← two_smul ℂ ψ_enc,
          smul_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact ih hnd.2 ψ_enc (act (1 + rowPauli (Hx i) (Hz i)) ψ_stab) hnorm hsupp' hstab hprop'

lemma normalizedVec_pos_smul {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 < C)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    normalizedVec ((C : ℂ) • ψ) = ψ := by
  unfold normalizedVec
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC.le, hψ, mul_one,
    smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hC.ne',
    Complex.ofReal_one, one_smul]

end StabEncoderProof

open StabEncoderProof

theorem solution {m k r : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hstd : IsStandardForm r Hx Hz) (hcomm : SymplecticCommuting Hx Hz) (c : Qubits k) :
    act (stabEncoder r Hx Hz).unitary (ket (Fin.append (fun _ : Fin m => false) c)) =
      normalizedVec (stabEncodedState r Hx Hz c) := by
  unfold stabEncoder stabEncodedState
  rw [circuit_unitary_append, act_mul, act_stabEncoderPart1, act_orderedProd_logicalX,
    act_circuit_unitary, List.foldl_flatMap, act_orderedProd]
  let z₀ := initStab1 r Hz c Finset.univ
  have hnorm0 : ‖ket z₀‖ = 1 := by simp [ket]
  have hsupp0 : ∀ i ∈ List.finRange m, (i : ℕ) < r →
      ∀ z : Qubits (m + k), z (Fin.castAdd k i) = true → ket z₀ z = 0 := by
    intro i _ hir z hz
    rw [ket_apply, if_neg]
    intro hzz
    subst hzz
    have h0 : z₀ (Fin.castAdd k i) = false := by
      simp [z₀, initStab1, Fin.append_left, not_le.mpr hir]
    rw [h0] at hz
    exact Bool.false_ne_true hz
  have hstab0 : ∀ i : Fin m, r ≤ (i : ℕ) → act (rowPauli (Hx i) (Hz i)) (ket z₀) = ket z₀ :=
    act_rowPauli_ge_initStab1 hstd c
  have hprop0 : ∃ C : ℝ, 0 < C ∧ ket z₀ = (C : ℂ) • ket z₀ :=
    ⟨1, zero_lt_one, by simp⟩
  rcases stabEncoderPart2_invariant
    (Set.mem_union_left _ (Set.mem_insert _ _))
    (Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl))
    hstd hcomm (List.finRange m) (List.nodup_finRange m)
    (ket z₀) (ket z₀) hnorm0 hsupp0 hstab0 hprop0 with ⟨hnorm_end, C, hC, hprop_end⟩
  rw [hprop_end, normalizedVec_pos_smul C hC _ hnorm_end]
