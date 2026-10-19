-- Prove2me | solution 1 for Paley_construction_II
-- status  : ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-05T23:24:00.520904+00:00
-- url     : https://prove2.me/submissions/18895591-7ed9-4108-a03d-ce5ec475415e

import Mathlib

open Finset Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Key character-sum identity: for `d ≠ 0`, `∑ w, χ(w) χ(w - d) = -1`. -/
theorem quadraticChar_shift_product_sum (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ w : F, quadraticChar F w * quadraticChar F (w - d) = -1 := by
  set g : F → F := fun w => 1 - d * w⁻¹ with hgdef
  have hginj : Function.Injective g := by
    intro w1 w2 h
    simp only [hgdef, sub_right_inj] at h
    have h2 : w1⁻¹ = w2⁻¹ := mul_left_cancel₀ hd h
    have h3 := congrArg Inv.inv h2
    simpa using h3
  have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp hginj
  have hgsum : ∑ w : F, quadraticChar F (g w) = ∑ w : F, quadraticChar F w :=
    Fintype.sum_bijective g hgbij _ _ (fun w => rfl)
  rw [quadraticChar_sum_zero hF] at hgsum
  have hstep : ∀ w : F, quadraticChar F w * quadraticChar F (w - d) =
      quadraticChar F (w ^ 2) * quadraticChar F (g w) := by
    intro w
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [hgdef]
    by_cases hw : w = 0
    · simp [hw]
    · have hcancel : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
      have heq : w ^ 2 * (1 - d * w⁻¹) = w ^ 2 - w * d * (w * w⁻¹) := by ring
      rw [heq, hcancel, mul_one]
      ring
  simp_rw [hstep]
  rw [← Finset.add_sum_erase Finset.univ
      (fun w => quadraticChar F (w ^ 2) * quadraticChar F (g w)) (mem_univ (0 : F))]
  have hzero_term : quadraticChar F ((0 : F) ^ 2) * quadraticChar F (g 0) = 0 := by simp
  rw [hzero_term, zero_add]
  have hrw : ∀ w ∈ (Finset.univ.erase (0 : F)),
      quadraticChar F (w ^ 2) * quadraticChar F (g w) = quadraticChar F (g w) := by
    intro w hw
    rw [quadraticChar_sq_one' (Finset.mem_erase.mp hw).1, one_mul]
  rw [Finset.sum_congr rfl hrw]
  have hsplit : quadraticChar F (g 0) + ∑ w ∈ Finset.univ.erase (0 : F), quadraticChar F (g w) =
      ∑ w : F, quadraticChar F (g w) :=
    Finset.add_sum_erase Finset.univ (fun w => quadraticChar F (g w)) (mem_univ (0 : F))
  rw [hgsum] at hsplit
  have hg0 : g 0 = 1 := by simp [hgdef]
  rw [hg0, map_one] at hsplit
  linarith [hsplit]

private lemma sum_quadraticChar_shift_eq_zero (hchar : ringChar F ≠ 2) (c : F) :
    ∑ x : F, quadraticChar F (c - x) = 0 := by
  have hbij : Function.Bijective (fun x : F => c - x) := by
    constructor
    · intro a b hab; simpa using hab
    · intro y; exact ⟨c - y, by ring⟩
  have heq : ∑ x : F, quadraticChar F (c - x) = ∑ z : F, quadraticChar F z :=
    Fintype.sum_bijective (fun x : F => c - x) hbij (fun x => quadraticChar F (c - x))
      (fun z => quadraticChar F z) (fun x => rfl)
  rw [heq]
  exact quadraticChar_sum_zero hchar

private lemma sum_quadraticChar_translate_eq_zero (hchar : ringChar F ≠ 2) (a : F) :
    ∑ y : F, quadraticChar F (y - a) = 0 := by
  have hbij : Function.Bijective (fun y : F => y - a) := by
    constructor
    · intro p q hpq; simpa using hpq
    · intro w; exact ⟨w + a, by ring⟩
  have heq : ∑ y : F, quadraticChar F (y - a) = ∑ z : F, quadraticChar F z :=
    Fintype.sum_bijective (fun y : F => y - a) hbij (fun y => quadraticChar F (y - a))
      (fun z => quadraticChar F z) (fun y => rfl)
  rw [heq]
  exact quadraticChar_sum_zero hchar

private lemma sum_quadraticChar_sq (hchar : ringChar F ≠ 2) :
    ∑ w : F, (quadraticChar F w : ℝ) ^ 2 = (Fintype.card F : ℝ) - 1 := by
  rw [← Finset.add_sum_erase Finset.univ (fun w => (quadraticChar F w : ℝ) ^ 2) (mem_univ (0 : F))]
  have h0 : (quadraticChar F (0 : F) : ℝ) ^ 2 = 0 := by simp
  rw [h0, zero_add]
  have h1 : ∀ w ∈ Finset.univ.erase (0 : F), (quadraticChar F w : ℝ) ^ 2 = 1 := by
    intro w hw
    have := quadraticChar_sq_one (Finset.mem_erase.mp hw).1
    exact_mod_cast this
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (mem_univ (0 : F)),
      Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [Nat.cast_sub hcard]
  norm_num

/-- The bordered Jacobsthal matrix with a *symmetric* border (both border entries `1`),
used for `q ≡ 1 (mod 4)`, where `χ(-1) = 1` makes the whole matrix symmetric. -/
private noncomputable def paleyC2 (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | none, none => (0 : ℝ)
    | none, some _ => 1
    | some _, none => 1
    | some x, some y => (quadraticChar F (y - x) : ℝ)

private lemma paleyC2_diag (i : Option F) : paleyC2 F i i = 0 := by
  cases i with
  | none => simp [paleyC2]
  | some x => simp [paleyC2, sub_self]

private lemma paleyC2_off_pm (i j : Option F) (hij : i ≠ j) :
    paleyC2 F i j = 1 ∨ paleyC2 F i j = -1 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some y => left; simp [paleyC2]
  | some x =>
    cases j with
    | none => left; simp [paleyC2]
    | some y =>
      have hxy : (y - x : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm (fun h => hij (by rw [h])))
      have hsq : quadraticChar F (y - x) ^ 2 = 1 := quadraticChar_sq_one hxy
      have hfact : (quadraticChar F (y - x) - 1) * (quadraticChar F (y - x) + 1) = 0 := by
        nlinarith [hsq]
      rcases mul_eq_zero.mp hfact with h | h
      · left; show (quadraticChar F (y - x) : ℝ) = 1
        have : quadraticChar F (y - x) = 1 := by linarith
        rw [this]; norm_num
      · right; show (quadraticChar F (y - x) : ℝ) = -1
        have : quadraticChar F (y - x) = -1 := by linarith
        rw [this]; norm_num

private lemma paleyC2_symm (hpos1 : quadraticChar F (-1) = 1) :
    (paleyC2 F)ᵀ = paleyC2 F := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply]
  cases i with
  | none =>
    cases j with
    | none => simp [paleyC2]
    | some y => simp [paleyC2]
  | some x =>
    cases j with
    | none => simp [paleyC2]
    | some y =>
      show (quadraticChar F (x - y) : ℝ) = (quadraticChar F (y - x) : ℝ)
      have hxy : (x - y : F) = -(y - x) := by ring
      have hone : (-1 : F) = (-1 : F) := rfl
      have hchar_eq : quadraticChar F (x - y) = quadraticChar F (y - x) := by
        rw [hxy]
        have : (- (y - x) : F) = (-1) * (y - x) := by ring
        rw [this, map_mul, hpos1, one_mul]
      rw [hchar_eq]

private lemma paleyC2_orth (hchar : ringChar F ≠ 2) :
    paleyC2 F * (paleyC2 F)ᵀ = (Fintype.card F : ℝ) • (1 : Matrix (Option F) (Option F) ℝ) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [Fintype.sum_option]
  cases i with
  | none =>
    cases j with
    | none =>
      have hsum : ∑ x : F, (1 : ℝ) * (1 : ℝ) = (Fintype.card F : ℝ) * 1 := by
        rw [mul_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      simp only [paleyC2, Matrix.of_apply, mul_zero, zero_add, hsum, if_pos rfl, if_true]
    | some y =>
      have h0 : ∑ x : F, (quadraticChar F (x - y) : ℝ) = 0 := by
        exact_mod_cast sum_quadraticChar_translate_eq_zero (F := F) hchar y
      have hne : (none : Option F) ≠ some y := by simp
      have hsum : ∑ x : F, (1 : ℝ) * (quadraticChar F (x - y) : ℝ) = 0 := by simpa using h0
      simp only [paleyC2, Matrix.of_apply, zero_mul, mul_zero, zero_add, hsum, if_neg hne]
  | some x =>
    cases j with
    | none =>
      have h0 : ∑ y : F, (quadraticChar F (y - x) : ℝ) = 0 := by
        exact_mod_cast sum_quadraticChar_translate_eq_zero (F := F) hchar x
      have hne : (some x : Option F) ≠ none := by simp
      have hsum : ∑ y : F, (quadraticChar F (y - x) : ℝ) * (1 : ℝ) = 0 := by simpa using h0
      simp only [paleyC2, Matrix.of_apply, mul_zero, zero_add, hsum, if_neg hne]
    | some y =>
      by_cases hxy : x = y
      · subst hxy
        have hsum : ∑ z : F, (quadraticChar F (z - x) : ℝ) * (quadraticChar F (z - x) : ℝ) =
            (Fintype.card F : ℝ) - 1 := by
          have heach : ∀ z : F, (quadraticChar F (z - x) : ℝ) * (quadraticChar F (z - x) : ℝ) =
              (quadraticChar F (z - x) : ℝ) ^ 2 := by intro z; ring
          simp_rw [heach]
          have hbij : Function.Bijective (fun z : F => z - x) := by
            constructor
            · intro p q hpq; simpa using hpq
            · intro w; exact ⟨w + x, by ring⟩
          have heq : ∑ z : F, (quadraticChar F (z - x) : ℝ) ^ 2 =
              ∑ w : F, (quadraticChar F w : ℝ) ^ 2 :=
            Fintype.sum_bijective (fun z : F => z - x) hbij
              (fun z => (quadraticChar F (z - x) : ℝ) ^ 2) (fun w => (quadraticChar F w : ℝ) ^ 2)
              (fun z => rfl)
          rw [heq, sum_quadraticChar_sq (F := F) hchar]
        simp only [paleyC2, Matrix.of_apply, hsum, if_pos rfl, if_true]
        ring
      · have hd : (y - x : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
        have hsum : ∑ z : F, (quadraticChar F (z - x) : ℝ) * (quadraticChar F (z - y) : ℝ) = -1 := by
          have hbij : Function.Bijective (fun z : F => z - x) := by
            constructor
            · intro p q hpq; simpa using hpq
            · intro w; exact ⟨w + x, by ring⟩
          have heq : ∑ z : F, (quadraticChar F (z - x) : ℝ) * (quadraticChar F (z - y) : ℝ) =
              ∑ w : F, (quadraticChar F w : ℝ) * (quadraticChar F (w - (y - x)) : ℝ) :=
            Fintype.sum_bijective (fun z : F => z - x) hbij
              (fun z => (quadraticChar F (z - x) : ℝ) * (quadraticChar F (z - y) : ℝ))
              (fun w => (quadraticChar F w : ℝ) * (quadraticChar F (w - (y - x)) : ℝ))
              (fun z => by rw [show z - x - (y - x) = z - y by ring])
          rw [heq]
          have hshift : ∑ w : F, quadraticChar F w * quadraticChar F (w - (y - x)) = -1 :=
            quadraticChar_shift_product_sum (F := F) hchar hd
          exact_mod_cast hshift
        have hne : (some x : Option F) ≠ some y := fun h => hxy (Option.some.inj h)
        simp only [paleyC2, Matrix.of_apply, hsum, if_neg hne, mul_zero]
        ring

/-- Transport a `±1`-entried orthogonal matrix across an index equivalence. -/
private lemma transport_hadamard {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (M : Matrix ι ι ℝ) (c : ℝ)
    (hpm : ∀ i j, M i j = 1 ∨ M i j = -1)
    (horth : M * Mᵀ = c • (1 : Matrix ι ι ℝ)) :
    (∀ i j, (M.submatrix e e) i j = 1 ∨ (M.submatrix e e) i j = -1) ∧
      (M.submatrix e e) * (M.submatrix e e)ᵀ = c • (1 : Matrix ι' ι' ℝ) := by
  refine ⟨fun i j => hpm (e i) (e j), ?_⟩
  apply Matrix.ext
  intro i j
  have hlhs : ((M.submatrix e e) * (M.submatrix e e)ᵀ) i j = (M * Mᵀ) (e i) (e j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun l => M (e i) l * M (e j) l)
  rw [hlhs, horth]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · have hne : e i ≠ e j := fun heq => h (e.injective heq)
    simp [h, hne]

theorem solution {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 1) :
    ∃ M : Matrix (Fin (2 * (Fintype.card F + 1))) (Fin (2 * (Fintype.card F + 1))) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((2 * (Fintype.card F + 1) : ℕ) : ℝ) •
          (1 : Matrix (Fin (2 * (Fintype.card F + 1))) (Fin (2 * (Fintype.card F + 1))) ℝ) := by
  have hpos1 : quadraticChar F (-1) = 1 := by
    rw [quadraticChar_neg_one hchar]
    exact ZMod.χ₄_nat_one_mod_four hmod
  set C := paleyC2 F with hCdef
  set A : Matrix (Option F) (Option F) ℝ := C + 1 with hAdef
  set B : Matrix (Option F) (Option F) ℝ := C - 1 with hBdef
  have hCsymm : Cᵀ = C := paleyC2_symm (F := F) hpos1
  have hCorth : C * Cᵀ = (Fintype.card F : ℝ) • (1 : Matrix (Option F) (Option F) ℝ) :=
    paleyC2_orth (F := F) hchar
  have hCC : C * C = (Fintype.card F : ℝ) • (1 : Matrix (Option F) (Option F) ℝ) := by
    rw [← hCorth, hCsymm]
  have hApm : ∀ i j, A i j = 1 ∨ A i j = -1 := by
    intro i j
    by_cases hij : i = j
    · subst hij; left; simp [hAdef, hCdef, paleyC2_diag]
    · rcases paleyC2_off_pm (F := F) i j hij with h | h
      · left; simp [hAdef, hCdef, h, Matrix.one_apply_ne hij]
      · right; simp [hAdef, hCdef, h, Matrix.one_apply_ne hij]
  have hBpm : ∀ i j, B i j = 1 ∨ B i j = -1 := by
    intro i j
    by_cases hij : i = j
    · subst hij; right; simp [hBdef, hCdef, paleyC2_diag]
    · rcases paleyC2_off_pm (F := F) i j hij with h | h
      · left; simp [hBdef, hCdef, h, Matrix.one_apply_ne hij]
      · right; simp [hBdef, hCdef, h, Matrix.one_apply_ne hij]
  have hAsymm : Aᵀ = A := by rw [hAdef, Matrix.transpose_add, hCsymm, Matrix.transpose_one]
  have hBsymm : Bᵀ = B := by rw [hBdef, Matrix.transpose_sub, hCsymm, Matrix.transpose_one]
  have hAB : A * B = ((Fintype.card F : ℝ) - 1) • (1 : Matrix (Option F) (Option F) ℝ) := by
    have hexpand : A * B = C * C - 1 := by rw [hAdef, hBdef]; noncomm_ring
    rw [hexpand, hCC, sub_smul, one_smul]
  have hBA : B * A = ((Fintype.card F : ℝ) - 1) • (1 : Matrix (Option F) (Option F) ℝ) := by
    have hexpand : B * A = C * C - 1 := by rw [hAdef, hBdef]; noncomm_ring
    rw [hexpand, hCC, sub_smul, one_smul]
  have hABeq : A * B = B * A := by rw [hAB, hBA]
  have hsumsq : A * A + B * B = ((2 : ℝ) * (Fintype.card F : ℝ) + 2) •
      (1 : Matrix (Option F) (Option F) ℝ) := by
    have hexpand : A * A + B * B =
        (C * C + C * C) + ((1 : Matrix (Option F) (Option F) ℝ) + 1) := by
      rw [hAdef, hBdef]; noncomm_ring
    rw [hexpand, hCC]
    module
  set H : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℝ :=
    Matrix.fromBlocks A B B (-A) with hHdef
  have hHpm : ∀ i j, H i j = 1 ∨ H i j = -1 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [hHdef, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · exact hApm i j
    · exact hBpm i j
    · exact hBpm i j
    · rcases hApm i j with h | h
      · right; rw [Matrix.neg_apply, h]
      · left; rw [Matrix.neg_apply, h]; ring
  have hHsymm : Hᵀ = H := by
    rw [hHdef, Matrix.fromBlocks_transpose, hAsymm, hBsymm, Matrix.transpose_neg, hAsymm]
  have hHorth : H * Hᵀ = ((2 : ℝ) * (Fintype.card F : ℝ) + 2) •
      (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℝ) := by
    rw [hHsymm, hHdef, Matrix.fromBlocks_multiply]
    have e1 : A * B + B * (-A) = 0 := by rw [Matrix.mul_neg, ← hABeq]; abel
    have e2 : B * A + (-A) * B = 0 := by rw [Matrix.neg_mul, hABeq]; abel
    have e3 : B * B + (-A) * (-A) = A * A + B * B := by rw [neg_mul_neg]; abel
    rw [e1, e2, e3, hsumsq, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  set e : Fin (2 * (Fintype.card F + 1)) ≃ Option F ⊕ Option F :=
    (finCongr (by rw [Fintype.card_sum, Fintype.card_option]; ring)).trans
      (Fintype.equivFin (Option F ⊕ Option F)).symm
  obtain ⟨hpm', horth'⟩ := transport_hadamard e H ((2 : ℝ) * (Fintype.card F : ℝ) + 2) hHpm hHorth
  have hcast : ((2 : ℝ) * (Fintype.card F : ℝ) + 2) = ((2 * (Fintype.card F + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast] at horth'
  exact ⟨H.submatrix e e, hpm', horth'⟩
