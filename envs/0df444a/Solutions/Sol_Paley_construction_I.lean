-- Prove2me | solution 1 for Paley_construction_I
-- status  : ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-05T21:48:32.002032+00:00
-- url     : https://prove2.me/submissions/ae2a8c6f-97e9-4b21-93a9-8cda45aebce5

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

/-- `χ(-a) = -χ(a)` when `χ(-1) = -1`. -/
private lemma quadraticChar_neg_of_neg_one (hneg1 : quadraticChar F (-1) = -1) (a : F) :
    quadraticChar F (-a) = -quadraticChar F a := by
  have : (-a : F) = (-1) * a := by ring
  rw [this, map_mul, hneg1, neg_one_mul]

/-- The bordered Jacobsthal matrix: `C none none = 0`, `C none (some x) = 1`,
`C (some x) none = -1`, `C (some x) (some y) = χ(y - x)`. -/
private noncomputable def paleyC (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | none, none => (0 : ℝ)
    | none, some _ => 1
    | some _, none => -1
    | some x, some y => (quadraticChar F (y - x) : ℝ)

private lemma paleyC_diag (i : Option F) : paleyC F i i = 0 := by
  cases i with
  | none => simp [paleyC]
  | some x => simp [paleyC, sub_self]

private lemma paleyC_off_pm (i j : Option F) (hij : i ≠ j) :
    paleyC F i j = 1 ∨ paleyC F i j = -1 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some y => left; simp [paleyC]
  | some x =>
    cases j with
    | none => right; simp [paleyC]
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

private lemma paleyC_skew (hneg1 : quadraticChar F (-1) = -1) :
    (paleyC F)ᵀ = -paleyC F := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  cases i with
  | none =>
    cases j with
    | none => simp [paleyC]
    | some y => simp [paleyC]
  | some x =>
    cases j with
    | none => simp [paleyC]
    | some y =>
      show (quadraticChar F (x - y) : ℝ) = -(quadraticChar F (y - x) : ℝ)
      have hxy : (x - y : F) = -(y - x) := by ring
      have hchar_eq : quadraticChar F (x - y) = -quadraticChar F (y - x) := by
        rw [hxy]; exact quadraticChar_neg_of_neg_one hneg1 (y - x)
      rw [hchar_eq]
      push_cast
      ring

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

private lemma quadraticChar_swap (hneg1 : quadraticChar F (-1) = -1) (a b : F) :
    quadraticChar F (a - b) = -quadraticChar F (b - a) := by
  have h : (a - b : F) = -(b - a) := by ring
  rw [h]; exact quadraticChar_neg_of_neg_one hneg1 (b - a)

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

private lemma paleyC_orth (hchar : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) :
    paleyC F * paleyC F = (-(Fintype.card F : ℝ)) • (1 : Matrix (Option F) (Option F) ℝ) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Fintype.sum_option]
  cases i with
  | none =>
    cases j with
    | none =>
      have hsum : ∑ x : F, (1 : ℝ) * (-1 : ℝ) = -(Fintype.card F : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      simp only [paleyC, Matrix.of_apply, mul_zero, zero_add, hsum, if_pos rfl, if_true, mul_one]
    | some y =>
      have h0 : ∑ x : F, (quadraticChar F (y - x) : ℝ) = 0 := by
        exact_mod_cast sum_quadraticChar_shift_eq_zero (F := F) hchar y
      have hne : (none : Option F) ≠ some y := by simp
      simp only [paleyC, Matrix.of_apply, one_mul, zero_mul, zero_add, h0, if_neg hne, mul_zero]
  | some x =>
    cases j with
    | none =>
      have h0 : ∑ y : F, (quadraticChar F (y - x) : ℝ) = 0 := by
        exact_mod_cast sum_quadraticChar_translate_eq_zero (F := F) hchar x
      have hsum : ∑ y : F, (quadraticChar F (y - x) : ℝ) * (-1 : ℝ) = 0 := by
        simpa using h0
      have hne : (some x : Option F) ≠ none := by simp
      simp only [paleyC, Matrix.of_apply, mul_neg, mul_one, zero_add, if_neg hne, mul_zero,
        Finset.sum_neg_distrib, h0, neg_zero]
    | some y =>
      by_cases hxy : x = y
      · subst hxy
        have hswap : ∀ z : F, (quadraticChar F (x - z) : ℝ) = -(quadraticChar F (z - x) : ℝ) := by
          intro z; exact_mod_cast quadraticChar_swap hneg1 x z
        have hsum : ∑ z : F, (quadraticChar F (z - x) : ℝ) * (quadraticChar F (x - z) : ℝ) =
            -((Fintype.card F : ℝ) - 1) := by
          simp_rw [hswap, mul_neg]
          rw [Finset.sum_neg_distrib]
          congr 1
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
        simp only [paleyC, Matrix.of_apply, hsum, if_pos rfl, if_true]
        ring
      · have hd : (y - x : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
        have hswap : ∀ z : F, (quadraticChar F (y - z) : ℝ) = -(quadraticChar F (z - y) : ℝ) := by
          intro z; exact_mod_cast quadraticChar_swap hneg1 y z
        have hsum : ∑ z : F, (quadraticChar F (z - x) : ℝ) * (quadraticChar F (y - z) : ℝ) = 1 := by
          simp_rw [hswap, mul_neg]
          rw [Finset.sum_neg_distrib]
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
          have hshift' : ∑ w : F, (quadraticChar F w : ℝ) * (quadraticChar F (w - (y - x)) : ℝ) =
              -1 := by exact_mod_cast hshift
          rw [hshift']
          ring
        have hne : (some x : Option F) ≠ some y := fun h => hxy (Option.some.inj h)
        simp only [paleyC, Matrix.of_apply, hsum, if_neg hne, mul_zero]
        ring

private lemma paleyH_pm :
    ∀ i j : Option F, (paleyC F + 1) i j = 1 ∨ (paleyC F + 1) i j = -1 := by
  intro i j
  by_cases hij : i = j
  · subst hij
    left
    simp [Matrix.add_apply, paleyC_diag, Matrix.one_apply_eq]
  · rcases paleyC_off_pm (F := F) i j hij with h | h
    · left; simp [Matrix.add_apply, h, Matrix.one_apply_ne hij]
    · right; simp [Matrix.add_apply, h, Matrix.one_apply_ne hij]

private lemma paleyH_orth (hchar : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) :
    (paleyC F + 1) * (paleyC F + 1)ᵀ =
      ((Fintype.card F + 1 : ℕ) : ℝ) • (1 : Matrix (Option F) (Option F) ℝ) := by
  have hskew := paleyC_skew (F := F) hneg1
  have horth := paleyC_orth (F := F) hchar hneg1
  have htranspose : (paleyC F + 1)ᵀ = -paleyC F + 1 := by
    rw [Matrix.transpose_add, hskew, Matrix.transpose_one]
  rw [htranspose]
  have hexpand : (paleyC F + 1) * (-paleyC F + 1) = -(paleyC F * paleyC F) + 1 := by
    noncomm_ring
  have hcast : ((Fintype.card F + 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) + 1 := by push_cast; ring
  rw [hexpand, horth, neg_smul, neg_neg, hcast, add_smul, one_smul]

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
    (hchar : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3) :
    ∃ M : Matrix (Fin (Fintype.card F + 1)) (Fin (Fintype.card F + 1)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((Fintype.card F + 1 : ℕ) : ℝ) •
          (1 : Matrix (Fin (Fintype.card F + 1)) (Fin (Fintype.card F + 1)) ℝ) := by
  have hneg1 : quadraticChar F (-1) = -1 := by
    rw [quadraticChar_neg_one hchar]
    exact ZMod.χ₄_nat_three_mod_four hmod
  have hpm := paleyH_pm (F := F)
  have horth := paleyH_orth (F := F) hchar hneg1
  set e : Fin (Fintype.card F + 1) ≃ Option F :=
    (finCongr (Fintype.card_option (α := F)).symm).trans (Fintype.equivFin (Option F)).symm
  obtain ⟨hpm', horth'⟩ := transport_hadamard e (paleyC F + 1) ((Fintype.card F + 1 : ℕ) : ℝ)
    hpm horth
  exact ⟨(paleyC F + 1).submatrix e e, hpm', horth'⟩
