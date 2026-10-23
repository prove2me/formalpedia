-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P43.depolarizingKrausRange
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:46:22.431252+00:00
-- url     : https://prove2.me/submissions/755bf60b-12de-4eb3-b21f-f7e22c3da9fe

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
open QAlgorithms.Papers.Independent.Information100.P34 (weyl cyclicPhase)

section x8weyl
variable {d : ℕ} [NeZero d]

lemma x8_cp (x : ZMod d) : cyclicPhase d x = ZMod.stdAddChar x := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, cyclicPhase]

lemma x8_conj (x : ZMod d) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

lemma x8_esum (c : ZMod d) :
    ∑ x : ZMod d, (ZMod.stdAddChar (x * c) : ℂ) = if c = 0 then (d : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  split_ifs <;> simp

lemma x8_shift_pow (k : ℕ) (a b : ZMod d) :
    ((Matrix.of fun a b : ZMod d => if a = b + 1 then (1 : ℂ) else 0) ^ k) a b =
      if a = b + k then 1 else 0 := by
  induction k generalizing a b with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (b + 1)]
    · simp; congr 1; apply propext; constructor <;> intro h <;> rw [h] <;> ring
    · intro c _ hc; simp [hc]
    · simp

lemma x8_weyl (n m a b : ZMod d) :
    weyl n m a b = if a = b + n then (ZMod.stdAddChar (b * m) : ℂ) else 0 := by
  simp only [weyl, Matrix.diagonal_pow, Matrix.mul_diagonal, x8_shift_pow, ZMod.natCast_zmod_val]
  split_ifs <;> simp [x8_cp, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]

/-- Frobenius orthogonality of the Weyl operators. -/
lemma x8_weyl_orth (a b a' b' : ZMod d) :
    ∑ l, ∑ k, conj (weyl a b l k) * weyl a' b' l k =
      if (a, b) = (a', b') then (d : ℂ) else 0 := by
  simp only [x8_weyl]
  rw [Finset.sum_comm]
  have : ∀ k : ZMod d, ∑ l : ZMod d, conj (if l = k + a then (ZMod.stdAddChar (k * b) : ℂ) else 0) *
      (if l = k + a' then (ZMod.stdAddChar (k * b') : ℂ) else 0) =
      if a = a' then (ZMod.stdAddChar (k * (b' - b)) : ℂ) else 0 := by
    intro k
    rw [Finset.sum_eq_single (k + a)]
    · by_cases h : a = a'
      · subst h; simp only [if_true, x8_conj, ← AddChar.map_add_eq_mul]; congr 1; ring
      · rw [if_neg h, if_pos rfl, if_neg]; · simp
        intro h'; exact h (add_left_cancel h')
    · intro l _ hl; rw [if_neg hl]; simp
    · simp
  simp only [this]
  by_cases h : a = a'
  · subst h; simp only [if_true, x8_esum, sub_eq_zero, Prod.mk.injEq, true_and]
    by_cases hb : b' = b
    · subst hb; simp
    · rw [if_neg hb, if_neg (Ne.symm hb)]
  · simp [h]

/-- Completeness of the Weyl operators. -/
lemma x8_weyl_compl (l k l' k' : ZMod d) :
    ∑ x : ZMod d × ZMod d, weyl x.1 x.2 l k * conj (weyl x.1 x.2 l' k') =
      if k = k' ∧ l = l' then (d : ℂ) else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [x8_weyl]
  rw [Finset.sum_eq_single (l - k)]
  · have hl : l = k + (l - k) := by ring
    simp only [show (l = k + (l - k)) = True from eq_true hl, if_true]
    by_cases hk : k = k' ∧ l = l'
    · obtain ⟨rfl, rfl⟩ := hk
      simp only [show (l = k + (l - k)) = True from eq_true hl, if_true, and_self, x8_conj,
        ← AddChar.map_add_eq_mul]
      rw [show ∑ x : ZMod d, (ZMod.stdAddChar (k * x + -(k * x)) : ℂ) = ∑ x : ZMod d, 1 from
        Finset.sum_congr rfl fun x _ => by rw [add_neg_cancel, AddChar.map_zero_eq_one]]
      simp
    · rw [if_neg hk]
      by_cases h2 : l' = k' + (l - k)
      · simp only [h2, if_true, x8_conj, ← AddChar.map_add_eq_mul]
        have hkk : k ≠ k' := by
          intro e; apply hk; refine ⟨e, ?_⟩; rw [h2, ← e]; ring
        rw [Finset.sum_congr rfl (fun x _ => by rw [show k * x + -(k' * x) = x * (k - k') by ring]),
          x8_esum, if_neg (sub_ne_zero.mpr hkk)]
      · simp [h2]
  · intro a _ ha
    have : l ≠ k + a := by intro e; apply ha; rw [e]; ring
    simp [this]
  · simp

end x8weyl

section x8fin
variable {d : ℕ} [NeZero d]

local notation "eZ" => (ZMod.finEquiv d)

lemma x8_fw (hd : 0 < d) (a b i j : Fin d) :
    finiteWeyl d hd a b i j = weyl (eZ a) (eZ b) (eZ i) (eZ j) := rfl

lemma x8_fw_compl (hd : 0 < d) (l k l' k' : Fin d) :
    ∑ x : Fin d × Fin d, finiteWeyl d hd x.1 x.2 l k * conj (finiteWeyl d hd x.1 x.2 l' k') =
      if k = k' ∧ l = l' then (d : ℂ) else 0 := by
  refine (Fintype.sum_equiv ((eZ).toEquiv.prodCongr (eZ).toEquiv) _
    (fun z : ZMod d × ZMod d => weyl z.1 z.2 (eZ l) (eZ k) * conj (weyl z.1 z.2 (eZ l') (eZ k')))
    (fun x => rfl)).trans ?_
  rw [x8_weyl_compl]
  simp only [EmbeddingLike.apply_eq_iff_eq]

lemma x8_weyl_col (a b k k' : ZMod d) :
    ∑ l, conj (weyl a b l k) * weyl a b l k' = if k = k' then 1 else 0 := by
  simp only [x8_weyl]
  rw [Finset.sum_eq_single (k + a)]
  · by_cases h : k = k'
    · subst h; simp only [if_true, x8_conj, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one]
    · rw [if_pos rfl, if_neg, if_neg h]; · simp
      intro h'; exact h (add_right_cancel h')
  · intro l _ hl; rw [if_neg hl]; simp
  · simp

lemma x8_fw_unit (hd : 0 < d) (a b : Fin d) :
    (finiteWeyl d hd a b)ᴴ * finiteWeyl d hd a b = 1 := by
  ext k k'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  refine (Fintype.sum_equiv (eZ).toEquiv _
    (fun z : ZMod d => conj (weyl (eZ a) (eZ b) z (eZ k)) * weyl (eZ a) (eZ b) z (eZ k'))
    (fun x => rfl)).trans ?_
  rw [x8_weyl_col]
  simp only [EmbeddingLike.apply_eq_iff_eq]

lemma x8_fw_zero (hd : 0 < d) : finiteWeyl d hd ⟨0, hd⟩ ⟨0, hd⟩ = 1 := by
  ext i j
  have h0 : (⟨0, hd⟩ : Fin d) = 0 := Fin.ext (by simp)
  rw [x8_fw, h0, map_zero, x8_weyl, Matrix.one_apply]
  simp only [add_zero, mul_zero, AddChar.map_zero_eq_one, EmbeddingLike.apply_eq_iff_eq]

omit [NeZero d] in
lemma x8_gen_tw {X I : Type} [Fintype X] [Fintype I] (f : X → I → I → ℂ) (Y : I → I → ℂ)
    (l l' : I) :
    ∑ x, ∑ k', (∑ k, f x l k * Y k k') * conj (f x l' k') =
      ∑ k', ∑ k, Y k k' * ∑ x, f x l k * conj (f x l' k') := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => by ring

lemma x8_twirl (hd : 0 < d) (Y : Matrix (Fin d) (Fin d) ℂ) :
    ∑ x : Fin d × Fin d, finiteWeyl d hd x.1 x.2 * Y * (finiteWeyl d hd x.1 x.2)ᴴ =
      ((d : ℂ) * Y.trace) • 1 := by
  ext l l'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h := x8_gen_tw (fun (x : Fin d × Fin d) (l k : Fin d) => finiteWeyl d hd x.1 x.2 l k)
    (fun k k' => Y k k') l l'
  rw [h]
  simp only [x8_fw_compl]
  by_cases hl : l = l'
  · subst hl
    simp only [and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Matrix.trace, Matrix.diag, Finset.mul_sum, mul_one]
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp [hl]

end x8fin

section x8kraus

lemma x8_sum_ite {X M : Type} [Fintype X] [DecidableEq X] [AddCommMonoid M] (x0 : X) (A B : M) :
    ∑ x, (if x = x0 then A else B) = A + (Fintype.card X - 1) • B := by
  rw [Fintype.sum_eq_add_sum_compl x0, if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun x hx => if_neg (Finset.mem_compl.mp hx |> fun h => by
    simpa using h)), Finset.sum_const, Finset.card_compl, Finset.card_singleton]

lemma x8_sq (a : ℝ) (ha : 0 ≤ a) : conj ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = a := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]

lemma x8_sq' (a : ℝ) (ha : 0 ≤ a) : ((Real.sqrt a : ℝ) : ℂ) * conj ((Real.sqrt a : ℝ) : ℂ) = a := by
  rw [mul_comm, x8_sq a ha]

variable {d : ℕ}

lemma x8_cond (hd : 0 < d) (x : Fin d × Fin d) :
    (x.1.val = 0 ∧ x.2.val = 0) ↔ x = (⟨0, hd⟩, ⟨0, hd⟩) := by
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · rintro rfl; exact ⟨rfl, rfl⟩

lemma x8_K_eq (hd : 0 < d) (p : ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d × Fin d) :
    weylDepolarizingKraus d hd p U x =
      if x = (⟨0, hd⟩, ⟨0, hd⟩) then
        (Real.sqrt (1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      else (Real.sqrt (p / (d : ℝ)^2) : ℂ) •
        ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd x.1 x.2 *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  rw [weylDepolarizingKraus]
  exact if_congr (x8_cond hd x) rfl rfl

lemma x8_G_unit (hd : 0 < d) (U : Matrix.unitaryGroup (Fin d) ℂ) (a b : Fin d) :
    ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd a b * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᴴ *
      ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd a b * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = 1 := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hU : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hU' : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix (Fin d) (Fin d) ℂ)ᴴ (U : Matrix (Fin d) (Fin d) ℂ), hU,
    Matrix.one_mul, ← Matrix.mul_assoc (finiteWeyl d hd a b)ᴴ, x8_fw_unit, Matrix.one_mul, hU']

lemma x8_family (hd : 0 < d) (p : ℝ) (hp : 0 ≤ p)
    (hp1 : p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) (hd2 : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsKrausFamily (weylDepolarizingKraus d hd p U) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hD : (0 : ℝ) < (d : ℝ)^2 - 1 := by nlinarith
  have hD2 : (0 : ℝ) < (d : ℝ)^2 := by positivity
  have ha0 : 0 ≤ 1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2 := by
    rw [le_div_iff₀ hD] at hp1
    rw [sub_nonneg, div_le_one hD2]; linarith
  have ha1 : 0 ≤ p / (d : ℝ)^2 := div_nonneg hp hD2.le
  unfold IsKrausFamily
  simp only [x8_K_eq]
  have e : ∀ x : Fin d × Fin d, (if x = (⟨0, hd⟩, ⟨0, hd⟩) then
        (Real.sqrt (1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      else (Real.sqrt (p / (d : ℝ)^2) : ℂ) •
        ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd x.1 x.2 *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ))ᴴ * (if x = (⟨0, hd⟩, ⟨0, hd⟩) then
        (Real.sqrt (1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      else (Real.sqrt (p / (d : ℝ)^2) : ℂ) •
        ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd x.1 x.2 *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)) =
      if x = (⟨0, hd⟩, ⟨0, hd⟩) then
        (((1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2 : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
      else (((p / (d : ℝ)^2 : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    intro x
    split_ifs
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, smul_smul, RCLike.star_def, x8_sq _ ha0]
    · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, x8_G_unit, smul_smul,
        RCLike.star_def, x8_sq _ ha1]
  rw [Finset.sum_congr rfl (fun x _ => e x), x8_sum_ite, Fintype.card_prod, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
  convert one_smul ℂ (1 : Matrix (Fin d) (Fin d) ℂ) using 2
  have h1 : 1 ≤ d * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.cast_sub h1]
  push_cast
  field_simp
  ring

lemma x8_Gsum (hd : 0 < d) (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ x : Fin d × Fin d,
      ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd x.1 x.2 * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) *
        X * ((U : Matrix (Fin d) (Fin d) ℂ) * finiteWeyl d hd x.1 x.2 *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᴴ = ((d : ℂ) * X.trace) • 1 := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hU' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have e : ∀ x : Fin d × Fin d, (V * finiteWeyl d hd x.1 x.2 * Vᴴ) * X *
      (V * finiteWeyl d hd x.1 x.2 * Vᴴ)ᴴ =
      V * (finiteWeyl d hd x.1 x.2 * (Vᴴ * X * V) * (finiteWeyl d hd x.1 x.2)ᴴ) * Vᴴ := by
    intro x
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl (fun x _ => e x), ← Matrix.sum_mul, ← Matrix.mul_sum, x8_twirl,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU', Matrix.trace_mul_cycle,
    hU', Matrix.one_mul]

lemma x8_apply (hd : 0 < d) (p : ℝ) (hp : 0 ≤ p)
    (hp1 : p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) (hd2 : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    QAlgorithms.QuditFidelity.depolarizingMap d hd p =
      krausApply (weylDepolarizingKraus d hd p U) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hD : (0 : ℝ) < (d : ℝ)^2 - 1 := by nlinarith
  have hD2 : (0 : ℝ) < (d : ℝ)^2 := by positivity
  have ha0 : 0 ≤ 1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2 := by
    rw [le_div_iff₀ hD] at hp1
    rw [sub_nonneg, div_le_one hD2]; linarith
  have ha1 : 0 ≤ p / (d : ℝ)^2 := div_nonneg hp hD2.le
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hU' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  funext X
  rw [krausApply]
  simp only [x8_K_eq]
  set a0 : ℝ := 1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2
  set a1 : ℝ := p / (d : ℝ)^2
  have e : ∀ x : Fin d × Fin d, (if x = (⟨0, hd⟩, ⟨0, hd⟩) then
        (Real.sqrt a0 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      else (Real.sqrt a1 : ℂ) • (V * finiteWeyl d hd x.1 x.2 * Vᴴ)) * X *
      (if x = (⟨0, hd⟩, ⟨0, hd⟩) then
        (Real.sqrt a0 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      else (Real.sqrt a1 : ℂ) • (V * finiteWeyl d hd x.1 x.2 * Vᴴ))ᴴ =
      (a1 : ℂ) • ((V * finiteWeyl d hd x.1 x.2 * Vᴴ) * X * (V * finiteWeyl d hd x.1 x.2 * Vᴴ)ᴴ) +
        (if x = (⟨0, hd⟩, ⟨0, hd⟩) then ((a0 : ℂ) - a1) • X else 0) := by
    intro x
    split_ifs with hx
    · subst hx
      rw [x8_fw_zero, Matrix.mul_one, hU', Matrix.one_mul, Matrix.conjTranspose_one,
        Matrix.mul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, RCLike.star_def,
        x8_sq _ ha0, ← add_smul]
      congr 1; ring
    · simp only [add_zero, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        RCLike.star_def, x8_sq _ ha1, x8_sq' _ ha1]
  rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, ← Finset.smul_sum, x8_Gsum,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  simp only [QAlgorithms.QuditFidelity.depolarizingMap, smul_smul]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  congr 2
  · simp only [a1]; push_cast; field_simp
  · simp only [a0, a1]; push_cast; field_simp; ring

lemma x8_conj_single {n : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (k k' : Fin n) (i i' : Fin d) :
    (A * Matrix.single k k' (1 : ℂ) * Aᴴ) i i' = A i k * conj (A i' k') := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_eq_single k']
  · rw [Finset.sum_eq_single k]; · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma x8_gen_tr {n : ℕ} (f : Fin n → Fin d → ℂ) :
    ∑ k, ∑ k', ∑ j, f j k * conj (f j k') = ∑ j, ((Complex.normSq (∑ k, f j k) : ℝ) : ℂ) := by
  have e : ∀ j, ((Complex.normSq (∑ k, f j k) : ℝ) : ℂ) = ∑ k, ∑ k', f j k * conj (f j k') := by
    intro j; rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  simp only [e]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

lemma x8_necessary (hd : 0 < d) (hd2 : 2 ≤ d) (p : ℝ)
    (h : IsChannel (QAlgorithms.QuditFidelity.depolarizingMap d hd p)) :
    0 ≤ p ∧ p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1) := by
  obtain ⟨n, E, -, hE⟩ := h
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hD : (0 : ℝ) < (d : ℝ)^2 - 1 := by nlinarith
  have hdpos : (0 : ℝ) < d := by linarith
  set k0 : Fin d := ⟨0, hd⟩
  set k1 : Fin d := ⟨1, by omega⟩
  have h01 : k0 ≠ k1 := by simp [k0, k1, Fin.ext_iff]
  -- first test
  have t1 := congrFun (congrFun (hE (Matrix.single k1 k1 1)) k0) k0
  simp only [krausApply, Matrix.sum_apply, x8_conj_single, Complex.mul_conj] at t1
  simp only [QAlgorithms.QuditFidelity.depolarizingMap, Matrix.add_apply, Matrix.smul_apply,
    Matrix.trace_single_eq_same, mul_one, Matrix.one_apply_eq, Matrix.single_apply, h01.symm, false_and, if_false,
    smul_eq_mul, mul_one, mul_zero, add_zero] at t1
  have t1' := congrArg Complex.re t1
  simp only [Complex.ofReal_re, Complex.re_sum] at t1'
  have hp0 : 0 ≤ p / d := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => Complex.normSq_nonneg (E j k0 k1))
    linarith
  -- second test
  have t2 : ∑ k, ∑ k', (QAlgorithms.QuditFidelity.depolarizingMap d hd p
      (Matrix.single k k' 1)) k k' = ∑ k, ∑ k', krausApply E (Matrix.single k k' 1) k k' := by
    simp only [hE]
  simp only [krausApply, Matrix.sum_apply, x8_conj_single] at t2
  have hL : ∀ k k' : Fin d, (QAlgorithms.QuditFidelity.depolarizingMap d hd p
      (Matrix.single k k' 1)) k k' = if k = k' then ((p / d : ℝ) : ℂ) + ((1 - p : ℝ) : ℂ)
        else ((1 - p : ℝ) : ℂ) := by
    intro k k'
    simp only [QAlgorithms.QuditFidelity.depolarizingMap, Matrix.add_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul, and_self, if_true, mul_one]
    split_ifs with hk
    · subst hk; simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne _ _ _ hk, hk]
  simp only [hL] at t2
  have hR := x8_gen_tr (fun j k => E j k k)
  beta_reduce at hR
  have t3 := t2.trans hR
  have hite : ∀ k k' : Fin d, (if k = k' then ((p / d : ℝ) : ℂ) + ((1 - p : ℝ) : ℂ)
      else ((1 - p : ℝ) : ℂ)) = ((1 - p : ℝ) : ℂ) + (if k = k' then ((p / d : ℝ) : ℂ) else 0) := by
    intro k k'; split_ifs <;> ring
  simp only [hite, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at t3
  have t4 := congrArg Complex.re t3
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero] at t4
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
    Complex.normSq_nonneg (∑ k, E j k k))
  have hp : 0 ≤ p := by
    have := mul_nonneg hdpos.le hp0
    rwa [mul_div_cancel₀ _ hdpos.ne'] at this
  refine ⟨hp, ?_⟩
  rw [le_div_iff₀ hD]
  have h5 : (d : ℝ) * (p / d) = p := mul_div_cancel₀ _ hdpos.ne'
  nlinarith

theorem x8_main (d : ℕ) (hd : 2 ≤ d) (p : ℝ) :
    (IsChannel (QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p) ↔
      0 ≤ p ∧ p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) ∧
    (0 ≤ p → p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1) →
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        IsKrausFamily (weylDepolarizingKraus d (by omega) p U) ∧
        QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p =
          krausApply (weylDepolarizingKraus d (by omega) p U)) := by
  have hd0 : 0 < d := by omega
  refine ⟨⟨x8_necessary hd0 hd p, fun ⟨hp, hp1⟩ => ?_⟩, fun hp hp1 U =>
    ⟨x8_family hd0 p hp hp1 hd U, x8_apply hd0 p hp hp1 hd U⟩⟩
  -- reindex the Weyl Kraus family by `Fin (d * d)`
  let e : Fin (d * d) ≃ Fin d × Fin d := finProdFinEquiv.symm
  let K := weylDepolarizingKraus d hd0 p 1
  refine ⟨d * d, fun i => K (e i), ?_, fun ρ => ?_⟩
  · have h := x8_family hd0 p hp hp1 hd 1
    unfold IsKrausFamily at h ⊢
    rw [← h]
    exact e.sum_comp (fun x => (K x)ᴴ * K x)
  · rw [x8_apply hd0 p hp hp1 hd 1, krausApply, krausApply]
    exact (e.sum_comp (fun x => K x * ρ * (K x)ᴴ)).symm

end x8kraus

end QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Claimed50.P43 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (p : ℝ) :
    (QAlgorithms.IsChannel (QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p) ↔
      0 ≤ p ∧ p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) ∧
    (0 ≤ p → p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1) →
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        QAlgorithms.IsKrausFamily (weylDepolarizingKraus d (by omega) p U) ∧
        QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p =
          QAlgorithms.krausApply (weylDepolarizingKraus d (by omega) p U)) :=
  x8_main d hd p
