-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P43.denseCodingIdentities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:35:11.80451+00:00
-- url     : https://prove2.me/submissions/57cd8914-fdb9-4d40-9e89-8052069893c7

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

section x8main
variable {A : Type} [Fintype A] [DecidableEq A] {m : ℕ} [NeZero m]

lemma x8_fw_mul (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) (a b : ZMod m) :
    frameWeyl J a b * J = J * weyl a b := by
  simp only [frameWeyl, extendEncodedUnitary, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc,
    hJ, Matrix.mul_one, Matrix.one_mul]
  abel

lemma x8_act_kron (F : Matrix A A ℂ) (v : EuclideanSpace ℂ (A × A)) (y : A × A) :
    act (Matrix.kronecker (1 : Matrix A A ℂ) F) v y = ∑ z, F y.2 z * v (y.1, z) := by
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single y.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma x8_fb_apply (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) (x : ZMod m × ZMod m)
    (y : A × A) :
    frameBell J x y = ((Real.sqrt m)⁻¹ : ℂ) *
      ∑ k, J y.1 k * (J * weyl x.1 x.2) y.2 k := by
  rw [← x8_fw_mul J hJ, frameBell, x8_act_kron]
  simp only [frameResource, PiLp.toLp_apply, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun z _ => by ring

lemma x8_fb_apply2 (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) (x : ZMod m × ZMod m)
    (y : A × A) :
    frameBell J x y = ((Real.sqrt m)⁻¹ : ℂ) *
      ∑ p : ZMod m × ZMod m, (J y.1 p.1 * J y.2 p.2) * weyl x.1 x.2 p.2 p.1 := by
  rw [x8_fb_apply J hJ, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma x8_JJ (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) (k k' : ZMod m) :
    ∑ a, conj (J a k) * J a k' = if k = k' then 1 else 0 := by
  have := congrFun (congrFun hJ k) k'
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [Matrix.conjTranspose_apply] using this

lemma x8_ff (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) (p q : ZMod m × ZMod m) :
    ∑ y : A × A, conj (J y.1 p.1 * J y.2 p.2) * (J y.1 q.1 * J y.2 q.2) =
      if p = q then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  have : ∀ a b : A, conj (J a p.1 * J b p.2) * (J a q.1 * J b q.2) =
      (conj (J a p.1) * J a q.1) * (conj (J b p.2) * J b q.2) := by
    intro a b; rw [map_mul]; ring
  simp only [this, ← Finset.mul_sum, ← Finset.sum_mul, x8_JJ J hJ]
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp [h1, h2]

lemma x8_c2 : conj ((Real.sqrt m)⁻¹ : ℂ) * ((Real.sqrt m)⁻¹ : ℂ) * (m : ℂ) = 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul]
  rw [← mul_inv, hs, inv_mul_cancel₀ hm, Complex.ofReal_one]

omit [Fintype A] [DecidableEq A] [NeZero m] in
lemma x8_gen {Y P : Type} [Fintype Y] [Fintype P] [DecidableEq P] (c : ℂ) (f : Y → P → ℂ)
    (u v : P → ℂ) (hf : ∀ p q, ∑ y, conj (f y p) * f y q = if p = q then 1 else 0) :
    ∑ y, (c * ∑ q, f y q * v q) * conj (c * ∑ p, f y p * u p) =
      conj c * c * ∑ p, conj (u p) * v p := by
  have e1 : ∀ y, (c * ∑ q, f y q * v q) * conj (c * ∑ p, f y p * u p) =
      conj c * c * ∑ p, ∑ q, (conj (u p) * v q) * (conj (f y p) * f y q) := by
    intro y
    rw [map_mul, map_sum]
    rw [show ∀ a b C D : ℂ, (a * C) * (b * D) = b * a * (D * C) from fun _ _ _ _ => by ring]
    rw [Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [map_mul]; ring
  simp only [e1, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

lemma x8_inner (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) (x x' : ZMod m × ZMod m) :
    inner ℂ (frameBell J x) (frameBell J x') = if x = x' then 1 else 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, x8_fb_apply2 J hJ]
  have h := x8_gen (Y := A × A) (P := ZMod m × ZMod m) ((Real.sqrt m)⁻¹ : ℂ)
    (fun (y : A × A) (p : ZMod m × ZMod m) => J y.1 p.1 * J y.2 p.2)
    (fun p : ZMod m × ZMod m => weyl x.1 x.2 p.2 p.1)
    (fun p : ZMod m × ZMod m => weyl x'.1 x'.2 p.2 p.1) (x8_ff J hJ)
  rw [h, Fintype.sum_prod_type, Finset.sum_comm, x8_weyl_orth]
  simp only [Prod.mk.eta]
  split_ifs
  · rw [x8_c2]
  · simp

omit [Fintype A] [DecidableEq A] [NeZero m] in
lemma x8_gen2 {X P : Type} [Fintype X] [Fintype P] [DecidableEq P] (c K : ℂ) (f g : P → ℂ)
    (w : X → P → ℂ) (hw : ∀ p q, ∑ x, w x p * conj (w x q) = if p = q then K else 0) :
    ∑ x, (c * ∑ p, f p * w x p) * conj (c * ∑ q, g q * w x q) =
      c * conj c * K * ∑ p, f p * conj (g p) := by
  have e1 : ∀ x, (c * ∑ p, f p * w x p) * conj (c * ∑ q, g q * w x q) =
      c * conj c * ∑ p, ∑ q, (f p * conj (g q)) * (w x p * conj (w x q)) := by
    intro x
    rw [map_mul, map_sum]
    rw [show ∀ a b C D : ℂ, (a * C) * (b * D) = a * b * (C * D) from fun _ _ _ _ => by ring]
    rw [Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [map_mul]; ring
  simp only [e1, ← Finset.mul_sum]
  rw [mul_assoc (c * conj c) K]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hw, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma x8_proj (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) :
    ∑ x : ZMod m × ZMod m, pureDensity (frameBell J x) =
      Matrix.kronecker (frameProjector J) (frameProjector J) := by
  ext y y'
  simp only [Matrix.sum_apply, pureDensity, Matrix.of_apply, x8_fb_apply2 J hJ]
  have h := x8_gen2 (X := ZMod m × ZMod m) (P := ZMod m × ZMod m) ((Real.sqrt m)⁻¹ : ℂ) (m : ℂ)
    (fun p : ZMod m × ZMod m => J y.1 p.1 * J y.2 p.2)
    (fun p : ZMod m × ZMod m => J y'.1 p.1 * J y'.2 p.2)
    (fun (x : ZMod m × ZMod m) (p : ZMod m × ZMod m) => weyl x.1 x.2 p.2 p.1)
    (fun p q => by rw [x8_weyl_compl]; congr 1; apply propext; constructor
                   · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
                   · rintro rfl; exact ⟨rfl, rfl⟩)
  rw [h, mul_comm ((Real.sqrt m)⁻¹ : ℂ), x8_c2, one_mul]
  obtain ⟨y1, y2⟩ := y
  obtain ⟨y1', y2'⟩ := y'
  rw [show Matrix.kronecker (frameProjector J) (frameProjector J) (y1, y2) (y1', y2') =
    frameProjector J y1 y1' * frameProjector J y2 y2' from rfl]
  simp only [frameProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    simp only [RCLike.star_def, map_mul]; ring

theorem x8_main {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    {m : ℕ} [NeZero m] (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) :
    Orthonormal ℂ (frameBell J) ∧
    (m = Fintype.card A → Submodule.span ℂ (Set.range (frameBell J)) = ⊤) ∧
    ∑ x : ZMod m × ZMod m, pureDensity (frameBell J x) =
      Matrix.kronecker (frameProjector J) (frameProjector J) := by
  have hon : Orthonormal ℂ (frameBell J) := orthonormal_iff_ite.mpr (x8_inner J hJ)
  refine ⟨hon, fun hm => ?_, x8_proj J hJ⟩
  apply hon.linearIndependent.span_eq_top_of_card_eq_finrank
  simp [Fintype.card_prod, ZMod.card, hm]

end x8main

end QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Claimed50.P43 in
theorem solution {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    {m : ℕ} [NeZero m] (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) :
    Orthonormal ℂ (frameBell J) ∧
    (m = Fintype.card A → Submodule.span ℂ (Set.range (frameBell J)) = ⊤) ∧
    ∑ x : ZMod m × ZMod m, QAlgorithms.pureDensity (frameBell J x) =
      Matrix.kronecker (frameProjector J) (frameProjector J) :=
  x8_main J hJ
