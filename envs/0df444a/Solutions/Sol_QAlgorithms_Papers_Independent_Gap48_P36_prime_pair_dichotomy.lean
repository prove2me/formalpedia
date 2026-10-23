-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.prime_pair_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:51:14.586727+00:00
-- url     : https://prove2.me/submissions/4cdf6aaa-9ef9-4b2e-a75d-2d9fb6c3529c

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

open scoped Matrix ComplexConjugate Kronecker ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P36


open QAlgorithms.Papers.Independent.Information100.P34 (weyl cyclicPhase)

section x8weyl
variable {d : ℕ} [NeZero d]

local notation "eZ" => (ZMod.finEquiv d)

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


lemma x8_fwe (k : WeylLabel d) (i j : Fin d) :
    finWeyl d k i j = weyl k.1 k.2 (eZ i) (eZ j) := rfl

lemma x8_fw_compl (l k l' k' : Fin d) :
    ∑ x : WeylLabel d, finWeyl d x l k * conj (finWeyl d x l' k') =
      if k = k' ∧ l = l' then (d : ℂ) else 0 := by
  simp only [x8_fwe]
  rw [x8_weyl_compl]
  simp only [EmbeddingLike.apply_eq_iff_eq]

lemma x8_fw_unit (k : WeylLabel d) :
    (finWeyl d k)ᴴ * finWeyl d k = 1 := by
  ext a a'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, x8_fwe]
  refine (Fintype.sum_equiv (eZ).toEquiv _
    (fun z : ZMod d => conj (weyl k.1 k.2 z (eZ a)) * weyl k.1 k.2 z (eZ a'))
    (fun x => rfl)).trans ?_
  rw [x8_weyl_col]
  simp only [EmbeddingLike.apply_eq_iff_eq]

lemma x8_fw_zero : finWeyl d 0 = 1 := by
  ext i j
  rw [x8_fwe, x8_weyl, Matrix.one_apply]
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero, mul_zero, AddChar.map_zero_eq_one,
    EmbeddingLike.apply_eq_iff_eq]

lemma x8_weyl_mul (n m n' m' : ZMod d) :
    weyl n m * weyl n' m' = (ZMod.stdAddChar (n' * m) : ℂ) • weyl (n + n') (m + m') := by
  ext a c
  rw [Matrix.mul_apply, Matrix.smul_apply, x8_weyl]
  simp only [x8_weyl]
  rw [Finset.sum_eq_single (c + n')]
  · by_cases h : a = c + (n + n')
    · rw [if_pos (by rw [h]; ring), if_pos rfl, if_pos h, smul_eq_mul, ← AddChar.map_add_eq_mul,
        ← AddChar.map_add_eq_mul]
      congr 1; ring
    · rw [if_neg (by intro h'; apply h; rw [h']; ring), if_neg h]; simp
  · intro b _ hb; rw [if_neg (fun h => hb h) ]; simp
  · simp

lemma x8_fw_mul (a b : WeylLabel d) :
    ∃ φ : ℂ, finWeyl d a * finWeyl d b = φ • finWeyl d (a + b) := by
  refine ⟨ZMod.stdAddChar (b.1 * a.2), ?_⟩
  unfold finWeyl
  rw [← Matrix.submatrix_mul _ _ _ _ _ (ZMod.finEquiv d).bijective, x8_weyl_mul, Matrix.submatrix_smul]
  rfl

lemma x8_fw_trace (k : WeylLabel d) :
    (finWeyl d k).trace = if k = 0 then (d : ℂ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, x8_fwe]
  refine (Fintype.sum_equiv (eZ).toEquiv _ (fun z : ZMod d => weyl k.1 k.2 z z)
    (fun x => rfl)).trans ?_
  simp only [x8_weyl]
  by_cases h1 : k.1 = 0
  · simp only [h1, add_zero, if_true]
    rw [x8_esum]
    by_cases h2 : k.2 = 0
    · rw [if_pos h2, if_pos (Prod.ext h1 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (by rw [h]; rfl))]
  · rw [if_neg (fun h => h1 (by rw [h]; rfl))]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    rw [if_neg]; intro h; apply h1
    have := congrArg (fun t => t - z) h; simpa using this.symm

end x8weyl


section x8gen

lemma x8_pars_gen {K P : Type*} [Fintype K] [Fintype P] [DecidableEq P] (D : ℂ)
    (f : K → P → ℂ) (X : P → ℂ)
    (h : ∀ p q, ∑ k, conj (f k p) * f k q = if p = q then D else 0) :
    ∑ k, (∑ p, conj (f k p) * X p) * conj (∑ q, conj (f k q) * X q) =
      D * ∑ p, X p * conj (X p) := by
  simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]
  have : ∀ q, ∑ k, conj (f k p) * X p * (f k q * conj (X q)) =
      (∑ k, conj (f k p) * f k q) * (X p * conj (X q)) := by
    intro q; rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => by ring)
  simp only [this, h, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma x8_tr_form {I : Type*} [Fintype I] (A X : Matrix I I ℂ) :
    (Aᴴ * X).trace = ∑ p : I × I, conj (A p.1 p.2) * X p.1 p.2 := by
  rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [Matrix.mul_apply]

variable {d : ℕ} [NeZero d]

lemma x8_hh (p q : Fin d × Fin d) : ∑ k : WeylLabel d, conj (finWeyl d k p.1 p.2) * finWeyl d k q.1 q.2 =
      if p = q then (d : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun k _ => mul_comm _ _), x8_fw_compl q.1 q.2 p.1 p.2]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [if_neg hpq, if_neg]
    intro h; exact hpq (Prod.ext h.2.symm h.1.symm)

lemma x8_fw_pars (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k : WeylLabel d, ((finWeyl d k)ᴴ * X).trace * conj (((finWeyl d k)ᴴ * X).trace) =
      (d : ℂ) * ∑ p : Fin d × Fin d, X p.1 p.2 * conj (X p.1 p.2) := by
  simp only [x8_tr_form]
  have hh : ∀ p q : Fin d × Fin d, ∑ k : WeylLabel d, conj (finWeyl d k p.1 p.2) * finWeyl d k q.1 q.2 =
      if p = q then (d : ℂ) else 0 := by
    intro p q
    exact x8_hh p q
  have key := x8_pars_gen (K := WeylLabel d) (P := Fin d × Fin d) (d : ℂ) (fun k p => finWeyl d k p.1 p.2) (fun p => X p.1 p.2) hh
  exact key

/-- eigenvector from saturated Cauchy–Schwarz -/
lemma x8_eig {X : Type*} [Fintype X] [DecidableEq X] (U : Matrix X X ℂ) (hU : Uᴴ * U = 1)
    (v : X → ℂ) (hv : star v ⬝ᵥ v = 1)
    (hl : (star v ⬝ᵥ (U *ᵥ v)) * conj (star v ⬝ᵥ (U *ᵥ v)) = 1) :
    U *ᵥ v = (star v ⬝ᵥ (U *ᵥ v)) • v := by
  set l := star v ⬝ᵥ (U *ᵥ v) with hl_def
  have hUU : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = 1 := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one, hv]
  have hc : star (U *ᵥ v) ⬝ᵥ v = conj l := by
    rw [hl_def, Matrix.star_dotProduct]; rfl
  have h0 : star (U *ᵥ v - l • v) ⬝ᵥ (U *ᵥ v - l • v) = 0 := by
    rw [star_sub, star_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
      hUU, hc, ← hl_def, hv]
    simp only [smul_eq_mul, RCLike.star_def]
    linear_combination -hl
  exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp h0)

end x8gen


section x8gen2
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma x8_trR (A : Matrix I I ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    ((A ⊗ₖ (1 : Matrix J J ℂ))ᴴ * X).trace = (Aᴴ * traceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, traceRight,
    Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [mul_ite, mul_one, mul_zero, apply_ite (starRingEnd ℂ), map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, RCLike.star_def]

lemma x8_trL (A : Matrix J J ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    (((1 : Matrix I I ℂ) ⊗ₖ A)ᴴ * X).trace = (Aᴴ * traceLeft X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, traceLeft,
    Matrix.of_apply, Finset.mul_sum]
  have key : ∀ (x : I) (x1 x3 : J), ∑ x2 : I, star ((if x2 = x then (1 : ℂ) else 0) * A x3 x1) *
      X (x2, x3) (x, x1) = star (A x3 x1) * X (x, x3) (x, x1) := by
    intro x x1 x3
    simp only [ite_mul, one_mul, zero_mul, apply_ite star, star_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  conv_lhs => arg 2; ext x; arg 2; ext x1; rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [Finset.sum_comm]

lemma x8_sum4 (f : I → J → ℂ) (g : I → J → ℂ) :
    ∑ i, ∑ j, ∑ h, ∑ h', f i h * g j h' = (∑ i, ∑ h, f i h) * (∑ j, ∑ h', g j h') := by
  rw [Finset.sum_mul_sum]; simp_rw [Finset.sum_mul_sum]

lemma x8_reorder (F : I → I → J → J → ℂ) :
    ∑ i, ∑ j, ∑ h, ∑ h', F i j h h' = ∑ h, ∑ h', ∑ i, ∑ j, F i j h h' := by
  calc _ = ∑ i, ∑ h, ∑ j, ∑ h', F i j h h' := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ h, ∑ h', ∑ j, F i j h h' :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun h _ => Finset.sum_comm))
    _ = ∑ h, ∑ i, ∑ h', ∑ j, F i j h h' := Finset.sum_comm
    _ = ∑ h, ∑ h', ∑ i, ∑ j, F i j h h' := Finset.sum_congr rfl (fun h _ => Finset.sum_comm)

/-- Lagrange identity for the 2x2 minors of a coefficient matrix. -/
lemma x8_lag (M : I → J → ℂ) :
    ∑ i, ∑ j, ∑ h, ∑ h', (M i h * M j h' - M i h' * M j h) * conj (M i h * M j h' - M i h' * M j h) =
      2 * ((∑ i, ∑ h, M i h * conj (M i h)) ^ 2 -
        ∑ i, ∑ j, (∑ h, M i h * conj (M j h)) * conj (∑ h, M i h * conj (M j h))) := by
  have e1 : ∀ i j h h', (M i h * M j h' - M i h' * M j h) * conj (M i h * M j h' - M i h' * M j h) =
      (M i h * conj (M i h)) * (M j h' * conj (M j h')) - (M i h * conj (M j h)) * (M j h' * conj (M i h'))
      - (M i h' * conj (M j h')) * (M j h * conj (M i h)) + (M i h' * conj (M i h')) * (M j h * conj (M j h)) := by
    intro i j h h'; simp only [map_sub, map_mul]; ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s4 : ∑ i, ∑ j, ∑ h, ∑ h', (M i h' * conj (M i h')) * (M j h * conj (M j h)) =
      ∑ i, ∑ j, ∑ h, ∑ h', (M i h * conj (M i h)) * (M j h' * conj (M j h')) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact Finset.sum_comm
  have s3 : ∑ i, ∑ j, ∑ h, ∑ h', (M i h' * conj (M j h')) * (M j h * conj (M i h)) =
      ∑ i, ∑ j, ∑ h, ∑ h', (M i h * conj (M j h)) * (M j h' * conj (M i h')) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact Finset.sum_comm
  have s2 : ∑ i, ∑ j, ∑ h, ∑ h', (M i h * conj (M j h)) * (M j h' * conj (M i h')) =
      ∑ i, ∑ j, (∑ h, M i h * conj (M j h)) * conj (∑ h, M i h * conj (M j h)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
    simp only [map_mul, Complex.conj_conj]; ring
  rw [s4, s3, s2, x8_sum4 (fun i h => M i h * conj (M i h)) (fun i h => M i h * conj (M i h))]
  ring

lemma x8_P12 (M : I → J → ℂ) :
    ∑ i, ∑ j, (∑ h, M i h * conj (M j h)) * conj (∑ h, M i h * conj (M j h)) =
      ∑ h, ∑ h', (∑ i, M i h * conj (M i h')) * conj (∑ i, M i h * conj (M i h')) := by
  simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
  rw [x8_reorder]
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ =>
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))))

end x8gen2


section x8prod
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma x8_state_iff {X : Type*} [Fintype X] (x : EuclideanSpace ℂ X) :
    IsState x ↔ ∑ i, ‖x.ofLp i‖ ^ 2 = 1 := by
  unfold IsState
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]

lemma x8_prod (ψ : EuclideanSpace ℂ (I × J)) (hψ : IsState ψ)
    (hmin : ∀ i j h h', ψ.ofLp (i, h) * ψ.ofLp (j, h') = ψ.ofLp (i, h') * ψ.ofLp (j, h)) :
    ∃ u : EuclideanSpace ℂ I, ∃ w : EuclideanSpace ℂ J, IsState u ∧ IsState w ∧
      pureDensity ψ = pureDensity u ⊗ₖ pureDensity w := by
  set v := ψ.ofLp with hv
  rw [x8_state_iff] at hψ
  obtain ⟨⟨i0, h0⟩, hx0⟩ : ∃ x, v x ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [← hv, hc] at hψ
  set a := v (i0, h0)
  set S := ∑ i, ‖v (i, h0)‖ ^ 2 with hS
  have hSpos : 0 < S := by
    rw [hS]
    exact lt_of_lt_of_le (by positivity : 0 < ‖v (i0, h0)‖ ^ 2)
      (Finset.single_le_sum (f := fun i => ‖v (i, h0)‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ i0))
  set Nu := Real.sqrt S with hNu
  have hNu0 : 0 < Nu := Real.sqrt_pos.2 hSpos
  have hNu2 : Nu ^ 2 = S := Real.sq_sqrt hSpos.le
  have hNuC : (Nu : ℂ) ≠ 0 := by exact_mod_cast hNu0.ne'
  have hfac : ∀ i h, v (i, h) = v (i, h0) * v (i0, h) / a := by
    intro i h
    rw [eq_div_iff hx0, hmin i i0 h0 h]
  refine ⟨WithLp.toLp 2 (fun i => v (i, h0) / (Nu : ℂ)),
    WithLp.toLp 2 (fun h => (Nu : ℂ) * v (i0, h) / a), ?_, ?_, ?_⟩
  · rw [x8_state_iff]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNu0, div_pow]
    rw [← Finset.sum_div, ← hS, hNu2, div_self hSpos.ne']
  · rw [x8_state_iff]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNu0, div_pow,
      mul_pow]
    have h1 : ∑ i, ∑ h, ‖v (i, h)‖ ^ 2 = 1 := by rw [← hψ, Fintype.sum_prod_type]
    have h2 : ∑ i, ∑ h, ‖v (i, h)‖ ^ 2 = S * ∑ h, ‖v (i0, h)‖ ^ 2 / ‖a‖ ^ 2 := by
      rw [hS, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hfac i h, norm_div, norm_mul, div_pow, mul_pow]; ring
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum, hNu2, ← h2, h1]
  · ext ⟨i, h⟩ ⟨j, h'⟩
    simp only [pureDensity, Matrix.kroneckerMap_apply, Matrix.of_apply]
    rw [← hv, hfac i h, hfac j h']
    simp only [map_div₀, map_mul, Complex.conj_ofReal]
    field_simp

end x8prod


section x8main
variable {d : ℕ} [NeZero d]

def x8T (d : ℕ) [NeZero d] (k : WeylLabel d × WeylLabel d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  finWeyl d k.1 ⊗ₖ finWeyl d k.2

lemma x8T_unit (k : WeylLabel d × WeylLabel d) : (x8T d k)ᴴ * x8T d k = 1 := by
  rw [x8T, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, x8_fw_unit, x8_fw_unit,
    Matrix.one_kronecker_one]

lemma x8T_zero : x8T d 0 = 1 := by
  rw [x8T, Prod.fst_zero, Prod.snd_zero, x8_fw_zero, Matrix.one_kronecker_one]

lemma x8T_mul (a b : WeylLabel d × WeylLabel d) :
    ∃ φ : ℂ, x8T d a * x8T d b = φ • x8T d (a + b) := by
  obtain ⟨φ1, h1⟩ := x8_fw_mul a.1 b.1
  obtain ⟨φ2, h2⟩ := x8_fw_mul a.2 b.2
  refine ⟨φ1 * φ2, ?_⟩
  rw [x8T, x8T, x8T, ← Matrix.mul_kronecker_mul, h1, h2, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, Prod.fst_add, Prod.snd_add]

lemma x8T_left (m : WeylLabel d) : x8T d (m, 0) = finWeyl d m ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [x8T, x8_fw_zero]

lemma x8T_right (m : WeylLabel d) : x8T d (0, m) = (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ finWeyl d m := by
  rw [x8T, x8_fw_zero]

omit [NeZero d] in
lemma x8_coef_pd {X : Type*} [Fintype X] (A : Matrix X X ℂ) (ψ : EuclideanSpace ℂ X) :
    (Aᴴ * pureDensity ψ).trace = conj (star ψ.ofLp ⬝ᵥ (A *ᵥ ψ.ofLp)) := by
  rw [x8_tr_form, Fintype.sum_prod_type]
  simp only [pureDensity, Matrix.of_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => by ring))

omit [NeZero d] in
lemma x8_hv1 {X : Type*} [Fintype X] (ψ : EuclideanSpace ℂ X) (h : IsState ψ) :
    star ψ.ofLp ⬝ᵥ ψ.ofLp = 1 := by
  rw [x8_state_iff] at h
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  exact_mod_cast h

lemma x8_neg (x : WeylLabel d) : -x = (d - 1) • x := by
  have hd : (d • x) = 0 := by
    ext <;> simp [nsmul_eq_mul]
  have h1 : (d - 1) • x + x = 0 := by
    rw [← succ_nsmul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)), hd]
  exact (eq_neg_of_add_eq_zero_left h1).symm

lemma x8_card_sub (hd : d.Prime) (P : WeylLabel d → Prop) [DecidablePred P] (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) :
    ∃ i ≤ 2, (Finset.univ.filter P).card = d ^ i := by
  have hns : ∀ (n : ℕ) x, P x → P (n • x) := by
    intro n x hx
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul]; exact hadd _ _ ih hx
  let H : AddSubgroup (WeylLabel d) :=
    { carrier := {x | P x}
      zero_mem' := h0
      add_mem' := fun ha hb => hadd _ _ ha hb
      neg_mem' := fun {x} hx => by
        show P (-x)
        rw [x8_neg]; exact hns _ _ hx }
  have hdvd := AddSubgroup.card_addSubgroup_dvd_card H
  have hG : Nat.card (WeylLabel d) = d ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod, sq]
  have hH : Nat.card H = (Finset.univ.filter P).card := by
    have : Nat.card H = Nat.card {x // P x} := rfl
    rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hG, hH] at hdvd
  exact (Nat.dvd_prime_pow hd).1 hdvd

lemma x8_zero_of_coef (X : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ k, ((finWeyl d k)ᴴ * X).trace = 0) : X = 0 := by
  have hp := x8_fw_pars X
  simp only [h, zero_mul, Finset.sum_const_zero] at hp
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hs : ∑ p : Fin d × Fin d, ((Complex.normSq (X p.1 p.2) : ℝ) : ℂ) = 0 := by
    simp only [← Complex.mul_conj]
    exact (mul_eq_zero.1 hp.symm).resolve_left hdC
  have hs' : ∑ p : Fin d × Fin d, Complex.normSq (X p.1 p.2) = 0 := by exact_mod_cast hs
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Complex.normSq_nonneg _)).1 hs'
  ext i j
  exact Complex.normSq_eq_zero.1 (this (i, j) (Finset.mem_univ _))

end x8main


section x8main2

lemma x8_rho1 {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∑ p : Fin d × Fin d, traceRight (pureDensity ψ) p.1 p.2 * conj (traceRight (pureDensity ψ) p.1 p.2) =
      ∑ i, ∑ j, (∑ h, ψ.ofLp (i, h) * conj (ψ.ofLp (j, h))) *
        conj (∑ h, ψ.ofLp (i, h) * conj (ψ.ofLp (j, h))) := by
  rw [Fintype.sum_prod_type]; simp [traceRight, pureDensity]

lemma x8_rho2 {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∑ p : Fin d × Fin d, traceLeft (pureDensity ψ) p.1 p.2 * conj (traceLeft (pureDensity ψ) p.1 p.2) =
      ∑ h, ∑ h', (∑ i, ψ.ofLp (i, h) * conj (ψ.ofLp (i, h'))) *
        conj (∑ i, ψ.ofLp (i, h) * conj (ψ.ofLp (i, h'))) := by
  rw [Fintype.sum_prod_type]; simp [traceLeft, pureDensity]

lemma x8_sum4_zero {I J : Type*} [Fintype I] [Fintype J] (f : I → I → J → J → ℝ)
    (hf : ∀ i j h h', 0 ≤ f i j h h') (hs : ∑ i, ∑ j, ∑ h, ∑ h', f i j h h' = 0) :
    ∀ i j h h', f i j h h' = 0 := by
  intro i j h h'
  have n3 : ∀ i j h, 0 ≤ ∑ h', f i j h h' := fun i j h => Finset.sum_nonneg fun h' _ => hf i j h h'
  have n2 : ∀ i j, 0 ≤ ∑ h, ∑ h', f i j h h' := fun i j => Finset.sum_nonneg fun h _ => n3 i j h
  have n1 : ∀ i, 0 ≤ ∑ j, ∑ h, ∑ h', f i j h h' := fun i => Finset.sum_nonneg fun j _ => n2 i j
  have z1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => n1 i)).1 hs i (Finset.mem_univ _)
  have z2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => n2 i j)).1 z1 j (Finset.mem_univ _)
  have z3 := (Finset.sum_eq_zero_iff_of_nonneg (fun h _ => n3 i j h)).1 z2 h (Finset.mem_univ _)
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun h' _ => hf i j h h')).1 z3 h' (Finset.mem_univ _)

theorem x8_main (d : ℕ) [NeZero d] (hd : Nat.Prime d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) (hpsi : IsState psi)
    (hflat : FlatSupport (fun k : WeylLabel d × WeylLabel d => finWeyl d k.1 ⊗ₖ finWeyl d k.2)
      (pureDensity psi) (d^2)) :
    (∃ u v : EuclideanSpace ℂ (Fin d), IsState u ∧ IsState v ∧
      pureDensity psi = pureDensity u ⊗ₖ pureDensity v) ∨
    (traceRight (pureDensity psi) = (d : ℂ)⁻¹ • 1 ∧
      traceLeft (pureDensity psi) = (d : ℂ)⁻¹ • 1) := by
  classical
  set v := psi.ofLp with hv
  have hv1 : star v ⬝ᵥ v = 1 := x8_hv1 psi hpsi
  set e : WeylLabel d × WeylLabel d → ℂ := fun k => star v ⬝ᵥ (x8T d k *ᵥ v) with he
  have hc : ∀ k, basisCoefficient (fun k : WeylLabel d × WeylLabel d => finWeyl d k.1 ⊗ₖ finWeyl d k.2)
      (pureDensity psi) k = conj (e k) := fun k => x8_coef_pd (x8T d k) psi
  have hfl : ∀ k, e k = 0 ∨ e k * conj (e k) = 1 := by
    intro k
    rcases hflat.2 k with h | h
    · left; rw [hc] at h; simpa using h
    · right; rw [hc, Complex.norm_conj] at h
      rw [Complex.mul_conj', h]; simp
  have he0 : e 0 = 1 := by simp only [he, x8T_zero, Matrix.one_mulVec, hv1]
  have heig : ∀ k, e k ≠ 0 → x8T d k *ᵥ v = e k • v := fun k hk =>
    x8_eig _ (x8T_unit k) v hv1 ((hfl k).resolve_left hk)
  have hadd : ∀ a b, e a ≠ 0 → e b ≠ 0 → e (a + b) ≠ 0 := by
    intro a b ha hb hab
    obtain ⟨φ, hφ⟩ := x8T_mul a b
    have h1 : (x8T d a * x8T d b) *ᵥ v = (e a * e b) • v := by
      rw [← Matrix.mulVec_mulVec, heig b hb, Matrix.mulVec_smul, heig a ha, smul_smul, mul_comm]
    rw [hφ, Matrix.smul_mulVec] at h1
    have h2 := congrArg (fun w => star v ⬝ᵥ w) h1
    simp only [dotProduct_smul, smul_eq_mul, hv1, mul_one] at h2
    have : e (a + b) = star v ⬝ᵥ (x8T d (a + b) *ᵥ v) := rfl
    rw [← this, hab, mul_zero] at h2
    exact mul_ne_zero ha hb h2.symm
  -- Lagrange data
  set M : Fin d → Fin d → ℂ := fun i h => v (i, h) with hM
  have hN : ∑ i, ∑ h, M i h * conj (M i h) = 1 := by
    rw [← hv1]; simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, RCLike.star_def, hM]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun h _ => mul_comm _ _))
  set P1 := ∑ i, ∑ j, (∑ h, M i h * conj (M j h)) * conj (∑ h, M i h * conj (M j h)) with hP1
  set L : ℝ := ∑ i, ∑ j, ∑ h, ∑ h', Complex.normSq (M i h * M j h' - M i h' * M j h) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun h _ =>
      Finset.sum_nonneg fun h' _ => Complex.normSq_nonneg _
  have hLag : (L : ℂ) = 2 * (1 - P1) := by
    have hl := x8_lag M
    rw [hN, one_pow] at hl
    rw [hP1, ← hl, hL]; push_cast; simp only [Complex.mul_conj]
  -- counts
  have hcnt1 : (((Finset.univ.filter fun m : WeylLabel d => e (m, 0) ≠ 0).card : ℕ) : ℂ) = d * P1 := by
    have hp := x8_fw_pars (traceRight (pureDensity psi))
    rw [x8_rho1] at hp
    rw [hP1, ← hp, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← x8_trR, ← x8T_left, x8_coef_pd, ← hv,
      show star v ⬝ᵥ (x8T d (m, 0) *ᵥ v) = e (m, 0) from rfl]
    rcases hfl (m, 0) with h | h
    · rw [if_neg (not_not.2 h), h]; simp
    · rw [if_pos (fun h' => by rw [h'] at h; simp at h), Complex.conj_conj, mul_comm, h]
  have hcnt2 : (((Finset.univ.filter fun m : WeylLabel d => e (0, m) ≠ 0).card : ℕ) : ℂ) = d * P1 := by
    have hp := x8_fw_pars (traceLeft (pureDensity psi))
    rw [x8_rho2, ← x8_P12] at hp
    rw [hP1, ← hp, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← x8_trL, ← x8T_right, x8_coef_pd, ← hv,
      show star v ⬝ᵥ (x8T d (0, m) *ᵥ v) = e (0, m) from rfl]
    rcases hfl (0, m) with h | h
    · rw [if_neg (not_not.2 h), h]; simp
    · rw [if_pos (fun h' => by rw [h'] at h; simp at h), Complex.conj_conj, mul_comm, h]
  have hP1L : P1 = ((1 - L / 2 : ℝ) : ℂ) := by
    push_cast; linear_combination (1 / 2 : ℂ) * hLag
  set N1 := (Finset.univ.filter fun m : WeylLabel d => e (m, 0) ≠ 0).card with hN1
  set N2 := (Finset.univ.filter fun m : WeylLabel d => e (0, m) ≠ 0).card with hN2
  have hr1 : (N1 : ℝ) = d * (1 - L / 2) := by
    have := hcnt1; rw [hP1L] at this; exact_mod_cast this
  have hr2 : (N2 : ℝ) = d * (1 - L / 2) := by
    have := hcnt2; rw [hP1L] at this; exact_mod_cast this
  have h12 : N1 = N2 := by exact_mod_cast hr1.trans hr2.symm
  have he00 : e (0, 0) ≠ 0 := by
    rw [show ((0 : WeylLabel d), (0 : WeylLabel d)) = 0 from rfl, he0]; exact one_ne_zero
  obtain ⟨i, hi, hci⟩ := x8_card_sub hd (fun m => e (m, 0) ≠ 0) he00
    (fun a b ha hb => by
      have := hadd (a, 0) (b, 0) ha hb
      rwa [Prod.mk_add_mk, add_zero] at this)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd.two_le
  replace hci : N1 = d ^ i := by rw [hN1]; convert hci
  interval_cases i
  · -- maximally mixed marginals
    right
    have hK : ∀ (f : WeylLabel d → WeylLabel d × WeylLabel d),
        (Finset.univ.filter fun m : WeylLabel d => e (f m) ≠ 0).card = 1 → e (f 0) ≠ 0 →
        ∀ m, e (f m) ≠ 0 → m = 0 := by
      intro f hcard h0 m hm
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
      have h0' : (0 : WeylLabel d) ∈ Finset.univ.filter fun m => e (f m) ≠ 0 := by simp [h0]
      have hm' : m ∈ Finset.univ.filter fun m => e (f m) ≠ 0 := by simp [hm]
      rw [ha, Finset.mem_singleton] at h0' hm'
      rw [hm', h0']
    have hK1 := hK (fun m => (m, 0)) (by rw [← hN1, hci, pow_zero]) he00
    have hK2 := hK (fun m => (0, m)) (by rw [← hN2, ← h12, hci, pow_zero]) he00
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
    have hWtr : ∀ k : WeylLabel d, ((finWeyl d k)ᴴ).trace = if k = 0 then (d : ℂ) else 0 := by
      intro k; rw [Matrix.trace_conjTranspose, x8_fw_trace]; split_ifs <;> simp
    constructor
    · refine sub_eq_zero.1 (x8_zero_of_coef _ (fun k => ?_))
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        smul_eq_mul, hWtr, ← x8_trR, ← x8T_left, x8_coef_pd, ← hv,
        show star v ⬝ᵥ (x8T d (k, 0) *ᵥ v) = e (k, 0) from rfl]
      by_cases hk : k = 0
      · subst hk
        rw [if_pos rfl, show ((0 : WeylLabel d), (0 : WeylLabel d)) = 0 from rfl, he0]
        field_simp; simp
      · rw [if_neg hk, show e (k, 0) = 0 from by_contra fun h => hk (hK1 k h)]; simp
    · refine sub_eq_zero.1 (x8_zero_of_coef _ (fun k => ?_))
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        smul_eq_mul, hWtr, ← x8_trL, ← x8T_right, x8_coef_pd, ← hv,
        show star v ⬝ᵥ (x8T d (0, k) *ᵥ v) = e (0, k) from rfl]
      by_cases hk : k = 0
      · subst hk
        rw [if_pos rfl, show ((0 : WeylLabel d), (0 : WeylLabel d)) = 0 from rfl, he0]
        field_simp; simp
      · rw [if_neg hk, show e (0, k) = 0 from by_contra fun h => hk (hK2 k h)]; simp
  · -- product
    left
    have hL' : L = 0 := by
      have h := hr1
      rw [hci, pow_one] at h
      have : (d : ℝ) * (L / 2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · linarith
    have hz := x8_sum4_zero _ (fun i j h h' => Complex.normSq_nonneg _) (hL ▸ hL')
    exact x8_prod psi hpsi (fun i j h h' => sub_eq_zero.1 (Complex.normSq_eq_zero.1 (hz i j h h')))
  · exfalso
    have h := hr1
    rw [hci] at h
    push_cast at h
    have : (d : ℝ) * d ≤ d * 1 := by nlinarith
    nlinarith

end x8main2

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (d : ℕ) [NeZero d] (hd : Nat.Prime d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) (hpsi : IsState psi)
    (hflat : FlatSupport (fun k : WeylLabel d × WeylLabel d => finWeyl d k.1 ⊗ₖ finWeyl d k.2)
      (pureDensity psi) (d^2)) :
    (∃ u v : EuclideanSpace ℂ (Fin d), IsState u ∧ IsState v ∧
      pureDensity psi = pureDensity u ⊗ₖ pureDensity v) ∨
    (traceRight (pureDensity psi) = (d : ℂ)⁻¹ • 1 ∧
      traceLeft (pureDensity psi) = (d : ℂ)⁻¹ • 1) :=
  x8_main d hd psi hpsi hflat
