-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.fourier_robustness_and_dimension_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:46:49.932621+00:00
-- url     : https://prove2.me/submissions/eedeab48-fec8-49c1-aac8-bcf5de9ee9f5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

section generic

set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma x8_ch_zero {M : Superop A B} (h : IsChannel M) : M 0 = 0 := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply]; simp

lemma x8_ch_trace {M : Superop A B} (h : IsChannel M)
    (X : Matrix A A ℂ) : (M X).trace = X.trace := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X ((E _)ᴴ)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

lemma x8_ch_expand {M : Superop A B} (h : IsChannel M) (X : Matrix A A ℂ) (β γ : B) :
    M X β γ = ∑ i, ∑ j, X i j * choi M (i, β) (j, γ) := by
  obtain ⟨m, E, hK, hM⟩ := h
  simp only [choi, hM, krausApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply]
  simp [ite_and, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma x8_choi_trB {M : Superop A B} (h : IsChannel M) (i j : A) :
    ∑ β, choi M (i, β) (j, β) = if i = j then 1 else 0 := by
  have := x8_ch_trace h (Matrix.single i j 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [choi]
  rw [this]
  by_cases hij : i = j
  · subst hij; simp [Matrix.single_apply]
  · simp [Matrix.single_apply, hij, Ne.symm hij]

lemma x8_deph_single (i j : A) :
    dephasing (Matrix.single i j (1 : ℂ)) = if i = j then Matrix.single i j 1 else 0 := by
  ext k l
  by_cases hij : i = j
  · subst hij; by_cases hkl : k = l
    · subst hkl; simp [dephasing, Matrix.single_apply]
    · simp [dephasing, Matrix.single_apply, hkl]
      intro h1 h2; exact hkl (h1.symm.trans h2)
  · simp only [dephasing, hij, if_false, Matrix.diagonal_apply, Matrix.single_apply]
    by_cases hkl : k = l
    · subst hkl; simp; intro h1 h2; exact hij (h1.trans h2.symm)
    · simp [hkl]

lemma x8_mio_choi {M : Superop A B} (hO : Free .mio M) (i : A) (β γ : B)
    (hβγ : β ≠ γ) : choi M (i, β) (i, γ) = 0 := by
  have := congrFun (congrFun (hO.2 (Matrix.single i i 1)) β) γ
  rw [x8_deph_single, if_pos rfl] at this
  rw [choi, this]
  simp [dephasing, Matrix.diagonal_apply, hβγ]

lemma x8_di_choi {M : Superop A B} (hO : Free .di M) (i j : A) (β : B)
    (hij : i ≠ j) : choi M (i, β) (j, β) = 0 := by
  have := congrFun (congrFun (hO.2 (Matrix.single i j 1)) β) β
  rw [x8_deph_single, if_neg hij, x8_ch_zero hO.1] at this
  simpa [dephasing, choi] using this

lemma x8_dio_choi {M : Superop A B} (hO : Free .dio M) :
    (∀ i β γ, β ≠ γ → choi M (i, β) (i, γ) = 0) ∧
    (∀ i j β, i ≠ j → choi M (i, β) (j, β) = 0) := by
  constructor
  · intro i β γ hβγ
    have := congrFun (congrFun (hO.2 (Matrix.single i i 1)) β) γ
    rw [x8_deph_single, if_pos rfl] at this
    rw [choi, ← this]
    simp [dephasing, Matrix.diagonal_apply, hβγ]
  · intro i j β hij
    have := congrFun (congrFun (hO.2 (Matrix.single i j 1)) β) β
    rw [x8_deph_single, if_neg hij, x8_ch_zero hO.1] at this
    simpa [dephasing, choi] using this

lemma x8_free_of_choi {M : Superop A B} (h : IsChannel M)
    (O : Theory) (hmio : O ≠ .di → ∀ i β γ, β ≠ γ → choi M (i, β) (i, γ) = 0)
    (hdi : O ≠ .mio → ∀ i j β, i ≠ j → choi M (i, β) (j, β) = 0) : Free O M := by
  have hd : ∀ X : Matrix A A ℂ, ∀ β γ, M (Matrix.diagonal fun i => X i i) β γ = ∑ i, X i i * choi M (i, β) (i, γ) := by
    intro X β γ
    rw [x8_ch_expand h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [dephasing, Matrix.diagonal_apply]
  have hM : O ≠ .mio → ∀ X : Matrix A A ℂ, ∀ β, M X β β = ∑ i, X i i * choi M (i, β) (i, β) := by
    intro hO X β
    rw [x8_ch_expand h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · intro j _ hj; rw [hdi hO i j β (Ne.symm hj), mul_zero]
    · simp
  refine ⟨h, ?_⟩
  cases O with
  | mio =>
    intro X; ext β γ
    by_cases hβγ : β = γ
    · subst hβγ; simp [dephasing]
    · simp only [dephasing, Matrix.diagonal_apply, hβγ, if_false]
      rw [hd]; exact Finset.sum_eq_zero fun i _ => by rw [hmio (by decide) i β γ hβγ, mul_zero]
  | di =>
    intro X; ext β γ
    simp only [dephasing, Matrix.diagonal_apply]
    split_ifs with hβγ
    · subst hβγ; rw [hM (by decide), hd]
    · rfl
  | dio =>
    intro X; ext β γ
    simp only [dephasing, Matrix.diagonal_apply]
    split_ifs with hβγ
    · subst hβγ; rw [hM (by decide), hd]
    · rw [hd]
      exact (Finset.sum_eq_zero fun i _ => by rw [hmio (by decide) i β γ hβγ, mul_zero]).symm

end generic

section family

variable {a b : ℕ}

def x8ch {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ) :
    Superop (Fin a) (Fin b) :=
  krausApply (fun k => Matrix.of fun β i => W k (i, β))

lemma x8ch_channel {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ)
    (hW : ∀ i j, ∑ k, ∑ β, star (W k (i, β)) * W k (j, β) = if i = j then 1 else 0) :
    IsChannel (x8ch W) := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun n => Matrix.of fun β i => W (e.symm n) (i, β), ?_, ?_⟩
  · unfold IsKrausFamily
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← hW i j]
    exact e.symm.sum_comp (fun k => ∑ β, star (W k (i, β)) * W k (j, β))
  · intro ρ; unfold x8ch krausApply
    exact (e.symm.sum_comp (fun k => (Matrix.of fun β i => W k (i, β)) * ρ *
      (Matrix.of fun β i => W k (i, β))ᴴ)).symm

lemma x8ch_choi {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ)
    (p q : Fin a × Fin b) : choi (x8ch W) p q = ∑ k, W k p * star (W k q) := by
  simp [choi, x8ch, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma x8_trace_mul (X J : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (X * J).trace = ∑ p, ∑ q, X p q * J q p := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma x8ch_value {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (X * choi (x8ch W)).trace = ∑ k, ∑ p, ∑ q, star (W k p) * X p q * W k q := by
  rw [x8_trace_mul]
  simp only [x8ch_choi, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => by ring

def x8bg (S : Finset (Fin a)) (β0 : Fin b) (k : Fin a) : Fin a × Fin b → ℂ :=
  if k ∈ S then 0 else Pi.single (k, β0) 1

def x8W (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ) :
    Fin 2 ⊕ Fin a → Fin a × Fin b → ℂ :=
  Sum.elim V (x8bg S β0)

lemma x8bg_tp (S : Finset (Fin a)) (β0 : Fin b) (i j : Fin a) :
    ∑ k, ∑ β, star (x8bg S β0 k (i, β)) * x8bg S β0 k (j, β) =
      if i = j ∧ i ∉ S then 1 else 0 := by
  have : ∀ k, ∑ β, star (x8bg S β0 k (i, β)) * x8bg S β0 k (j, β) =
      if k = i ∧ k = j ∧ k ∉ S then 1 else 0 := by
    intro k
    unfold x8bg
    by_cases hk : k ∈ S
    · simp [hk]
    · simp only [hk, if_false, Pi.single_apply, Prod.ext_iff]
      by_cases hki : k = i
      · subst hki
        by_cases hkj : k = j
        · subst hkj; simp
        · simp [hkj, Ne.symm hkj]
      · simp [hki, Ne.symm hki]
  rw [Finset.sum_congr rfl fun k _ => this k]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i (fun k _ hk => if_neg (fun h => hk h.1)) (by simp)]
    by_cases hi : i ∈ S <;> simp [hi]
  · rw [Finset.sum_eq_zero, if_neg (fun h => hij h.1)]
    intro k _; rw [if_neg]; rintro ⟨rfl, rfl, -⟩; exact hij rfl

lemma x8W_channel (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
    (hsupp : ∀ m p, p.1 ∉ S → V m p = 0)
    (htp : ∀ i ∈ S, ∀ j ∈ S, ∑ m, ∑ β, star (V m (i, β)) * V m (j, β) =
      if i = j then 1 else 0) :
    IsChannel (x8ch (x8W S β0 V)) := by
  refine x8ch_channel _ fun i j => ?_
  rw [Fintype.sum_sum_type]
  simp only [x8W, Sum.elim_inl, Sum.elim_inr, x8bg_tp]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [htp i hi j hj]; simp [hi]
    · have : j ≠ i := fun h => hj (h ▸ hi)
      simp [hsupp _ (j, _) hj, hi, Ne.symm this]
  · simp [hsupp _ (i, _) hi, hi]

lemma x8W_choi_ne (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
    (p q : Fin a × Fin b) (hpq : p ≠ q) :
    choi (x8ch (x8W S β0 V)) p q = ∑ m, V m p * star (V m q) := by
  rw [x8ch_choi, Fintype.sum_sum_type]
  simp only [x8W, Sum.elim_inl, Sum.elim_inr, add_eq_left]
  refine Finset.sum_eq_zero fun k _ => ?_
  unfold x8bg
  split_ifs
  · simp
  · simp only [Pi.single_apply]
    split_ifs with h1 h2 <;> simp_all

lemma x8W_value (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (X * choi (x8ch (x8W S β0 V))).trace =
      ∑ m, (∑ p, ∑ q, star (V m p) * X p q * V m q) +
        ∑ k, if k ∈ S then 0 else X (k, β0) (k, β0) := by
  rw [x8ch_value, Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [x8W, Sum.elim_inr, x8bg]
  split_ifs
  · simp
  · simp [Pi.single_apply]

lemma x8_form1 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p1 : Fin a × Fin b) (x : ℂ) :
    ∑ p, ∑ q, star (Pi.single (M := fun _ => ℂ) p1 x p) * X p q * Pi.single (M := fun _ => ℂ) p1 x q =
      star x * X p1 p1 * x := by
  simp [Pi.single_apply, apply_ite (starRingEnd ℂ)]

lemma x8_form2 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p1 p2 : Fin a × Fin b)
    (h : p1 ≠ p2) (x y : ℂ) :
    ∑ p, ∑ q, star ((Pi.single p1 x + Pi.single p2 y : Fin a × Fin b → ℂ) p) * X p q *
      (Pi.single p1 x + Pi.single p2 y : Fin a × Fin b → ℂ) q =
      star x * X p1 p1 * x + star x * X p1 p2 * y + star y * X p2 p1 * x +
        star y * X p2 p2 * y := by
  simp only [Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
  simp [Pi.single_apply, apply_ite (starRingEnd ℂ), Ne.symm h]
  ring

lemma x8W_free (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
    (hsupp : ∀ m p, p.1 ∉ S → V m p = 0)
    (htp : ∀ i ∈ S, ∀ j ∈ S, ∑ m, ∑ β, star (V m (i, β)) * V m (j, β) =
      if i = j then 1 else 0) (O : Theory)
    (hmio : O ≠ .di → ∀ i β γ, β ≠ γ → ∑ m, V m (i, β) * star (V m (i, γ)) = 0)
    (hdi : O ≠ .mio → ∀ i j β, i ≠ j → ∑ m, V m (i, β) * star (V m (j, β)) = 0) :
    Free O (x8ch (x8W S β0 V)) := by
  refine x8_free_of_choi (x8W_channel S β0 V hsupp htp) O ?_ ?_
  · intro hO i β γ hβγ
    rw [x8W_choi_ne _ _ _ _ _ (by simp [hβγ])]
    exact hmio hO i β γ hβγ
  · intro hO i j β hij
    rw [x8W_choi_ne _ _ _ _ _ (by simp [hij])]
    exact hdi hO i j β hij

lemma x8_rest (S : Finset (Fin a)) (Y : Fin a → ℂ) :
    (∑ k, if k ∈ S then 0 else Y k) = ∑ k, Y k - ∑ k ∈ S, Y k := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) Y]
  rw [Finset.sum_ite, add_comm]
  simp only [Finset.sum_const_zero, zero_add]
  congr 1
  · congr 1; ext k; simp

lemma x8_v2_apply (i j k : Fin a) (β γ β' : Fin b) (x y : ℂ) :
    (Pi.single (i, β) x + Pi.single (j, γ) y : Fin a × Fin b → ℂ) (k, β') =
      (if k = i ∧ β' = β then x else 0) + (if k = j ∧ β' = γ then y else 0) := by
  simp [Pi.single_apply, Prod.ext_iff]

end family

section main

variable {a b : ℕ}

abbrev x8Y (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (β0 : Fin b) (k : Fin a) : ℂ :=
  X (k, β0) (k, β0)

lemma x8_D (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (O : Theory) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0) :
    ∑ k, x8Y X β0 k = 0 := by
  have h := hT _ (x8W_free ∅ β0 0 (by simp) (by simp) O (by simp) (by simp))
  rw [x8W_value] at h
  simpa using h

lemma x8_C (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (O : Theory) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0) (i : Fin a) (β : Fin b) :
    X (i, β) (i, β) = x8Y X β0 i := by
  have hD := x8_D X O β0 hT
  have h := hT _ (x8W_free {i} β0 ![Pi.single (i, β) 1, 0]
    (by intro m p hp; fin_cases m <;> simp [Pi.single_apply] <;> rintro rfl <;> simp at hp)
    (by intro k hk l hl; simp at hk hl; subst hk hl; simp [Pi.single_apply]) O
    (by intro _ k β' γ' h; simp [Pi.single_apply]; intros; simp_all)
    (by intro _ k l β' h; simp [Pi.single_apply]; intros; simp_all))
  rw [x8W_value, x8_rest, hD, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, x8_form1] at h
  simp at h
  linear_combination h

lemma x8_A_aux (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (O : Theory) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0) (i j : Fin a)
    (β γ : Fin b) (hij : i ≠ j) (hβγ : β ≠ γ) (c : ℂ) (hc : (starRingEnd ℂ) c * c = 1) :
    X (i, β) (j, γ) * c + (starRingEnd ℂ) c * X (j, γ) (i, β) = 0 := by
  have hD := x8_D X O β0 hT
  have h := hT _ (x8W_free {i, j} β0 ![Pi.single (i, β) 1 + Pi.single (j, γ) c, 0]
    (by intro m p hp; fin_cases m <;> simp [Pi.single_apply] <;> simp at hp <;> aesop)
    (by
      intro k hk l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
      rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
        simp [Pi.single_apply, hij, Ne.symm hij, hβγ, Ne.symm hβγ, ite_and]; exact hc)
    O
    (by
      intro _ k β' γ' h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, x8_v2_apply,
        Pi.zero_apply, zero_mul, add_zero]
      split_ifs <;> simp_all)
    (by
      intro _ k l β' h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, x8_v2_apply,
        Pi.zero_apply, zero_mul, add_zero]
      split_ifs <;> simp_all))
  rw [x8W_value, x8_rest, hD, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [x8_form2 X (i, β) (j, γ) (by simp [hij])] at h
  rw [x8_C X O β0 hT i β, x8_C X O β0 hT j γ, Finset.sum_pair hij] at h
  simp only [x8Y] at h
  simp at h
  linear_combination h - (X (j, β0) (j, β0)) * hc

lemma x8_zero_of (z w : ℂ) (hw : w = star z) (h1 : z * 1 + (starRingEnd ℂ) 1 * w = 0)
    (h2 : z * Complex.I + (starRingEnd ℂ) Complex.I * w = 0) : z = 0 := by
  subst hw
  apply Complex.ext <;> simp [Complex.ext_iff] at h1 h2 ⊢ <;> linarith

lemma x8_A (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (O : Theory) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0) (i j : Fin a)
    (β γ : Fin b) (hij : i ≠ j) (hβγ : β ≠ γ) : X (i, β) (j, γ) = 0 :=
  x8_zero_of _ _ (hX.apply _ _).symm (x8_A_aux X O β0 hT i j β γ hij hβγ 1 (by simp))
    (x8_A_aux X O β0 hT i j β γ hij hβγ _ (by simp))

lemma x8_A0_aux (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free .di E → (X * choi E).trace = 0) (i : Fin a)
    (β γ : Fin b) (hβγ : β ≠ γ) (c : ℂ) (hc : (starRingEnd ℂ) c * c = 1) :
    X (i, β) (i, γ) * c + (starRingEnd ℂ) c * X (i, γ) (i, β) = 0 := by
  have hD := x8_D X .di β0 hT
  have h := hT _ (x8W_free {i} β0 ![Pi.single (i, β) (3/5) + Pi.single (i, γ) (4/5 * c), 0]
    (by intro m p hp; fin_cases m <;> simp [Pi.single_apply] <;> simp at hp <;> aesop)
    (by
      intro k hk l hl
      simp only [Finset.mem_singleton] at hk hl
      subst hk hl
      simp [Pi.single_apply, hβγ, Ne.symm hβγ, ite_and, add_mul, mul_add, Finset.sum_add_distrib,
        apply_ite (starRingEnd ℂ), ite_mul, mul_ite, map_ofNat, map_div₀]
      linear_combination (16/25 : ℂ) * hc)
    .di (fun h => absurd rfl h)
    (by
      intro _ k l β' h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, x8_v2_apply,
        Pi.zero_apply, zero_mul, add_zero]
      split_ifs <;> simp_all))
  rw [x8W_value, x8_rest, hD, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [x8_form2 X (i, β) (i, γ) (by simp [hβγ])] at h
  rw [x8_C X .di β0 hT i β, x8_C X .di β0 hT i γ, Finset.sum_singleton] at h
  simp only [x8Y] at h
  simp at h
  linear_combination (25/12 : ℂ) * h - (4/3 : ℂ) * (X (i, β0) (i, β0)) * hc

lemma x8_A0 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free .di E → (X * choi E).trace = 0) (i : Fin a)
    (β γ : Fin b) (hβγ : β ≠ γ) : X (i, β) (i, γ) = 0 :=
  x8_zero_of _ _ (hX.apply _ _).symm (x8_A0_aux X β0 hT i β γ hβγ 1 (by simp))
    (x8_A0_aux X β0 hT i β γ hβγ _ (by simp))

lemma x8_B_aux (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free .mio E → (X * choi E).trace = 0) (i j : Fin a)
    (β δ : Fin b) (hij : i ≠ j) (hβδ : β ≠ δ) (c : ℂ) (hc : (starRingEnd ℂ) c * c = 1) :
    (X (i, β) (j, β) - X (i, δ) (j, δ)) * c +
      (starRingEnd ℂ) c * (X (j, β) (i, β) - X (j, δ) (i, δ)) = 0 := by
  have hD := x8_D X .mio β0 hT
  have h := hT _ (x8W_free {i, j} β0
    ![Pi.single (i, β) (3/5) + Pi.single (j, β) (4/5 * c),
      Pi.single (i, δ) (4/5) + Pi.single (j, δ) (-(3/5) * c)]
    (by intro m p hp; fin_cases m <;> simp [Pi.single_apply] <;> simp at hp <;> aesop)
    (by
      intro k hk l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
      rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
        simp [Pi.single_apply, hij, Ne.symm hij, hβδ, Ne.symm hβδ, ite_and, Fin.sum_univ_two,
          map_ofNat, map_div₀]
      all_goals first | ring1 | linear_combination hc | exact hc)
    .mio
    (by
      intro _ k β' γ' h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, x8_v2_apply]
      split_ifs <;> simp_all)
    (fun h => absurd rfl h))
  rw [x8W_value, x8_rest, hD, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [x8_form2 X (i, β) (j, β) (by simp [hij]), x8_form2 X (i, δ) (j, δ) (by simp [hij])] at h
  rw [x8_C X .mio β0 hT i β, x8_C X .mio β0 hT j β, x8_C X .mio β0 hT i δ,
    x8_C X .mio β0 hT j δ, Finset.sum_pair hij] at h
  simp only [x8Y] at h
  simp at h
  linear_combination (25/12 : ℂ) * h - (25/12 : ℂ) * (X (j, β0) (j, β0)) * hc

lemma x8_B (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free .mio E → (X * choi E).trace = 0) (i j : Fin a)
    (β δ : Fin b) (hij : i ≠ j) : X (i, β) (j, β) = X (i, δ) (j, δ) := by
  by_cases hβδ : β = δ
  · rw [hβδ]
  have := x8_zero_of _ (X (j, β) (i, β) - X (j, δ) (i, δ))
    (by rw [star_sub, hX.apply, hX.apply]) (x8_B_aux X β0 hT i j β δ hij hβδ 1 (by simp))
    (x8_B_aux X β0 hT i j β δ hij hβδ _ (by simp))
  exact sub_eq_zero.mp this

lemma x8_tr_P {E : Superop (Fin a) (Fin b)} (h : IsChannel E) (P : Matrix (Fin a) (Fin a) ℂ) :
    (Matrix.kronecker P (1 : Matrix (Fin b) (Fin b) ℂ) * choi E).trace = P.trace := by
  rw [x8_trace_mul]
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  have : ∀ i β j, (∑ γ, if β = γ then P i j * choi E (j, γ) (i, β) else 0) =
      P i j * choi E (j, β) (i, β) := by
    intro i β j; simp
  simp only [this]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, x8_choi_trB h]
  simp

lemma x8_back_mio {E : Superop (Fin a) (Fin b)} (hE : Free .mio E)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Fin a → Matrix (Fin b) (Fin b) ℂ) (hP : P.trace = 0)
    (hQ : ∀ i, dephasing (Q i) = 0) :
    ((Matrix.kronecker P 1 + ∑ i, Matrix.kronecker (Matrix.single i i 1) (Q i)) * choi E).trace
      = 0 := by
  rw [Matrix.add_mul, Matrix.trace_add, x8_tr_P hE.1, hP, zero_add, Matrix.sum_mul,
    Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [x8_trace_mul]
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply]
  refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun β _ =>
    Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun γ _ => ?_
  by_cases h1 : i = i' ∧ i = j'
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases hβγ : β = γ
    · subst hβγ
      have := congrFun (congrFun (hQ i) β) β
      simp only [dephasing, Matrix.diagonal_apply_eq, Matrix.zero_apply] at this
      simp [this]
    · rw [x8_mio_choi hE i γ β (Ne.symm hβγ)]; simp
  · rw [if_neg h1]; simp

lemma x8_back_di {E : Superop (Fin a) (Fin b)} (hE : Free .di E)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Fin b → Matrix (Fin a) (Fin a) ℂ) (hP : P.trace = 0)
    (hQ : ∀ i, dephasing (Q i) = 0) :
    ((Matrix.kronecker P 1 + ∑ i, Matrix.kronecker (Q i) (Matrix.single i i 1)) * choi E).trace
      = 0 := by
  rw [Matrix.add_mul, Matrix.trace_add, x8_tr_P hE.1, hP, zero_add, Matrix.sum_mul,
    Matrix.trace_sum]
  refine Finset.sum_eq_zero fun β0 _ => ?_
  rw [x8_trace_mul]
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun β _ =>
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun γ _ => ?_
  by_cases h1 : β0 = β ∧ β0 = γ
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases hij : i = j
    · subst hij
      have := congrFun (congrFun (hQ β0) i) i
      simp only [dephasing, Matrix.diagonal_apply_eq, Matrix.zero_apply] at this
      simp [this]
    · rw [x8_di_choi hE j i β0 (Ne.symm hij)]; simp
  · rw [if_neg h1]; simp

lemma x8_back_dio {E : Superop (Fin a) (Fin b)} (hE : Free .dio E)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.trace = 0) :
    ((Matrix.kronecker P 1 + (dephaseInput Q - dephaseOutput Q)) * choi E).trace = 0 := by
  rw [Matrix.add_mul, Matrix.trace_add, x8_tr_P hE.1, hP, zero_add, x8_trace_mul]
  obtain ⟨hm, hd⟩ := x8_dio_choi hE
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  simp only [Matrix.sub_apply, dephaseInput, dephaseOutput]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2
  · simp [h1, h2]
  · have := hm q.1 q.2 p.2 (Ne.symm h2)
    rw [show (q.1, q.2) = q from rfl, show (q.1, p.2) = p from Prod.ext h1.symm rfl] at this
    simp [h1, h2, this]
  · have := hd q.1 p.1 q.2 (Ne.symm h1)
    rw [show (q.1, q.2) = q from rfl, show (p.1, q.2) = p from Prod.ext rfl h2.symm] at this
    simp [h1, h2, this]
  · simp [h1, h2]

end main

section part1

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma x8_isChannel_of {K : Type*} [Fintype K] (E : K → Matrix B A ℂ)
    (hK : ∑ k, (E k)ᴴ * E k = 1) : IsChannel (krausApply E) := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun n => E (e.symm n), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hK]
    exact e.symm.sum_comp (fun k => (E k)ᴴ * E k)
  · intro ρ; unfold krausApply
    exact (e.symm.sum_comp (fun k => E k * ρ * (E k)ᴴ)).symm

lemma x8_choi_kraus {M : Superop A B} (h : IsChannel M) :
    ∃ (m : ℕ) (w : Fin m → A × B → ℂ),
      choi M = ∑ k, Matrix.vecMulVec (w k) (star (w k)) := by
  obtain ⟨m, E, -, hM⟩ := h
  refine ⟨m, fun k p => E k p.2 p.1, ?_⟩
  ext p q
  simp [choi, hM, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.vecMulVec_apply, ite_and]

/-- Pinching inequality: `n • (block-diagonal part of w wᴴ) - w wᴴ ⪰ 0`. -/
lemma x8_pinch_one {T G : Type*} [Fintype T] [Fintype G] [DecidableEq G]
    (g : T → G) (w : T → ℂ) :
    (Matrix.of fun p q => ((Fintype.card G : ℂ) * (if g p = g q then w p * star (w q) else 0)) -
      w p * star (w q)).PosSemidef := by
  set u : G → T → ℂ := fun x p => if g p = x then w p else 0
  have e : (Matrix.of fun p q => ((Fintype.card G : ℂ) * (if g p = g q then w p * star (w q) else 0)) -
      w p * star (w q)) = (1/2 : ℂ) • ∑ x, ∑ y,
        Matrix.vecMulVec (u x - u y) (star (u x - u y)) := by
    ext p q
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.sub_apply, Pi.star_apply, star_sub, u]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    simp [apply_ite (star : ℂ → ℂ), ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs with h <;> ring
  rw [e]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun x _ =>
    Matrix.posSemidef_sum _ fun y _ => Matrix.posSemidef_vecMulVec_self_star _) ?_
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

lemma x8_pinch_sum {T G : Type*} [Fintype T] [Fintype G] [DecidableEq G]
    (g : T → G) {m : ℕ} (w : Fin m → T → ℂ) (J J' : Matrix T T ℂ)
    (hJ : J = ∑ k, Matrix.vecMulVec (w k) (star (w k)))
    (hJ' : ∀ p q, J' p q = if g p = g q then J p q else 0) :
    (((Fintype.card G : ℝ) : ℂ) • J' - J).PosSemidef := by
  have e : ((Fintype.card G : ℝ) : ℂ) • J' - J = ∑ k, (Matrix.of fun p q =>
      ((Fintype.card G : ℂ) * (if g p = g q then w k p * star (w k q) else 0)) -
        w k p * star (w k q)) := by
    ext p q
    simp only [Matrix.sub_apply, Matrix.smul_apply, hJ', hJ, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Matrix.of_apply, Finset.sum_sub_distrib,
      smul_eq_mul, Complex.ofReal_natCast]
    split_ifs <;> simp [Finset.mul_sum]
  rw [e]
  exact Matrix.posSemidef_sum _ fun k _ => x8_pinch_one g (w k)

lemma x8_deph_sum (Y : Matrix A A ℂ) :
    ∑ i, Matrix.single i i (1 : ℂ) * Y * Matrix.single i i 1 = dephasing Y := by
  simp only [Matrix.single_mul_mul_single, one_mul, mul_one]
  ext p q
  simp only [Matrix.sum_apply, dephasing, Matrix.diagonal_apply, Matrix.single_apply]
  by_cases h : p = q
  · subst h; simp
  · simp only [h, if_false]
    exact Finset.sum_eq_zero fun c _ => if_neg (fun h' => h (h'.1.symm.trans h'.2))

lemma x8_deph_deph (Y : Matrix A A ℂ) : dephasing (dephasing Y) = dephasing Y := by
  ext p q; simp [dephasing, Matrix.diagonal_apply]

lemma x8_mioM_channel {E : Superop A B} (h : IsChannel E) :
    IsChannel (fun X => dephasing (E X)) := by
  obtain ⟨m, K, hK, hE⟩ := h
  have hc := x8_isChannel_of (fun bk : B × Fin m => Matrix.single bk.1 bk.1 (1 : ℂ) * K bk.2) (by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one]
    rw [Finset.sum_comm]
    unfold IsKrausFamily at hK
    rw [← hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ x : B, (K k)ᴴ * (Matrix.single x x (1 : ℂ) : Matrix B B ℂ) *
        ((Matrix.single x x 1 : Matrix B B ℂ) * K k) =
        (K k)ᴴ * (Matrix.single x x (1 : ℂ) : Matrix B B ℂ) * K k := by
      intro x
      rw [Matrix.mul_assoc ((K k)ᴴ), ← Matrix.mul_assoc (Matrix.single x x (1 : ℂ) : Matrix B B ℂ),
        Matrix.single_mul_single_same, mul_one, ← Matrix.mul_assoc]
    simp only [this]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    rw [show ∑ x : B, Matrix.single x x (1 : ℂ) = 1 from by
      ext p q
      simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
      by_cases h : p = q
      · subst h; simp
      · simp only [h, if_false]
        exact Finset.sum_eq_zero fun c _ => if_neg (fun h' => h (h'.1.symm.trans h'.2))]
    simp)
  convert hc using 1
  funext X
  rw [krausApply, Fintype.sum_prod_type, hE, krausApply, ← x8_deph_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one, Finset.mul_sum,
    Finset.sum_mul, Matrix.mul_assoc]

lemma x8_diM_channel {E : Superop A B} (h : IsChannel E) :
    IsChannel (fun X => E (dephasing X)) := by
  obtain ⟨m, K, hK, hE⟩ := h
  have hc := x8_isChannel_of (fun ka : Fin m × A => K ka.1 * Matrix.single ka.2 ka.2 (1 : ℂ)) (by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one]
    have : ∀ k (x : A), (Matrix.single x x (1 : ℂ) : Matrix A A ℂ) * (K k)ᴴ *
        (K k * (Matrix.single x x 1 : Matrix A A ℂ)) =
        (Matrix.single x x (1 : ℂ) : Matrix A A ℂ) * ((K k)ᴴ * K k) * Matrix.single x x 1 := by
      intro k x
      simp only [Matrix.mul_assoc]
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    unfold IsKrausFamily at hK
    rw [hK]
    simp only [mul_one, Matrix.single_mul_single_same]
    ext p q
    simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h; simp
    · simp only [h, if_false]
      exact Finset.sum_eq_zero fun c _ => if_neg (fun h' => h (h'.1.symm.trans h'.2)))
  convert hc using 1
  funext X
  rw [krausApply, Fintype.sum_prod_type, hE, krausApply, ← x8_deph_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]

lemma x8_bound_mio {E : Superop A B} (h : IsChannel E) [Nonempty B] :
    maxRobustness .mio E ≤ (Fintype.card B : ℝ≥0∞) := by
  obtain ⟨m, w, hw⟩ := x8_choi_kraus h
  unfold maxRobustness
  apply sInf_le
  refine ⟨Fintype.card B, by exact_mod_cast Fintype.card_pos, by simp, _,
    ⟨x8_mioM_channel h, fun X => (x8_deph_deph _).symm⟩, ?_⟩
  refine x8_pinch_sum (g := Prod.snd) w _ _ hw fun p q => ?_
  simp only [choi, dephasing, Matrix.diagonal_apply]
  split_ifs with h1
  · rw [h1]
  · rfl

lemma x8_bound_di {E : Superop A B} (h : IsChannel E) [Nonempty A] :
    maxRobustness .di E ≤ (Fintype.card A : ℝ≥0∞) := by
  obtain ⟨m, w, hw⟩ := x8_choi_kraus h
  unfold maxRobustness
  apply sInf_le
  refine ⟨Fintype.card A, by exact_mod_cast Fintype.card_pos, by simp, _,
    ⟨x8_diM_channel h, fun X => by simp only [x8_deph_deph]⟩, ?_⟩
  refine x8_pinch_sum (g := Prod.fst) w _ _ hw fun p q => ?_
  simp only [choi]
  rw [x8_deph_single]
  split_ifs with h1
  · rfl
  · rw [x8_ch_zero h]; rfl

end part1

section fourier

variable {d : ℕ} [NeZero d]

lemma x8_conj (x : ZMod d) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

lemma x8_esum (c : ZMod d) :
    ∑ x : ZMod d, (ZMod.stdAddChar (x * c) : ℂ) = if c = 0 then (d : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  split_ifs <;> simp

lemma x8_cf (j k : ZMod d) :
    cyclicFourier d j k = (ZMod.stdAddChar (j * k) : ℂ) / (Real.sqrt d : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  simp only [cyclicFourier, Matrix.submatrix_apply, qftMatrix, Matrix.of_apply]
  rw [ZMod.stdAddChar_apply, ← ZMod.natCast_zmod_val (j * k), ZMod.toCircle_natCast]
  rw [← ZMod.toCircle_natCast, ← ZMod.toCircle_natCast]
  have h : ((((ZMod.finEquiv n.succ).symm j : ℕ) * ((ZMod.finEquiv n.succ).symm k : ℕ) : ℕ) :
      ZMod n.succ) = (((j * k).val : ℕ) : ZMod n.succ) := by
    rw [ZMod.natCast_zmod_val]; push_cast
    congr 1
    · exact ZMod.natCast_zmod_val (n := n.succ) j
    · exact ZMod.natCast_zmod_val (n := n.succ) k
  rw [h]

lemma x8_sqrt_sq : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp

lemma x8_d_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)

lemma x8_qft_cf (β i : Fin d) :
    qftMatrix d β i = cyclicFourier d (ZMod.finEquiv d β) (ZMod.finEquiv d i) := by
  simp [cyclicFourier]

lemma x8_F_orth (i j : Fin d) :
    ∑ β, star (qftMatrix d β i) * qftMatrix d β j = if i = j then 1 else 0 := by
  simp only [x8_qft_cf]
  rw [Fintype.sum_bijective (ZMod.finEquiv d) (ZMod.finEquiv d).bijective _
    (fun x => star (cyclicFourier d x (ZMod.finEquiv d i)) * cyclicFourier d x (ZMod.finEquiv d j))
    (fun _ => rfl)]
  simp only [x8_cf, star_div₀, Complex.star_def, Complex.conj_ofReal, x8_conj]
  have : ∀ x : ZMod d, (ZMod.stdAddChar (-(x * ZMod.finEquiv d i)) : ℂ) / (Real.sqrt d : ℂ) *
      ((ZMod.stdAddChar (x * ZMod.finEquiv d j) : ℂ) / (Real.sqrt d : ℂ)) =
      (ZMod.stdAddChar (x * (ZMod.finEquiv d j - ZMod.finEquiv d i)) : ℂ) / d := by
    intro x
    rw [div_mul_div_comm, x8_sqrt_sq, ← AddChar.map_add_eq_mul]
    congr 2; ring
  simp only [this, ← Finset.sum_div, x8_esum, sub_eq_zero]
  have hinj : ZMod.finEquiv d j = ZMod.finEquiv d i ↔ i = j :=
    ⟨fun h => ((ZMod.finEquiv d).injective h).symm, fun h => h ▸ rfl⟩
  by_cases h : i = j
  · rw [if_pos (hinj.2 h), if_pos h, div_self x8_d_ne]
  · rw [if_neg (fun h' => h (hinj.1 h')), if_neg h, zero_div]

lemma x8_F_normSq (β i : Fin d) : star (qftMatrix d β i) * qftMatrix d β i = 1 / d := by
  rw [x8_qft_cf, x8_cf, star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm,
    x8_sqrt_sq, ← Complex.star_def]
  rw [Complex.star_def, x8_conj, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

lemma x8_F_unitary : (qftMatrix d)ᴴ * qftMatrix d = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [Matrix.conjTranspose_apply] using x8_F_orth i j

lemma x8_F_channel : IsChannel (fourierChannel d) :=
  ⟨1, fun _ => qftMatrix d, by simp [IsKrausFamily, x8_F_unitary], fun ρ => by
    simp [fourierChannel, conjSuperop, krausApply]⟩

lemma x8_choiF (p q : Fin d × Fin d) :
    choi (fourierChannel d) p q = qftMatrix d p.2 p.1 * star (qftMatrix d q.2 q.1) := by
  simp [choi, fourierChannel, conjSuperop, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and]

lemma x8_quad {T : Type*} [Fintype T] (A : Matrix T T ℂ) (x : T → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) = ∑ p, ∑ q, star (x p) * A p q * x q := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma x8_lower_mio (t : ℝ) (M : Superop (Fin d) (Fin d)) (hM : Free .mio M)
    (hP : ((t : ℂ) • choi M - choi (fourierChannel d)).PosSemidef) : (d : ℝ) ≤ t := by
  set i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  set x : Fin d × Fin d → ℂ := fun p => if p.1 = i0 then qftMatrix d p.2 i0 else 0
  have h := hP.dotProduct_mulVec_nonneg x
  rw [x8_quad] at h
  have hF : ∑ p, ∑ q, star (x p) * choi (fourierChannel d) p q * x q = 1 := by
    simp only [x8_choiF]
    have : ∀ p q, star (x p) * (qftMatrix d p.2 p.1 * star (qftMatrix d q.2 q.1)) * x q =
        (star (x p) * qftMatrix d p.2 p.1) * star (star (x q) * qftMatrix d q.2 q.1) := by
      intro p q; simp; ring
    simp only [this, ← Finset.mul_sum, ← Finset.sum_mul, ← star_sum]
    have h1 : ∑ p, star (x p) * qftMatrix d p.2 p.1 = 1 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
      simpa [x] using x8_F_orth (d := d) i0 i0
    rw [h1]; simp
  have hJ : ∑ p, ∑ q, star (x p) * choi M p q * x q = 1 / d := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
    have : ∀ β, ∑ q, star (x (i0, β)) * choi M (i0, β) q * x q =
        star (qftMatrix d β i0) * qftMatrix d β i0 * choi M (i0, β) (i0, β) := by
      intro β
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
      rw [Finset.sum_eq_single β (fun γ _ hγ => by rw [x8_mio_choi hM i0 β γ (Ne.symm hγ)]; simp)
        (by simp)]
      simp [x]; ring
    simp only [this, x8_F_normSq, ← Finset.mul_sum, x8_choi_trB hM.1]
    simp
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, sub_mul,
    Finset.sum_sub_distrib] at h
  have e2 : ∑ p, ∑ q, star (x p) * ((t : ℂ) * choi M p q) * x q =
      (t : ℂ) * ∑ p, ∑ q, star (x p) * choi M p q * x q := by
    simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [e2, hF, hJ] at h
  have : (0 : ℂ) ≤ ((t / d - 1 : ℝ) : ℂ) := by
    convert h using 1; push_cast; ring
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have := Complex.zero_le_real.mp this
  rw [sub_nonneg, le_div_iff₀ hd] at this
  linarith

lemma x8_lower_di (t : ℝ) (M : Superop (Fin d) (Fin d)) (hM : Free .di M)
    (hP : ((t : ℂ) • choi M - choi (fourierChannel d)).PosSemidef) : (d : ℝ) ≤ t := by
  set x : Fin d → Fin d × Fin d → ℂ := fun β p => if p.2 = β then qftMatrix d β p.1 else 0
  have hrow : ∀ β, ∑ i, star (qftMatrix d β i) * qftMatrix d β i = 1 := by
    intro β; simp only [x8_F_normSq]; simp [x8_d_ne]
  have hF : ∀ β, ∑ p, ∑ q, star (x β p) * choi (fourierChannel d) p q * x β q = 1 := by
    intro β
    simp only [x8_choiF]
    have : ∀ p q, star (x β p) * (qftMatrix d p.2 p.1 * star (qftMatrix d q.2 q.1)) * x β q =
        (star (x β p) * qftMatrix d p.2 p.1) * star (star (x β q) * qftMatrix d q.2 q.1) := by
      intro p q; simp; ring
    simp only [this, ← Finset.mul_sum, ← Finset.sum_mul, ← star_sum]
    have h1 : ∑ p, star (x β p) * qftMatrix d p.2 p.1 = 1 := by
      rw [Fintype.sum_prod_type]
      rw [← hrow β]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single β (fun γ _ hγ => by simp [x, hγ]) (by simp)]
      simp [x]
    rw [h1]; simp
  have hJ : ∀ β, ∑ p, ∑ q, star (x β p) * choi M p q * x β q =
      1 / d * ∑ i, choi M (i, β) (i, β) := by
    intro β
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single β (fun γ _ hγ => by simp [x, hγ]) (by simp)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
    · rw [Finset.sum_eq_single β (fun γ _ hγ => by simp [x, hγ]) (by simp)]
      simp only [x, if_true]
      rw [← x8_F_normSq β i]; ring
    · rw [Finset.sum_eq_single β (fun γ _ hγ => by simp [x, hγ]) (by simp)]
      rw [x8_di_choi hM i j β (Ne.symm hj)]; simp
  have h : ∀ β, (0 : ℂ) ≤ (t : ℂ) * (1 / d * ∑ i, choi M (i, β) (i, β)) - 1 := by
    intro β
    have h := (hP.dotProduct_mulVec_nonneg (x β))
    rw [x8_quad] at h
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, sub_mul,
      Finset.sum_sub_distrib] at h
    have e2 : ∑ p, ∑ q, star (x β p) * ((t : ℂ) * choi M p q) * x β q =
        (t : ℂ) * ∑ p, ∑ q, star (x β p) * choi M p q * x β q := by
      simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => by ring
    rwa [e2, hF, hJ] at h
  have hs := Finset.sum_nonneg (fun β (_ : β ∈ Finset.univ) => h β)
  have htot : ∑ β : Fin d, ∑ i, choi M (i, β) (i, β) = d := by
    rw [Finset.sum_comm]
    simp only [x8_choi_trB hM.1]; simp
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htot] at hs
  have : (0 : ℂ) ≤ ((t - d : ℝ) : ℂ) := by
    convert hs using 1; push_cast; field_simp [x8_d_ne]; simp
  have := Complex.zero_le_real.mp this
  linarith

lemma x8_maxRob_mio : maxRobustness .mio (fourierChannel d) = d := by
  apply le_antisymm
  · simpa using x8_bound_mio (x8_F_channel (d := d))
  · unfold maxRobustness
    apply le_sInf
    rintro s ⟨t, -, rfl, M, hM, hP⟩
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (x8_lower_mio t M hM hP)

lemma x8_maxRob_di : maxRobustness .di (fourierChannel d) = d := by
  apply le_antisymm
  · simpa using x8_bound_di (x8_F_channel (d := d))
  · unfold maxRobustness
    apply le_sInf
    rintro s ⟨t, -, rfl, M, hM, hP⟩
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (x8_lower_di t M hM hP)

/-- `φ = (1 ⊗ F) ψ`. -/
def x8phi (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (p : Fin d × Fin d) : ℂ :=
  ∑ γ, qftMatrix d p.2 γ * ψ (p.1, γ)

/-- `v(β,δ) = ⟨ψ_β, φ_δ⟩`. -/
def x8v (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (p : Fin d × Fin d) : ℂ :=
  ∑ r, star (ψ (r, p.1)) * x8phi ψ (r, p.2)

lemma x8_rhoF (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (p q : Fin d × Fin d) :
    idTensorSuperop (R := Fin d) (fourierChannel d) (pureDensity ψ) p q =
      x8phi ψ p * star (x8phi ψ q) := by
  simp only [idTensorSuperop, fourierChannel, conjSuperop, pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, x8phi, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ' _ => Finset.sum_congr rfl fun γ _ => ?_
  simp; ring

lemma x8_rhoM (ψ : EuclideanSpace ℂ (Fin d × Fin d)) {M : Superop (Fin d) (Fin d)}
    (hM : IsChannel M) (q p : Fin d × Fin d) :
    idTensorSuperop (R := Fin d) M (pureDensity ψ) q p =
      ∑ β, ∑ β', ψ (q.1, β) * star (ψ (p.1, β')) * choi M (β, q.2) (β', p.2) := by
  simp only [idTensorSuperop, Matrix.of_apply]
  rw [x8_ch_expand hM]
  simp [pureDensity]

end fourier

section affine

variable {d : ℕ} [NeZero d]

private def x8e6 : (Fin d × Fin d × Fin d × Fin d × Fin d × Fin d) ≃
    (Fin d × Fin d × Fin d × Fin d × Fin d × Fin d) where
  toFun x := (x.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.2, x.2.1, x.1, x.2.2.1)
  invFun y := (y.2.2.2.2.1, y.2.2.2.1, y.2.2.2.2.2, y.2.1, y.1, y.2.2.1)
  left_inv x := rfl
  right_inv y := rfl

lemma x8_val (ψ : EuclideanSpace ℂ (Fin d × Fin d)) {M : Superop (Fin d) (Fin d)}
    (hM : IsChannel M) :
    (idTensorSuperop (R := Fin d) (fourierChannel d) (pureDensity ψ) *
      idTensorSuperop (R := Fin d) M (pureDensity ψ)).trace =
      ∑ p, ∑ q, star (x8v ψ p) * choi M p q * x8v ψ q := by
  rw [x8_trace_mul]
  simp only [x8_rhoF, x8_rhoM ψ hM]
  have hL : ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, x8phi ψ p * star (x8phi ψ q) *
      ∑ β, ∑ β', ψ (q.1, β) * star (ψ (p.1, β')) * choi M (β, q.2) (β', p.2) =
      ∑ x : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d,
        x8phi ψ (x.1, x.2.1) * star (x8phi ψ (x.2.2.1, x.2.2.2.1)) *
          (ψ (x.2.2.1, x.2.2.2.2.1) * star (ψ (x.1, x.2.2.2.2.2)) *
            choi M (x.2.2.2.2.1, x.2.2.2.1) (x.2.2.2.2.2, x.2.1)) := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
  have hR : ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, star (x8v ψ p) * choi M p q * x8v ψ q =
      ∑ y : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d,
        ψ (y.2.2.2.2.2, y.1) * star (x8phi ψ (y.2.2.2.2.2, y.2.1)) *
          choi M (y.1, y.2.1) (y.2.2.1, y.2.2.2.1) *
          (star (ψ (y.2.2.2.2.1, y.2.2.1)) * x8phi ψ (y.2.2.2.2.1, y.2.2.2.1)) := by
    simp only [x8v, star_sum, star_mul', star_star, Fintype.sum_prod_type, Finset.mul_sum,
      Finset.sum_mul]
  rw [hL, hR]
  exact Fintype.sum_equiv x8e6 _ _ fun x => by simp [x8e6]; ring

lemma x8_choi_star {M : Superop (Fin d) (Fin d)} (hM : IsChannel M) (p q : Fin d × Fin d) :
    star (choi M p q) = choi M q p := by
  obtain ⟨m, w, hw⟩ := x8_choi_kraus hM
  rw [hw]
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]

lemma x8_quad_real {M : Superop (Fin d) (Fin d)} (hM : IsChannel M) (v : Fin d × Fin d → ℂ) :
    star (∑ p, ∑ q, star (v p) * choi M p q * v q) = ∑ p, ∑ q, star (v p) * choi M p q * v q := by
  simp only [star_sum, star_mul', star_star, x8_choi_star hM]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

lemma x8_norm_sum (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (hψ : ‖ψ‖ = 1) :
    ∑ p, star (ψ p) * ψ p = 1 := by
  have h := @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ ψ
  simp only [hψ, RCLike.ofReal_one, one_pow, PiLp.inner_apply, RCLike.inner_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_comm]; rfl

lemma x8_star_mul_self_eq_zero {z : ℂ} (h : z * star z = 0) : z = 0 := by
  rw [Complex.star_def, Complex.mul_conj] at h
  exact Complex.normSq_eq_zero.mp (by exact_mod_cast h)

/-- Gram matrix of the slices of `ψ`. -/
def x8G (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (β γ : Fin d) : ℂ :=
  ∑ r, star (ψ (r, β)) * ψ (r, γ)

lemma x8_v_G (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (β δ : Fin d) :
    x8v ψ (β, δ) = ∑ γ, qftMatrix d δ γ * x8G ψ β γ := by
  simp only [x8v, x8phi, x8G, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun γ _ => by ring

lemma x8_G_v (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (β γ : Fin d) :
    x8G ψ β γ = ∑ δ, star (qftMatrix d δ γ) * x8v ψ (β, δ) := by
  simp only [x8_v_G, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ γ', ∑ δ, star (qftMatrix d δ γ) * (qftMatrix d δ γ' * x8G ψ β γ') =
      (if γ = γ' then 1 else 0) * x8G ψ β γ' := by
    intro γ'
    rw [← x8_F_orth γ γ', Finset.sum_mul]
    exact Finset.sum_congr rfl fun δ _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma x8_G_trace (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (hψ : ‖ψ‖ = 1) :
    ∑ β, x8G ψ β β = 1 := by
  rw [← x8_norm_sum ψ hψ, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma x8_G_diag_zero (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (j : Fin d) (h : x8G ψ j j = 0)
    (r : Fin d) : ψ (r, j) = 0 := by
  have e : x8G ψ j j = ((∑ r, Complex.normSq (ψ (r, j)) : ℝ) : ℂ) := by
    simp only [x8G, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  rw [e] at h
  have h' : ∑ r, Complex.normSq (ψ (r, j)) = 0 := by exact_mod_cast h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun r _ => Complex.normSq_nonneg _)] at h'
  exact Complex.normSq_eq_zero.mp (h' r (Finset.mem_univ r))

lemma x8_aff_lower (ψ : EuclideanSpace ℂ (Fin d × Fin d)) (hψ : ‖ψ‖ = 1) (t : ℝ)
    (h : ∀ M : Superop (Fin d) (Fin d), Free .mio M →
      ((idTensorSuperop (R := Fin d) (fourierChannel d) (pureDensity ψ)) *
        (idTensorSuperop (R := Fin d) M (pureDensity ψ))).trace.re = t) : t = 1 / d := by
  set v := x8v ψ with hv_def
  have hval : ∀ M, Free .mio M → ∑ p, ∑ q, star (v p) * choi M p q * v q = (t : ℂ) := by
    intro M hM
    have h1 := h M hM
    rw [x8_val ψ hM.1] at h1
    have h2 := x8_quad_real hM.1 v
    rw [Complex.star_def, Complex.conj_eq_iff_im] at h2
    apply Complex.ext
    · simpa using h1
    · simpa using h2
  set X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.vecMulVec v (star v) - ((t / d : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) with hX_def
  have hXe : ∀ p q, X p q = v p * star (v q) - if p = q then ((t / d : ℝ) : ℂ) else 0 := by
    intro p q
    simp [X, Matrix.vecMulVec_apply, Matrix.one_apply]
  have hX : X.IsHermitian := by
    ext p q
    rw [Matrix.conjTranspose_apply, hXe, hXe]
    by_cases hpq : p = q
    · subst hpq; simp [mul_comm]
    · simp [hpq, Ne.symm hpq, mul_comm]
  have hT : ∀ M : Superop (Fin d) (Fin d), Free .mio M → (X * choi M).trace = 0 := by
    intro M hM
    rw [x8_trace_mul]
    simp only [hXe, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have e1 : ∑ p, ∑ q, v p * star (v q) * choi M q p = t := by
      rw [← hval M hM, Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    have e2 : ∑ p : Fin d × Fin d, choi M p p = d := by
      rw [Fintype.sum_prod_type]
      simp only [x8_choi_trB hM.1]; simp
    rw [e1, ← Finset.mul_sum, e2]
    push_cast
    rw [div_mul_cancel₀ _ x8_d_ne, sub_self]
  set β0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hC : ∀ i β, v (i, β) * star (v (i, β)) = v (i, β0) * star (v (i, β0)) := by
    intro i β
    have := x8_C X .mio β0 hT i β
    simpa [hXe] using this
  have hA : ∀ i j β γ, i ≠ j → β ≠ γ → v (i, β) * star (v (j, γ)) = 0 := by
    intro i j β γ hij hβγ
    have := x8_A X hX .mio β0 hT i j β γ hij hβγ
    simpa [hXe, hij] using this
  have hD : ∑ i, v (i, β0) * star (v (i, β0)) = t := by
    have := x8_D X .mio β0 hT
    simp only [x8Y, hXe, if_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at this
    rw [sub_eq_zero] at this
    rw [this]; push_cast; rw [mul_div_cancel₀ _ x8_d_ne]
  have hrow0 : ∀ j, v (j, β0) * star (v (j, β0)) = 0 → ∀ δ, v (j, δ) = 0 := by
    intro j hj δ
    exact x8_star_mul_self_eq_zero (by rw [hC j δ, hj])
  obtain ⟨k, hk⟩ : ∃ k, v (k, β0) * star (v (k, β0)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hG : ∀ β γ, x8G ψ β γ = 0 := by
      intro β γ
      rw [x8_G_v]
      exact Finset.sum_eq_zero fun δ _ => by rw [← hv_def, hrow0 β (hall β) δ, mul_zero]
    have := x8_G_trace ψ hψ
    simp [hG] at this
  have hother : ∀ j, j ≠ k → ∀ δ, v (j, δ) = 0 := by
    intro j hjk
    apply hrow0
    have h1 := hA j k j k hjk hjk
    have : (v (j, j) * star (v (j, j))) * (v (k, k) * star (v (k, k))) = 0 := by
      calc _ = (v (j, j) * star (v (k, k))) * star (v (j, j) * star (v (k, k))) := by
              simp only [star_mul', star_star]; ring
        _ = 0 := by rw [h1]; simp
    rw [hC j j, hC k k] at this
    exact (mul_eq_zero.mp this).resolve_right hk
  have hψj : ∀ j, j ≠ k → ∀ r, ψ (r, j) = 0 := by
    intro j hjk
    apply x8_G_diag_zero
    rw [x8_G_v]
    exact Finset.sum_eq_zero fun δ _ => by rw [← hv_def, hother j hjk δ, mul_zero]
  have hGk : ∀ γ, γ ≠ k → x8G ψ k γ = 0 := by
    intro γ hγ
    simp only [x8G, hψj γ hγ, mul_zero, Finset.sum_const_zero]
  have hGkk : x8G ψ k k = 1 := by
    have := x8_G_trace ψ hψ
    rw [Finset.sum_eq_single k (fun β _ hβ => ?_) (by simp)] at this
    · exact this
    · simp only [x8G, hψj β hβ, star_zero, zero_mul, Finset.sum_const_zero]
  have hvk : v (k, β0) = qftMatrix d β0 k := by
    rw [hv_def, x8_v_G, Finset.sum_eq_single k (fun γ _ hγ => by rw [hGk γ hγ, mul_zero])
      (by simp), hGkk, mul_one]
  have hsum : ∑ i, v (i, β0) * star (v (i, β0)) = v (k, β0) * star (v (k, β0)) :=
    Finset.sum_eq_single k (fun j _ hj => by rw [hother j hj β0]; simp) (by simp)
  rw [hsum, hvk, mul_comm, x8_F_normSq] at hD
  have : ((t : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by rw [← hD]; push_cast; ring
  exact_mod_cast this

lemma x8_quad_e0 (i0 : Fin d) (M : Superop (Fin d) (Fin d)) (hM : Free .mio M) :
    ∑ p, ∑ q, star (if p.1 = i0 then qftMatrix d p.2 i0 else 0) * choi M p q *
      (if q.1 = i0 then qftMatrix d q.2 i0 else 0) = 1 / d := by
  set x : Fin d × Fin d → ℂ := fun p => if p.1 = i0 then qftMatrix d p.2 i0 else 0
  show ∑ p, ∑ q, star (x p) * choi M p q * x q = 1 / d
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
  have : ∀ β, ∑ q, star (x (i0, β)) * choi M (i0, β) q * x q =
      star (qftMatrix d β i0) * qftMatrix d β i0 * choi M (i0, β) (i0, β) := by
    intro β
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i0 (fun i _ hi => by simp [x, hi]) (by simp)]
    rw [Finset.sum_eq_single β (fun γ _ hγ => by rw [x8_mio_choi hM i0 β γ (Ne.symm hγ)]; simp)
      (by simp)]
    simp [x]; ring
  simp only [this, x8_F_normSq, ← Finset.mul_sum, x8_choi_trB hM.1]
  simp

lemma x8_v_e0 (i0 : Fin d) (p : Fin d × Fin d) :
    x8v (EuclideanSpace.single (i0, i0) (1 : ℂ)) p =
      if p.1 = i0 then qftMatrix d p.2 i0 else 0 := by
  simp only [x8v, x8phi, EuclideanSpace.single_apply, Prod.ext_iff]
  by_cases h : p.1 = i0
  · simp [h]
  · simp [h]

lemma x8_aff : isometricAffineMinRobustness .mio (fourierChannel d) = d := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  set i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  unfold isometricAffineMinRobustness
  have hS : sInf {s | ∃ t : ℝ, 0 ≤ t ∧ s = ENNReal.ofReal t ∧
      ∃ psi : EuclideanSpace ℂ (Fin d × Fin d), ‖psi‖ = 1 ∧
        ∀ M : Superop (Fin d) (Fin d), Free .mio M →
          ((idTensorSuperop (R := Fin d) (fourierChannel d) (pureDensity psi)) *
            (idTensorSuperop (R := Fin d) M (pureDensity psi))).trace.re = t} =
      ENNReal.ofReal (1 / d) := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨1 / d, by positivity, rfl, EuclideanSpace.single (i0, i0) 1, by simp, ?_⟩
      intro M hM
      rw [x8_val _ hM.1]
      simp only [x8_v_e0]
      rw [x8_quad_e0 i0 M hM]
      simp
    · apply le_sInf
      rintro s ⟨t, -, rfl, ψ, hψ, hall⟩
      rw [x8_aff_lower ψ hψ t hall]
  rw [hS, one_div, ENNReal.ofReal_inv_of_pos hd, ENNReal.ofReal_natCast, inv_inv]

end affine

theorem x8_main :
    (∀ (a b : ℕ), 0 < a → 0 < b → ∀ E : Superop (Fin a) (Fin b),
      IsChannel E → maxRobustness .mio E ≤ (b : ℝ≥0∞) ∧
        maxRobustness .di E ≤ (a : ℝ≥0∞)) ∧
    (∀ d : ℕ, 0 < d →
      maxRobustness .mio (fourierChannel d) = (d : ℝ≥0∞) ∧
      maxRobustness .di (fourierChannel d) = (d : ℝ≥0∞) ∧
      maxRobustness .mio (fourierChannel d) =
        isometricAffineMinRobustness .mio (fourierChannel d)) := by
  refine ⟨fun a b ha hb E hE => ?_, fun d hd => ?_⟩
  · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    haveI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    exact ⟨by simpa using x8_bound_mio hE, by simpa using x8_bound_di hE⟩
  · haveI : NeZero d := ⟨by omega⟩
    exact ⟨x8_maxRob_mio, x8_maxRob_di, by rw [x8_maxRob_mio, x8_aff]⟩

end QAlgorithms.Papers.Independent.Information100.P34

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution :
    (∀ (a b : ℕ), 0 < a → 0 < b → ∀ E : Superop (Fin a) (Fin b),
      IsChannel E → maxRobustness .mio E ≤ (b : ℝ≥0∞) ∧
        maxRobustness .di E ≤ (a : ℝ≥0∞)) ∧
    (∀ d : ℕ, 0 < d →
      maxRobustness .mio (fourierChannel d) = (d : ℝ≥0∞) ∧
      maxRobustness .di (fourierChannel d) = (d : ℝ≥0∞) ∧
      maxRobustness .mio (fourierChannel d) =
        isometricAffineMinRobustness .mio (fourierChannel d)) :=
  x8_main
