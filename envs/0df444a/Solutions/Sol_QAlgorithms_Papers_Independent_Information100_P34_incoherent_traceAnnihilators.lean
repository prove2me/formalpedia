-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.incoherent_traceAnnihilators
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:04:42.507982+00:00
-- url     : https://prove2.me/submissions/577bcb36-f015-4dab-a068-b708074c625e

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

section generic

set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

private lemma x8_ch_zero {M : Superop A B} (h : IsChannel M) : M 0 = 0 := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply]; simp

private lemma x8_ch_trace {M : Superop A B} (h : IsChannel M)
    (X : Matrix A A ℂ) : (M X).trace = X.trace := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X ((E _)ᴴ)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

private lemma x8_ch_expand {M : Superop A B} (h : IsChannel M) (X : Matrix A A ℂ) (β γ : B) :
    M X β γ = ∑ i, ∑ j, X i j * choi M (i, β) (j, γ) := by
  obtain ⟨m, E, hK, hM⟩ := h
  simp only [choi, hM, krausApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply]
  simp [ite_and, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private lemma x8_choi_trB {M : Superop A B} (h : IsChannel M) (i j : A) :
    ∑ β, choi M (i, β) (j, β) = if i = j then 1 else 0 := by
  have := x8_ch_trace h (Matrix.single i j 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [choi]
  rw [this]
  by_cases hij : i = j
  · subst hij; simp [Matrix.single_apply]
  · simp [Matrix.single_apply, hij, Ne.symm hij]

private lemma x8_deph_single (i j : A) :
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

private lemma x8_mio_choi {M : Superop A B} (hO : Free .mio M) (i : A) (β γ : B)
    (hβγ : β ≠ γ) : choi M (i, β) (i, γ) = 0 := by
  have := congrFun (congrFun (hO.2 (Matrix.single i i 1)) β) γ
  rw [x8_deph_single, if_pos rfl] at this
  rw [choi, this]
  simp [dephasing, Matrix.diagonal_apply, hβγ]

private lemma x8_di_choi {M : Superop A B} (hO : Free .di M) (i j : A) (β : B)
    (hij : i ≠ j) : choi M (i, β) (j, β) = 0 := by
  have := congrFun (congrFun (hO.2 (Matrix.single i j 1)) β) β
  rw [x8_deph_single, if_neg hij, x8_ch_zero hO.1] at this
  simpa [dephasing, choi] using this

private lemma x8_dio_choi {M : Superop A B} (hO : Free .dio M) :
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

private lemma x8_free_of_choi {M : Superop A B} (h : IsChannel M)
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

private def x8ch {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ) :
    Superop (Fin a) (Fin b) :=
  krausApply (fun k => Matrix.of fun β i => W k (i, β))

private lemma x8ch_channel {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ)
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

private lemma x8ch_choi {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ)
    (p q : Fin a × Fin b) : choi (x8ch W) p q = ∑ k, W k p * star (W k q) := by
  simp [choi, x8ch, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and]

private lemma x8_trace_mul (X J : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (X * J).trace = ∑ p, ∑ q, X p q * J q p := by
  simp [Matrix.trace, Matrix.mul_apply]

private lemma x8ch_value {K : Type*} [Fintype K] (W : K → Fin a × Fin b → ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (X * choi (x8ch W)).trace = ∑ k, ∑ p, ∑ q, star (W k p) * X p q * W k q := by
  rw [x8_trace_mul]
  simp only [x8ch_choi, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => by ring

private def x8bg (S : Finset (Fin a)) (β0 : Fin b) (k : Fin a) : Fin a × Fin b → ℂ :=
  if k ∈ S then 0 else Pi.single (k, β0) 1

private def x8W (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ) :
    Fin 2 ⊕ Fin a → Fin a × Fin b → ℂ :=
  Sum.elim V (x8bg S β0)

private lemma x8bg_tp (S : Finset (Fin a)) (β0 : Fin b) (i j : Fin a) :
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

private lemma x8W_channel (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
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

private lemma x8W_choi_ne (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
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

private lemma x8W_value (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
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

private lemma x8_form1 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p1 : Fin a × Fin b) (x : ℂ) :
    ∑ p, ∑ q, star (Pi.single (M := fun _ => ℂ) p1 x p) * X p q * Pi.single (M := fun _ => ℂ) p1 x q =
      star x * X p1 p1 * x := by
  simp [Pi.single_apply, apply_ite (starRingEnd ℂ)]

private lemma x8_form2 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p1 p2 : Fin a × Fin b)
    (h : p1 ≠ p2) (x y : ℂ) :
    ∑ p, ∑ q, star ((Pi.single p1 x + Pi.single p2 y : Fin a × Fin b → ℂ) p) * X p q *
      (Pi.single p1 x + Pi.single p2 y : Fin a × Fin b → ℂ) q =
      star x * X p1 p1 * x + star x * X p1 p2 * y + star y * X p2 p1 * x +
        star y * X p2 p2 * y := by
  simp only [Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
  simp [Pi.single_apply, apply_ite (starRingEnd ℂ), Ne.symm h]
  ring

private lemma x8W_free (S : Finset (Fin a)) (β0 : Fin b) (V : Fin 2 → Fin a × Fin b → ℂ)
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

private lemma x8_rest (S : Finset (Fin a)) (Y : Fin a → ℂ) :
    (∑ k, if k ∈ S then 0 else Y k) = ∑ k, Y k - ∑ k ∈ S, Y k := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) Y]
  rw [Finset.sum_ite, add_comm]
  simp only [Finset.sum_const_zero, zero_add]
  congr 1
  · congr 1; ext k; simp

private lemma x8_v2_apply (i j k : Fin a) (β γ β' : Fin b) (x y : ℂ) :
    (Pi.single (i, β) x + Pi.single (j, γ) y : Fin a × Fin b → ℂ) (k, β') =
      (if k = i ∧ β' = β then x else 0) + (if k = j ∧ β' = γ then y else 0) := by
  simp [Pi.single_apply, Prod.ext_iff]

end family

section main

variable {a b : ℕ}

private abbrev x8Y (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (β0 : Fin b) (k : Fin a) : ℂ :=
  X (k, β0) (k, β0)

private lemma x8_D (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (O : Theory) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0) :
    ∑ k, x8Y X β0 k = 0 := by
  have h := hT _ (x8W_free ∅ β0 0 (by simp) (by simp) O (by simp) (by simp))
  rw [x8W_value] at h
  simpa using h

private lemma x8_C (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (O : Theory) (β0 : Fin b)
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

private lemma x8_A_aux (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (O : Theory) (β0 : Fin b)
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

private lemma x8_zero_of (z w : ℂ) (hw : w = star z) (h1 : z * 1 + (starRingEnd ℂ) 1 * w = 0)
    (h2 : z * Complex.I + (starRingEnd ℂ) Complex.I * w = 0) : z = 0 := by
  subst hw
  apply Complex.ext <;> simp [Complex.ext_iff] at h1 h2 ⊢ <;> linarith

private lemma x8_A (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (O : Theory) (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0) (i j : Fin a)
    (β γ : Fin b) (hij : i ≠ j) (hβγ : β ≠ γ) : X (i, β) (j, γ) = 0 :=
  x8_zero_of _ _ (hX.apply _ _).symm (x8_A_aux X O β0 hT i j β γ hij hβγ 1 (by simp))
    (x8_A_aux X O β0 hT i j β γ hij hβγ _ (by simp))

private lemma x8_A0_aux (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (β0 : Fin b)
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

private lemma x8_A0 (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free .di E → (X * choi E).trace = 0) (i : Fin a)
    (β γ : Fin b) (hβγ : β ≠ γ) : X (i, β) (i, γ) = 0 :=
  x8_zero_of _ _ (hX.apply _ _).symm (x8_A0_aux X β0 hT i β γ hβγ 1 (by simp))
    (x8_A0_aux X β0 hT i β γ hβγ _ (by simp))

private lemma x8_B_aux (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (β0 : Fin b)
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

private lemma x8_B (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (β0 : Fin b)
    (hT : ∀ E : Superop (Fin a) (Fin b), Free .mio E → (X * choi E).trace = 0) (i j : Fin a)
    (β δ : Fin b) (hij : i ≠ j) : X (i, β) (j, β) = X (i, δ) (j, δ) := by
  by_cases hβδ : β = δ
  · rw [hβδ]
  have := x8_zero_of _ (X (j, β) (i, β) - X (j, δ) (i, δ))
    (by rw [star_sub, hX.apply, hX.apply]) (x8_B_aux X β0 hT i j β δ hij hβδ 1 (by simp))
    (x8_B_aux X β0 hT i j β δ hij hβδ _ (by simp))
  exact sub_eq_zero.mp this

private lemma x8_tr_P {E : Superop (Fin a) (Fin b)} (h : IsChannel E) (P : Matrix (Fin a) (Fin a) ℂ) :
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

private lemma x8_back_mio {E : Superop (Fin a) (Fin b)} (hE : Free .mio E)
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

private lemma x8_back_di {E : Superop (Fin a) (Fin b)} (hE : Free .di E)
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

private lemma x8_back_dio {E : Superop (Fin a) (Fin b)} (hE : Free .dio E)
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

private lemma x8_herm_entry {X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} (hX : X.IsHermitian)
    (p q : Fin a × Fin b) : star (X q p) = X p q := hX.apply p q

private lemma x8_real_diag {X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} (hX : X.IsHermitian)
    (p : Fin a × Fin b) : star (X p p) = X p p := hX.apply p p

private lemma x8_mio_iff (ha : 0 < a) (hb : 0 < b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian) :
    TraceAnnihilator .mio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin a → Matrix (Fin b) (Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Matrix.single i i 1) (Q i) := by
  constructor
  · rintro ⟨-, hT⟩
    set β0 : Fin b := ⟨0, hb⟩
    refine ⟨Matrix.of fun i j => X (i, β0) (j, β0),
      fun i => Matrix.of fun β γ => X (i, β) (i, γ) - if β = γ then X (i, β0) (i, β0) else 0,
      ?_, ?_, ?_, ?_⟩
    · ext i j; simp [Matrix.conjTranspose_apply, x8_herm_entry hX]
    · simpa [Matrix.trace, x8Y] using x8_D X .mio β0 hT
    · intro i
      constructor
      · ext β γ
        simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_sub, x8_herm_entry hX]
        by_cases h : β = γ
        · subst h; simp [x8_real_diag hX]
        · simp [h, Ne.symm h]
      · ext β γ
        simp only [dephasing, Matrix.diagonal_apply, Matrix.of_apply, Matrix.zero_apply]
        split_ifs with h
        · subst h; rw [x8_C X .mio β0 hT i β]; simp
        · rfl
    · ext ⟨i, β⟩ ⟨j, γ⟩
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.single_apply, Matrix.one_apply, Matrix.of_apply]
      by_cases hij : i = j
      · subst hij
        rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk, Ne.symm hk]) (by simp)]
        by_cases h : β = γ
        · subst h; simp
        · simp [h]
      · rw [Finset.sum_eq_zero (fun k _ => by simp; intro h1 h2; exact absurd (h1.symm.trans h2) hij)]
        by_cases h : β = γ
        · subst h; simp; exact x8_B X hX β0 hT i j β β0 hij
        · simp [h]; exact x8_A X hX .mio β0 hT i j β γ hij h
  · rintro ⟨P, Q, -, hP, hQ, rfl⟩
    exact ⟨hX, fun E hE => x8_back_mio hE P Q hP (fun i => (hQ i).2)⟩

private lemma x8_di_iff (ha : 0 < a) (hb : 0 < b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian) :
    TraceAnnihilator .di X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin b → Matrix (Fin a) (Fin a) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Q i) (Matrix.single i i 1) := by
  constructor
  · rintro ⟨-, hT⟩
    set β0 : Fin b := ⟨0, hb⟩
    refine ⟨Matrix.diagonal fun i => X (i, β0) (i, β0),
      fun β => Matrix.of fun i j => X (i, β) (j, β) - if i = j then X (i, β0) (i, β0) else 0,
      ?_, ?_, ?_, ?_⟩
    · ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.conjTranspose_apply, x8_real_diag hX]
      · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
    · simpa [Matrix.trace, x8Y] using x8_D X .di β0 hT
    · intro β
      constructor
      · ext i j
        simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_sub, x8_herm_entry hX]
        by_cases h : i = j
        · subst h; simp [x8_real_diag hX]
        · simp [h, Ne.symm h]
      · ext i j
        simp only [dephasing, Matrix.diagonal_apply, Matrix.of_apply, Matrix.zero_apply]
        split_ifs with h
        · subst h; rw [x8_C X .di β0 hT i β]; simp
        · rfl
    · ext ⟨i, β⟩ ⟨j, γ⟩
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.single_apply, Matrix.one_apply, Matrix.of_apply, Matrix.diagonal_apply]
      by_cases h : β = γ
      · subst h
        rw [Finset.sum_eq_single β (fun k _ hk => by simp [hk]) (by simp)]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      · rw [Finset.sum_eq_zero (fun k _ => by simp; intro h1 h2; exact absurd (h1.symm.trans h2) h)]
        simp only [h, if_false, mul_zero, add_zero]
        by_cases hij : i = j
        · subst hij; exact x8_A0 X hX β0 hT i β γ h
        · exact x8_A X hX .di β0 hT i j β γ hij h
  · rintro ⟨P, Q, -, hP, hQ, rfl⟩
    exact ⟨hX, fun E hE => x8_back_di hE P Q hP (fun i => (hQ i).2)⟩

private lemma x8_dio_iff (ha : 0 < a) (hb : 0 < b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian) :
    TraceAnnihilator .dio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ,
      ∃ Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧ Q.IsHermitian ∧
        X = Matrix.kronecker P 1 + (dephaseInput Q - dephaseOutput Q) := by
  constructor
  · rintro ⟨-, hT⟩
    set β0 : Fin b := ⟨0, hb⟩
    refine ⟨Matrix.diagonal fun i => X (i, β0) (i, β0),
      Matrix.of fun p q => if p.1 = q.1 then (if p.2 = q.2 then 0 else X p q)
        else (if p.2 = q.2 then -X p q else 0),
      ?_, ?_, ?_, ?_⟩
    · ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.conjTranspose_apply, x8_real_diag hX]
      · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
    · simpa [Matrix.trace, x8Y] using x8_D X .dio β0 hT
    · ext ⟨i, β⟩ ⟨j, γ⟩
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases h1 : i = j <;> by_cases h2 : β = γ
      · subst h1 h2; simp
      · subst h1; simp [h2, Ne.symm h2, x8_herm_entry hX]
      · subst h2; simp [h1, Ne.symm h1, x8_herm_entry hX]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    · ext ⟨i, β⟩ ⟨j, γ⟩
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.of_apply, Matrix.diagonal_apply, dephaseInput, dephaseOutput]
      by_cases hij : i = j <;> by_cases h : β = γ
      · subst hij h; simp; exact (x8_C X .dio β0 hT i β)
      · simp [hij, h]
      · simp [hij, h]
      · simp [hij, h]; exact x8_A X hX .dio β0 hT i j β γ hij h
  · rintro ⟨P, Q, -, hP, -, rfl⟩
    exact ⟨hX, fun E hE => x8_back_dio hE P Q hP⟩

end main

theorem x8_main {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian) :
    (TraceAnnihilator .mio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin a → Matrix (Fin b) (Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Matrix.single i i 1) (Q i)) ∧
    (TraceAnnihilator .di X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin b → Matrix (Fin a) (Fin a) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Q i) (Matrix.single i i 1)) ∧
    (TraceAnnihilator .dio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ,
      ∃ Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧ Q.IsHermitian ∧
        X = Matrix.kronecker P 1 + (dephaseInput Q - dephaseOutput Q)) :=
  ⟨x8_mio_iff ha hb X hX, x8_di_iff ha hb X hX, x8_dio_iff ha hb X hX⟩

end QAlgorithms.Papers.Independent.Information100.P34

open QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian) :
    (TraceAnnihilator .mio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin a → Matrix (Fin b) (Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Matrix.single i i 1) (Q i)) ∧
    (TraceAnnihilator .di X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin b → Matrix (Fin a) (Fin a) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Q i) (Matrix.single i i 1)) ∧
    (TraceAnnihilator .dio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ,
      ∃ Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧ Q.IsHermitian ∧
        X = Matrix.kronecker P 1 + (dephaseInput Q - dephaseOutput Q)) :=
  x8_main ha hb X hX
