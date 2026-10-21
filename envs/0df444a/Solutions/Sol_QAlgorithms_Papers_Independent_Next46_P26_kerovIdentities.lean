-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.kerovIdentities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:36:51.479998+00:00
-- url     : https://prove2.me/submissions/eaed6c0c-f7a0-44ea-ba21-c54431d88fa3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P26
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section g61a_poly
open Polynomial


theorem g61a_top3 (s : Finset ℕ) (a : ℕ → ℝ) :
    (∀ m, s.card + 2 < m → ((∏ j ∈ s, (X - C (a j))) * X ^ 2).coeff m = 0) ∧
    ((∏ j ∈ s, (X - C (a j))) * X ^ 2).coeff (s.card + 2) = 1 ∧
    ((∏ j ∈ s, (X - C (a j))) * X ^ 2).coeff (s.card + 1) = -(∑ j ∈ s, a j) ∧
    ((∏ j ∈ s, (X - C (a j))) * X ^ 2).coeff s.card =
      ((∑ j ∈ s, a j) ^ 2 - ∑ j ∈ s, a j ^ 2) / 2 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, one_mul, Finset.card_empty, Finset.sum_empty, coeff_X_pow]
    refine ⟨fun m hm => ?_, by simp, by simp, by simp⟩
    rw [if_neg (by omega)]
  | insert b t hb ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have he : (∏ j ∈ insert b t, (X - C (a j))) * X ^ 2 =
        ((∏ j ∈ t, (X - C (a j))) * X ^ 2) * (X - C (a b)) := by
      rw [Finset.prod_insert hb]; ring
    rw [he, Finset.card_insert_of_notMem hb, Finset.sum_insert hb, Finset.sum_insert hb]
    set P := (∏ j ∈ t, (X - C (a j))) * X ^ 2
    refine ⟨fun m hm => ?_, ?_, ?_, ?_⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [coeff_mul_X_sub_C, h0 m' (by omega), h0 (m' + 1) (by omega)]; ring
    · rw [show t.card + 1 + 2 = (t.card + 2) + 1 by ring, coeff_mul_X_sub_C, h1,
        h0 _ (by omega)]; ring
    · rw [show t.card + 1 + 1 = (t.card + 1) + 1 by ring, coeff_mul_X_sub_C, h1, h2]; ring
    · rw [coeff_mul_X_sub_C, h2, h3]; ring

/-- Lagrange: p = Σ_k π_k ∏_{j≠k} (X - u_j). -/
theorem g61a_lagr (d : ℕ) (hd : 0 < d) (u v : ℕ → ℝ) (hinj : Set.InjOn u (Finset.range d)) :
    (∏ i ∈ Finset.Ico 1 d, (X - C (v i))) =
      ∑ k ∈ Finset.range d, C ((∏ i ∈ Finset.Ico 1 d, (u k - v i)) /
        ∏ i ∈ (Finset.range d).erase k, (u k - u i)) *
        ∏ j ∈ (Finset.range d).erase k, (X - C (u j)) := by
  have hdeg : (∏ i ∈ Finset.Ico 1 d, (X - C (v i))).degree < ((Finset.range d).card : WithBot ℕ) := by
    rw [degree_prod]
    simp only [degree_X_sub_C, Finset.sum_const, Nat.card_Ico, Finset.card_range,
      nsmul_eq_mul, mul_one]
    rcases d with _ | d
    · omega
    · simp only [Nat.add_sub_cancel]
      exact_mod_cast (by omega : d < d + 1)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_sub, eval_X, eval_C]
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← C_mul, div_eq_mul_inv,
    Finset.prod_inv_distrib]

theorem g61a_moments (d : ℕ) (hd : 0 < d) (u v : ℕ → ℝ) (hinj : Set.InjOn u (Finset.range d))
    (π : ℕ → ℝ) (hπ : ∀ k, π k = (∏ i ∈ Finset.Ico 1 d, (u k - v i)) /
        ∏ i ∈ (Finset.range d).erase k, (u k - u i)) :
    (∑ k ∈ Finset.range d, π k) = 1 ∧
    (∑ k ∈ Finset.range d, π k * u k) =
      (∑ k ∈ Finset.range d, u k) - ∑ i ∈ Finset.Ico 1 d, v i ∧
    (∑ k ∈ Finset.range d, π k * u k ^ 2) =
      ((∑ i ∈ Finset.Ico 1 d, v i) ^ 2 - ∑ i ∈ Finset.Ico 1 d, v i ^ 2) / 2
      - ((∑ k ∈ Finset.range d, u k) ^ 2 - ∑ k ∈ Finset.range d, u k ^ 2) / 2
      + (∑ k ∈ Finset.range d, u k) *
          ((∑ k ∈ Finset.range d, u k) - ∑ i ∈ Finset.Ico 1 d, v i) := by
  have hL := congrArg (fun p => p * X ^ 2) (g61a_lagr d hd u v hinj)
  simp only [Finset.sum_mul, mul_assoc] at hL
  simp_rw [← hπ] at hL
  have hc : ∀ m, ((∏ i ∈ Finset.Ico 1 d, (X - C (v i))) * X ^ 2).coeff m =
      ∑ k ∈ Finset.range d, π k * ((∏ j ∈ (Finset.range d).erase k, (X - C (u j))) * X ^ 2).coeff m := by
    intro m
    have := congrArg (fun p => Polynomial.coeff p m) hL
    simp only [finsetSum_coeff, coeff_C_mul] at this
    exact this
  have hcardI : (Finset.Ico 1 d).card = d - 1 := by simp
  have hcardE : ∀ k ∈ Finset.range d, ((Finset.range d).erase k).card = d - 1 := by
    intro k hk; rw [Finset.card_erase_of_mem hk, Finset.card_range]
  obtain ⟨-, a1, a2, a3⟩ := g61a_top3 (Finset.Ico 1 d) v
  rw [hcardI] at a1 a2 a3
  have e1 := hc (d - 1 + 2); have e2 := hc (d - 1 + 1); have e3 := hc (d - 1)
  rw [a1] at e1; rw [a2] at e2; rw [a3] at e3
  have hs : ∀ k ∈ Finset.range d, ∑ j ∈ (Finset.range d).erase k, u j =
      (∑ j ∈ Finset.range d, u j) - u k := fun k hk => Finset.sum_erase_eq_sub hk
  have hs2 : ∀ k ∈ Finset.range d, ∑ j ∈ (Finset.range d).erase k, u j ^ 2 =
      (∑ j ∈ Finset.range d, u j ^ 2) - u k ^ 2 := fun k hk => Finset.sum_erase_eq_sub hk
  set B1 := ∑ j ∈ Finset.range d, u j
  set B2 := ∑ j ∈ Finset.range d, u j ^ 2
  set A1 := ∑ j ∈ Finset.Ico 1 d, v j
  set A2 := ∑ j ∈ Finset.Ico 1 d, v j ^ 2
  have E1 : ∑ k ∈ Finset.range d, π k = 1 := by
    rw [e1]; refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨-, b1, -, -⟩ := g61a_top3 ((Finset.range d).erase k) u
    rw [hcardE k hk] at b1; rw [b1, mul_one]
  have E2 : ∑ k ∈ Finset.range d, π k * u k = B1 - A1 := by
    have : -A1 = ∑ k ∈ Finset.range d, π k * u k - B1 * ∑ k ∈ Finset.range d, π k := by
      rw [e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      obtain ⟨-, -, b2, -⟩ := g61a_top3 ((Finset.range d).erase k) u
      rw [hcardE k hk, hs k hk] at b2; rw [b2]; ring
    rw [E1] at this; linarith
  refine ⟨E1, E2, ?_⟩
  have : (A1 ^ 2 - A2) / 2 =
      ∑ k ∈ Finset.range d, π k * u k ^ 2 - B1 * ∑ k ∈ Finset.range d, π k * u k
        + (B1 ^ 2 - B2) / 2 * ∑ k ∈ Finset.range d, π k := by
    rw [e3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨-, -, -, b3⟩ := g61a_top3 ((Finset.range d).erase k) u
    rw [hcardE k hk, hs k hk, hs2 k hk] at b3; rw [b3]; ring
  rw [E1, E2] at this; linarith

end g61a_poly

theorem g61a_S (u v : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range d, ∑ j ∈ Finset.Ico i d, (v i - u i) * (u j - v (j + 1))) =
      -(((∑ i ∈ Finset.Ico 1 d, v i) ^ 2 - ∑ i ∈ Finset.Ico 1 d, v i ^ 2) / 2
      - ((∑ k ∈ Finset.range d, u k) ^ 2 - ∑ k ∈ Finset.range d, u k ^ 2) / 2
      + (∑ k ∈ Finset.range d, u k) *
          ((∑ k ∈ Finset.range d, u k) - ∑ i ∈ Finset.Ico 1 d, v i))
      + (v 0 + v d) * ((∑ k ∈ Finset.range d, u k) - ∑ i ∈ Finset.Ico 1 d, v i) - v 0 * v d := by
  induction d, hd using Nat.le_induction with
  | base => simp; ring
  | succ d hd ih =>
    have hin : ∀ i ∈ Finset.range d, ∑ j ∈ Finset.Ico i (d + 1), (v i - u i) * (u j - v (j + 1)) =
        ∑ j ∈ Finset.Ico i d, (v i - u i) * (u j - v (j + 1)) + (v i - u i) * (u d - v (d + 1)) :=
      fun i hi => Finset.sum_Ico_succ_top (by simp at hi; omega) _
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hin, Finset.sum_add_distrib, ih,
      ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_Ico_succ_top hd, Finset.sum_Ico_succ_top hd, Nat.Ico_succ_singleton,
      Finset.sum_singleton]
    have hv : ∑ x ∈ Finset.range d, v x = v 0 + ∑ x ∈ Finset.Ico 1 d, v x := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < d) v]
    rw [hv]
    ring

theorem g61a_pi_eq (d : ℕ) (u v : ℕ → ℝ) (k : ℕ) (hk : k < d) :
    ((∏ i ∈ Finset.range k, (v (i + 1) - u k) / (u i - u k)) *
      ∏ i ∈ Finset.Ico (k + 1) d, (u k - v i) / (u k - u i)) =
    (∏ i ∈ Finset.Ico 1 d, (u k - v i)) / ∏ i ∈ (Finset.range d).erase k, (u k - u i) := by
  have h1 : ∀ i ∈ Finset.range k, (v (i + 1) - u k) / (u i - u k) =
      (u k - v (i + 1)) / (u k - u i) := fun i _ => by rw [← neg_div_neg_eq]; ring_nf
  rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hE : (Finset.range d).erase k = Finset.range k ∪ Finset.Ico (k + 1) d := by
    ext i; simp; omega
  have hD : Disjoint (Finset.range k) (Finset.Ico (k + 1) d) := by
    rw [Finset.disjoint_left]; intro i; simp; omega
  have hN : ∏ i ∈ Finset.Ico 1 d, (u k - v i) =
      (∏ i ∈ Finset.range k, (u k - v (i + 1))) * ∏ i ∈ Finset.Ico (k + 1) d, (u k - v i) := by
    rw [← Finset.prod_Ico_consecutive _ (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ d)]
    congr 1
    rw [Finset.prod_Ico_eq_prod_range]; simp [add_comm]
  rw [hE, Finset.prod_union hD, hN]
  ring

theorem solution (d : ℕ) (hd : 0 < d) (q : ℝ) (hq : 0 < q) (hqone : q ≠ 1)
    (X Y : ℕ → ℝ) (hinterlace : ∀ i < d, Y i < X i ∧ X i < Y (i + 1)) :
    ((∑ k ∈ Finset.range d, kerovPi d q X Y k) = 1) ∧
    ((∑ k ∈ Finset.range d,
      (q ^ Y 0 - q ^ X k) / (q ^ Y 0 - kerovZ d q X Y) * kerovPi d q X Y k) = 1) ∧
    ((∑ k ∈ Finset.range d,
      (q ^ X k - q ^ Y d) / (kerovZ d q X Y - q ^ Y d) * kerovPi d q X Y k) = 1) ∧
    ((∑ k ∈ Finset.range d,
      ((q ^ Y 0 - q ^ X k) * (q ^ X k - q ^ Y d)) / kerovS d q X Y *
        kerovPi d q X Y k) = 1) := by
  set u : ℕ → ℝ := fun k => q ^ X k with hu
  set v : ℕ → ℝ := fun k => q ^ Y k with hv
  set π : ℕ → ℝ := fun k => (∏ i ∈ Finset.Ico 1 d, (u k - v i)) /
        ∏ i ∈ (Finset.range d).erase k, (u k - u i) with hπdef
  have hpi : ∀ k ∈ Finset.range d, kerovPi d q X Y k = π k := fun k hk => by
    rw [Finset.mem_range] at hk
    exact g61a_pi_eq d u v k hk
  -- strict monotonicity of X
  have hXmono : ∀ i j, i < j → j < d → X i < X j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have h1 := (hinterlace j (by omega)).2
      have h2 := (hinterlace (j + 1) hj).1
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · linarith [ih h (by omega)]
      · subst h; linarith
  have hlog : Real.log q ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq hqone
  have hinj : Set.InjOn u (Finset.range d) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have := congrArg Real.log hij
    simp only [hu, Real.log_rpow hq] at this
    have hX : X i = X j := mul_right_cancel₀ hlog this
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · linarith [hXmono i j h hj]
    · linarith [hXmono j i h hi]
  obtain ⟨E1, E2, E3⟩ := g61a_moments d hd u v hinj π (fun k => rfl)
  have hS := g61a_S u v d hd
  -- sign structure
  have hsign : (∀ a b : ℝ, a < b → q ^ a < q ^ b) ∨ (∀ a b : ℝ, a < b → q ^ b < q ^ a) := by
    rcases lt_or_gt_of_ne hqone with h | h
    · right; intro a b hab; exact Real.rpow_lt_rpow_of_exponent_gt hq h hab
    · left; intro a b hab; exact Real.rpow_lt_rpow_of_exponent_lt h hab
  have hZ : kerovZ d q X Y = ∑ k ∈ Finset.range d, u k - ∑ i ∈ Finset.Ico 1 d, v i := rfl
  have hSdef : kerovS d q X Y =
      ∑ i ∈ Finset.range d, ∑ j ∈ Finset.Ico i d, (v i - u i) * (u j - v (j + 1)) := rfl
  have hv0 : ∑ x ∈ Finset.range d, v x = v 0 + ∑ x ∈ Finset.Ico 1 d, v x := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hd v]
  have hvd : ∑ x ∈ Finset.Ico 1 d, v x + v d = ∑ x ∈ Finset.range d, v (x + 1) := by
    rw [← Finset.sum_Ico_succ_top (by omega : 1 ≤ d), Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have hZ0 : kerovZ d q X Y - v 0 = ∑ k ∈ Finset.range d, (u k - v k) := by
    rw [hZ, Finset.sum_sub_distrib, hv0]; ring
  have hZd : kerovZ d q X Y - v d = ∑ k ∈ Finset.range d, (u k - v (k + 1)) := by
    rw [hZ, Finset.sum_sub_distrib, ← hvd]; ring
  have hne : (Finset.range d).Nonempty := ⟨0, by simp; omega⟩
  have hpos : (0 < kerovZ d q X Y - v 0 ∧ kerovZ d q X Y - v d < 0) ∨
      (kerovZ d q X Y - v 0 < 0 ∧ 0 < kerovZ d q X Y - v d) := by
    rcases hsign with h | h
    · left; constructor
      · rw [hZ0]; exact Finset.sum_pos (fun k hk => by
          simp at hk; have := h _ _ (hinterlace k hk).1; simp only [hu, hv]; linarith) hne
      · rw [hZd]; exact Finset.sum_neg (fun k hk => by
          simp at hk; have := h _ _ (hinterlace k hk).2; simp only [hu, hv]; linarith) hne
    · right; constructor
      · rw [hZ0]; exact Finset.sum_neg (fun k hk => by
          simp at hk; have := h _ _ (hinterlace k hk).1; simp only [hu, hv]; linarith) hne
      · rw [hZd]; exact Finset.sum_pos (fun k hk => by
          simp at hk; have := h _ _ (hinterlace k hk).2; simp only [hu, hv]; linarith) hne
  have hSpos : 0 < kerovS d q X Y := by
    rw [hSdef]
    refine Finset.sum_pos (fun i hi => Finset.sum_pos (fun j hj => ?_) ⟨i, by simp at hi ⊢; omega⟩) hne
    simp at hi hj
    have hi' := hinterlace i hi
    have hj' := hinterlace j hj.2
    rcases hsign with h | h
    · have a := h _ _ hi'.1; have b := h _ _ hj'.2
      exact mul_pos_of_neg_of_neg (by simp only [hu, hv]; linarith) (by simp only [hu, hv]; linarith)
    · have a := h _ _ hi'.1; have b := h _ _ hj'.2
      exact mul_pos (by simp only [hu, hv]; linarith) (by simp only [hu, hv]; linarith)
  have h0ne : v 0 - kerovZ d q X Y ≠ 0 := by rcases hpos with h | h <;> intro e <;> linarith [h.1]
  have hdne : kerovZ d q X Y - v d ≠ 0 := by rcases hpos with h | h <;> intro e <;> linarith [h.2]
  have hSne : kerovS d q X Y ≠ 0 := hSpos.ne'
  rw [Finset.sum_congr rfl hpi]
  refine ⟨E1, ?_, ?_, ?_⟩
  · have : ∑ k ∈ Finset.range d, (v 0 - u k) / (v 0 - kerovZ d q X Y) * kerovPi d q X Y k =
        (v 0 * ∑ k ∈ Finset.range d, π k - ∑ k ∈ Finset.range d, π k * u k) /
          (v 0 - kerovZ d q X Y) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun k hk => by rw [hpi k hk]; ring
    rw [this, E1, E2, ← hZ, mul_one, div_self h0ne]
  · have : ∑ k ∈ Finset.range d, (u k - v d) / (kerovZ d q X Y - v d) * kerovPi d q X Y k =
        (∑ k ∈ Finset.range d, π k * u k - v d * ∑ k ∈ Finset.range d, π k) /
          (kerovZ d q X Y - v d) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun k hk => by rw [hpi k hk]; ring
    rw [this, E1, E2, ← hZ, mul_one, div_self hdne]
  · have : ∑ k ∈ Finset.range d, ((v 0 - u k) * (u k - v d)) / kerovS d q X Y * kerovPi d q X Y k =
        (-(∑ k ∈ Finset.range d, π k * u k ^ 2) + (v 0 + v d) * ∑ k ∈ Finset.range d, π k * u k
          - v 0 * v d * ∑ k ∈ Finset.range d, π k) / kerovS d q X Y := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun k hk => by rw [hpi k hk]; ring
    rw [this, div_eq_one_iff_eq hSne, hSdef, hS, E1, E2, E3]; ring

end
