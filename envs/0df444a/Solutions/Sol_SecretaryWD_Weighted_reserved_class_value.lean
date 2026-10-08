-- Prove2me | solution 1 for SecretaryWD.Weighted.reserved_class_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:44:50.982644+00:00
-- url     : https://prove2.me/submissions/c8ea0857-bd6f-4354-b5c6-562b5d3bb48f

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm



namespace SecretaryWD.Weighted

open Classical

lemma rs_better_irrefl {n : ℕ} (v : Fin n → ℝ) (e : Fin n) : ¬ better v e e := by
  unfold better; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma rs_better_trans {n : ℕ} (v : Fin n → ℝ) (a b c : Fin n) :
    better v a b → better v b c → better v a c := by
  unfold better
  rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

lemma rs_better_total {n : ℕ} (v : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    better v a b ∨ better v b a := by
  unfold better
  rcases lt_trichotomy (v a) (v b) with h | h | h
  · right; left; exact h
  · rcases lt_trichotomy a.val b.val with h' | h' | h'
    · left; right; exact ⟨h, h'⟩
    · exact absurd (Fin.ext h') hab
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; exact h

lemma rs_rank_injOn {n : ℕ} (v : Fin n → ℝ) (T : Finset (Fin n)) :
    Set.InjOn (fun e => (T.filter (fun f => better v f e)).card) (T : Set (Fin n)) := by
  intro a ha b hb hab
  by_contra hne
  have key : ∀ x y : Fin n, x ∈ T → better v x y →
      (T.filter (fun f => better v f x)).card < (T.filter (fun f => better v f y)).card := by
    intro x y hx hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨x, by simp [hx, hxy], by simp [rs_better_irrefl]⟩
    · intro f hf
      simp only [Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, rs_better_trans v _ _ _ hf.2 hxy⟩
  rcases rs_better_total v a b hne with h | h
  · have := key a b ha h; simp only at hab; omega
  · have := key b a hb h; simp only at hab; omega

lemma rs_top_card_le {n : ℕ} (v : Fin n → ℝ) (T : Finset (Fin n)) (K : ℕ) :
    (T.filter (fun e => (T.filter (fun f => better v f e)).card < K)).card ≤ K := by
  have h := Finset.card_le_card_of_injOn
    (fun e => (T.filter (fun f => better v f e)).card)
    (s := T.filter (fun e => (T.filter (fun f => better v f e)).card < K))
    (t := Finset.range K)
    (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; simpa using he.2)
    ((rs_rank_injOn v T).mono (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; exact he.1))
  simpa using h

lemma rs_class_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : valueClass x ≤ valueClass y := by
  unfold valueClass
  rw [if_pos hx, if_pos (lt_of_lt_of_le hx hxy)]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := Real.log_le_log hx hxy
  have : Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := div_le_div_of_nonneg_right this h2.le
  have := Int.floor_mono this
  omega

theorem rs_core {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) :
    reservationStart v π τ K i ≤ optimalStart (K := K) v i := by
  set C : Finset (Fin n) := Finset.univ.filter (fun e => 0 < v e ∧ i < valueClass (v e)) with hC
  have hup : ∀ e f, e ∈ C → better v f e → f ∈ C := by
    intro e f he hfe
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    have hle : v e ≤ v f := by
      rcases hfe with h | ⟨h, _⟩
      · exact h.le
      · exact h.ge
    exact ⟨lt_of_lt_of_le he.1 hle, lt_of_lt_of_le he.2 (rs_class_mono he.1 hle)⟩
  -- rank equals rank within C
  have hrank : ∀ e ∈ C, valueRank v e = (C.filter (fun f => better v f e)).card := by
    intro e he
    unfold valueRank
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨hup e f he h, h⟩
    · intro h; exact h.2
  have hB : optimalStart (K := K) v i = (C.filter (fun e => (C.filter (fun f => better v f e)).card < K)).card := by
    unfold optimalStart
    congr 1
    ext e
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h2, h3⟩, ?_⟩
      rw [← hrank e (by simp [hC, h2, h3])]; exact h1
    · rintro ⟨⟨h2, h3⟩, h1⟩
      refine ⟨?_, h2, h3⟩
      rw [hrank e (by simp [hC, h2, h3])]; exact h1
  -- card of B = min K |C|
  have himg : C.image (fun e => (C.filter (fun f => better v f e)).card) = Finset.range C.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      simp only [Finset.mem_range]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨e, he, by simp [rs_better_irrefl]⟩
    · rw [Finset.card_image_of_injOn (rs_rank_injOn v C)]; simp
  have hBc : (C.filter (fun e => (C.filter (fun f => better v f e)).card < K)).card = min C.card K := by
    have h1 := Finset.card_image_of_injOn
      (s := C.filter (fun e => (C.filter (fun f => better v f e)).card < K))
      ((rs_rank_injOn v C).mono (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; exact he.1))
    have hfi : (C.filter (fun e => (C.filter (fun f => better v f e)).card < K)).image
        (fun e => (C.filter (fun f => better v f e)).card) =
        (C.image (fun e => (C.filter (fun f => better v f e)).card)).filter (fun x => x < K) := by
      ext x; simp only [Finset.mem_image, Finset.mem_filter]; constructor
      · rintro ⟨e, ⟨he, hk⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hk⟩
      · rintro ⟨⟨e, he, rfl⟩, hk⟩; exact ⟨e, ⟨he, hk⟩, rfl⟩
    rw [← h1, hfi, himg]
    have : (Finset.range C.card).filter (fun x => x < K) = Finset.range (min C.card K) := by
      ext x; simp [Finset.mem_filter, Finset.mem_range]
    rw [this, Finset.card_range]
  rw [hB, hBc]
  set T : Finset (Fin n) := Finset.univ.filter (fun e => inSample π τ e) with hT
  have hA : reservationStart v π τ K i ≤ (T.filter (fun e => (T.filter (fun f => better v f e)).card < K)).card := by
    unfold reservationStart
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    have he' := he.2.1
    unfold sampleTop at he'
    refine ⟨he'.1, ?_⟩
    have := he'.2
    convert this using 2
    ext f; simp [Finset.mem_filter]
  have hA2 : reservationStart v π τ K i ≤ C.card := by
    unfold reservationStart
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hC]
    exact he.2.2
  have := rs_top_card_le v T K
  omega


lemma ac_two_trans {n : ℕ} (p q p' q' : Fin n) (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ σ : Equiv.Perm (Fin n), σ p' = p ∧ σ q' = q := by
  set r := Equiv.swap p' p q' with hr
  have hrp : r ≠ p := by
    intro h
    have : Equiv.swap p' p q' = Equiv.swap p' p p' := by rw [← hr, h]; simp
    exact hpq' ((Equiv.swap p' p).injective this).symm
  refine ⟨Equiv.swap r q * Equiv.swap p' p, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hrp.symm hpq
  · simp only [Equiv.Perm.mul_apply]
    rw [← hr]; exact Equiv.swap_apply_left r q

noncomputable def acC {n : ℕ} (a b p q : Fin n) : ℕ :=
  (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π.symm a = p ∧ π.symm b = q)).card

lemma acC_eq {n : ℕ} (a b p q p' q' : Fin n) (hpq : p ≠ q) (hpq' : p' ≠ q') :
    acC a b p q = acC a b p' q' := by
  obtain ⟨σ, h1, h2⟩ := ac_two_trans p q p' q' hpq hpq'
  unfold acC
  apply Finset.card_nbij' (fun π => π * σ) (fun π => π * σ⁻¹)
  · intro π hπ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hπ.1, hπ.2]
    constructor
    · rw [Equiv.symm_apply_eq]; exact h1.symm
    · rw [Equiv.symm_apply_eq]; exact h2.symm
  · intro π hπ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hπ.1, hπ.2, Equiv.Perm.inv_def,
      Equiv.symm_symm]
    exact ⟨h1, h2⟩
  · intro π _; simp
  · intro π _; simp

lemma acC_diag {n : ℕ} (a b p : Fin n) (hab : a ≠ b) : acC a b p p = 0 := by
  unfold acC
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro π - ⟨h1, h2⟩
  exact hab (π.symm.injective (h1.trans h2.symm))

lemma ac_card_split {n : ℕ} (a b : Fin n) (S : Finset (Fin n × Fin n)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => (π.symm a, π.symm b) ∈ S)).card =
      ∑ pq ∈ S, acC a b pq.1 pq.2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm (Fin n) => (π.symm a, π.symm b))
    (t := S)]
  · apply Finset.sum_congr rfl
    intro pq hpq
    unfold acC
    congr 1
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; refine ⟨?_, h⟩; rw [h.1, h.2]; exact hpq
  · intro π hπ; simpa using hπ

lemma ac_c0 {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    (n * (n - 1)) * acC a b ⟨0, by omega⟩ ⟨1, by omega⟩ = Nat.factorial n := by
  have htot := ac_card_split a b (Finset.univ ×ˢ Finset.univ)
  have hl : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (π.symm a, π.symm b) ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)))).card
      = Nat.factorial n := by simp [Fintype.card_perm]
  rw [hl] at htot
  rw [htot]
  have : ∀ pq ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)),
      acC a b pq.1 pq.2 = if pq.1 ≠ pq.2 then acC a b ⟨0, by omega⟩ ⟨1, by omega⟩ else 0 := by
    intro pq _
    split_ifs with h
    · exact acC_eq a b _ _ _ _ h (by simp [Fin.ext_iff])
    · push_neg at h; rw [h]; exact acC_diag a b _ hab
  rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  congr 1
  -- card of off-diagonal
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))) (fun pq => pq.1 ≠ pq.2)
  have h2 : ((Finset.univ ×ˢ Finset.univ).filter (fun pq : Fin n × Fin n => ¬ pq.1 ≠ pq.2)).card = n := by
    have : ((Finset.univ ×ˢ Finset.univ).filter (fun pq : Fin n × Fin n => ¬ pq.1 ≠ pq.2)) =
        (Finset.univ : Finset (Fin n)).diag := by
      ext ⟨x, y⟩; simp [Finset.mem_diag]
    rw [this, Finset.diag_card]; simp
  rw [h2, Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  have : n * n = n * (n - 1) + n := by
    rcases n with _ | m
    · omega
    · rw [Nat.add_sub_cancel]; ring
  omega

lemma ac_count_tau {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) (τ : ℕ) (hτ : τ ≤ n) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (π.symm a).val < τ ∧ τ ≤ (π.symm b).val)).card : ℝ) * (n * (n - 1)) =
      (τ * (n - τ) : ℝ) * Nat.factorial n := by
  set S := ((Finset.univ : Finset (Fin n)).filter (fun p => p.val < τ)) ×ˢ
    ((Finset.univ : Finset (Fin n)).filter (fun q => τ ≤ q.val)) with hS
  have hsplit := ac_card_split a b S
  have hfe : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      (π.symm a).val < τ ∧ τ ≤ (π.symm b).val)) =
      Finset.univ.filter (fun π : Equiv.Perm (Fin n) => (π.symm a, π.symm b) ∈ S) := by
    ext π; simp [hS]
  rw [hfe, hsplit]
  have : ∀ pq ∈ S, acC a b pq.1 pq.2 = acC a b ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    intro pq hpq
    simp only [hS, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hpq
    exact acC_eq a b _ _ _ _ (by intro h; rw [h] at hpq; omega) (by simp [Fin.ext_iff])
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  have hc := ac_c0 hn a b hab
  have hcardS : S.card = τ * (n - τ) := by
    rw [hS, Finset.card_product]
    have e1 : ((Finset.univ : Finset (Fin n)).filter (fun p => p.val < τ)).card = τ := by
      rw [Fin.card_filter_val_lt]; omega
    have e2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun p => p.val < τ)
    have e3 : ((Finset.univ : Finset (Fin n)).filter (fun q => τ ≤ q.val)) =
        (Finset.univ : Finset (Fin n)).filter (fun q => ¬ q.val < τ) := by
      ext q; simp
    rw [e3, e1]; rw [e1, Finset.card_univ, Fintype.card_fin] at e2; congr 1; omega
  rw [hcardS]
  have hc' : ((n : ℝ) * ((n : ℝ) - 1)) * (acC a b ⟨0, by omega⟩ ⟨1, by omega⟩ : ℝ) =
      (Nat.factorial n : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hc
    simp only [Nat.cast_mul] at this
    rw [Nat.cast_sub (by omega)] at this; simpa using this
  push_cast [Nat.cast_sub hτ]
  rw [← hc']; ring

lemma ac_binom (m : ℕ) :
    ∑ τ ∈ Finset.range (m + 2 + 1), ((m + 2).choose τ) * (τ * (m + 2 - τ)) =
      (m + 2) * (m + 1) * 2 ^ m := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_self, mul_zero, add_zero, zero_mul]
  have : ∀ j ∈ Finset.range (m + 1), ((m + 2).choose (j + 1)) * ((j + 1) * (m + 2 - (j + 1))) =
      (m + 2) * (m + 1) * m.choose j := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have e1 : (m + 2).choose (j + 1) * (j + 1) = (m + 2) * (m + 1).choose j := by
      have := Nat.add_one_mul_choose_eq (m + 1) j
      linarith
    have e2 : (m + 1).choose j * (m + 1 - j) = (m + 1) * m.choose j := by
      have := Nat.choose_mul_succ_eq m j
      have h3 : (m + 1).choose j * (m + 1 - j) = m.choose j * (m + 1) := by
        rw [← this]
      linarith
    have e3 : m + 2 - (j + 1) = m + 1 - j := by omega
    rw [e3, ← mul_assoc, e1, mul_assoc, e2]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Nat.sum_range_choose]

lemma ac_pair_prob {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    orderAverage (fun π => binomialAverage n (fun τ =>
      if (π.symm a).val < τ ∧ τ ≤ (π.symm b).val then (1 : ℝ) else 0)) = 1 / 4 := by
  unfold orderAverage binomialAverage
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hτ : ∀ τ ∈ Finset.range (n + 1),
      (n.choose τ : ℝ) / 2 ^ n * ∑ π : Equiv.Perm (Fin n),
        (if (π.symm a).val < τ ∧ τ ≤ (π.symm b).val then (1 : ℝ) else 0) =
      (n.choose τ : ℝ) / 2 ^ n * ((τ * (n - τ) : ℝ) * Nat.factorial n / (n * (n - 1))) := by
    intro τ hτ
    simp only [Finset.mem_range] at hτ
    rw [Finset.sum_boole]
    have := ac_count_tau hn a b hab τ (by omega)
    have hne : (n : ℝ) * (n - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    congr 1
    rw [eq_div_iff hne, this]
  rw [Finset.sum_congr rfl hτ]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hb := ac_binom m
  have hb' : ∑ τ ∈ Finset.range (m + 2 + 1), (((m + 2).choose τ : ℝ) * (τ * ((m + 2 : ℕ) - τ : ℝ))) =
      ((m : ℝ) + 2) * (m + 1) * 2 ^ m := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hb
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add] at this
    calc _ = ∑ x ∈ Finset.range (m + 2 + 1), ((m + 2).choose x : ℝ) * ((x : ℝ) * ((m + 2 - x : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          simp only [Finset.mem_range] at hτ
          rw [Nat.cast_sub (by omega)]; (try push_cast); (try ring)
      _ = _ := by rw [this]; (try push_cast); (try ring)
  have hf : (Nat.factorial (m + 2) : ℝ) ≠ 0 := by positivity
  have hrw : ∀ τ ∈ Finset.range (m + 2 + 1),
      ((m + 2).choose τ : ℝ) / 2 ^ (m + 2) * ((τ * ((m + 2 : ℕ) - τ) : ℝ) *
        Nat.factorial (m + 2) / ((m + 2 : ℕ) * ((m + 2 : ℕ) - 1))) =
      (Nat.factorial (m + 2) / (2 ^ (m + 2) * ((m + 2 : ℕ) * ((m + 2 : ℕ) - 1)))) *
        (((m + 2).choose τ : ℝ) * (τ * ((m + 2 : ℕ) - τ : ℝ))) := by
    intro τ _; field_simp
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, hb']
  push_cast
  have h1 : (1 : ℝ) + m ≠ 0 := by positivity
  have h2 : (m : ℝ) + 1 ≠ 0 := by positivity
  have h3 : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  have hinv : (1 + (m : ℝ)) * (1 + (m : ℝ))⁻¹ = 1 := mul_inv_cancel₀ h1
  linear_combination (2 ^ m * 4 : ℝ) * hinv


/-! ## generic rank -/

lemma gen_rank_injOn {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (irr : ∀ x, ¬ R x x) (tr : ∀ x y z, R x y → R y z → R x z)
    (tot : ∀ x y, x ≠ y → R x y ∨ R y x) (T : Finset α) :
    Set.InjOn (fun e => (T.filter (fun f => R f e)).card) (T : Set α) := by
  intro a ha b hb hab
  by_contra hne
  have key : ∀ x y : α, x ∈ T → R x y →
      (T.filter (fun f => R f x)).card < (T.filter (fun f => R f y)).card := by
    intro x y hx hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨x, by simp [hx, hxy], by simp [irr]⟩
    · intro f hf
      simp only [Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, tr _ _ _ hf.2 hxy⟩
  rcases tot a b hne with h | h
  · have := key a b ha h; simp only at hab; omega
  · have := key b a hb h; simp only at hab; omega

lemma gen_rank_count {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (irr : ∀ x, ¬ R x x) (tr : ∀ x y z, R x y → R y z → R x z)
    (tot : ∀ x y, x ≠ y → R x y ∨ R y x) (C : Finset α) (K : ℕ) :
    (C.filter (fun e => (C.filter (fun f => R f e)).card < K)).card = min C.card K := by
  have hinj := gen_rank_injOn R irr tr tot C
  have himg : C.image (fun e => (C.filter (fun f => R f e)).card) = Finset.range C.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      simp only [Finset.mem_range]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨e, he, by simp [irr]⟩
    · rw [Finset.card_image_of_injOn hinj]; simp
  have h1 := Finset.card_image_of_injOn
    (s := C.filter (fun e => (C.filter (fun f => R f e)).card < K))
    (hinj.mono (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; exact he.1))
  have hfi : (C.filter (fun e => (C.filter (fun f => R f e)).card < K)).image
      (fun e => (C.filter (fun f => R f e)).card) =
      (C.image (fun e => (C.filter (fun f => R f e)).card)).filter (fun x => x < K) := by
    ext x; simp only [Finset.mem_image, Finset.mem_filter]; constructor
    · rintro ⟨e, ⟨he, hk⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hk⟩
    · rintro ⟨⟨e, he, rfl⟩, hk⟩; exact ⟨e, ⟨he, hk⟩, rfl⟩
  rw [← h1, hfi, himg]
  have : (Finset.range C.card).filter (fun x => x < K) = Finset.range (min C.card K) := by
    ext x; simp [Finset.mem_filter, Finset.mem_range]
  rw [this, Finset.card_range]

/-! ## deterministic part -/

lemma ac_sampleTop_card {n : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ K : ℕ) :
    (Finset.univ.filter (fun e => sampleTop v π τ K e)).card ≤ K := by
  set T : Finset (Fin n) := Finset.univ.filter (fun e => inSample π τ e) with hT
  refine le_trans (Finset.card_le_card ?_) (rs_top_card_le v T K)
  intro e he
  rw [Finset.mem_filter] at he
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
  have he' := he.2
  unfold sampleTop at he'
  refine ⟨he'.1, ?_⟩
  have := he'.2
  convert this using 2
  ext f; simp [Finset.mem_filter]

lemma ac_br_le_K {n : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ K : ℕ) (i : ℤ) :
    reservationStart v π τ K i + reservedCount v π τ K i ≤ K := by
  refine le_trans ?_ (ac_sampleTop_card v π τ K)
  unfold reservationStart reservedCount
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rcases he with h | h
    · exact h.1
    · exact h.1
  · rw [Finset.disjoint_filter]
    intro e _ h1 h2
    unfold inClass at h2
    omega

lemma ac_br_le_b {n : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ K : ℕ) (i j : ℤ)
    (hij : i < j) :
    reservationStart v π τ K j + reservedCount v π τ K j ≤ reservationStart v π τ K i := by
  unfold reservationStart reservedCount
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    unfold inClass at he
    rcases he with h | h
    · exact ⟨h.1, h.2.1, by omega⟩
    · exact ⟨h.1, h.2.1, by omega⟩
  · rw [Finset.disjoint_filter]
    intro e _ h1 h2
    unfold inClass at h2
    omega

lemma ac_reservedGood_some {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ)
    (e : Fin n) (k : Fin K) (h : reservedGood (K := K) v π τ e = some k) :
    0 < v e ∧ earlierInClass v π τ e < reservedCount v π τ K (valueClass (v e)) ∧
      k.val = reservationStart v π τ K (valueClass (v e)) + earlierInClass v π τ e := by
  unfold reservedGood at h
  simp only at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨hc.2.1, hc.2.2.1, rfl⟩

lemma ac_class_of_good {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ)
    (e : Fin n) (k : Fin K) (h : reservedGood (K := K) v π τ e = some k) (i : ℤ)
    (h1 : reservationStart v π τ K i ≤ k.val)
    (h2 : k.val < reservationStart v π τ K i + reservedCount v π τ K i) :
    inClass (v e) i := by
  obtain ⟨hv, hq, hk⟩ := ac_reservedGood_some v π τ e k h
  refine ⟨hv, ?_⟩
  set j := valueClass (v e)
  rcases lt_trichotomy i j with hij | hij | hij
  · have := ac_br_le_b v π τ K i j hij; omega
  · exact hij.symm
  · have := ac_br_le_b v π τ K j i hij; omega

lemma ac_det {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) :
    min ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card)
      ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card) ≤ assignedClassCount (K := K) v π τ i := by
  set P : Finset (Fin n) := Finset.univ.filter (fun e => τ ≤ (π.symm e).val ∧ inClass (v e) i)
    with hP
  set r := reservedCount v π τ K i with hr
  set b := reservationStart v π τ K i with hb
  let R : Fin n → Fin n → Prop := fun f e => (π.symm f).val < (π.symm e).val
  have irr : ∀ x, ¬ R x x := fun x => lt_irrefl _
  have tr : ∀ x y z, R x y → R y z → R x z := fun x y z h1 h2 => lt_trans h1 h2
  have tot : ∀ x y, x ≠ y → R x y ∨ R y x := by
    intro x y hxy
    rcases lt_trichotomy (π.symm x).val (π.symm y).val with h | h | h
    · exact Or.inl h
    · exact absurd (π.symm.injective (Fin.ext h)) hxy
    · exact Or.inr h
  have hq : ∀ e ∈ P, earlierInClass v π τ e = (P.filter (fun f => R f e)).card := by
    intro e he
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at he
    unfold earlierInClass
    congr 1
    ext f
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, R]
    rw [he.2.2]
    tauto
  have hbr := ac_br_le_K v π τ K i
  -- main injection
  have hmain : min P.card r ≤ assignedClassCount (K := K) v π τ i := by
    rw [← gen_rank_count R irr tr tot P r]
    unfold assignedClassCount
    have hinj := (gen_rank_injOn R irr tr tot P).mono
      (s₁ := ((P.filter (fun e => (P.filter (fun f => R f e)).card < r)) : Set (Fin n)))
      (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; exact he.1)
    rw [← Finset.card_image_of_injOn (f := fun e => b + (P.filter (fun f => R f e)).card)
      (by intro x hx y hy hxy; exact hinj hx hy (by simpa using hxy))]
    refine le_trans ?_ (Finset.card_image_le (f := Fin.val))
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter] at hx
    obtain ⟨e, ⟨heP, heq⟩, rfl⟩ := hx
    have hlt : b + (P.filter (fun f => R f e)).card < K := by omega
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨_, hlt⟩, ?_, rfl⟩
    have hgood : reservedGood (K := K) v π τ e = some ⟨_, hlt⟩ := by
      have heP' := heP
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at heP'
      have hci : valueClass (v e) = i := heP'.2.2
      have hqe := hq e heP
      unfold reservedGood
      simp only
      rw [dif_pos (by rw [hci, hqe]; exact ⟨heP'.1, heP'.2.1, heq, hlt⟩)]
      congr 1; ext; simp only []; rw [hci, hqe]
    have hex : ∃ e' : Fin n, reservedGood (K := K) v π τ e' = some ⟨_, hlt⟩ := ⟨e, hgood⟩
    unfold reservationAssignment
    simp only [dif_pos hex]
    refine ⟨_, rfl, ?_⟩
    exact ac_class_of_good v π τ _ _ (Classical.choose_spec hex) i (Nat.le_add_right _ _)
      (by show b + _ < reservationStart v π τ K i + reservedCount v π τ K i; omega)
  -- X ≤ r, Y ≤ |P|
  have hX : (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card ≤ r := by
    rw [hr]; unfold reservedCount
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    refine ⟨?_, he.2.1⟩
    unfold sampleTop
    refine ⟨he.2.2, lt_of_le_of_lt ?_ he.1⟩
    unfold valueRank
    apply Finset.card_le_card
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact hf.2
  have hY : (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card ≤ P.card := by
    apply Finset.card_le_card
    intro e he
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨he.2.2, he.2.1⟩
  omega

/-! ## expectation operator -/

noncomputable def acEx {n : ℕ} (F : Equiv.Perm (Fin n) → ℕ → ℝ) : ℝ :=
  orderAverage (fun π => binomialAverage n (fun τ => F π τ))

lemma acEx_mono {n : ℕ} (F G : Equiv.Perm (Fin n) → ℕ → ℝ) (h : ∀ π τ, F π τ ≤ G π τ) :
    acEx F ≤ acEx G := by
  unfold acEx orderAverage binomialAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum; intro π _
  apply Finset.sum_le_sum; intro τ _
  exact mul_le_mul_of_nonneg_left (h π τ) (by positivity)

lemma acEx_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → Equiv.Perm (Fin n) → ℕ → ℝ) :
    acEx (fun π τ => ∑ a ∈ s, F a π τ) = ∑ a ∈ s, acEx (F a) := by
  unfold acEx orderAverage binomialAverage
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro π _
  conv_rhs => rw [Finset.sum_comm]

lemma acEx_mul {n : ℕ} (c : ℝ) (F : Equiv.Perm (Fin n) → ℕ → ℝ) :
    acEx (fun π τ => c * F π τ) = c * acEx F := by
  unfold acEx orderAverage binomialAverage
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π _
  apply Finset.sum_congr rfl; intro τ _
  ring

lemma acEx_zero {n : ℕ} : acEx (fun (_ : Equiv.Perm (Fin n)) (_ : ℕ) => (0 : ℝ)) = 0 := by
  unfold acEx orderAverage binomialAverage; simp

theorem ac_core {n K : ℕ} (v : Fin n → ℝ) (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    (optimalClassCount (K := K) v i : ℝ) / 4 ≤
      expectedAssignedClassCount (K := K) v i := by
  set O : Finset (Fin n) := Finset.univ.filter (fun e => valueRank v e < K ∧ inClass (v e) i)
    with hO
  have hu : optimalClassCount (K := K) v i = O.card := by
    unfold optimalClassCount; rfl
  rw [hu] at hi ⊢
  set u := O.card with hudef
  have hn : 2 ≤ n := by
    have := Finset.card_le_univ O
    simp only [Fintype.card_fin] at this; omega
  -- G
  let G : Equiv.Perm (Fin n) → ℕ → ℝ := fun π τ => ∑ a ∈ O, ∑ c ∈ O,
    if (π.symm a).val < τ ∧ τ ≤ (π.symm c).val then (1 : ℝ) else 0
  have hG : acEx G = ((u : ℝ) * u - u) / 4 := by
    have : acEx G = ∑ a ∈ O, ∑ c ∈ O, (if a = c then (0 : ℝ) else 1 / 4) := by
      simp only [G]
      rw [acEx_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [acEx_sum]
      apply Finset.sum_congr rfl; intro c _
      split_ifs with hac
      · subst hac
        have : (fun (π : Equiv.Perm (Fin n)) (τ : ℕ) =>
            if (π.symm a).val < τ ∧ τ ≤ (π.symm a).val then (1 : ℝ) else 0) = fun _ _ => 0 := by
          funext π τ; rw [if_neg]; omega
        rw [this, acEx_zero]
      · exact ac_pair_prob hn a c hac
    rw [this]
    have : ∀ a ∈ O, ∑ c ∈ O, (if a = c then (0 : ℝ) else 1 / 4) = ((u : ℝ) - 1) / 4 := by
      intro a ha
      rw [← Finset.sum_erase_add _ _ ha, if_pos rfl, add_zero]
      rw [Finset.sum_congr rfl (g := fun _ => (1 / 4 : ℝ))]
      · rw [Finset.sum_const, Finset.card_erase_of_mem ha, nsmul_eq_mul]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      · intro c hc; rw [if_neg]; exact (Finset.ne_of_mem_erase hc).symm
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  -- pointwise
  have hpt : ∀ π τ, G π τ ≤ ((u : ℝ) - 1) * (assignedClassCount (K := K) v π τ i : ℝ) := by
    intro π τ
    set X := (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card with hXd
    set Y := (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card with hYd
    have hdet := ac_det (K := K) v π τ i
    rw [← hXd, ← hYd] at hdet
    have hXO : X = (O.filter (fun e => (π.symm e).val < τ)).card := by
      rw [hXd, hO, Finset.filter_filter]; congr 1; ext e; simp [and_assoc]
    have hYO : Y = (O.filter (fun e => ¬ (π.symm e).val < τ)).card := by
      rw [hYd, hO, Finset.filter_filter]; congr 1; ext e; simp [and_assoc]
    have hXY : X + Y = u := by
      rw [hXO, hYO]; exact Finset.card_filter_add_card_filter_not _
    have hGXY : G π τ = (X : ℝ) * Y := by
      simp only [G]
      have : ∀ a ∈ O, ∀ c ∈ O, (if (π.symm a).val < τ ∧ τ ≤ (π.symm c).val then (1 : ℝ) else 0)
          = (if (π.symm a).val < τ then (1 : ℝ) else 0) *
            (if ¬ (π.symm c).val < τ then (1 : ℝ) else 0) := by
        intro a _ c _
        by_cases h1 : (π.symm a).val < τ <;> by_cases h2 : (π.symm c).val < τ <;>
          simp [h1, h2] <;> omega
      rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (this a ha))]
      rw [← Finset.sum_mul_sum, Finset.sum_boole, Finset.sum_boole, hXO, hYO]
    rw [hGXY]
    have hmin : (min X Y : ℝ) ≤ (assignedClassCount (K := K) v π τ i : ℝ) := by
      exact_mod_cast hdet
    have hu' : (u : ℝ) = X + Y := by exact_mod_cast hXY.symm
    rw [hu']
    have hX0 : (0 : ℝ) ≤ X := by positivity
    have hY0 : (0 : ℝ) ≤ Y := by positivity
    have h2n : 2 ≤ X + Y := by omega
    have h2 : (2 : ℝ) ≤ (X : ℝ) + Y := by exact_mod_cast h2n
    have hF0 : (0 : ℝ) ≤ (assignedClassCount (K := K) v π τ i : ℝ) := by positivity
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · have hX0' : (X : ℝ) = 0 := by exact_mod_cast h0
      rw [hX0', zero_mul]
      apply mul_nonneg (by linarith) hF0
    rcases Nat.eq_zero_or_pos Y with h1 | h1
    · have hY0' : (Y : ℝ) = 0 := by exact_mod_cast h1
      rw [hY0', mul_zero]
      apply mul_nonneg (by linarith) hF0
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast h0
    have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast h1
    rcases le_total X Y with hle | hle
    · have hm : (min X Y : ℝ) = X := by exact_mod_cast min_eq_left hle
      rw [hm] at hmin
      have hle' : (X : ℝ) ≤ Y := by exact_mod_cast hle
      nlinarith
    · have hm : (min X Y : ℝ) = Y := by exact_mod_cast min_eq_right hle
      rw [hm] at hmin
      have hle' : (Y : ℝ) ≤ X := by exact_mod_cast hle
      nlinarith
  have hE := acEx_mono G _ hpt
  rw [acEx_mul, hG] at hE
  have hEdef : acEx (fun π τ => (assignedClassCount (K := K) v π τ i : ℝ)) =
      expectedAssignedClassCount (K := K) v i := rfl
  rw [hEdef] at hE
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hi
  by_contra hcon
  push_neg at hcon
  have : ((u : ℝ) - 1) * expectedAssignedClassCount (K := K) v i < ((u : ℝ) - 1) * (u / 4) :=
    mul_lt_mul_of_pos_left hcon (by linarith)
  nlinarith


/-! ## reserved class value -/

lemma gen_rank_image {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (irr : ∀ x, ¬ R x x) (tr : ∀ x y z, R x y → R y z → R x z)
    (tot : ∀ x y, x ≠ y → R x y ∨ R y x) (C : Finset α) :
    C.image (fun e => (C.filter (fun f => R f e)).card) = Finset.range C.card := by
  have hinj := gen_rank_injOn R irr tr tot C
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simp only [Finset.mem_range]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨e, he, by simp [irr]⟩
  · rw [Finset.card_image_of_injOn hinj]; simp

lemma rc_good_assigned {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ)
    (x : ℕ) (hx : x < K) (h1 : reservationStart v π τ K i ≤ x)
    (h2 : x < reservationStart v π τ K i +
      min (Finset.univ.filter (fun e => τ ≤ (π.symm e).val ∧ inClass (v e) i)).card
        (reservedCount v π τ K i)) :
    ∃ e', reservationAssignment (K := K) v π τ ⟨x, hx⟩ = some e' ∧ inClass (v e') i := by
  set P : Finset (Fin n) := Finset.univ.filter (fun e => τ ≤ (π.symm e).val ∧ inClass (v e) i)
    with hP
  set r := reservedCount v π τ K i with hr
  set b := reservationStart v π τ K i with hb
  let R : Fin n → Fin n → Prop := fun f e => (π.symm f).val < (π.symm e).val
  have irr : ∀ x, ¬ R x x := fun x => lt_irrefl _
  have tr : ∀ x y z, R x y → R y z → R x z := fun x y z h1 h2 => lt_trans h1 h2
  have tot : ∀ x y, x ≠ y → R x y ∨ R y x := by
    intro x y hxy
    rcases lt_trichotomy (π.symm x).val (π.symm y).val with h | h | h
    · exact Or.inl h
    · exact absurd (π.symm.injective (Fin.ext h)) hxy
    · exact Or.inr h
  have hq : ∀ e ∈ P, earlierInClass v π τ e = (P.filter (fun f => R f e)).card := by
    intro e he
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at he
    unfold earlierInClass
    congr 1
    ext f
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, R]
    rw [he.2.2]
    tauto
  have hj : x - b ∈ P.image (fun e => (P.filter (fun f => R f e)).card) := by
    rw [gen_rank_image R irr tr tot P, Finset.mem_range]; omega
  obtain ⟨e, heP, heq⟩ := Finset.mem_image.mp hj
  have hxe : x = b + (P.filter (fun f => R f e)).card := by omega
  have hlt : b + (P.filter (fun f => R f e)).card < K := by omega
  have hqr : (P.filter (fun f => R f e)).card < r := by omega
  have hgood : reservedGood (K := K) v π τ e = some ⟨x, hx⟩ := by
    have heP' := heP
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at heP'
    have hci : valueClass (v e) = i := heP'.2.2
    have hqe := hq e heP
    unfold reservedGood
    simp only
    rw [dif_pos (by rw [hci, hqe]; exact ⟨heP'.1, heP'.2.1, hqr, hlt⟩)]
    congr 1; ext; simp only []; rw [hci, hqe]; omega
  have hex : ∃ e' : Fin n, reservedGood (K := K) v π τ e' = some ⟨x, hx⟩ := ⟨e, hgood⟩
  unfold reservationAssignment
  simp only [dif_pos hex]
  refine ⟨_, rfl, ?_⟩
  exact ac_class_of_good v π τ _ _ (Classical.choose_spec hex) i h1 (by
    show x < reservationStart v π τ K i + reservedCount v π τ K i; omega)

lemma rc_M_le {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) :
    min ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card)
      ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card) ≤
    min (Finset.univ.filter (fun e => τ ≤ (π.symm e).val ∧ inClass (v e) i)).card
        (reservedCount v π τ K i) := by
  have hX : (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card ≤ reservedCount v π τ K i := by
    unfold reservedCount
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    refine ⟨?_, he.2.1⟩
    unfold sampleTop
    refine ⟨he.2.2, lt_of_le_of_lt ?_ he.1⟩
    unfold valueRank
    apply Finset.card_le_card
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact hf.2
  have hY : (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card ≤
      (Finset.univ.filter (fun e => τ ≤ (π.symm e).val ∧ inClass (v e) i)).card := by
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨he.2.2, he.2.1⟩
  omega

lemma rc_class_bounds {x : ℝ} {i : ℤ} (h : inClass x i) :
    (2 : ℝ) ^ ((i : ℝ) - 1) ≤ x ∧ x < (2 : ℝ) ^ (i : ℝ) := by
  obtain ⟨hx, hc⟩ := h
  unfold valueClass at hc
  rw [if_pos hx] at hc
  have hfl : Int.floor (Real.log x / Real.log 2) = i - 1 := by omega
  have hL1 : ((i - 1 : ℤ) : ℝ) ≤ Real.log x / Real.log 2 := by
    rw [← hfl]; exact Int.floor_le _
  have hL2 : Real.log x / Real.log 2 < ((i - 1 : ℤ) : ℝ) + 1 := by
    rw [← hfl]; exact Int.lt_floor_add_one _
  have hx2 : (2 : ℝ) ^ (Real.log x / Real.log 2) = x := by
    have := Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hx
    rwa [Real.logb] at this
  push_cast at hL1 hL2
  constructor
  · rw [← hx2]
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hL1
  · rw [← hx2]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by linarith)

noncomputable def rcW {K : ℕ} (w : Fin K → ℝ) (j : ℕ) : ℝ := if h : j < K then w ⟨j, h⟩ else 0

lemma rcW_anti {K : ℕ} (w : Fin K → ℝ) (hmono : Antitone w) (j j' : ℕ) (hjj : j ≤ j')
    (hj' : j' < K) : rcW w j' ≤ rcW w j := by
  unfold rcW
  rw [dif_pos hj', dif_pos (lt_of_le_of_lt hjj hj')]
  exact hmono (Fin.mk_le_mk.mpr hjj)

lemma rcW_nonneg {K : ℕ} (w : Fin K → ℝ) (hw : ∀ k, 0 ≤ w k) (j : ℕ) : 0 ≤ rcW w j := by
  unfold rcW; split_ifs
  · exact hw _
  · exact le_rfl

lemma rc_prefix (a : ℕ → ℝ) (u M : ℕ) (hM : M ≤ u)
    (ha : ∀ p q, p ≤ q → q < u → a q ≤ a p) :
    (M : ℝ) * ∑ q ∈ Finset.range u, a q ≤ (u : ℝ) * ∑ q ∈ Finset.range M, a q := by
  have key : (u : ℝ) * ∑ q ∈ Finset.range M, a q - (M : ℝ) * ∑ q ∈ Finset.range u, a q =
      ∑ q ∈ Finset.range M, ∑ p ∈ Finset.Ico M u, (a q - a p) := by
    have hsplit : ∑ q ∈ Finset.range u, a q =
        ∑ q ∈ Finset.range M, a q + ∑ q ∈ Finset.Ico M u, a q :=
      (Finset.sum_range_add_sum_Ico _ hM).symm
    have hcard : ((Finset.Ico M u).card : ℝ) = (u : ℝ) - M := by
      rw [Nat.card_Ico, Nat.cast_sub hM]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    rw [← Finset.mul_sum, hsplit, hcard]
    ring
  have : 0 ≤ ∑ q ∈ Finset.range M, ∑ p ∈ Finset.Ico M u, (a q - a p) := by
    apply Finset.sum_nonneg; intro q hq
    apply Finset.sum_nonneg; intro p hp
    simp only [Finset.mem_range] at hq
    simp only [Finset.mem_Ico] at hp
    have := ha q p (by omega) hp.2
    linarith
  linarith

lemma rc_optStart_add {n K : ℕ} (v : Fin n → ℝ) (i : ℤ) :
    optimalStart (K := K) v i + optimalClassCount (K := K) v i ≤ K := by
  have htop : (Finset.univ.filter (fun e : Fin n => valueRank v e < K)).card ≤ K := by
    have := rs_top_card_le v Finset.univ K
    refine le_trans (Finset.card_le_card ?_) this
    intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h2 := he.2
    unfold valueRank at h2
    convert h2 using 2
  refine le_trans ?_ htop
  unfold optimalStart optimalClassCount
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rcases he with h | h
    · exact h.1
    · exact h.1
  · rw [Finset.disjoint_filter]
    intro e _ h1 h2
    unfold inClass at h2
    omega

lemma rc_R_lower {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) :
    (2 : ℝ) ^ ((i : ℝ) - 1) * ∑ q ∈ Finset.range
      (min ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card)
      ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card)),
        rcW w (optimalStart (K := K) v i + q) ≤ reservedClassValue v w π τ i := by
  set M := min ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card)
      ((Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card) with hM
  set b := reservationStart v π τ K i with hb
  set o := optimalStart (K := K) v i with ho
  have hMle := rc_M_le (K := K) v π τ i
  rw [← hM] at hMle
  have hbo : b ≤ o := rs_core v π τ i
  have hou := rc_optStart_add (K := K) v i
  have hMu : M ≤ optimalClassCount (K := K) v i := by
    have : M ≤ (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card + (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧
        inClass (v e) i ∧ τ ≤ (π.symm e).val)).card := by omega
    refine le_trans this ?_
    unfold optimalClassCount
    rw [← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rcases he with h | h
      · exact ⟨h.1, h.2.1⟩
      · exact ⟨h.1, h.2.1⟩
    · rw [Finset.disjoint_filter]
      intro e _ h1 h2
      omega
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ ((i : ℝ) - 1) := by positivity
  -- step 1: lower bound by the block
  have hstep : ∑ k : Fin K, (if b ≤ k.val ∧ k.val < b + M then (2 : ℝ) ^ ((i : ℝ) - 1) * w k else 0)
      ≤ reservedClassValue v w π τ i := by
    unfold reservedClassValue
    apply Finset.sum_le_sum
    intro k _
    split_ifs with h1 h2 h2
    · have hs := Classical.choose_spec h2
      have := (rc_class_bounds hs.2).1
      exact mul_le_mul_of_nonneg_right this (hw k)
    · exfalso
      exact h2 (rc_good_assigned v π τ i k.val k.isLt h1.1 (by omega))
    · exact mul_nonneg (hv _) (hw k)
    · exact le_rfl
  refine le_trans ?_ hstep
  have hsum : ∑ k : Fin K, (if b ≤ k.val ∧ k.val < b + M then (2 : ℝ) ^ ((i : ℝ) - 1) * w k else 0)
      = (2 : ℝ) ^ ((i : ℝ) - 1) * ∑ q ∈ Finset.range M, rcW w (b + q) := by
    have e1 : ∀ k : Fin K, (if b ≤ k.val ∧ k.val < b + M then (2 : ℝ) ^ ((i : ℝ) - 1) * w k else 0)
        = (fun j : ℕ => if b ≤ j ∧ j < b + M then (2 : ℝ) ^ ((i : ℝ) - 1) * rcW w j else 0) k.val := by
      intro k
      simp only [rcW, dif_pos k.isLt]
    rw [Finset.sum_congr rfl (fun k _ => e1 k), Fin.sum_univ_eq_sum_range
      (fun j : ℕ => if b ≤ j ∧ j < b + M then (2 : ℝ) ^ ((i : ℝ) - 1) * rcW w j else 0) K]
    rw [← Finset.sum_filter]
    have : (Finset.range K).filter (fun j => b ≤ j ∧ j < b + M) = Finset.Ico b (b + M) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, ← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    simp
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Finset.sum_le_sum
  intro q hq
  simp only [Finset.mem_range] at hq
  exact rcW_anti w hmono _ _ (by omega) (by omega)

lemma rc_opt_upper {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w) (i : ℤ) :
    optimalClassValue v w i ≤ (2 : ℝ) ^ (i : ℝ) * ∑ q ∈ Finset.range (optimalClassCount (K := K) v i),
      rcW w (optimalStart (K := K) v i + q) := by
  set O : Finset (Fin n) := Finset.univ.filter (fun e => valueRank v e < K ∧ inClass (v e) i)
    with hO
  set o := optimalStart (K := K) v i with ho
  have hu : optimalClassCount (K := K) v i = O.card := by unfold optimalClassCount; rfl
  rw [hu]
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (i : ℝ) := by positivity
  -- (a)
  have ha : optimalClassValue v w i ≤ ∑ k : Fin K, ∑ e ∈ O,
      (if valueRank v e = k.val then (2 : ℝ) ^ (i : ℝ) * w k else 0) := by
    unfold optimalClassValue
    apply Finset.sum_le_sum
    intro k _
    split_ifs with h
    · have hs := Classical.choose_spec h
      set e0 := Classical.choose h
      have hrk : valueRank v e0 = k.val := by
        have h1 := hs.1
        unfold optimalAssignment at h1
        try simp only at h1
        split_ifs at h1 with h'
        simp only [Option.some.injEq] at h1
        rw [← h1]; exact Classical.choose_spec h'
      have he0 : e0 ∈ O := by
        simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by rw [hrk]; exact k.isLt, hs.2⟩
      refine le_trans ?_ (Finset.single_le_sum (f := fun e =>
        (if valueRank v e = k.val then (2 : ℝ) ^ (i : ℝ) * w k else 0))
        (fun e _ => by split_ifs; exact mul_nonneg hc (hw k); exact le_rfl) he0)
      simp only [if_pos hrk]
      exact mul_le_mul_of_nonneg_right (rc_class_bounds hs.2).2.le (hw k)
    · apply Finset.sum_nonneg; intro e _; split_ifs; exact mul_nonneg hc (hw k); exact le_rfl
  refine le_trans ha ?_
  rw [Finset.sum_comm]
  have hb : ∀ e ∈ O, ∑ k : Fin K, (if valueRank v e = k.val then (2 : ℝ) ^ (i : ℝ) * w k else 0)
      = (2 : ℝ) ^ (i : ℝ) * rcW w (valueRank v e) := by
    intro e he
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have : ∀ k : Fin K, (if valueRank v e = k.val then (2 : ℝ) ^ (i : ℝ) * w k else 0) =
        if (⟨valueRank v e, he.1⟩ : Fin K) = k then (2 : ℝ) ^ (i : ℝ) * w k else 0 := by
      intro k; congr 1; simp [Fin.ext_iff]
    rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_ite_eq]
    simp [rcW, he.1]
  rw [Finset.sum_congr rfl hb, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hc
  -- (c),(d)
  let R : Fin n → Fin n → Prop := fun f e => better v f e
  have irr : ∀ x, ¬ R x x := rs_better_irrefl v
  have tr : ∀ x y z, R x y → R y z → R x z := rs_better_trans v
  have tot : ∀ x y, x ≠ y → R x y ∨ R y x := rs_better_total v
  have hinj := gen_rank_injOn R irr tr tot O
  have himg := gen_rank_image R irr tr tot O
  have hrhs : ∑ q ∈ Finset.range O.card, rcW w (o + q) =
      ∑ e ∈ O, rcW w (o + (O.filter (fun f => R f e)).card) := by
    rw [← himg, Finset.sum_image (fun x hx y hy hxy => hinj hx hy hxy)]
  rw [hrhs]
  apply Finset.sum_le_sum
  intro e he
  have he' := he
  simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at he'
  apply rcW_anti w hmono _ _ _ he'.1
  -- rank e ≥ o + rankO e
  set C' : Finset (Fin n) := Finset.univ.filter
    (fun f : Fin n => valueRank v f < K ∧ 0 < v f ∧ i < valueClass (v f)) with hC'
  have hoC : o = C'.card := by rw [ho]; unfold optimalStart; rfl
  rw [hoC]
  unfold valueRank
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro f hf
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hC', hO] at hf ⊢
    rcases hf with h | h
    · -- class of f > i = class of e, so v f > v e
      obtain ⟨hev, hec⟩ := he'.2
      left
      by_contra hle
      push_neg at hle
      have := rs_class_mono h.2.1 hle
      omega
    · exact h.2
  · rw [Finset.disjoint_left]
    intro f h1 h2
    simp only [hC', hO, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    unfold inClass at h2
    omega

theorem rc_core {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    optimalClassValue v w i / 8 ≤ expectedReservedClassValue v w i := by
  set O : Finset (Fin n) := Finset.univ.filter (fun e => valueRank v e < K ∧ inClass (v e) i)
    with hO
  have hu : optimalClassCount (K := K) v i = O.card := by
    unfold optimalClassCount; rfl
  set u := O.card with hudef
  set o := optimalStart (K := K) v i with ho
  set A := ∑ q ∈ Finset.range u, rcW w (o + q) with hA
  have hou := rc_optStart_add (K := K) v i
  rw [hu] at hou hi
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun q _ => rcW_nonneg w hw _)
  have hopt := rc_opt_upper v w hv hw hmono i
  rw [hu] at hopt
  have hn : 2 ≤ n := by
    have := Finset.card_le_univ O
    simp only [Fintype.card_fin] at this; omega
  set c := (2 : ℝ) ^ ((i : ℝ) - 1) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have h2c : (2 : ℝ) ^ (i : ℝ) = 2 * c := by
    have := Real.rpow_add (show (0 : ℝ) < 2 by norm_num) 1 ((i : ℝ) - 1)
    rw [Real.rpow_one] at this
    rw [hcdef, ← this]; ring_nf
  have hanti : ∀ p q, p ≤ q → q < u → rcW w (o + q) ≤ rcW w (o + p) := by
    intro p q hpq hq
    exact rcW_anti w hmono _ _ (by omega) (by omega)
  -- G
  let G : Equiv.Perm (Fin n) → ℕ → ℝ := fun π τ => ∑ a ∈ O, ∑ c ∈ O,
    if (π.symm a).val < τ ∧ τ ≤ (π.symm c).val then (1 : ℝ) else 0
  have hG : acEx G = ((u : ℝ) * u - u) / 4 := by
    have : acEx G = ∑ a ∈ O, ∑ c ∈ O, (if a = c then (0 : ℝ) else 1 / 4) := by
      simp only [G]
      rw [acEx_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [acEx_sum]
      apply Finset.sum_congr rfl; intro c _
      split_ifs with hac
      · subst hac
        have : (fun (π : Equiv.Perm (Fin n)) (τ : ℕ) =>
            if (π.symm a).val < τ ∧ τ ≤ (π.symm a).val then (1 : ℝ) else 0) = fun _ _ => 0 := by
          funext π τ; rw [if_neg]; omega
        rw [this, acEx_zero]
      · exact ac_pair_prob hn a c hac
    rw [this]
    have : ∀ a ∈ O, ∑ c ∈ O, (if a = c then (0 : ℝ) else 1 / 4) = ((u : ℝ) - 1) / 4 := by
      intro a ha
      rw [← Finset.sum_erase_add _ _ ha, if_pos rfl, add_zero]
      rw [Finset.sum_congr rfl (g := fun _ => (1 / 4 : ℝ))]
      · rw [Finset.sum_const, Finset.card_erase_of_mem ha, nsmul_eq_mul]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      · intro c hc; rw [if_neg]; exact (Finset.ne_of_mem_erase hc).symm
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hi
  have huu : (0 : ℝ) < (u : ℝ) * ((u : ℝ) - 1) := by nlinarith
  have hpt : ∀ π τ, (c * A / ((u : ℝ) * ((u : ℝ) - 1))) * G π τ ≤ reservedClassValue v w π τ i := by
    intro π τ
    set X := (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        (π.symm e).val < τ)).card with hXd
    set Y := (Finset.univ.filter (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i ∧
        τ ≤ (π.symm e).val)).card with hYd
    have hRl := rc_R_lower v w hv hw hmono π τ i
    rw [← hXd, ← hYd] at hRl
    have hXO : X = (O.filter (fun e => (π.symm e).val < τ)).card := by
      rw [hXd, hO, Finset.filter_filter]; congr 1; ext e; simp [and_assoc]
    have hYO : Y = (O.filter (fun e => ¬ (π.symm e).val < τ)).card := by
      rw [hYd, hO, Finset.filter_filter]; congr 1; ext e; simp [and_assoc]
    have hXY : X + Y = u := by
      rw [hXO, hYO]; exact Finset.card_filter_add_card_filter_not _
    have hGXY : G π τ = (X : ℝ) * Y := by
      simp only [G]
      have : ∀ a ∈ O, ∀ c ∈ O, (if (π.symm a).val < τ ∧ τ ≤ (π.symm c).val then (1 : ℝ) else 0)
          = (if (π.symm a).val < τ then (1 : ℝ) else 0) *
            (if ¬ (π.symm c).val < τ then (1 : ℝ) else 0) := by
        intro a _ c _
        by_cases h1 : (π.symm a).val < τ <;> by_cases h2 : (π.symm c).val < τ <;>
          simp [h1, h2] <;> omega
      rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (this a ha))]
      rw [← Finset.sum_mul_sum, Finset.sum_boole, Finset.sum_boole, hXO, hYO]
    rw [hGXY]
    set M := min X Y with hMd
    have hMu : M ≤ u := by omega
    -- (u-1) M ≥ X Y
    have hmin : (X : ℝ) * Y ≤ ((u : ℝ) - 1) * M := by
      have hu' : (u : ℝ) = X + Y := by exact_mod_cast hXY.symm
      rw [hu']
      have hX0 : (0 : ℝ) ≤ X := by positivity
      have hY0 : (0 : ℝ) ≤ Y := by positivity
      have h2n : 2 ≤ X + Y := by omega
      have h2 : (2 : ℝ) ≤ (X : ℝ) + Y := by exact_mod_cast h2n
      have hM0 : (0 : ℝ) ≤ M := by positivity
      rcases Nat.eq_zero_or_pos X with h0 | h0
      · have hX0' : (X : ℝ) = 0 := by exact_mod_cast h0
        rw [hX0', zero_mul]
        apply mul_nonneg (by linarith) hM0
      rcases Nat.eq_zero_or_pos Y with h1 | h1
      · have hY0' : (Y : ℝ) = 0 := by exact_mod_cast h1
        rw [hY0', mul_zero]
        apply mul_nonneg (by linarith) hM0
      have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast h0
      have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast h1
      rcases le_total X Y with hle | hle
      · have hm : (M : ℝ) = X := by rw [hMd]; exact_mod_cast min_eq_left hle
        rw [hm]
        have hle' : (X : ℝ) ≤ Y := by exact_mod_cast hle
        nlinarith
      · have hm : (M : ℝ) = Y := by rw [hMd]; exact_mod_cast min_eq_right hle
        rw [hm]
        have hle' : (Y : ℝ) ≤ X := by exact_mod_cast hle
        nlinarith
    have hpre := rc_prefix (fun q => rcW w (o + q)) u M hMu hanti
    try simp only at hpre
    rw [← hA] at hpre
    set S := ∑ q ∈ Finset.range M, rcW w (o + q) with hS
    -- goal: c*A/(u(u-1)) * (X*Y) ≤ R, with c*S ≤ R
    rw [div_mul_eq_mul_div, div_le_iff₀ huu]
    have h1 : c * A * ((X : ℝ) * Y) ≤ c * A * (((u : ℝ) - 1) * M) :=
      mul_le_mul_of_nonneg_left hmin (mul_nonneg hc0 hA0)
    have h2 : c * (((u : ℝ) - 1) * (M * A)) ≤ c * (((u : ℝ) - 1) * (u * S)) := by
      apply mul_le_mul_of_nonneg_left _ hc0
      exact mul_le_mul_of_nonneg_left hpre (by linarith)
    have h3 : c * S * ((u : ℝ) * ((u : ℝ) - 1)) ≤
        reservedClassValue v w π τ i * ((u : ℝ) * ((u : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right hRl huu.le
    nlinarith
  have hE := acEx_mono _ _ hpt
  rw [acEx_mul, hG] at hE
  have hEdef : acEx (fun π τ => reservedClassValue v w π τ i) =
      expectedReservedClassValue v w i := rfl
  rw [hEdef] at hE
  have hval : c * A / ((u : ℝ) * ((u : ℝ) - 1)) * (((u : ℝ) * u - u) / 4) = c * A / 4 := by
    have hne : (u : ℝ) * ((u : ℝ) - 1) ≠ 0 := huu.ne'
    have hne1 : (u : ℝ) - 1 ≠ 0 := by linarith
    rw [show ((u : ℝ) * u - u) = (u : ℝ) * ((u : ℝ) - 1) by ring]
    field_simp
  rw [hval] at hE
  have : optimalClassValue v w i ≤ 2 * c * A := by rw [← h2c]; exact hopt
  linarith

end SecretaryWD.Weighted

open SecretaryWD.Weighted


theorem solution {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    optimalClassValue v w i / 8 ≤ expectedReservedClassValue v w i := by
  exact rc_core v w hv hw hmono i hi
