-- Prove2me | solution 1 for SecretaryWD.Weighted.weighted_secretary_competitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:56:05.56977+00:00
-- url     : https://prove2.me/submissions/954b299a-28ef-4d31-a0ef-bcb7e6d68f92

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


lemma cs_find_iff {m : ℕ} (p : Fin m → Bool) (t : Fin m) :
    (List.finRange m).find? p = some t ↔ p t = true ∧ ∀ s : Fin m, s < t → p s = false := by
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hp, i, hi, hit, hj⟩
    refine ⟨hp, fun s hs => ?_⟩
    simp only [List.getElem_finRange] at hit
    subst hit
    have := hj s.val (by simpa [Fin.lt_def] using hs)
    simpa using this
  · rintro ⟨hp, hs⟩
    refine ⟨hp, t.val, by simp, by simp, fun j hj => ?_⟩
    have := hs ⟨j, by omega⟩ (by simp [Fin.lt_def]; omega)
    simp [this]

variable {L : Type*} [LinearOrder L]

/-- `a` is the position of the maximum among the first `t` arrivals. -/
def IsPA {m : ℕ} (k : Fin m → L) (σ : Equiv.Perm (Fin m)) (t a : Fin m) : Prop :=
  a < t ∧ ∀ u : Fin m, u < t → u ≠ a → k (σ u) < k (σ a)

noncomputable def NN {m : ℕ} (k : Fin m → L) (e₀ : Fin m) (t a : Fin m) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ t = e₀ ∧ IsPA k σ t a).card

noncomputable def AA {m : ℕ} (e₀ : Fin m) (t : Fin m) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ t = e₀).card

lemma NN_le {m : ℕ} (k : Fin m → L) (e₀ t a a' : Fin m) (ha : a < t) (ha' : a' < t) :
    NN k e₀ t a ≤ NN k e₀ t a' := by
  unfold NN
  apply Finset.card_le_card_of_injOn (fun σ => σ * Equiv.swap a a')
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    obtain ⟨h1, h2, h3⟩ := hσ
    have hta : t ≠ a := ne_of_gt ha
    have hta' : t ≠ a' := ne_of_gt ha'
    refine ⟨?_, ha', ?_⟩
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hta hta', h1]
    · intro u hu hua'
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      apply h3
      · rcases eq_or_ne u a with rfl | hua
        · rw [Equiv.swap_apply_left]; exact ha'
        · rw [Equiv.swap_apply_of_ne_of_ne hua hua']; exact hu
      · intro h
        apply hua'
        have := congrArg (Equiv.swap a a') h
        simpa using this
  · intro σ _ τ _ h
    simpa using h

lemma NN_eq {m : ℕ} (k : Fin m → L) (e₀ t a a' : Fin m) (ha : a < t) (ha' : a' < t) :
    NN k e₀ t a = NN k e₀ t a' :=
  le_antisymm (NN_le k e₀ t a a' ha ha') (NN_le k e₀ t a' a ha' ha)

lemma AA_le {m : ℕ} (e₀ t t' : Fin m) : AA e₀ t ≤ AA e₀ t' := by
  unfold AA
  apply Finset.card_le_card_of_injOn (fun σ => σ * Equiv.swap t t')
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    simp [Equiv.Perm.mul_apply, hσ]
  · intro σ _ τ _ h
    simpa using h

lemma AA_eq {m : ℕ} (e₀ t t' : Fin m) : AA e₀ t = AA e₀ t' :=
  le_antisymm (AA_le e₀ t t') (AA_le e₀ t' t)

lemma AA_sum {m : ℕ} (e₀ : Fin m) : ∑ t, AA e₀ t = m.factorial := by
  unfold AA
  rw [show m.factorial = (Finset.univ : Finset (Equiv.Perm (Fin m))).card by
    simp [Fintype.card_perm]]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin m) => σ.symm e₀)
    (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [← h]; simp

lemma AA_val {m : ℕ} (e₀ t : Fin m) : (m : ℝ) * AA e₀ t = m.factorial := by
  have h := AA_sum e₀
  rw [Finset.sum_congr rfl (fun t' _ => AA_eq e₀ t' t)] at h
  simp at h
  exact_mod_cast h

lemma NN_sum {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ t : Fin m) (ht : 0 < t.val) :
    ∑ a ∈ Finset.univ.filter (· < t), NN k e₀ t a = AA e₀ t := by
  unfold NN AA
  rw [← Finset.card_biUnion]
  · congr 1
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, _, h, _⟩; exact h
    · intro h
      obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (· < t))
        (fun u => k (σ u)) ⟨⟨0, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; exact ht⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
      refine ⟨a, ha, h, ha, fun u hu hua => lt_of_le_of_ne (hmax u hu) ?_⟩
      intro heq
      exact hua (σ.injective (hk heq))
  · intro a _ a' _ haa'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have := h1.2.2 a' h2.2.1 (Ne.symm haa')
    have := h2.2.2 a h1.2.1 haa'
    exact absurd (lt_trans ‹k (σ a') < k (σ a)› this) (lt_irrefl _)

lemma NN_val {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ t a : Fin m) (ha : a < t) :
    (m : ℝ) * t.val * NN k e₀ t a = m.factorial := by
  have ht : 0 < t.val := lt_of_le_of_lt (Nat.zero_le _) ha
  have h := NN_sum k hk e₀ t ht
  rw [Finset.sum_congr rfl (fun a' ha' => NN_eq k e₀ t a' a (by simpa using ha') ha)] at h
  rw [Finset.sum_const, smul_eq_mul] at h
  have hc : (Finset.univ.filter (· < t)).card = t.val := by
    rw [show Finset.univ.filter (· < t) = Finset.Iio t by ext; simp]
    simp
  rw [hc] at h
  rw [← AA_val e₀ t, ← h]; push_cast; ring


def SuccP {m : ℕ} (k : Fin m → L) (r : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∃ t : Fin m, (List.finRange m).find? (fun t => decide (r ≤ t.val ∧
      ∀ s : Fin m, s < t → k (σ s) < k (σ t))) = some t ∧ ∀ e : Fin m, k e ≤ k (σ t)

lemma max_iff {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (y : Fin m) : (∀ e, k e ≤ k y) ↔ y = e₀ := by
  constructor
  · intro h; exact hk (le_antisymm (he₀ y) (h e₀))
  · rintro rfl; exact he₀

lemma SuccP_iff {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (r : ℕ) (hr : 1 ≤ r) (σ : Equiv.Perm (Fin m)) :
    SuccP k r σ ↔ ∃ t a : Fin m, r ≤ t.val ∧ a.val < r ∧ σ t = e₀ ∧ IsPA k σ t a := by
  unfold SuccP
  simp only [cs_find_iff, decide_eq_true_eq, decide_eq_false_iff_not, max_iff k hk e₀ he₀]
  constructor
  · rintro ⟨t, ⟨⟨hrt, _⟩, hs⟩, hte⟩
    have ht : 0 < t.val := by omega
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (· < t))
      (fun u => k (σ u)) ⟨⟨0, by omega⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; exact ht⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
    have hPA : IsPA k σ t a := ⟨ha, fun u hu hua => lt_of_le_of_ne (hmax u hu)
      (fun heq => hua (σ.injective (hk heq)))⟩
    refine ⟨t, a, hrt, ?_, hte, hPA⟩
    by_contra hra
    push_neg at hra
    apply hs a ha
    refine ⟨hra, fun u hu => hPA.2 u (lt_trans hu ha) (ne_of_lt hu)⟩
  · rintro ⟨t, a, hrt, har, hte, hPA⟩
    refine ⟨t, ⟨⟨hrt, fun s hs => ?_⟩, fun s hs ⟨hrs, hrec⟩ => ?_⟩, hte⟩
    · rw [hte]
      refine lt_of_le_of_ne (he₀ _) (fun heq => ?_)
      have := σ.injective ((hk heq).trans hte.symm)
      exact absurd this (ne_of_lt hs)
    · have has : a < s := by rw [Fin.lt_def]; omega
      have h1 := hrec a has
      have h2 := hPA.2 s hs (ne_of_gt has)
      exact absurd (lt_trans h1 h2) (lt_irrefl _)

lemma SuccP_count {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) :
    ((Finset.univ.filter (SuccP k r)).card : ℝ) =
      ∑ i ∈ Finset.Ico r m, (r : ℝ) * (m.factorial : ℝ) / ((m : ℝ) * i) := by
  have hset : Finset.univ.filter (SuccP k r) =
      (Finset.univ.filter fun p : Fin m × Fin m => r ≤ p.1.val ∧ p.2.val < r).biUnion
        (fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ p.1 = e₀ ∧ IsPA k σ p.1 p.2) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      SuccP_iff k hk e₀ he₀ r hr, Prod.exists]
    constructor
    · rintro ⟨t, a, h1, h2, h3, h4⟩; exact ⟨t, a, ⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨t, a, ⟨h1, h2⟩, h3, h4⟩; exact ⟨t, a, h1, h2, h3, h4⟩
  rw [hset, Finset.card_biUnion]
  · push_cast
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    have hinner : ∀ t : Fin m, (∑ a : Fin m, if r ≤ t.val ∧ a.val < r then
        ((NN k e₀ t a : ℕ) : ℝ) else 0) =
        if r ≤ t.val then (r : ℝ) * m.factorial / (m * t.val) else 0 := by
      intro t
      split_ifs with hrt
      · have hm : (0 : ℝ) < m := by
          have := t.isLt; exact_mod_cast (show 0 < m by omega)
        have ht : (0 : ℝ) < t.val := by exact_mod_cast (show 0 < t.val by omega)
        have : ∀ a : Fin m, (if r ≤ t.val ∧ a.val < r then ((NN k e₀ t a : ℕ) : ℝ) else 0) =
            if a.val < r then (m.factorial : ℝ) / (m * t.val) else 0 := by
          intro a
          by_cases har : a.val < r
          · rw [if_pos ⟨hrt, har⟩, if_pos har]
            have := NN_val k hk e₀ t a (by rw [Fin.lt_def]; omega)
            field_simp
            linarith
          · rw [if_neg (fun h => har h.2), if_neg har]
        rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
        have hc : (Finset.univ.filter fun a : Fin m => a.val < r).card = r := by
          rw [Fin.card_filter_val_lt]
          omega
        rw [hc]; ring
      · exact Finset.sum_eq_zero (fun a _ => if_neg (fun h => hrt h.1))
    refine (Finset.sum_congr rfl (fun t _ => hinner t)).trans ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => if r ≤ i then (r : ℝ) * m.factorial / (m * i) else 0),
      ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i; simp [Finset.mem_Ico]; omega
    · intro i _; rfl
  · intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    apply hpq
    have ht : p.1 = q.1 := σ.injective (h1.1.trans h2.1.symm)
    have ha : p.2 = q.2 := by
      by_contra hne
      have := h1.2.2 q.2 (ht ▸ h2.2.1) (Ne.symm hne)
      have := h2.2.2 p.2 (ht ▸ h1.2.1) hne
      exact absurd (lt_trans ‹k (σ q.2) < k (σ p.2)› this) (lt_irrefl _)
    exact Prod.ext ht ha

lemma an_log_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  let h : ℝ → ℝ := fun y => (y - y⁻¹) / 2 - Real.log y
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt h ((1 + (y ^ 2)⁻¹) / 2 - y⁻¹) y := by
    intro y hy
    have h1 := (hasDerivAt_id y).sub (hasDerivAt_inv hy.ne')
    have h2 := (h1.div_const 2).sub (Real.hasDerivAt_log hy.ne')
    refine h2.congr_deriv ?_
    ring
  have hmono : MonotoneOn h (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro y hy
      exact (hd y (lt_of_lt_of_le one_pos hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hd y (lt_trans one_pos hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : 0 < y := lt_trans one_pos hy
      rw [(hd y hy0).deriv]
      have : (1 + (y ^ 2)⁻¹) / 2 - y⁻¹ = (1 - y⁻¹) ^ 2 / 2 := by
        field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 (le_refl (1:ℝ))) hx hx
  simp only [h, inv_one, sub_self, zero_div, Real.log_one] at this
  linarith

lemma an_step (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) - Real.log n ≤ (1 / n + 1 / (n + 1)) / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [← Real.log_div (by positivity) hpos.ne']
  refine (an_log_le _ (by rw [le_div_iff₀ hpos]; linarith)).trans (le_of_eq ?_)
  field_simp
  ring

lemma an_sum (r : ℕ) (hr : 1 ≤ r) (n : ℕ) (hn : r ≤ n) :
    Real.log n - Real.log r + (1 / r - 1 / n) / 2 ≤ ∑ i ∈ Finset.Ico r n, (1 : ℝ) / i := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hrn ih =>
    rw [Finset.sum_Ico_succ_top hrn]
    have := an_step n (le_trans hr hrn)
    push_cast
    linarith

lemma an_main (m : ℕ) (hm : 1 ≤ m) (r : ℕ) (hr : r = Nat.floor ((m : ℝ) / Real.exp 1)) :
    1 / Real.exp 1 ≤ (if r = 0 then (1 : ℝ) / m else
      (r : ℝ) / m * ∑ i ∈ Finset.Ico r m, (1 : ℝ) / i) := by
  have hE1 := Real.exp_one_gt_d9
  have hE2 := Real.exp_one_lt_d9
  set E := Real.exp 1 with hEdef
  have hEpos : 0 < E := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfl := Nat.floor_le (show 0 ≤ (m : ℝ) / E by positivity)
  have hlt := Nat.lt_floor_add_one ((m : ℝ) / E)
  rw [← hr] at hfl hlt
  rw [le_div_iff₀ hEpos] at hfl
  rw [div_lt_iff₀ hEpos] at hlt
  have h1n : 2718281 * r < 1000000 * m := by
    have : (2718281:ℝ) * r < 1000000 * m := by nlinarith
    exact_mod_cast this
  have h2n : 1000000 * m < 2718282 * (r + 1) := by
    have : (1000000:ℝ) * m < 2718282 * (r + 1) := by nlinarith
    exact_mod_cast this
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    subst hr0
    have hm2 : m ≤ 2 := by omega
    have : (m : ℝ) ≤ E := by
      have : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
      linarith
    exact one_div_le_one_div_of_le hm0 this
  rw [if_neg hr0]
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.2 hr0
  by_cases hm8 : m ≤ 8
  · have hr3 : r ≤ 3 := by omega
    interval_cases m <;> interval_cases r <;> first
      | omega
      | (norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
         rw [inv_eq_one_div, div_le_iff₀ hEpos]; linarith)
  push_neg at hm8
  have hm9 : (9 : ℝ) ≤ m := by exact_mod_cast hm8
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrm : r ≤ m := by omega
  have hS := an_sum r hr1 m hrm
  have hlog : 2 - E * r / m ≤ Real.log m - Real.log r := by
    have hx : 0 < (m : ℝ) / (E * r) := by positivity
    have := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div hm0.ne' (by positivity), Real.log_mul hEpos.ne' (by positivity),
      hEdef, Real.log_exp, ← hEdef, inv_div] at this
    linarith
  have hkey : (m - E * r) ^ 2 ≤ E * (m - r) / 2 := by
    have hd0 : 0 ≤ m - E * r := by linarith
    have hdE : m - E * r < E := by linarith
    have hmr : 2 * E ≤ m - r := by nlinarith
    nlinarith
  have hL : 1 / E ≤ r / m * ((2 - E * r / m) + (1 / r - 1 / m) / 2) := by
    rw [div_le_iff₀ hEpos]
    have : r / m * ((2 - E * r / m) + (1 / r - 1 / m) / 2) * E =
        1 + (E * (m - r) / 2 - (m - E * r) ^ 2) / m ^ 2 := by
      field_simp; ring
    rw [this]
    have : 0 ≤ (E * (m - r) / 2 - (m - E * r) ^ 2) / m ^ 2 := by
      apply div_nonneg <;> nlinarith
    linarith
  refine hL.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

lemma SuccP_zero {m : ℕ} (hm : 1 ≤ m) (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (σ : Equiv.Perm (Fin m)) :
    SuccP k 0 σ ↔ σ ⟨0, hm⟩ = e₀ := by
  unfold SuccP
  simp only [cs_find_iff, decide_eq_true_eq, decide_eq_false_iff_not, max_iff k hk e₀ he₀,
    Nat.zero_le, true_and]
  constructor
  · rintro ⟨t, ⟨_, hs⟩, hte⟩
    have : t = ⟨0, hm⟩ := by
      by_contra hne
      have hlt : (⟨0, hm⟩ : Fin m) < t := by
        rw [Fin.lt_def]; have : t.val ≠ 0 := fun h => hne (Fin.ext h); simp; omega
      exact hs _ hlt (fun u hu => absurd hu (by simp [Fin.lt_def]))
    rw [← this]; exact hte
  · intro h
    refine ⟨⟨0, hm⟩, ⟨fun s hs => absurd hs (by simp [Fin.lt_def]), fun s hs => absurd hs
      (by simp [Fin.lt_def])⟩, h⟩


lemma cs_key_lt {n : ℕ} (v : Fin n → ℝ) (e f : Fin n) :
    (toLex (v e, OrderDual.toDual e) : Lex (ℝ × (Fin n)ᵒᵈ)) < toLex (v f, OrderDual.toDual f) ↔
      better v f e := by
  rw [Prod.Lex.toLex_lt_toLex]
  unfold better
  simp only [OrderDual.toDual_lt_toDual, Fin.lt_def]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1.symm, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1.symm, h2⟩

lemma cs_classical_iff (m : ℕ) (x : Fin m → ℝ × Fin m) (t : Fin m) :
    classicalSecretary m x = some t ↔
      ((Nat.floor ((m : ℝ) / Real.exp 1) ≤ t.val ∧ ∀ s : Fin m, s.val < t.val → betterEntry x t s) ∧
        ∀ s : Fin m, s < t → ¬ (Nat.floor ((m : ℝ) / Real.exp 1) ≤ s.val ∧
          ∀ s' : Fin m, s'.val < s.val → betterEntry x s s')) := by
  unfold classicalSecretary
  simp only
  split_ifs with h
  · have hs := Classical.choose_spec h
    constructor
    · intro he
      simp only [Option.some.injEq] at he
      rw [← he]
      refine ⟨hs.1, fun s hs' hc => ?_⟩
      have := hs.2 s hc
      rw [Fin.lt_def] at hs'
      omega
    · rintro ⟨hc, hmin⟩
      simp only [Option.some.injEq]
      apply le_antisymm
      · exact Fin.le_def.mpr (hs.2 t hc)
      · by_contra hlt
        push_neg at hlt
        exact hmin _ hlt hs.1
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨hc, hmin⟩
    apply h
    refine ⟨t, hc, fun s hcs => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hmin s hlt hcs

theorem cs_core {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    1 / Real.exp 1 ≤
      orderAverage (fun π =>
        if ∃ t : Fin n,
            classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
              valueRank v (π t) = 0 then (1 : ℝ) else 0) := by
  set k : Fin n → Lex (ℝ × (Fin n)ᵒᵈ) := fun e => toLex (v e, OrderDual.toDual e) with hkdef
  have hk : Function.Injective k := by
    intro a b h
    have := congrArg (fun p => OrderDual.ofDual (ofLex p).2) h
    simpa [hkdef] using this
  have hm : 1 ≤ n := hn
  obtain ⟨e₀, _, he₀⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  replace he₀ : ∀ e, k e ≤ k e₀ := fun e => he₀ e (Finset.mem_univ _)
  set r := Nat.floor ((n : ℝ) / Real.exp 1) with hr
  have hsucc : ∀ π : Equiv.Perm (Fin n), (∃ t : Fin n,
            classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
              valueRank v (π t) = 0) ↔ SuccP k r π := by
    intro π
    unfold SuccP
    simp only [cs_find_iff, decide_eq_true_eq, decide_eq_false_iff_not, cs_classical_iff]
    have hbe : ∀ a b : Fin n, betterEntry (fun s => (v (π s), π s)) a b ↔ k (π b) < k (π a) := by
      intro a b
      rw [hkdef]; simp only
      rw [cs_key_lt]
      unfold betterEntry better; simp only
    have hrank : ∀ e : Fin n, valueRank v e = 0 ↔ ∀ f, k f ≤ k e := by
      intro e
      unfold valueRank
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      constructor
      · intro h f
        by_contra hlt
        push_neg at hlt
        exact h (Finset.mem_univ f) ((cs_key_lt v e f).mp hlt)
      · intro h f _ hb
        have := (cs_key_lt v e f).mpr hb
        exact absurd (h f) (not_le.mpr this)
    simp only [hbe, hrank, Fin.lt_def]
    rw [← hr]
  have hfilt : orderAverage (fun π =>
        if ∃ t : Fin n,
            classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
              valueRank v (π t) = 0 then (1 : ℝ) else 0) =
      (1 / (n.factorial : ℝ)) * ((Finset.univ.filter (SuccP k r)).card : ℝ) := by
    unfold orderAverage
    congr 1
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro π _
    by_cases h : SuccP k r π
    · rw [if_pos ((hsucc π).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hsucc π).mp h')), if_neg h]
  rw [hfilt]
  have hmain := an_main n hm r hr
  have hm0 : (0 : ℝ) < n := by exact_mod_cast hm
  have hf0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  by_cases hr0 : r = 0
  · rw [if_pos hr0] at hmain
    have : Finset.univ.filter (SuccP k r) =
        Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ ⟨0, hm⟩ = e₀ := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hr0]; exact SuccP_zero hm k hk e₀ he₀ σ
    rw [this]
    have h := AA_val e₀ ⟨0, hm⟩
    unfold AA at h
    refine hmain.trans (le_of_eq ?_)
    field_simp
    linarith
  · rw [if_neg hr0] at hmain
    have hrm : r ≤ n := by
      have : (r : ℝ) ≤ n := by
        have h1 := Nat.floor_le (show 0 ≤ (n : ℝ) / Real.exp 1 by positivity)
        rw [← hr] at h1
        have : (n : ℝ) / Real.exp 1 ≤ n := div_le_self hm0.le (by
          have := Real.add_one_le_exp (1 : ℝ); linarith)
        linarith
      exact_mod_cast this
    rw [SuccP_count k hk e₀ he₀ r (Nat.one_le_iff_ne_zero.2 hr0) hrm]
    refine hmain.trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : (0 : ℝ) < i := by
      have := (Finset.mem_Ico.1 hi).1
      exact_mod_cast (show 0 < i by omega)
    field_simp


/-! ## goal -/

lemma g_split {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ) (hv : ∀ e, 0 ≤ v e)
    (s : Fin K → Option (Fin n)) (k : Fin K) :
    ∑ i ∈ (Finset.univ.filter (fun e : Fin n => 0 < v e)).image (fun e => valueClass (v e)),
      (if h : ∃ e : Fin n, s k = some e ∧ inClass (v e) i then v (Classical.choose h) * w k else 0)
      = (s k).elim 0 v * w k := by
  rcases hs : s k with _ | e
  · simp only [Option.elim]
    rw [zero_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [dif_neg]
    rintro ⟨e, he, _⟩; exact absurd he (by simp)
  · simp only [Option.elim]
    by_cases hve : 0 < v e
    · rw [Finset.sum_eq_single (valueClass (v e))]
      · have h : ∃ e' : Fin n, some e = some e' ∧ inClass (v e') (valueClass (v e)) :=
          ⟨e, rfl, hve, rfl⟩
        rw [dif_pos h]
        exact congrArg (fun x => v x * w k) (Option.some.inj (Classical.choose_spec h).1).symm
      · intro i _ hi
        rw [dif_neg]
        rintro ⟨e', he', hc⟩
        simp only [Option.some.injEq] at he'
        subst he'
        exact hi hc.2.symm
      · intro hn
        exfalso; apply hn
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hve, rfl⟩
    · have : v e = 0 := le_antisymm (not_lt.mp hve) (hv e)
      rw [this, zero_mul]
      apply Finset.sum_eq_zero
      intro i _
      rw [dif_neg]
      rintro ⟨e', he', hc⟩
      simp only [Option.some.injEq] at he'
      subst he'
      exact hve hc.1

lemma g_opt_some {n K : ℕ} (v : Fin n → ℝ) (k : Fin K) (e : Fin n)
    (h : optimalAssignment v k = some e) : valueRank v e = k.val := by
  unfold optimalAssignment at h
  split_ifs at h with h'
  simp only [Option.some.injEq] at h
  subst h
  exact Classical.choose_spec h'

lemma g_opt_choose {n K : ℕ} (v : Fin n → ℝ) (i : ℤ) (k : Fin K)
    (h : ∃ e : Fin n, optimalAssignment v k = some e ∧ inClass (v e) i) :
    valueRank v (Classical.choose h) = k.val ∧ inClass (v (Classical.choose h)) i :=
  ⟨g_opt_some v k _ (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

lemma g_opt_small {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ) (hK : 0 < K)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w) (i : ℤ)
    (hi : optimalClassCount (K := K) v i ≤ 1) (vmax : ℝ) (hvmax : ∀ e, v e ≤ vmax)
    (hv0 : 0 ≤ vmax) :
    optimalClassValue v w i ≤ w ⟨0, hK⟩ * min vmax ((2 : ℝ) ^ (i : ℝ)) := by
  set O : Finset (Fin n) := Finset.univ.filter (fun e => valueRank v e < K ∧ inClass (v e) i)
    with hO
  have hu : optimalClassCount (K := K) v i = O.card := by unfold optimalClassCount; rfl
  rw [hu] at hi
  have hw0 : ∀ k : Fin K, w k ≤ w ⟨0, hK⟩ := fun k => hmono (Fin.le_def.mpr (Nat.zero_le _))
  have hmin0 : 0 ≤ min vmax ((2 : ℝ) ^ (i : ℝ)) := le_min hv0 (by positivity)
  have hmem : ∀ k : Fin K, ∀ h : ∃ e : Fin n, optimalAssignment v k = some e ∧ inClass (v e) i,
      Classical.choose h ∈ O := by
    intro k h
    obtain ⟨h1, h2⟩ := g_opt_choose v i k h
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [h1]; exact k.isLt, h2⟩
  rcases Finset.eq_empty_or_nonempty O with hE | ⟨e1, he1⟩
  · have : optimalClassValue v w i = 0 := by
      unfold optimalClassValue
      apply Finset.sum_eq_zero
      intro k _
      rw [dif_neg]
      intro h
      have := hmem k h
      rw [hE] at this; simp at this
    rw [this]; exact mul_nonneg (hw _) hmin0
  · have hOs : ∀ e ∈ O, e = e1 := fun e he => Finset.card_le_one.mp hi e he e1 he1
    have he1' := he1
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at he1'
    unfold optimalClassValue
    have hterm : ∀ k : Fin K, (if h : ∃ e : Fin n, optimalAssignment v k = some e ∧ inClass (v e) i
        then v (Classical.choose h) * w k else 0) ≤
        if (⟨valueRank v e1, he1'.1⟩ : Fin K) = k then v e1 * w ⟨0, hK⟩ else 0 := by
      intro k
      split_ifs with h hk hk
      · rw [hOs _ (hmem k h)]
        exact mul_le_mul_of_nonneg_left (hw0 k) (hv e1)
      · exfalso; apply hk
        have h1 := (g_opt_choose v i k h).1
        rw [hOs _ (hmem k h)] at h1
        exact Fin.ext h1
      · exact mul_nonneg (hv e1) (hw _)
      · exact le_rfl
    refine le_trans (Finset.sum_le_sum (fun k _ => hterm k)) ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (hw _)
    exact le_min (hvmax e1) (rc_class_bounds he1'.2).2.le

lemma g_geom (S : Finset ℤ) (a : ℤ) (hS : ∀ i ∈ S, i < a) :
    ∑ i ∈ S, (2 : ℝ) ^ (i : ℝ) ≤ (2 : ℝ) ^ (a : ℝ) := by
  simp only [Real.rpow_intCast]
  let j : ℤ → ℕ := fun i => (a - 1 - i).toNat
  have hj : ∀ i ∈ S, (2 : ℝ) ^ i = (2 : ℝ) ^ a / 2 * (1 / 2 : ℝ) ^ (j i) := by
    intro i hi
    have hai := hS i hi
    have : i = a - 1 - ((j i : ℕ) : ℤ) := by simp only [j]; omega
    conv_lhs => rw [this]
    rw [zpow_sub₀ (by norm_num), zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]
    rw [one_div_pow]; field_simp
  rw [Finset.sum_congr rfl hj, ← Finset.mul_sum]
  have hinj : Set.InjOn j S := by
    intro x hx y hy hxy
    simp only [j] at hxy
    have := hS x hx; have := hS y hy
    omega
  rw [← Finset.sum_image (f := fun t => (1 / 2 : ℝ) ^ t) hinj]
  obtain ⟨N, hN⟩ : ∃ N, S.image j ⊆ Finset.range N := by
    refine ⟨(S.image j).sup id + 1, fun x hx => ?_⟩
    simp only [Finset.mem_range]
    have := Finset.le_sup (f := id) hx
    simp only [id] at this; omega
  have h1 : ∑ t ∈ S.image j, (1 / 2 : ℝ) ^ t ≤ ∑ t ∈ Finset.range N, (1 / 2 : ℝ) ^ t :=
    Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
  have h2 := sum_geometric_two_le N
  have hpos : (0 : ℝ) < (2 : ℝ) ^ a / 2 := by positivity
  calc (2 : ℝ) ^ a / 2 * ∑ t ∈ S.image j, (1 / 2 : ℝ) ^ t ≤ (2 : ℝ) ^ a / 2 * 2 :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hpos.le
    _ = (2 : ℝ) ^ a := by ring

lemma g_small_sum (CL : Finset ℤ) (vmax : ℝ) (istar : ℤ) (hv0 : 0 ≤ vmax)
    (hb : (2 : ℝ) ^ ((istar : ℝ) - 1) ≤ vmax) (hCL : ∀ i ∈ CL, i ≤ istar) :
    ∑ i ∈ CL, min vmax ((2 : ℝ) ^ (i : ℝ)) ≤ 3 * vmax := by
  rw [← Finset.sum_filter_add_sum_filter_not CL (fun i => i < istar)]
  have h1 : ∑ i ∈ CL.filter (fun i => i < istar), min vmax ((2 : ℝ) ^ (i : ℝ)) ≤ 2 * vmax := by
    refine le_trans (Finset.sum_le_sum (fun i _ => min_le_right _ _)) ?_
    refine le_trans (g_geom _ istar (fun i hi => (Finset.mem_filter.mp hi).2)) ?_
    have := Real.rpow_add (show (0 : ℝ) < 2 by norm_num) 1 ((istar : ℝ) - 1)
    rw [Real.rpow_one, show (1 : ℝ) + ((istar : ℝ) - 1) = istar by ring] at this
    rw [this]; linarith
  have h2 : ∑ i ∈ CL.filter (fun i => ¬ i < istar), min vmax ((2 : ℝ) ^ (i : ℝ)) ≤ vmax := by
    have hsub : CL.filter (fun i => ¬ i < istar) ⊆ {istar} := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      have := hCL i hi.1
      simp only [Finset.mem_singleton]; omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => le_min hv0 (by positivity))) ?_
    simp
  linarith

lemma g_sec {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ e, 0 ≤ v e) (e0 : Fin n)
    (he0 : ∀ e, v e ≤ v e0) :
    v e0 / Real.exp 1 ≤ expectedSecretaryValue v := by
  have hcs := cs_core hn v
  unfold expectedSecretaryValue
  have hpt : ∀ π : Equiv.Perm (Fin n), v e0 * (if ∃ t : Fin n,
        classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
          valueRank v (π t) = 0 then (1 : ℝ) else 0) ≤
      ((classicalSecretary n (fun t => (v (π t), π t))).map (fun t => v (π t))).getD 0 := by
    intro π
    split_ifs with h
    · obtain ⟨t, ht, hr⟩ := h
      rw [ht]; simp only [Option.map_some, Option.getD_some, mul_one]
      by_contra hlt
      push_neg at hlt
      unfold valueRank at hr
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hr
      exact hr (Finset.mem_univ e0) (Or.inl hlt)
    · rw [mul_zero]
      rcases classicalSecretary n (fun t => (v (π t), π t)) with _ | t
      · simp
      · simp [hv]
  unfold orderAverage at hcs ⊢
  have hle : v e0 * ((1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), (if ∃ t : Fin n,
        classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
          valueRank v (π t) = 0 then (1 : ℝ) else 0)) ≤ (1 / (n.factorial : ℝ)) *
      ∑ π : Equiv.Perm (Fin n),
        ((classicalSecretary n (fun t => (v (π t), π t))).map (fun t => v (π t))).getD 0 := by
    rw [mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun π _ => hpt π)
  refine le_trans ?_ hle
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hcs (le_trans (hv e0) le_rfl)

theorem g_core {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hK : 0 < K) (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k)
    (hmono : Antitone w) :
    OPT v w ≤ (8 + 3 * Real.exp 1) * expectedAlgorithmA v w hK := by
  set CL := (Finset.univ.filter (fun e : Fin n => 0 < v e)).image (fun e => valueClass (v e))
    with hCL
  set E := Real.exp 1 with hE
  have hEpos : 0 < E := Real.exp_pos 1
  have hA : (8 + 3 * E) * expectedAlgorithmA v w hK =
      8 * expectedReservationValue v w + 3 * E * w ⟨0, hK⟩ * expectedSecretaryValue v := by
    unfold expectedAlgorithmA
    simp only
    rw [← hE]
    have : 3 * E + 8 ≠ 0 := by linarith
    field_simp
    ring
  rw [hA]
  -- OPT decomposition
  have hOPT : OPT v w = ∑ i ∈ CL, optimalClassValue v w i := by
    unfold OPT assignmentValue optimalClassValue
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact (g_split v w hv (optimalAssignment v) k).symm
  -- reservation decomposition
  have hR0 : ∀ π τ i, 0 ≤ reservedClassValue v w π τ i := by
    intro π τ i
    unfold reservedClassValue
    apply Finset.sum_nonneg; intro k _
    split_ifs
    · exact mul_nonneg (hv _) (hw _)
    · exact le_rfl
  set CL' := CL.filter (fun i => 2 ≤ optimalClassCount (K := K) v i) with hCL'
  have hRes : ∑ i ∈ CL', expectedReservedClassValue v w i ≤ expectedReservationValue v w := by
    have h1 : ∑ i ∈ CL', expectedReservedClassValue v w i =
        acEx (fun π τ => ∑ i ∈ CL', reservedClassValue v w π τ i) := by
      rw [acEx_sum]; rfl
    rw [h1]
    have h2 : expectedReservationValue v w =
        acEx (fun π τ => assignmentValue v w (reservationAssignment (K := K) v π τ)) := rfl
    rw [h2]
    apply acEx_mono
    intro π τ
    have h3 : assignmentValue v w (reservationAssignment (K := K) v π τ) =
        ∑ i ∈ CL, reservedClassValue v w π τ i := by
      unfold assignmentValue reservedClassValue
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact (g_split v w hv (reservationAssignment (K := K) v π τ) k).symm
    rw [h3]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hR0 π τ i)
  have hSec0 : 0 ≤ expectedSecretaryValue v := by
    unfold expectedSecretaryValue orderAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro π _
    rcases classicalSecretary n (fun t => (v (π t), π t)) with _ | t
    · simp
    · simp [hv]
  have hw0 := hw ⟨0, hK⟩
  rw [hOPT, ← Finset.sum_filter_add_sum_filter_not CL (fun i => 2 ≤ optimalClassCount (K := K) v i)]
  rw [← hCL']
  have hbig : ∑ i ∈ CL', optimalClassValue v w i ≤ 8 * expectedReservationValue v w := by
    have hb : ∀ i ∈ CL', optimalClassValue v w i ≤ 8 * expectedReservedClassValue v w i := by
      intro i hi
      have := rc_core v w hv hw hmono i (Finset.mem_filter.mp hi).2
      linarith
    calc ∑ i ∈ CL', optimalClassValue v w i ≤ ∑ i ∈ CL', 8 * expectedReservedClassValue v w i :=
          Finset.sum_le_sum hb
      _ = 8 * ∑ i ∈ CL', expectedReservedClassValue v w i := by rw [Finset.mul_sum]
      _ ≤ 8 * expectedReservationValue v w := by linarith
  have hResNN : 0 ≤ expectedReservationValue v w := by
    have := acEx_mono (fun _ _ => (0 : ℝ))
      (fun π τ => assignmentValue v w (reservationAssignment (K := K) v π τ)) (by
        intro π τ
        unfold assignmentValue
        apply Finset.sum_nonneg; intro k _
        apply mul_nonneg _ (hw k)
        rcases reservationAssignment (K := K) v π τ k with _ | e
        · simp
        · simp [hv])
    rw [acEx_zero] at this; exact this
  -- small classes
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have : CL = ∅ := by rw [hCL]; simp
    have hCL'e : CL' = ∅ := by rw [hCL', this, Finset.filter_empty]
    rw [hCL'e, this, Finset.filter_empty, Finset.sum_empty]
    have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * E) hw0) hSec0
    linarith
  obtain ⟨e0, _, he0⟩ := Finset.exists_max_image Finset.univ v ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
  replace he0 : ∀ e, v e ≤ v e0 := fun e => he0 e (Finset.mem_univ _)
  have hv0 : 0 ≤ v e0 := hv e0
  have hsmall : ∑ i ∈ CL.filter (fun i => ¬ 2 ≤ optimalClassCount (K := K) v i),
      optimalClassValue v w i ≤ w ⟨0, hK⟩ * (3 * v e0) := by
    refine le_trans (Finset.sum_le_sum (fun i hi => g_opt_small v w hK hv hw hmono i
      (by have := (Finset.mem_filter.mp hi).2; omega) (v e0) he0 hv0)) ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hw0
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => le_min hv0 (by positivity))) ?_
    rcases Finset.eq_empty_or_nonempty CL with hCe | hCne
    · rw [hCe]; simp; linarith
    · obtain ⟨i0, hi0⟩ := hCne
      have hpos : 0 < v e0 := by
        rw [hCL] at hi0
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi0
        obtain ⟨e, he, _⟩ := hi0
        exact lt_of_lt_of_le he (he0 e)
      apply g_small_sum CL (v e0) (valueClass (v e0)) hv0
      · exact (rc_class_bounds (i := valueClass (v e0)) ⟨hpos, rfl⟩).1
      · intro i hi
        rw [hCL] at hi
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨e, he, rfl⟩ := hi
        exact rs_class_mono he (he0 e)
  have hsec := g_sec hnpos v hv e0 he0
  have : v e0 ≤ E * expectedSecretaryValue v := by
    rw [div_le_iff₀ hEpos] at hsec; linarith
  have : w ⟨0, hK⟩ * (3 * v e0) ≤ 3 * E * w ⟨0, hK⟩ * expectedSecretaryValue v := by
    nlinarith
  linarith

end SecretaryWD.Weighted

open SecretaryWD.Weighted


theorem solution {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hK : 0 < K) (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k)
    (hmono : Antitone w) :
    OPT v w ≤ (8 + 3 * Real.exp 1) * expectedAlgorithmA v w hK := by
  exact g_core v w hK hv hw hmono
