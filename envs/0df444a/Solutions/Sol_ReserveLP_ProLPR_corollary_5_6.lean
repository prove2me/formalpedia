-- Prove2me | solution 1 for ReserveLP.ProLPR.corollary_5_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:30:32.456089+00:00
-- url     : https://prove2.me/submissions/500215a7-2ffa-4bdd-a54a-282aeff34dcb

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

open ReserveLP.ProLPR Finset

noncomputable def rlpSS {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ) : ℝ :=
  ∑ b ∈ U, c b * ∏ b' ∈ U.erase b, f b'

theorem rlpSS_insert {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ) (b : ι)
    (hb : b ∉ U) : rlpSS (insert b U) f c = rlpSS U f c * f b + c b * ∏ b' ∈ U, f b' := by
  unfold rlpSS
  rw [sum_insert hb, erase_insert hb, sum_mul, add_comm]
  congr 1
  refine sum_congr rfl fun b' hb' => ?_
  have hne : b' ≠ b := fun h => hb (h ▸ hb')
  rw [erase_insert_of_ne (Ne.symm hne), prod_insert (fun h => hb (mem_of_mem_erase h))]
  ring

theorem rlpSS_congr {ι : Type} [DecidableEq ι] (U : Finset ι) (f c f' c' : ι → ℝ)
    (hf : ∀ b ∈ U, f b = f' b) (hc : ∀ b ∈ U, c b = c' b) : rlpSS U f c = rlpSS U f' c' := by
  unfold rlpSS
  refine sum_congr rfl fun b hb => ?_
  rw [hc b hb, prod_congr rfl fun b' hb' => hf b' (mem_of_mem_erase hb')]

theorem rlpSS_union {ι : Type} [DecidableEq ι] (U V : Finset ι) (f c : ι → ℝ)
    (h : Disjoint U V) :
    rlpSS (U ∪ V) f c = rlpSS U f c * ∏ b ∈ V, f b + rlpSS V f c * ∏ b ∈ U, f b := by
  induction V using Finset.induction_on with
  | empty => simp [rlpSS]
  | insert b V hb ih =>
    have hbU : b ∉ U := fun hm => (disjoint_left.mp h) hm (mem_insert_self _ _)
    have hd : Disjoint U V := h.mono_right (subset_insert _ _)
    have hbUV : b ∉ U ∪ V := by simp [hbU, hb]
    rw [union_insert, rlpSS_insert _ _ _ _ hbUV, ih hd, rlpSS_insert _ _ _ _ hb,
      prod_insert hb, prod_union hd]
    ring

theorem rlpSS_const {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ) (φ γ : ℝ)
    (hf : ∀ b ∈ U, f b = φ) (hc : ∀ b ∈ U, c b = γ) :
    rlpSS U f c = U.card * γ * φ ^ (U.card - 1) := by
  unfold rlpSS
  rw [sum_congr rfl (fun b hb => by
    rw [hc b hb, prod_congr rfl (fun b' hb' => hf b' (mem_of_mem_erase hb')), prod_const,
      card_erase_of_mem hb])]
  simp [sum_const]; ring

/-- Splitting the objective along two coordinates. -/
theorem fobj_split {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) (k t : Fin n) (hkt : k ≠ t) :
    Fobj x θ = Real.exp (θ - 1) *
      ((∏ i ∈ (univ.erase k).erase t, (1 - x i) +
          rlpSS ((univ.erase k).erase t) (fun i => 1 - x i) x) * (1 - x k) * (1 - x t) +
        (∏ i ∈ (univ.erase k).erase t, (1 - x i)) * (x t * (1 - x k) + x k * (1 - x t))) := by
  set W := (univ.erase k).erase t with hW
  have htW : t ∉ W := by simp [hW]
  have hkW : k ∉ insert t W := by simp [hW, hkt]
  have huniv : (univ : Finset (Fin n)) = insert k (insert t W) := by
    rw [hW, insert_erase (mem_erase.mpr ⟨Ne.symm hkt, mem_univ t⟩), insert_erase (mem_univ k)]
  unfold Fobj
  have hS : ∑ i, x i * ∏ j ∈ univ.erase i, (1 - x j) = rlpSS univ (fun i => 1 - x i) x := rfl
  rw [hS, huniv, prod_insert hkW, prod_insert htW, rlpSS_insert _ _ _ _ hkW,
    rlpSS_insert _ _ _ _ htW, prod_insert htW]
  ring

theorem fobj_pair {n : ℕ} (x y : Fin n → ℝ) (θ : ℝ) (k t : Fin n) (hkt : k ≠ t)
    (hag : ∀ i, i ≠ k → i ≠ t → y i = x i) (hs : y k + y t = x k + x t) :
    Fobj y θ - Fobj x θ = Real.exp (θ - 1) *
      (rlpSS ((univ.erase k).erase t) (fun i => 1 - x i) x -
        ∏ i ∈ (univ.erase k).erase t, (1 - x i)) * (y k * y t - x k * x t) := by
  have hW : ∀ i ∈ (univ.erase k).erase t, y i = x i := by
    intro i hi
    simp only [mem_erase] at hi
    exact hag i hi.2.1 hi.1
  have hP : ∏ i ∈ (univ.erase k).erase t, (1 - y i) = ∏ i ∈ (univ.erase k).erase t, (1 - x i) :=
    prod_congr rfl fun i hi => by rw [hW i hi]
  have hR : rlpSS ((univ.erase k).erase t) (fun i => 1 - y i) y =
      rlpSS ((univ.erase k).erase t) (fun i => 1 - x i) x :=
    rlpSS_congr _ _ _ _ _ (fun i hi => by simp only [hW i hi]) hW
  rw [fobj_split y θ k t hkt, fobj_split x θ k t hkt, hP, hR]
  linear_combination (Real.exp (θ - 1)) *
    (-(rlpSS ((univ.erase k).erase t) (fun i => 1 - x i) x)) * hs

theorem sum_split2 {n : ℕ} (w : Fin n → ℝ) (k t : Fin n) (hkt : k ≠ t) :
    ∑ i, w i = w k + (w t + ∑ i ∈ (univ.erase k).erase t, w i) := by
  have htW : t ∉ (univ.erase k).erase t := by simp
  have hkW : k ∉ insert t ((univ.erase k).erase t) := by simp [hkt]
  have huniv : (univ : Finset (Fin n)) = insert k (insert t ((univ.erase k).erase t)) := by
    rw [insert_erase (mem_erase.mpr ⟨Ne.symm hkt, mem_univ t⟩), insert_erase (mem_univ k)]
  conv_lhs => rw [huniv]
  rw [sum_insert hkW, sum_insert htW]

/-- Perturbing two coordinates of a feasible point keeping their sum. -/
theorem feas_pair {n : ℕ} (θ : ℝ) (x : Fin n → ℝ) (hx : OPTFeasible n θ x) (k t : Fin n)
    (hkt : k ≠ t) (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ θ) (hb : 0 ≤ b) (hb' : b ≤ θ)
    (hab : a + b = x k + x t) :
    OPTFeasible n θ (fun i => if i = k then a else if i = t then b else x i) := by
  obtain ⟨h0, hsum, hle⟩ := hx
  refine ⟨fun i => ?_, ?_, fun i => ?_⟩
  · dsimp only; split_ifs
    · exact ha
    · exact hb
    · exact h0 i
  · rw [sum_split2 _ k t hkt]
    rw [sum_split2 _ k t hkt] at hsum
    have hW : ∑ i ∈ (univ.erase k).erase t, (if i = k then a else if i = t then b else x i) =
        ∑ i ∈ (univ.erase k).erase t, x i := by
      refine sum_congr rfl fun i hi => ?_
      simp only [mem_erase] at hi
      rw [if_neg hi.2.1, if_neg hi.1]
    rw [hW]
    rw [if_pos rfl, if_neg (Ne.symm hkt), if_pos rfl]
    linarith
  · dsimp only; split_ifs
    · exact ha'
    · exact hb'
    · exact hle i

noncomputable def cntB (n : ℕ) (θ : ℝ) (z : Fin n → ℝ) : ℕ :=
  (univ.filter (fun i => z i = 0 ∨ z i = θ)).card

theorem no_two_interior (n : ℕ) (θ : ℝ) (z : Fin n → ℝ) (hz : OPTFeasible n θ z)
    (hmax : ∀ y, OPTFeasible n θ y → Fobj y θ ≤ Fobj z θ)
    (hcnt : ∀ y, OPTFeasible n θ y → (∀ w, OPTFeasible n θ w → Fobj w θ ≤ Fobj y θ) →
      cntB n θ y ≤ cntB n θ z)
    (k t : Fin n) (ht0 : 0 < z t) (htk : z t < z k) (hkθ : z k < θ) : False := by
  have hkt : k ≠ t := fun h => by rw [h] at htk; exact lt_irrefl _ htk
  set D := rlpSS ((univ.erase k).erase t) (fun i => 1 - z i) z -
    ∏ i ∈ (univ.erase k).erase t, (1 - z i) with hD
  have he := Real.exp_pos (θ - 1)
  by_cases hDpos : 0 < D
  · let y : Fin n → ℝ := fun i =>
      if i = k then (z k + z t) / 2 else if i = t then (z k + z t) / 2 else z i
    have hyk : y k = (z k + z t) / 2 := by simp [y]
    have hyt : y t = (z k + z t) / 2 := by simp [y, Ne.symm hkt]
    have hy : OPTFeasible n θ y :=
      feas_pair θ z hz k t hkt _ _ (by linarith) (by linarith) (by linarith) (by linarith)
        (by ring)
    have hdiff := fobj_pair z y θ k t hkt
      (fun i hik hit => by simp only [y, if_neg hik, if_neg hit])
      (by rw [hyk, hyt]; ring)
    rw [hyk, hyt, ← hD] at hdiff
    have hpos : 0 < (z k + z t) / 2 * ((z k + z t) / 2) - z k * z t := by
      have : (z k + z t) / 2 * ((z k + z t) / 2) - z k * z t = (z k - z t) ^ 2 / 4 := by ring
      rw [this]; have : 0 < z k - z t := by linarith
      positivity
    have := hmax y hy
    have : 0 < Real.exp (θ - 1) * D * ((z k + z t) / 2 * ((z k + z t) / 2) - z k * z t) := by
      positivity
    linarith
  · push_neg at hDpos
    set δ := min (θ - z k) (z t)
    have hδ1 : δ ≤ θ - z k := min_le_left _ _
    have hδ2 : δ ≤ z t := min_le_right _ _
    have hδ0 : 0 < δ := lt_min (by linarith) ht0
    let y : Fin n → ℝ := fun i => if i = k then z k + δ else if i = t then z t - δ else z i
    have hyk : y k = z k + δ := by simp [y]
    have hyt : y t = z t - δ := by simp [y, Ne.symm hkt]
    have hy : OPTFeasible n θ y :=
      feas_pair θ z hz k t hkt _ _ (by linarith) (by linarith) (by linarith) (by linarith)
        (by ring)
    have hdiff := fobj_pair z y θ k t hkt
      (fun i hik hit => by simp only [y, if_neg hik, if_neg hit])
      (by rw [hyk, hyt]; ring)
    rw [hyk, hyt, ← hD] at hdiff
    have hprod : (z k + δ) * (z t - δ) - z k * z t ≤ 0 := by
      have : (z k + δ) * (z t - δ) - z k * z t = -(δ * (z k - z t)) - δ ^ 2 := by ring
      rw [this]
      have : 0 < δ * (z k - z t) := mul_pos hδ0 (by linarith)
      nlinarith
    have hge : 0 ≤ Real.exp (θ - 1) * D * ((z k + δ) * (z t - δ) - z k * z t) :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos he.le hDpos) hprod
    have hymax : ∀ w, OPTFeasible n θ w → Fobj w θ ≤ Fobj y θ :=
      fun w hw => (hmax w hw).trans (by linarith)
    have h1 := hcnt y hy hymax
    have hsub : univ.filter (fun i => z i = 0 ∨ z i = θ) ⊆
        univ.filter (fun i => y i = 0 ∨ y i = θ) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      have hik : i ≠ k := by rintro rfl; rcases hi with h | h <;> linarith
      have hit : i ≠ t := by rintro rfl; rcases hi with h | h <;> linarith
      simp only [y, if_neg hik, if_neg hit]; exact hi
    have hss : univ.filter (fun i => z i = 0 ∨ z i = θ) ⊂
        univ.filter (fun i => y i = 0 ∨ y i = θ) := by
      rw [ssubset_iff_of_subset hsub]
      rcases min_choice (θ - z k) (z t) with h | h
      · refine ⟨k, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and, hyk]
          right; rw [show δ = θ - z k from h]; ring
        · simp only [mem_filter, mem_univ, true_and, not_or]; constructor <;> intro h' <;> linarith
      · refine ⟨t, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and, hyt]
          left; rw [show δ = z t from h]; ring
        · simp only [mem_filter, mem_univ, true_and, not_or]; constructor <;> intro h' <;> linarith
    have h2 := card_lt_card hss
    unfold cntB at h1
    omega

theorem case_bound (θ v M : ℝ) (m j : ℕ) (hθ0 : 0 < θ) (hs : (m : ℝ) * θ + j * v = 2 * θ)
    (hvI : 0 < j → 0 < v ∧ v < θ)
    (hM : ∀ k : ℕ, 2 ≤ k → OPT1 θ k ≤ M ∧ OPT2 θ k ≤ M) :
    Real.exp (θ - 1) * ((1 - θ) ^ m * (1 - v) ^ j +
      (m * θ * (1 - θ) ^ (m - 1) * (1 - v) ^ j + j * v * (1 - v) ^ (j - 1) * (1 - θ) ^ m)) ≤ M := by
  have hjv : 0 ≤ (j : ℝ) * v := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h]; simp
    · have := (hvI h).1; positivity
  -- case analysis on m
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with hm0 | hm1 | hm2 | hm3
  · -- m = 0 : j ≥ 3, v = 2θ/j
    rw [hm0] at hs ⊢
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h] at hs; simp at hs; linarith
      · exact h
    obtain ⟨hv0, hvθ⟩ := hvI hjpos
    have hj3 : 3 ≤ j := by
      by_contra hcon
      have : (j : ℝ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by omega)
      simp at hs
      nlinarith
    have hjR : (j : ℝ) ≠ 0 := by positivity
    have hvj : v = 2 * θ / j := by field_simp; simp at hs; linarith
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have := (hM (j' + 1) (by omega)).1
    unfold OPT1 at this
    rw [← hvj] at this
    simp only [Nat.add_sub_cancel] at this ⊢
    refine le_trans (le_of_eq ?_) this
    simp only [CharP.cast_eq_zero, zero_mul, pow_zero, one_mul, zero_add, mul_one]
    rw [pow_succ]
    simp at hs
    have : ((j' + 1 : ℕ) : ℝ) * v = 2 * θ := by push_cast; linarith
    push_cast at this ⊢
    linear_combination (Real.exp (θ - 1) * (1 - v) ^ j') * this
  · -- m = 1 : j ≥ 2, v = θ/j
    rw [hm1] at hs ⊢
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h] at hs; simp at hs; linarith
      · exact h
    obtain ⟨hv0, hvθ⟩ := hvI hjpos
    have hj2 : 2 ≤ j := by
      by_contra hcon
      have : j = 1 := by omega
      rw [this] at hs; simp at hs; linarith
    have hjR : (j : ℝ) ≠ 0 := by positivity
    have hvj : v = θ / j := by field_simp; simp at hs; linarith
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have := (hM (j' + 1) hj2).2
    unfold OPT2 at this
    rw [← hvj] at this
    simp only [Nat.add_sub_cancel] at this ⊢
    refine le_trans (le_of_eq ?_) this
    simp at hs
    have hh : ((j' + 1 : ℕ) : ℝ) * v = θ := by push_cast; linarith
    push_cast at hh ⊢
    rw [pow_succ, hh]; ring
  · -- m = 2 : j = 0
    rw [hm2] at hs ⊢
    have hj0 : j = 0 := by
      by_contra hcon
      have := (hvI (Nat.pos_of_ne_zero hcon)).1
      have : (0:ℝ) < j * v := by
        have : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hcon
        positivity
      push_cast at hs; linarith
    rw [hj0]
    have := (hM 2 le_rfl).1
    unfold OPT1 at this
    refine le_trans (le_of_eq ?_) this
    norm_num
    ring
  · -- m ≥ 3 impossible
    exfalso
    have : (3:ℝ) ≤ m := by exact_mod_cast hm3
    nlinarith

theorem structured_le (n : ℕ) (θ : ℝ) (z : Fin n → ℝ) (hθ0 : 0 < θ) (hz : OPTFeasible n θ z)
    (heq : ∀ i j, 0 < z i → z i < θ → 0 < z j → z j < θ → z i = z j) (M : ℝ)
    (hM : ∀ k : ℕ, 2 ≤ k → OPT1 θ k ≤ M ∧ OPT2 θ k ≤ M) : Fobj z θ ≤ M := by
  classical
  obtain ⟨h0, hsum, hle⟩ := hz
  set Z := univ.filter (fun i => z i = 0) with hZ
  set Th := univ.filter (fun i => z i = θ) with hTh
  set I := univ.filter (fun i => 0 < z i ∧ z i < θ) with hI
  set v : ℝ := if h : I.Nonempty then z h.choose else 0 with hv
  have hIv : ∀ i ∈ I, z i = v := by
    intro i hi
    have hne : I.Nonempty := ⟨i, hi⟩
    rw [hv, dif_pos hne]
    have h1 := (mem_filter.mp hi).2
    have h2 := (mem_filter.mp hne.choose_spec).2
    exact heq _ _ h1.1 h1.2 h2.1 h2.2
  have hvI : I.Nonempty → 0 < v ∧ v < θ := by
    intro hne
    obtain ⟨i, hi⟩ := hne
    rw [← hIv i hi]; exact (mem_filter.mp hi).2
  have huniv : (univ : Finset (Fin n)) = Z ∪ (Th ∪ I) := by
    ext i
    simp only [hZ, hTh, hI, mem_univ, mem_union, mem_filter, true_and, true_iff]
    rcases (h0 i).lt_or_eq with h | h
    · rcases (hle i).lt_or_eq with h' | h'
      · exact Or.inr (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl h')
    · exact Or.inl h.symm
  have hd1 : Disjoint Th I := by
    rw [disjoint_left]; intro i hi hi'
    have := (mem_filter.mp hi).2; have := (mem_filter.mp hi').2; linarith
  have hd2 : Disjoint Z (Th ∪ I) := by
    rw [disjoint_left]; intro i hi hi'
    have h1 := (mem_filter.mp hi).2
    rcases mem_union.mp hi' with h | h
    · have := (mem_filter.mp h).2; linarith
    · have := (mem_filter.mp h).2; linarith
  have hprod : ∏ i, (1 - z i) = (1 - θ) ^ Th.card * (1 - v) ^ I.card := by
    rw [huniv, prod_union hd2, prod_union hd1,
      prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2] : ∀ i ∈ Z, 1 - z i = 1 - 0),
      prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2] : ∀ i ∈ Th, 1 - z i = 1 - θ),
      prod_congr rfl (fun i hi => by rw [hIv i hi] : ∀ i ∈ I, 1 - z i = 1 - v)]
    simp [prod_const]
  have hSS : rlpSS univ (fun i => 1 - z i) z =
      Th.card * θ * (1 - θ) ^ (Th.card - 1) * (1 - v) ^ I.card + I.card * v * (1 - v) ^ (I.card - 1) * (1 - θ) ^ Th.card := by
    rw [huniv, rlpSS_union _ _ _ _ hd2, rlpSS_union _ _ _ _ hd1,
      rlpSS_const Z _ _ 1 0 (fun i hi => by simp [(mem_filter.mp hi).2])
        (fun i hi => (mem_filter.mp hi).2),
      rlpSS_const Th _ _ (1 - θ) θ (fun i hi => by simp [(mem_filter.mp hi).2])
        (fun i hi => (mem_filter.mp hi).2),
      rlpSS_const I _ _ (1 - v) v (fun i hi => by simp [hIv i hi]) hIv,
      prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2] : ∀ i ∈ Th, 1 - z i = 1 - θ),
      prod_congr rfl (fun i hi => by rw [hIv i hi] : ∀ i ∈ I, 1 - z i = 1 - v),
      prod_union hd1,
      prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2] : ∀ i ∈ Th, 1 - z i = 1 - θ),
      prod_congr rfl (fun i hi => by rw [hIv i hi] : ∀ i ∈ I, 1 - z i = 1 - v),
      prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2] : ∀ i ∈ Z, 1 - z i = 1 - 0)]
    simp [prod_const]
  have hsz : ∑ i, z i = Th.card * θ + I.card * v := by
    rw [huniv, sum_union hd2, sum_union hd1,
      sum_congr rfl (fun i hi => (mem_filter.mp hi).2 : ∀ i ∈ Z, z i = 0),
      sum_congr rfl (fun i hi => (mem_filter.mp hi).2 : ∀ i ∈ Th, z i = θ),
      sum_congr rfl hIv]
    simp [sum_const]
  have hs : (Th.card : ℝ) * θ + I.card * v = 2 * θ := by rw [← hsz]; linarith
  have hF : Fobj z θ = Real.exp (θ - 1) * ((1 - θ) ^ Th.card * (1 - v) ^ I.card +
      (Th.card * θ * (1 - θ) ^ (Th.card - 1) * (1 - v) ^ I.card + I.card * v * (1 - v) ^ (I.card - 1) * (1 - θ) ^ Th.card)) := by
    rw [← hprod, ← hSS]; rfl
  rw [hF]
  exact case_bound θ v M Th.card I.card hθ0 hs
    (fun h => hvI (card_pos.mp h)) hM

theorem solution (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (M : ℝ)
    (hM : ∀ k : ℕ, 2 ≤ k → OPT1 θ k ≤ M ∧ OPT2 θ k ≤ M) :
    OPT n θ ≤ M := by
  classical
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hM0 : 0 ≤ M := by
    refine le_trans ?_ (hM 2 le_rfl).1
    unfold OPT1
    have : 0 ≤ 1 - 2 * θ / (2:ℕ) := by push_cast; linarith
    have : 0 ≤ 1 - 2 * θ / (2:ℕ) + 2 * θ := by linarith
    positivity
  unfold OPT
  apply Real.sSup_le _ hM0
  rintro _ ⟨x, hx, rfl⟩
  rcases hθ0.lt_or_eq with hθpos | hθz
  swap
  · -- θ = 0
    subst hθz
    have hx0 : ∀ i, x i = 0 := fun i => le_antisymm (hx.2.2 i) (hx.1 i)
    refine le_trans (le_of_eq ?_) (hM 2 le_rfl).1
    simp [Fobj, OPT1, hx0]
  -- θ > 0 : take a maximizer with the largest number of boundary coordinates
  let K : Set (Fin n → ℝ) := {y | OPTFeasible n θ y}
  have hKc : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := θ))
    · simp only [K, OPTFeasible, Set.ofPred_and, Set.ofPred_forall]
      refine IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop))
        (IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
          (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const))
    · intro y hy i _
      exact ⟨hy.1 i, hy.2.2 i⟩
  have hcont : Continuous fun y : Fin n → ℝ => Fobj y θ := by
    unfold Fobj; fun_prop
  obtain ⟨xm, hxmK, hxm⟩ := hKc.exists_isMaxOn ⟨x, hx⟩ hcont.continuousOn
  let Mx : (Fin n → ℝ) → Prop := fun z => OPTFeasible n θ z ∧
    ∀ y, OPTFeasible n θ y → Fobj y θ ≤ Fobj z θ
  have hxmM : Mx xm := ⟨hxmK, fun y hy => hxm hy⟩
  have hcle : ∀ z, cntB n θ z < n + 1 := by
    intro z; unfold cntB
    have := card_filter_le (univ : Finset (Fin n)) (fun i => z i = 0 ∨ z i = θ)
    simp at this; omega
  let C := (range (n + 1)).filter (fun c => ∃ z, Mx z ∧ cntB n θ z = c)
  have hC : C.Nonempty := ⟨cntB n θ xm, mem_filter.mpr ⟨mem_range.mpr (hcle xm), xm, hxmM, rfl⟩⟩
  obtain ⟨z, hzM, hzc⟩ := (mem_filter.mp (C.max'_mem hC)).2
  have hcnt : ∀ y, OPTFeasible n θ y → (∀ w, OPTFeasible n θ w → Fobj w θ ≤ Fobj y θ) →
      cntB n θ y ≤ cntB n θ z := by
    intro y hy hymax
    rw [hzc]
    exact C.le_max' _ (mem_filter.mpr ⟨mem_range.mpr (hcle y), y, ⟨hy, hymax⟩, rfl⟩)
  have heq : ∀ i j, 0 < z i → z i < θ → 0 < z j → z j < θ → z i = z j := by
    intro i j hi0 hiθ hj0 hjθ
    rcases lt_trichotomy (z i) (z j) with h | h | h
    · exact (no_two_interior n θ z hzM.1 hzM.2 hcnt j i hi0 h hjθ).elim
    · exact h
    · exact (no_two_interior n θ z hzM.1 hzM.2 hcnt i j hj0 h hiθ).elim
  exact (hzM.2 x hx).trans (structured_le n θ z hθpos hzM.1 heq M hM)
-- x
