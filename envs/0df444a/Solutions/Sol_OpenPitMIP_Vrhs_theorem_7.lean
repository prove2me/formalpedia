-- Prove2me | solution 1 for OpenPitMIP.Vrhs.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:07:49.266638+00:00
-- url     : https://prove2.me/submissions/54183d12-5e7d-4be0-b626-e63d5901b5d4

import Mathlib
import Definitions.Def_OpenPitMIP_Vrhs_Setting

namespace RRAux_OpenPitMIP_Vrhs_theorem_7

open OpenPitMIP.Vrhs

-- A predicate that is transitive and holds on covers of a finite strict order holds on the order.
theorem chain {α : Type} [Fintype α] (r : α → α → Prop) (hr : IsStrictOrder α r)
    (P : α → α → Prop) (htr : ∀ a b c, P a b → P b c → P a c)
    (hcov : ∀ a b, r a b → (¬ ∃ c, r a c ∧ r c b) → P a b) : ∀ a b, r a b → P a b := by
  classical
  have := hr
  suffices h : ∀ n, ∀ a b, (Finset.univ.filter (fun c => r a c ∧ r c b)).card = n →
      r a b → P a b from fun a b => h _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab
    by_cases hc : ∃ c, r a c ∧ r c b
    · obtain ⟨c, hac, hcb⟩ := hc
      have hcmem : c ∈ Finset.univ.filter (fun d => r a d ∧ r d b) := by simp [hac, hcb]
      have h1 : (Finset.univ.filter (fun d => r a d ∧ r d c)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        have hsub : Finset.univ.filter (fun d => r a d ∧ r d c) ⊆
            Finset.univ.filter (fun d => r a d ∧ r d b) := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
          exact ⟨hd.1, _root_.trans_of r hd.2 hcb⟩
        refine (Finset.ssubset_iff_of_subset hsub).2 ⟨c, hcmem, ?_⟩
        simp [irrefl_of r c]
      have h2 : (Finset.univ.filter (fun d => r c d ∧ r d b)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        have hsub : Finset.univ.filter (fun d => r c d ∧ r d b) ⊆
            Finset.univ.filter (fun d => r a d ∧ r d b) := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
          exact ⟨_root_.trans_of r hac hd.1, hd.2⟩
        refine (Finset.ssubset_iff_of_subset hsub).2 ⟨c, hcmem, ?_⟩
        simp [irrefl_of r c]
      exact htr a c b (ih _ h1 a c rfl hac) (ih _ h2 c b rfl hcb)
    · exact hcov a b hab hc

variable {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}

theorem x_nonneg (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) (c : C) (t : Fin T) : 0 ≤ x c t := by
  obtain ⟨b, rfl⟩ := hI.clu_surjective c
  rw [hf.1 b t]
  exact Finset.sum_nonneg fun d _ => hf.2.2.2.2.1 b d t

theorem cum_nonneg (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) (c : C) (t : Fin T) :
    0 ≤ PCPSPC.cum x c t :=
  Finset.sum_nonneg fun t' _ => x_nonneg I hI hf c t'

theorem cum_le_one (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) (c : C) (t : Fin T) :
    PCPSPC.cum x c t ≤ 1 := by
  refine le_trans ?_ (hf.2.1 c)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun t' _ _ => x_nonneg I hI hf c t')

theorem chain_le (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) :
    ∀ c' c, I.cprec c' c → ∀ t, PCPSPC.cum x c t ≤ PCPSPC.cum x c' t := by
  apply chain I.cprec hI.strictOrder (fun c' c => ∀ t, PCPSPC.cum x c t ≤ PCPSPC.cum x c' t)
  · intro a b c h1 h2 t; exact le_trans (h2 t) (h1 t)
  · intro a b hab hn t; exact hf.2.2.1 b a ⟨hab, hn⟩ t

theorem chain_P (I : PCPSPC B D C T m) (hI : I.Standing) {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible .P x y) :
    ∀ c' c, I.cprec c' c → ∀ t, 0 < PCPSPC.cum x c t → PCPSPC.cum x c' t = 1 := by
  apply chain I.cprec hI.strictOrder
    (fun c' c => ∀ t, 0 < PCPSPC.cum x c t → PCPSPC.cum x c' t = 1)
  · intro a b c h1 h2 t hc
    exact h1 t (by rw [h2 t hc]; norm_num)
  · intro a b hab hn t hc; exact hf.2.2.2.2.2 b a ⟨hab, hn⟩ t hc

theorem one_le_cum_F (I : PCPSPC B D C T m) (hI : I.Standing) {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible .F x y) (c : C) (t : Fin T)
    (hc : 0 < PCPSPC.cum x c t) : 1 ≤ PCPSPC.cum x c t := by
  obtain ⟨t', ht', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hc)
  have h1 : x c t' = 1 := (hf.2.2.2.2.2 c t').resolve_left hne
  rw [← h1]
  exact Finset.single_le_sum (fun i _ => x_nonneg I hI hf c i) ht'

theorem mem_rcl (I : PCPSPC B D C T m) (a c' : C) : c' ∈ I.rcl a ↔ c' = a ∨ I.cprec a c' := by
  simp [PCPSPC.rcl]

theorem mem_blocksOf (I : PCPSPC B D C T m) (S : Finset C) (b : B) :
    b ∈ I.blocksOf S ↔ I.clu b ∈ S := by
  simp [PCPSPC.blocksOf]

theorem rcl_sub (I : PCPSPC B D C T m) (hI : I.Standing) {a a' : C} (h : I.cprec a a') :
    I.rcl a' ⊆ I.rcl a := by
  have := hI.strictOrder
  intro c' hc'
  rw [mem_rcl] at hc' ⊢
  rcases hc' with rfl | h'
  · exact Or.inr h
  · exact Or.inr (_root_.trans_of I.cprec h h')

theorem y_le_cum (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) (b : B) (d : D) (t : Fin T) :
    y b d t ≤ PCPSPC.cum x (I.clu b) t := by
  have h1 : y b d t ≤ x (I.clu b) t := by
    rw [hf.1 b t]
    exact Finset.single_le_sum (fun d' _ => hf.2.2.2.2.1 b d' t) (Finset.mem_univ d)
  refine le_trans h1 ?_
  exact Finset.single_le_sum (f := fun t' => x (I.clu b) t')
    (fun i _ => x_nonneg I hI hf _ i) (Finset.mem_Iic.2 le_rfl)

-- A block in rcl(a) has y bounded by w_a.
theorem block_bound (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) (a : C) (b : B) (hb : I.clu b ∈ I.rcl a)
    (d : D) (t : Fin T) : y b d t ≤ PCPSPC.cum x a t := by
  refine le_trans (y_le_cum I hI hf b d t) ?_
  rw [mem_rcl] at hb
  rcases hb with h | h
  · rw [h]
  · exact chain_le I hI hf a _ h t

theorem sum_blocks_sdiff [DecidableEq C] (I : PCPSPC B D C T m) (F : B → ℝ)
    {S S' : Finset C} (h : S' ⊆ S) :
    ∑ b ∈ I.blocksOf (S \ S'), F b = ∑ b ∈ I.blocksOf S, F b - ∑ b ∈ I.blocksOf S', F b := by
  classical
  have he : I.blocksOf (S \ S') = I.blocksOf S \ I.blocksOf S' := by
    ext b; simp [mem_blocksOf, Finset.mem_sdiff]
  have hs : I.blocksOf S' ⊆ I.blocksOf S := by
    intro b hb; rw [mem_blocksOf] at hb ⊢; exact h hb
  rw [he, Finset.sum_sdiff_eq_sub hs]

theorem telescope [DecidableEq C] (I : PCPSPC B D C T m) (F : B → ℝ) (R : ℕ → Finset C)
    (k : ℕ) (hR : ∀ i, 1 ≤ i → i ≤ k → R (i + 1) ⊆ R i) :
    ∑ i ∈ Finset.Icc 1 k, ∑ b ∈ I.blocksOf (R i \ R (i + 1)), F b =
      ∑ b ∈ I.blocksOf (R 1), F b - ∑ b ∈ I.blocksOf (R (k + 1)), F b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih (fun i h1 h2 => hR i h1 (by omega)),
      sum_blocks_sdiff I F (hR (k + 1) (by omega) le_rfl)]
    ring

theorem chain_cprec (I : PCPSPC B D C T m) (hI : I.Standing) (c : ℕ → C) (n : ℕ)
    (h1 : ∀ k ∈ Finset.Ico 1 n, I.cprec (c k) (c (k + 1))) :
    ∀ j i, 1 ≤ i → i < j → j ≤ n → I.cprec (c i) (c j) := by
  have := hI.strictOrder
  intro j
  induction j with
  | zero => intro i _ h; omega
  | succ j ih =>
    intro i hi hij hjn
    have hj : I.cprec (c j) (c (j + 1)) := h1 j (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    rcases Nat.lt_or_ge i j with h | h
    · exact _root_.trans_of I.cprec (ih i hi h (by omega)) hj
    · have : i = j := by omega
      subst this; exact hj

theorem R_sub (I : PCPSPC B D C T m) (hI : I.Standing) (c : ℕ → C) (n : ℕ)
    (h1 : ∀ k ∈ Finset.Ico 1 n, I.cprec (c k) (c (k + 1))) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ n) : I.rcl (c j) ⊆ I.rcl (c i) := by
  rcases Nat.lt_or_ge i j with h | h
  · exact rcl_sub I hI (chain_cprec I hI c n h1 j i hi h hj)
  · have : i = j := by omega
    subst this; exact subset_rfl

theorem core [DecidableEq C] (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t : Fin T)
    (k : ℕ) (c : ℕ → C) (h1 : ∀ i ∈ Finset.Ico 1 (k + 1), I.cprec (c i) (c (i + 1)))
    (α : B → ℝ) (hα : ∀ b ∈ I.blocksOf {c (k + 1)}, 0 ≤ α b ∧ α b ≤ 1)
    {κ} (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hf : I.Feasible κ x y)
    (hd : I.DestCap y)
    (hcase : PCPSPC.cum x (c (k + 1)) t = 0 ∨ PCPSPC.cum x (c (k + 1)) t = 1 ∨
      ((∀ c', I.cprec (c (k + 1)) c' → PCPSPC.cum x c' t = 0) ∧
        ∑ b ∈ I.blocksOf {c (k + 1)}, α b * I.q b ≤
          I.Ud d t - I.qSet (I.rcl (c 1) \ I.rcl (c (k + 1))))) :
    I.vrhsLHS d t c (k + 1) α y ≤ I.vrhsRHS d t c (k + 1) x := by
  have hq := hI.q_nonneg
  have hy := hf.2.2.2.2.1
  have hL : I.vrhsLHS d t c (k + 1) α y =
      (∑ i ∈ Finset.Icc 1 k, ∑ b ∈ I.blocksOf (I.rcl (c i) \ I.rcl (c (i + 1))),
          I.q b * y b d t) +
        ∑ b ∈ I.blocksOf {c (k + 1)}, α b * I.q b * y b d t +
        ∑ b ∈ I.blocksOf (I.rcl (c (k + 1)) \ {c (k + 1)}), I.q b * y b d t := by
    unfold PCPSPC.vrhsLHS
    rw [Nat.add_sub_cancel]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [PCPSPC.Delta, if_pos (by omega)]
  have hR : I.vrhsRHS d t c (k + 1) x =
      (∑ i ∈ Finset.Icc 1 k, I.qSet (I.rcl (c i) \ I.rcl (c (i + 1))) * PCPSPC.cum x (c i) t)
        + (I.Ud d t - I.qSet (I.rcl (c 1) \ I.rcl (c (k + 1)))) *
          PCPSPC.cum x (c (k + 1)) t := by
    unfold PCPSPC.vrhsRHS
    rw [Finset.sum_Icc_succ_top (by omega)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [PCPSPC.delta, if_pos (by omega), PCPSPC.Delta, if_pos (by omega)]
    · rw [PCPSPC.delta, if_neg (lt_irrefl _)]
  rw [hL, hR]
  -- the general bound on the first part
  have hA : (∑ i ∈ Finset.Icc 1 k, ∑ b ∈ I.blocksOf (I.rcl (c i) \ I.rcl (c (i + 1))),
          I.q b * y b d t) ≤
      ∑ i ∈ Finset.Icc 1 k, I.qSet (I.rcl (c i) \ I.rcl (c (i + 1))) * PCPSPC.cum x (c i) t := by
    apply Finset.sum_le_sum
    intro i _
    rw [PCPSPC.qSet, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b hb
    rw [mem_blocksOf, Finset.mem_sdiff] at hb
    exact mul_le_mul_of_nonneg_left (block_bound I hI hf _ b hb.1 d t) (hq b)
  have hnn : ∀ b, 0 ≤ I.q b * y b d t := fun b => mul_nonneg (hq b) (hy b d t)
  rcases hcase with h0 | h1' | ⟨hsucc, h33⟩
  · -- w_{c_n} = 0: everything in rcl(c_n) is unmined
    have hz : ∀ b, I.clu b ∈ I.rcl (c (k + 1)) → y b d t = 0 := by
      intro b hb
      have := block_bound I hI hf _ b hb d t
      rw [h0] at this
      exact le_antisymm this (hy b d t)
    have hB : ∑ b ∈ I.blocksOf {c (k + 1)}, α b * I.q b * y b d t = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [mem_blocksOf, Finset.mem_singleton] at hb
      rw [hz b (by rw [hb, mem_rcl]; exact Or.inl rfl), mul_zero]
    have hC : ∑ b ∈ I.blocksOf (I.rcl (c (k + 1)) \ {c (k + 1)}), I.q b * y b d t = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [mem_blocksOf, Finset.mem_sdiff] at hb
      rw [hz b hb.1, mul_zero]
    rw [hB, hC, h0]
    linarith
  · -- w_{c_n} = 1: every w_{c_i} is 1 and the right-hand side is U^d_t
    have hw1 : ∀ i ∈ Finset.Icc 1 k, PCPSPC.cum x (c i) t = 1 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hc := chain_le I hI hf _ _
        (chain_cprec I hI c (k + 1) h1 (k + 1) i hi.1 (by omega) le_rfl) t
      rw [h1'] at hc
      exact le_antisymm (cum_le_one I hI hf _ t) hc
    have hRsub : ∀ i, 1 ≤ i → i ≤ k → I.rcl (c (i + 1)) ⊆ I.rcl (c i) :=
      fun i hi hik => R_sub I hI c (k + 1) h1 i (i + 1) hi (by omega) (by omega)
    have hsum1 : (∑ i ∈ Finset.Icc 1 k, I.qSet (I.rcl (c i) \ I.rcl (c (i + 1))) *
        PCPSPC.cum x (c i) t) = I.qSet (I.rcl (c 1)) - I.qSet (I.rcl (c (k + 1))) := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [hw1 i hi, mul_one])]
      exact telescope I I.q (fun i => I.rcl (c i)) k hRsub
    have hsub1 : I.rcl (c (k + 1)) ⊆ I.rcl (c 1) := R_sub I hI c (k + 1) h1 1 (k + 1) le_rfl
      (by omega) le_rfl
    have hq1 : I.qSet (I.rcl (c 1) \ I.rcl (c (k + 1))) =
        I.qSet (I.rcl (c 1)) - I.qSet (I.rcl (c (k + 1))) := sum_blocks_sdiff I I.q hsub1
    have hA1 := telescope I (fun b => I.q b * y b d t) (fun i => I.rcl (c i)) k hRsub
    have hB : ∑ b ∈ I.blocksOf {c (k + 1)}, α b * I.q b * y b d t ≤
        ∑ b ∈ I.blocksOf {c (k + 1)}, I.q b * y b d t := by
      apply Finset.sum_le_sum
      intro b hb
      have := hα b hb
      rw [mul_assoc]
      nlinarith [hnn b]
    have hsing : ({c (k + 1)} : Finset C) ⊆ I.rcl (c (k + 1)) := by
      intro c' hc'; rw [Finset.mem_singleton] at hc'; rw [mem_rcl]; exact Or.inl hc'
    have hC := sum_blocks_sdiff I (fun b => I.q b * y b d t) hsing
    have htot : ∑ b ∈ I.blocksOf (I.rcl (c 1)), I.q b * y b d t ≤ I.Ud d t :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b _ _ => hnn b)) (hd d t)
    rw [hsum1, hq1, h1']
    beta_reduce at hA1 hC
    rw [hA1, hC]
    linarith
  · -- 0 < w_{c_n} < 1 (P only): successors are unmined, and (33) bounds the c_n term
    have hC : ∑ b ∈ I.blocksOf (I.rcl (c (k + 1)) \ {c (k + 1)}), I.q b * y b d t = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [mem_blocksOf, Finset.mem_sdiff, mem_rcl, Finset.mem_singleton] at hb
      have hp : I.cprec (c (k + 1)) (I.clu b) := by
        rcases hb.1 with h | h
        · exact absurd h hb.2
        · exact h
      have := y_le_cum I hI hf b d t
      rw [hsucc _ hp] at this
      rw [le_antisymm this (hy b d t), mul_zero]
    have hB : ∑ b ∈ I.blocksOf {c (k + 1)}, α b * I.q b * y b d t ≤
        (∑ b ∈ I.blocksOf {c (k + 1)}, α b * I.q b) * PCPSPC.cum x (c (k + 1)) t := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro b hb
      have hyb : y b d t ≤ PCPSPC.cum x (c (k + 1)) t := by
        apply block_bound I hI hf _ b _ d t
        rw [mem_blocksOf, Finset.mem_singleton] at hb
        rw [hb, mem_rcl]; exact Or.inl rfl
      exact mul_le_mul_of_nonneg_left hyb (mul_nonneg (hα b hb).1 (hq b))
    have hB2 := mul_le_mul_of_nonneg_right h33 (cum_nonneg I hI hf (c (k + 1)) t)
    rw [hC]
    linarith

end RRAux_OpenPitMIP_Vrhs_theorem_7

open OpenPitMIP.Vrhs in
open PCPSPC in
-- Theorem 7, Oper. Res. 68(5), p. 1434.
theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t : Fin T) (n : ℕ) (hn : 1 ≤ n)
    (c : ℕ → C)
    (h1 : ∀ k ∈ Finset.Ico 1 n, I.cprec (c k) (c (k + 1)))
    (h2 : I.qSet (I.rcl (c 1) \ I.rcl (c n)) < I.Ud d t)
    (h3 : I.Ud d t < I.qSet (I.rcl (c 1)))
    (α : B → ℝ) (hα : ∀ b ∈ I.blocksOf {c n}, 0 ≤ α b ∧ α b ≤ 1) :
    (∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ), I.Feasible .F x y → I.DestCap y →
      I.vrhsLHS d t c n α y ≤ I.vrhsRHS d t c n x) ∧
    (∑ b ∈ I.blocksOf {c n}, α b * I.q b ≤ I.Ud d t - I.qSet (I.rcl (c 1) \ I.rcl (c n)) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ), I.Feasible .P x y → I.DestCap y →
        I.vrhsLHS d t c n α y ≤ I.vrhsRHS d t c n x) := by
  open RRAux_OpenPitMIP_Vrhs_theorem_7 in
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · intro x y hf hd
    apply core I hI d t k c h1 α hα x y hf hd
    rcases (cum_nonneg I hI hf (c (k + 1)) t).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl (le_antisymm (cum_le_one I hI hf _ t) (one_le_cum_F I hI hf _ t h)))
  · intro h33 x y hf hd
    apply core I hI d t k c h1 α hα x y hf hd
    by_cases hw1 : PCPSPC.cum x (c (k + 1)) t = 1
    · exact Or.inr (Or.inl hw1)
    by_cases hw0 : PCPSPC.cum x (c (k + 1)) t = 0
    · exact Or.inl hw0
    refine Or.inr (Or.inr ⟨?_, h33⟩)
    intro c' hc'
    rcases (cum_nonneg I hI hf c' t).eq_or_lt with h | h
    · exact h.symm
    · exact absurd (chain_P I hI hf _ _ hc' t h) hw1

#print axioms solution
