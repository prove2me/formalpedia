-- Prove2me | solution 1 for OpenPitMIP.Extraction.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:05:04.716082+00:00
-- url     : https://prove2.me/submissions/aa4b4047-ded6-444d-865a-821e5552887d

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

namespace RRAux_OpenPitMIP_Extraction_theorem_4

open OpenPitMIP.Extraction

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

theorem qSet_le (I : PCPSPC B D C T m) (hI : I.Standing) {κ} {x : C → Fin T → ℝ}
    {y : B → D → Fin T → ℝ} (hf : I.Feasible κ x y) (hcap : I.MiningCap y) (t : Fin T)
    (S : Finset C) (hS : ∀ c ∈ S, 1 ≤ PCPSPC.cum x c t) : I.qSet S ≤ I.Qcum t := by
  classical
  have hy := hf.2.2.2.2.1
  have hq := hI.q_nonneg
  calc I.qSet S = ∑ b ∈ I.blocksOf S, I.q b := rfl
    _ ≤ ∑ b ∈ I.blocksOf S, I.q b * PCPSPC.cum x (I.clu b) t := by
        apply Finset.sum_le_sum
        intro b hb
        have hb' : I.clu b ∈ S := by
          simpa [PCPSPC.blocksOf] using hb
        have := hS _ hb'
        nlinarith [hq b]
    _ = ∑ b ∈ I.blocksOf S, ∑ t' ∈ Finset.Iic t, ∑ d, I.q b * y b d t' := by
        apply Finset.sum_congr rfl
        intro b _
        rw [PCPSPC.cum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t' _
        rw [hf.1 b t', Finset.mul_sum]
    _ ≤ ∑ b, ∑ t' ∈ Finset.Iic t, ∑ d, I.q b * y b d t' := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro b _ _
        exact Finset.sum_nonneg fun t' _ => Finset.sum_nonneg fun d _ =>
          mul_nonneg (hq b) (hy b d t')
    _ = ∑ t' ∈ Finset.Iic t, ∑ b, ∑ d, I.q b * y b d t' := Finset.sum_comm
    _ ≤ ∑ t' ∈ Finset.Iic t, I.U t' := Finset.sum_le_sum fun t' _ => hcap t'
    _ = I.Qcum t := rfl

-- At most one positive member: the sum is bounded by any common upper bound.
theorem sum_le_of_atMostOne {K : Finset C} (w : C → ℝ) (M : ℝ) (hw : ∀ c, 0 ≤ w c)
    (hM : 0 ≤ M) (hle : ∀ c ∈ K, w c ≤ M)
    (h2 : ∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → 0 < w c₁ → 0 < w c₂ → False) :
    ∑ c ∈ K, w c ≤ M := by
  by_cases h : ∃ c ∈ K, 0 < w c
  · obtain ⟨c₁, hc₁, hpos⟩ := h
    rw [Finset.sum_eq_single_of_mem c₁ hc₁]
    · exact hle c₁ hc₁
    · intro b hb hne
      by_contra hb0
      exact h2 b hb c₁ hc₁ hne (lt_of_le_of_ne (hw b) (Ne.symm hb0)) hpos
  · push_neg at h
    have : ∑ c ∈ K, w c = 0 :=
      Finset.sum_eq_zero fun c hc => le_antisymm (h c hc) (hw c)
    rw [this]; exact hM

theorem twoF [DecidableEq C] (I : PCPSPC B D C T m) (hI : I.Standing) (t : Fin T)
    {x : C → Fin T → ℝ} {y : B → D → Fin T → ℝ} (hf : I.Feasible .F x y)
    (hcap : I.MiningCap y) (c₁ c₂ : C) (hinc : I.FIncompatible t c₁ c₂)
    (h1 : 0 < PCPSPC.cum x c₁ t) (h2 : 0 < PCPSPC.cum x c₂ t) : False := by
  have hle := qSet_le I hI hf hcap t (I.clSet {c₁, c₂}) ?_
  · linarith [hinc.2.2]
  intro c hc
  simp only [PCPSPC.clSet, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hc
  obtain ⟨ci, hci, hcc⟩ := hc
  have hci1 : 1 ≤ PCPSPC.cum x ci t := by
    rcases hci with rfl | rfl
    · exact one_le_cum_F I hI hf _ t h1
    · exact one_le_cum_F I hI hf _ t h2
  simp only [PCPSPC.cl, Finset.mem_filter, Finset.mem_univ, true_and] at hcc
  rcases hcc with rfl | hp
  · exact hci1
  · exact le_trans hci1 (chain_le I hI hf c ci hp t)

theorem twoP [DecidableEq C] (I : PCPSPC B D C T m) (hI : I.Standing) (t : Fin T)
    {x : C → Fin T → ℝ} {y : B → D → Fin T → ℝ} (hf : I.Feasible .P x y)
    (hcap : I.MiningCap y) (c₁ c₂ : C) (hinc : I.PIncompatible t c₁ c₂)
    (h1 : 0 < PCPSPC.cum x c₁ t) (h2 : 0 < PCPSPC.cum x c₂ t) : False := by
  have hle := qSet_le I hI hf hcap t (I.clSet {c₁, c₂} \ {c₁, c₂}) ?_
  · linarith [hinc.2.2]
  intro c hc
  rw [Finset.mem_sdiff] at hc
  obtain ⟨hc, hnot⟩ := hc
  simp only [PCPSPC.clSet, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hc
  obtain ⟨ci, hci, hcc⟩ := hc
  simp only [PCPSPC.cl, Finset.mem_filter, Finset.mem_univ, true_and] at hcc
  rcases hcc with rfl | hp
  · exact absurd (by rcases hci with h | h <;> simp [h]) hnot
  · have hpos : 0 < PCPSPC.cum x ci t := by rcases hci with rfl | rfl <;> assumption
    rw [chain_P I hI hf c ci hp t hpos]

end RRAux_OpenPitMIP_Extraction_theorem_4

open OpenPitMIP.Extraction in
-- Theorem 4 (clique and lifted clique cuts), p. 1433.
theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (t : Fin T) (K : Finset C) :
    ((∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.FIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .F x y → I.MiningCap y → ∑ c ∈ K, PCPSPC.cum x c t ≤ 1) ∧
    ((∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.PIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .P x y → I.MiningCap y → ∑ c ∈ K, PCPSPC.cum x c t ≤ 1) ∧
    (∀ c₀ : C, (∀ c ∈ K, I.cprec c₀ c) →
      (∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.FIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .F x y → I.MiningCap y →
          ∑ c ∈ K, PCPSPC.cum x c t ≤ PCPSPC.cum x c₀ t) ∧
    (∀ c₀ : C, (∀ c ∈ K, I.cprec c₀ c) →
      (∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.PIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .P x y → I.MiningCap y →
          ∑ c ∈ K, PCPSPC.cum x c t ≤ PCPSPC.cum x c₀ t) := by
  open RRAux_OpenPitMIP_Extraction_theorem_4 in
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hK x y hf hcap
    exact sum_le_of_atMostOne _ 1 (cum_nonneg I hI hf · t) zero_le_one
      (fun c _ => cum_le_one I hI hf c t)
      (fun c₁ h₁ c₂ h₂ hne p₁ p₂ => twoF I hI t hf hcap c₁ c₂ (hK c₁ h₁ c₂ h₂ hne) p₁ p₂)
  · intro hK x y hf hcap
    exact sum_le_of_atMostOne _ 1 (cum_nonneg I hI hf · t) zero_le_one
      (fun c _ => cum_le_one I hI hf c t)
      (fun c₁ h₁ c₂ h₂ hne p₁ p₂ => twoP I hI t hf hcap c₁ c₂ (hK c₁ h₁ c₂ h₂ hne) p₁ p₂)
  · intro c₀ hc₀ hK x y hf hcap
    exact sum_le_of_atMostOne _ _ (cum_nonneg I hI hf · t) (cum_nonneg I hI hf c₀ t)
      (fun c hc => chain_le I hI hf c₀ c (hc₀ c hc) t)
      (fun c₁ h₁ c₂ h₂ hne p₁ p₂ => twoF I hI t hf hcap c₁ c₂ (hK c₁ h₁ c₂ h₂ hne) p₁ p₂)
  · intro c₀ hc₀ hK x y hf hcap
    exact sum_le_of_atMostOne _ _ (cum_nonneg I hI hf · t) (cum_nonneg I hI hf c₀ t)
      (fun c hc => chain_le I hI hf c₀ c (hc₀ c hc) t)
      (fun c₁ h₁ c₂ h₂ hne p₁ p₂ => twoP I hI t hf hcap c₁ c₂ (hK c₁ h₁ c₂ h₂ hne) p₁ p₂)

#print axioms solution
