-- Prove2me | solution 1 for ProjSchedMinCut.Transform.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:00:26.954457+00:00
-- url     : https://prove2.me/submissions/a5e772fd-d92e-4f4d-9e96-547aa23b6dad

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_ProjSchedMinCut_Transform_Setting
import Theorems.Thm_ProjSchedMinCut_Transform_earliest_lag

open ProjSchedMinCut.Transform
open ProjSchedMinCut.Transform.Instance
open scoped ENNReal

private lemma feasible_bounds {n : ℕ} (I : Instance n) {S : Fin (n + 1) → ℤ}
    (hS : I.Feasible S) (j : Fin (n + 1)) :
    I.earliest j ≤ S j ∧ S j ≤ I.latest j := by
  have hbddBelow : BddBelow (I.startTimes j) := by
    refine ⟨0, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 j).1
  have hbddAbove : BddAbove (I.startTimes j) := by
    refine ⟨I.T, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  have hmem : S j ∈ I.startTimes j := ⟨S, hS, rfl⟩
  exact ⟨csInf_le hbddBelow hmem, le_csSup hbddAbove hmem⟩

private lemma not_inCut_of_cap_top {n : ℕ} (I : Instance n) {X : Set (Node n)}
    (hcap : I.cutCap X < ⊤) {α : Arc n} (hα : α ∈ I.A) (htop : I.cap α = ⊤) :
    ¬ I.InCut X α := by
  classical
  intro hin
  have hmem : α ∈ I.A.filter (fun β => I.InCut X β) :=
    Finset.mem_filter.mpr ⟨hα, hin⟩
  have hle : I.cap α ≤ I.cutCap X :=
    Finset.single_le_sum (fun _ _ => zero_le) hmem
  rw [htop] at hle
  exact not_top_lt (lt_of_le_of_lt hle hcap)

private lemma sum_lt_top_of_forall_lt_top {α : Type*} (S : Finset α) (f : α → ℝ≥0∞)
    (h : ∀ a ∈ S, f a < ⊤) : ∑ a ∈ S, f a < ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs, ENNReal.add_lt_top]
    exact ⟨h b (Finset.mem_insert_self b s),
      ih (fun a ha => h a (Finset.mem_insert_of_mem ha))⟩

private lemma sum_le_sum_of_subset {α : Type*} (S₁ S₂ : Finset α) (f : α → ℝ≥0∞)
    (h : S₁ ⊆ S₂) : ∑ a ∈ S₁, f a ≤ ∑ a ∈ S₂, f a := by
  classical
  induction S₁ using Finset.induction_on generalizing S₂ with
  | empty => exact zero_le
  | @insert b s hbs ih =>
    have hb : b ∈ S₂ := h (Finset.mem_insert_self b s)
    have hs : s ⊆ S₂.erase b := by
      intro a ha
      exact Finset.mem_erase.mpr ⟨fun hab => hbs (hab ▸ ha), h (Finset.mem_insert_of_mem ha)⟩
    rw [Finset.sum_insert hbs, ← Finset.insert_erase hb,
        Finset.sum_insert (by simp)]
    exact add_le_add le_rfl (ih (S₂.erase b) hs)

private def cutOfThreshold {n : ℕ} (I : Instance n) (τ : Fin (n + 1) → ℤ) : Set (Node n) :=
  {Node.a} ∪ {u | ∃ j t, u = Node.v j t ∧ I.earliest j ≤ t ∧ t ≤ τ j}

private lemma node_v_mem_cutOfThreshold {n : ℕ} (I : Instance n) (τ : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) (t : ℤ) :
    Node.v j t ∈ cutOfThreshold I τ ↔ I.earliest j ≤ t ∧ t ≤ τ j := by
  unfold cutOfThreshold
  simp only [Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, Set.mem_ofPred,
    Node.v.injEq, false_or]
  constructor
  · rintro ⟨j', t', ⟨rfl, rfl⟩, h⟩
    exact h
  · intro h
    exact ⟨j, t, ⟨rfl, rfl⟩, h⟩

private lemma assign_mem_A_iff {n : ℕ} (I : Instance n) (j : Fin (n + 1)) (t : ℤ) :
    Arc.assign j t ∈ I.A ↔ I.earliest j ≤ t ∧ t ≤ I.latest j := by
  unfold Instance.A
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, Arc.assign.injEq,
    reduceCtorEq, and_false, exists_false, or_false]
  constructor
  · rintro ⟨j', t', ht', rfl, rfl⟩
    exact ht'
  · intro ht
    exact ⟨j, t, ht, rfl, rfl⟩

private lemma temporal_mem_A {n : ℕ} (I : Instance n) {ij : Fin (n + 1) × Fin (n + 1)}
    (hij : ij ∈ I.L) {t : ℤ}
    (he1 : I.earliest ij.1 + 1 ≤ t) (hl1 : t ≤ I.latest ij.1)
    (he2 : I.earliest ij.2 + 1 ≤ t + I.d ij.1 ij.2) (hl2 : t + I.d ij.1 ij.2 ≤ I.latest ij.2) :
    Arc.temporal ij t ∈ I.A := by
  unfold Instance.A
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  rw [Finset.mem_biUnion]
  refine ⟨ij, hij, Finset.mem_image.mpr ⟨t, ?_, rfl⟩⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨he1, hl1⟩, he2, hl2⟩

private lemma src_mem_A {n : ℕ} (I : Instance n) (j : Fin (n + 1)) :
    Arc.src j ∈ I.A := by
  unfold Instance.A
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ j)))

private lemma snk_mem_A {n : ℕ} (I : Instance n) (j : Fin (n + 1)) :
    Arc.snk j ∈ I.A := by
  unfold Instance.A
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))

private lemma node_v_mem_V {n : ℕ} (I : Instance n) (j : Fin (n + 1)) (t : ℤ)
    (he : I.earliest j ≤ t) (hl : t ≤ I.latest j + 1) :
    Node.v j t ∈ I.V := by
  exact Or.inr ⟨j, t, rfl, he, hl⟩

private lemma assign_inCut_cutOfThreshold_iff {n : ℕ} (I : Instance n)
    {τ : Fin (n + 1) → ℤ} (hτ : ∀ j, I.earliest j ≤ τ j ∧ τ j ≤ I.latest j)
    (j : Fin (n + 1)) (t : ℤ) :
    (Arc.assign j t ∈ I.A ∧ I.InCut (cutOfThreshold I τ) (Arc.assign j t)) ↔ t = τ j := by
  have ⟨he_τ, hl_τ⟩ := hτ j
  rw [assign_mem_A_iff]
  unfold Instance.InCut Instance.tail Instance.head
  rw [node_v_mem_cutOfThreshold]
  constructor
  · rintro ⟨⟨he_t, hl_t⟩, ⟨_, ht_le⟩, ⟨_, hnot_mem⟩⟩
    rw [node_v_mem_cutOfThreshold] at hnot_mem
    omega
  · rintro rfl
    refine ⟨⟨he_τ, hl_τ⟩, ⟨he_τ, le_rfl⟩, ⟨?_, ?_⟩⟩
    · exact Or.inr ⟨j, τ j + 1, rfl, by omega, by omega⟩
    · rw [node_v_mem_cutOfThreshold]
      omega

private lemma isNCut_cutOfThreshold {n : ℕ} (I : Instance n)
    {τ : Fin (n + 1) → ℤ} (hτ : ∀ j, I.earliest j ≤ τ j ∧ τ j ≤ I.latest j) :
    I.IsNCut (cutOfThreshold I τ) := by
  refine ⟨⟨?_, Or.inl rfl, ?_⟩, ?_⟩
  · rintro u (rfl | ⟨j, t, rfl, he, ht⟩)
    · exact Or.inl (Or.inl rfl)
    · have ⟨_, hl_τ⟩ := hτ j
      exact Or.inr ⟨j, t, rfl, he, by omega⟩
  · unfold cutOfThreshold
    simp
  · intro j
    refine ⟨τ j, (assign_inCut_cutOfThreshold_iff I hτ j (τ j)).mpr rfl, ?_⟩
    intro t ht
    exact (assign_inCut_cutOfThreshold_iff I hτ j t).mp ht

private lemma cutCap_feasible_lt_top {n : ℕ} (I : Instance n) {S : Fin (n + 1) → ℤ}
    (hS : I.Feasible S) : I.cutCap (cutOfThreshold I S) < ⊤ := by
  classical
  have hS_bounds : ∀ j, I.earliest j ≤ S j ∧ S j ≤ I.latest j := feasible_bounds I hS
  unfold Instance.cutCap
  refine sum_lt_top_of_forall_lt_top _ _ ?_
  intro α hα
  obtain ⟨hαA, hin⟩ := Finset.mem_filter.mp hα
  rcases α with ⟨j, t⟩ | ⟨ij₀, t₀⟩ | ⟨j⟩ | ⟨j⟩
  · exact ENNReal.ofReal_lt_top
  · exfalso
    unfold Instance.A at hαA
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, reduceCtorEq,
      Arc.temporal.injEq, and_false, exists_false, or_false, false_or] at hαA
    obtain ⟨ij, hij, t, ⟨⟨he1, hl1⟩, he2, hl2⟩, rfl, rfl⟩ := hαA
    unfold Instance.InCut Instance.tail Instance.head at hin
    rw [node_v_mem_cutOfThreshold] at hin
    apply hin.2.2
    rw [node_v_mem_cutOfThreshold]
    have hlag := hS.1 ij hij
    have ht_le : t ≤ S ij.1 := hin.1.2
    omega
  · exfalso
    unfold Instance.InCut Instance.head at hin
    apply hin.2.2
    rw [node_v_mem_cutOfThreshold]
    exact ⟨le_rfl, (hS_bounds j).1⟩
  · exfalso
    unfold Instance.InCut Instance.tail at hin
    rw [node_v_mem_cutOfThreshold] at hin
    have ⟨_, hl_S⟩ := hS_bounds j
    omega

private lemma prefix_or_first_out {P : ℕ → Prop} (h0 : P 0) (k : ℕ) :
    (∀ i ≤ k, P i) ∨ ∃ m < k, (∀ i ≤ m, P i) ∧ ¬ P (m + 1) := by
  induction k with
  | zero =>
    left
    intro i hi
    have hi0 : i = 0 := by omega
    rwa [hi0]
  | succ k ih =>
    rcases ih with hall | ⟨m, hmk, hm, hnot⟩
    · by_cases hk1 : P (k + 1)
      · left
        intro i hi
        rcases (by omega : i ≤ k ∨ i = k + 1) with hik | rfl
        · exact hall i hik
        · exact hk1
      · right
        exact ⟨k, by omega, hall, hk1⟩
    · right
      exact ⟨m, by omega, hm, hnot⟩

theorem solution {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ X, I.IsMinCut X → ∃ Xs, I.IsNCut Xs ∧ I.cutCap Xs = I.cutCap X := by
  classical
  intro X hX
  have hcap : I.cutCap X < ⊤ := by
    rcases hfeas with ⟨S, hS⟩
    have hS_cut : I.IsCut (cutOfThreshold I S) :=
      (isNCut_cutOfThreshold I (feasible_bounds I hS)).1
    exact lt_of_le_of_lt (hX.2 (cutOfThreshold I S) hS_cut) (cutCap_feasible_lt_top I hS)
  have hex_τ : ∀ j, ∃ t : ℤ,
      (I.earliest j ≤ t ∧ t ≤ I.latest j) ∧
      (∀ s, I.earliest j ≤ s → s ≤ t → Node.v j s ∈ X) ∧
      Node.v j (t + 1) ∉ X := by
    intro j
    rcases hfeas with ⟨S, hS⟩
    have ⟨heS, hlS⟩ := feasible_bounds I hS j
    have hel : I.earliest j ≤ I.latest j := le_trans heS hlS
    have hsrc_not : ¬ I.InCut X (Arc.src j) :=
      not_inCut_of_cap_top I hcap (src_mem_A I j) rfl
    have hearliest_mem : Node.v j (I.earliest j) ∈ X := by
      by_contra hnot
      apply hsrc_not
      exact ⟨hX.1.2.1, node_v_mem_V I j (I.earliest j) le_rfl (by omega), hnot⟩
    have hsnk_not : ¬ I.InCut X (Arc.snk j) :=
      not_inCut_of_cap_top I hcap (snk_mem_A I j) rfl
    have hlatest_not_mem : Node.v j (I.latest j + 1) ∉ X := by
      intro hmem
      apply hsnk_not
      exact ⟨hmem, Or.inl (Or.inr rfl), hX.1.2.2⟩
    let K : ℕ := (I.latest j + 1 - I.earliest j).toNat
    have h0 : Node.v j (I.earliest j + ((0 : ℕ) : ℤ)) ∈ X := by simpa using hearliest_mem
    rcases prefix_or_first_out (P := fun i : ℕ => Node.v j (I.earliest j + (i : ℤ)) ∈ X) h0 K with
      hall | ⟨m, hmK, hm_mem, hm_not⟩
    · exfalso
      have hK_mem := hall K le_rfl
      have hK_eq : I.earliest j + (K : ℤ) = I.latest j + 1 := by omega
      rw [hK_eq] at hK_mem
      exact hlatest_not_mem hK_mem
    · refine ⟨I.earliest j + (m : ℤ), ⟨by omega, by omega⟩, ?_, ?_⟩
      · intro s hes hsm
        let i : ℕ := (s - I.earliest j).toNat
        have hi_eq : I.earliest j + (i : ℤ) = s := by omega
        rw [← hi_eq]
        exact hm_mem i (by omega)
      · have heq : I.earliest j + (m : ℤ) + 1 = I.earliest j + ((m + 1 : ℕ) : ℤ) := by omega
        rwa [heq]
  choose τ hτ_bounds hτ_mem hτ_not_mem using hex_τ
  let Xs := cutOfThreshold I τ
  have hncut : I.IsNCut Xs := isNCut_cutOfThreshold I hτ_bounds
  have hsub : I.A.filter (fun α => I.InCut Xs α) ⊆ I.A.filter (fun α => I.InCut X α) := by
    intro α hα
    rw [Finset.mem_filter] at hα ⊢
    obtain ⟨hαA, hin⟩ := hα
    refine ⟨hαA, ?_⟩
    rcases α with ⟨j, t⟩ | ⟨ij₀, t₀⟩ | ⟨j⟩ | ⟨j⟩
    · have ht : t = τ j := (assign_inCut_cutOfThreshold_iff I hτ_bounds j t).mp ⟨hαA, hin⟩
      subst ht
      have ⟨he_τ, hl_τ⟩ := hτ_bounds j
      exact ⟨hτ_mem j (τ j) he_τ le_rfl,
        node_v_mem_V I j (τ j + 1) (by omega) (by omega), hτ_not_mem j⟩
    · exfalso
      unfold Instance.A at hαA
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
        Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, reduceCtorEq,
        Arc.temporal.injEq, and_false, exists_false, or_false, false_or] at hαA
      obtain ⟨ij, hij, t, ⟨⟨he1, hl1⟩, he2, hl2⟩, rfl, rfl⟩ := hαA
      unfold Instance.InCut Instance.tail Instance.head at hin
      rw [node_v_mem_cutOfThreshold] at hin
      have ht_le_τ1 : t ≤ τ ij.1 := hin.1.2
      have hnot_head : ¬ (I.earliest ij.2 ≤ t + I.d ij.1 ij.2 ∧ t + I.d ij.1 ij.2 ≤ τ ij.2) := by
        intro hmem
        exact hin.2.2 ((node_v_mem_cutOfThreshold I τ ij.2 (t + I.d ij.1 ij.2)).mpr hmem)
      have helag := earliest_lag I hw hfeas ij hij
      have ⟨he_τ1, hl_τ1⟩ := hτ_bounds ij.1
      have ⟨he_τ2, hl_τ2⟩ := hτ_bounds ij.2
      let s : ℤ := τ ij.2 + 1 - I.d ij.1 ij.2
      have hs_mem_A : Arc.temporal ij s ∈ I.A :=
        temporal_mem_A I hij (by omega) (by omega) (by omega) (by omega)
      have hnot_in_X : ¬ I.InCut X (Arc.temporal ij s) :=
        not_inCut_of_cap_top I hcap hs_mem_A rfl
      apply hnot_in_X
      dsimp only [Instance.InCut, Instance.tail, Instance.head]
      have hs_in_X : Node.v ij.1 s ∈ X := hτ_mem ij.1 s (by omega) (by omega)
      have hs_head_eq : s + I.d ij.1 ij.2 = τ ij.2 + 1 := by omega
      rw [hs_head_eq]
      exact ⟨hs_in_X, node_v_mem_V I ij.2 (τ ij.2 + 1) (by omega) (by omega), hτ_not_mem ij.2⟩
    · exfalso
      unfold Instance.InCut Instance.head at hin
      apply hin.2.2
      rw [node_v_mem_cutOfThreshold]
      exact ⟨le_rfl, (hτ_bounds j).1⟩
    · exfalso
      unfold Instance.InCut Instance.tail at hin
      rw [node_v_mem_cutOfThreshold] at hin
      have ⟨_, hl_τ⟩ := hτ_bounds j
      omega
  refine ⟨Xs, hncut, ?_⟩
  exact le_antisymm (sum_le_sum_of_subset _ _ _ hsub) (hX.2 Xs hncut.1)
