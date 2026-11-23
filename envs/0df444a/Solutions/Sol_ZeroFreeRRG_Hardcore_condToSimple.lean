-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.condToSimple
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:11.709338+00:00
-- url     : https://prove2.me/submissions/972c0fc0-5989-4da2-b1a1-89045f536ac8

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_CMCond

open scoped Classical
open Filter Topology AFIsingKS ZeroFreeRRG.Hardcore

/-- Removing the simplicity conditioning in the final step of the configuration-model
argument. Off the simplicity event the requested implication is automatic; on that event,
zero-freeness of the truncated function forces the truncation event and hence zero-freeness
of the normalized partition function itself. -/
theorem solution (m : Model) (d : ℕ) (t : ℝ) (R : ℝ) (hR : 0 < R)
    (E : ∀ n : ℕ, Set (Matching n d))
    (hsimple : ∀ {n : ℕ} (M : Matching n d),
      IsSimpleM M ↔ cycleCount M 1 = 0 ∧ cycleCount M 2 = 0)
    (hcond : Tendsto (fun n => cmCondProb
        (fun M : Matching n d => cycleCount M 1 = 0 ∧ cycleCount M 2 = 0)
        (fun M => ∀ z ∈ Metric.closedBall (t : ℂ) R,
          (if M ∈ E n then normZ m z M else 0) ≠ 0))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1)) :
    Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M →
      ∀ z ∈ Metric.closedBall (t : ℂ) R, normZ m z M ≠ 0))
      (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1) := by
  have hprob_le_one (n : ℕ) (P : Matching n d → Prop) : cmProb P ≤ 1 := by
    unfold cmProb
    by_cases hN : Fintype.card (Matching n d) = 0
    · simp [hN]
    · have hN' : 0 < (Fintype.card (Matching n d) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      rw [div_le_one hN']
      exact_mod_cast (Finset.card_le_card (Finset.subset_univ
        (Finset.univ.filter P)) : (Finset.univ.filter P).card ≤ Finset.univ.card)
  have hbound (n : ℕ) :
      cmCondProb
        (fun M : Matching n d => cycleCount M 1 = 0 ∧ cycleCount M 2 = 0)
        (fun M => ∀ z ∈ Metric.closedBall (t : ℂ) R,
          (if M ∈ E n then normZ m z M else 0) ≠ 0) ≤
      cmProb (fun M : Matching n d => IsSimpleM M →
        ∀ z ∈ Metric.closedBall (t : ℂ) R, normZ m z M ≠ 0) := by
    classical
    let C : Matching n d → Prop := fun M => cycleCount M 1 = 0 ∧ cycleCount M 2 = 0
    let A : Matching n d → Prop := fun M => ∀ z ∈ Metric.closedBall (t : ℂ) R,
      (if M ∈ E n then normZ m z M else 0) ≠ 0
    let G : Matching n d → Prop := fun M => IsSimpleM M →
      ∀ z ∈ Metric.closedBall (t : ℂ) R, normZ m z M ≠ 0
    let S := Finset.univ.filter (fun M => ¬ C M)
    let T := Finset.univ.filter (fun M => C M ∧ A M)
    let Q := Finset.univ.filter C
    let H := Finset.univ.filter G
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro M hMS hMT
      have h1 : ¬ C M := (Finset.mem_filter.mp hMS).2
      have h2 : C M := (Finset.mem_filter.mp hMT).2.1
      exact h1 h2
    have hsub : S ∪ T ⊆ H := by
      intro M hM
      rw [Finset.mem_union] at hM
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ M, ?_⟩
      rcases hM with hMS | hMT
      · have hnC : ¬ C M := (Finset.mem_filter.mp hMS).2
        intro hs
        exact (hnC ((hsimple M).mp hs)).elim
      · have hCA : C M ∧ A M := (Finset.mem_filter.mp hMT).2
        intro hs z hz
        have hA := hCA.2
        have hE : M ∈ E n := by
          by_contra hE
          have h0 := hA (t : ℂ) (Metric.mem_closedBall_self hR.le)
          simp [hE] at h0
        have hz' := hA z hz
        simpa [hE] using hz'
    have hcardST : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisj
    have hgrow : S.card + T.card ≤ H.card := by
      rw [← hcardST]
      exact Finset.card_le_card hsub
    have hTQ : T.card ≤ Q.card := by
      apply Finset.card_le_card
      intro M hM
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ M, (Finset.mem_filter.mp hM).2.1⟩
    have hpartition : S.card + Q.card = Fintype.card (Matching n d) := by
      rw [← Finset.card_univ, add_comm]
      exact Finset.card_filter_add_card_filter_not C
    change cmCondProb C A ≤ cmProb G
    have hcond_eq : cmCondProb C A = (T.card : ℝ) / Q.card := by
      simp only [cmCondProb, T, Q]
      congr 2 <;>
        apply congrArg Finset.card <;>
        apply Finset.filter_congr_decidable
    have hprob_eq : cmProb G = (H.card : ℝ) / (Fintype.card (Matching n d) : ℝ) := by
      simp only [cmProb, H]
      congr 2
      apply congrArg Finset.card
      apply Finset.filter_congr_decidable
    rw [hcond_eq, hprob_eq]
    by_cases hQ : Q.card = 0
    · rw [hQ]
      simp only [Nat.cast_zero, div_zero]
      positivity
    · have hQpos : 0 < (Q.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQ
      have hN : Fintype.card (Matching n d) ≠ 0 := by
        intro hN
        have : Q.card ≤ Fintype.card (Matching n d) := by
          rw [← Finset.card_univ]
          exact Finset.card_le_card (Finset.subset_univ Q)
        omega
      have hNpos : 0 < (Fintype.card (Matching n d) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      have hQle : (Q.card : ℝ) ≤ (Fintype.card (Matching n d) : ℝ) := by
        have : Q.card ≤ Fintype.card (Matching n d) := by
          rw [← Finset.card_univ]
          exact Finset.card_le_card (Finset.subset_univ Q)
        exact_mod_cast this
      rw [div_le_div_iff₀ hQpos hNpos]
      have hgrow' : (S.card : ℝ) + T.card ≤ H.card := by exact_mod_cast hgrow
      have hTQ' : (T.card : ℝ) ≤ Q.card := by exact_mod_cast hTQ
      have hpartition' : (S.card : ℝ) + Q.card = (Fintype.card (Matching n d) : ℝ) := by
        exact_mod_cast hpartition
      nlinarith [mul_nonneg (sub_nonneg.mpr hTQ') (sub_nonneg.mpr hQle)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hcond tendsto_const_nhds
    (Filter.Eventually.of_forall hbound) (Filter.Eventually.of_forall (fun n => hprob_le_one n _))
