-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:28.821305+00:00
-- url     : https://prove2.me/submissions/e7aec4f1-537b-48f4-a4e1-b08c0911c6c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) : ∀ k : ℕ, ∀ a : Fin n,
    (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card = k →
    ∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), mexp ε m c = m a := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih a hk
  have hsplit : Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c) =
      insert a (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inr ⟨h, h1.symm⟩
      · exact Or.inl h.symm
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        exact ⟨rfl, le_rfl⟩
      · exact ⟨h2.symm, h1.le⟩
  have hnot : a ∉ Finset.univ.filter (fun b : Fin n => a < b ∧ ε b = ε a) := by simp
  rw [hsplit, Finset.sum_insert hnot]
  by_cases hne : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty
  · obtain ⟨a', ha'def⟩ : ∃ a', (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' hne = a' :=
      ⟨_, rfl⟩
    have ha'mem : a < a' ∧ ε a' = ε a := by
      have := Finset.min'_mem _ hne
      rw [ha'def] at this
      exact (Finset.mem_filter.1 this).2
    have hset : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) =
        Finset.univ.filter (fun c : Fin n => ε a' = ε c ∧ a' ≤ c) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨ha'mem.2.trans h2.symm, ?_⟩
        rw [← ha'def]
        exact Finset.min'_le _ _ (by simp [h1, h2])
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_lt_of_le ha'mem.1 h2, h1.symm.trans ha'mem.2⟩
    have hcard : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a').card < k := by
      rw [← hk]
      have hsub : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a') ⊆
          (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact ⟨ha'mem.1.trans hc.1, hc.2.trans ha'mem.2⟩
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨a', by simp [ha'mem.1, ha'mem.2], by simp⟩
    rw [hset, ih _ hcard a' rfl]
    unfold mexp
    rw [dif_pos hne, ha'def]
    ring
  · have hemp := Finset.not_nonempty_iff_eq_empty.1 hne
    rw [hemp, Finset.sum_empty, add_zero]
    unfold mexp
    rw [dif_neg hne]
end ReciprocityTheory.ChartRestriction.DS.HW
