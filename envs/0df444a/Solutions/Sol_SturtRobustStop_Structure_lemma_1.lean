-- Prove2me | solution 1 for SturtRobustStop.Structure.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:20:09.686839+00:00
-- url     : https://prove2.me/submissions/1a4beaf5-f466-47bf-b745-9b5ee01019e2

import Definitions.Def_SturtRobustStop_Structure_Pruning

open scoped ENNReal

namespace Aux_SRSlemma1

open SturtRobustStop.Structure

theorem fi_iff {T : ℕ} (p : Fin T → Prop) (t : Fin T) :
    firstIndex p = some t ↔ p t ∧ ∀ s, p s → t ≤ s := by
  classical
  unfold firstIndex
  by_cases h : (Finset.univ.filter p).Nonempty
  · simp only [h, dite_true, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).2, fun s hs =>
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)⟩
    · rintro ⟨ht, hmin⟩
      apply le_antisymm (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
      apply Finset.le_min'
      intro s hs
      exact hmin s (Finset.mem_filter.mp hs).2
  · have hnt : ¬ p t := fun ht => h ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
    simp only [h, dite_false]
    constructor
    · intro hc; cases hc
    · rintro ⟨ht, _⟩; exact absurd ht hnt

noncomputable def ext' {T d : ℕ} (hT : 0 < T) (μ : Policy T (State d)) : Policy T (State d) where
  stop t := if t = ⟨T - 1, by omega⟩ then Set.univ else μ.stop t
  measurable_stop t := by
    by_cases h : t = ⟨T - 1, by omega⟩
    · simp only [h, ite_true]; exact MeasurableSet.univ
    · simp only [h, ite_false]; exact μ.measurable_stop t

end Aux_SRSlemma1

open SturtRobustStop.Structure Aux_SRSlemma1 in
theorem solution {T N d : ℕ} (D : Model T N d) :
    SturtRobustStop.Structure.optimalValue D = SturtRobustStop.Structure.terminalValue D := by
  have hT := D.horizon_pos
  have hfeas : ∀ μ : Policy T (State d), TerminalFeasible D (ext' hT μ) := by
    intro μ i
    refine ⟨⟨T - 1, by omega⟩, ?_⟩
    intro z _
    show z ∈ (if (⟨T - 1, by omega⟩ : Fin T) = ⟨T - 1, by omega⟩ then Set.univ else μ.stop _)
    simp
  have hpay : ∀ (μ : Policy T (State d)) (i : Fin N) (y : SturtRobustStop.Structure.Path T d),
      D.payoff (stoppingTime μ y) (D.sample i) ≤
        D.payoff (stoppingTime (ext' hT μ) y) (D.sample i) := by
    intro μ i y
    rcases hst : stoppingTime μ y with _ | t
    · simp [Model.payoff]
    · unfold stoppingTime at hst
      rw [fi_iff] at hst
      obtain ⟨ht, hmin⟩ := hst
      have : stoppingTime (ext' hT μ) y = some t := by
        unfold stoppingTime
        rw [fi_iff]
        constructor
        · show y t ∈ (if t = ⟨T - 1, by omega⟩ then Set.univ else μ.stop t)
          split_ifs
          · exact Set.mem_univ _
          · exact ht
        · intro s hs
          change y s ∈ (if s = ⟨T - 1, by omega⟩ then Set.univ else μ.stop s) at hs
          by_contra hlt
          rw [not_le] at hlt
          have hne : s ≠ ⟨T - 1, by omega⟩ := by
            intro hs'
            have h2 : (t : ℕ) < T := t.2
            have h1 : (s : ℕ) < (t : ℕ) := hlt
            have h3 : (s : ℕ) = T - 1 := by rw [hs']
            omega
          rw [if_neg hne] at hs
          exact absurd (hmin s hs) (not_le.mpr hlt)
      rw [this]
  have hobj : ∀ μ : Policy T (State d), objective D μ ≤ objective D (ext' hT μ) := by
    intro μ
    unfold objective
    apply ENNReal.div_le_div_right
    apply Finset.sum_le_sum
    intro i _
    unfold sampleReward
    apply le_iInf
    intro y
    apply (iInf_le _ y).trans
    exact ENNReal.coe_le_coe.mpr (hpay μ i y.val)
  apply le_antisymm
  · unfold SturtRobustStop.Structure.optimalValue SturtRobustStop.Structure.terminalValue
    apply iSup_le
    intro μ
    exact (hobj μ).trans
      (le_iSup (fun μ : {μ : Policy T (State d) // TerminalFeasible D μ} => objective D μ.val)
        ⟨ext' hT μ, hfeas μ⟩)
  · unfold SturtRobustStop.Structure.optimalValue SturtRobustStop.Structure.terminalValue
    apply iSup_le
    intro μ
    exact le_iSup (fun μ : Policy T (State d) => objective D μ) μ.val
