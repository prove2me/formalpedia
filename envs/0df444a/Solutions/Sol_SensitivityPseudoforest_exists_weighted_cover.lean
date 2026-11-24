-- Prove2me | solution 1 for SensitivityPseudoforest.exists_weighted_cover
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:32:26.746019+00:00
-- url     : https://prove2.me/submissions/61af12d0-250b-465f-a406-3fb1ff1fb886

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Tauto
import Theorems.Thm_SensitivityPseudoforest_exists_three_coloring

namespace SensitivityPseudoforest
end SensitivityPseudoforest

section


/-!
Three independent palettes for a finite orientation of outdegree at most one.
Sinks receive two colors, all other vertices one. This directly gives the
population-plus-sinks inequality without classifying connected components.
-/

namespace SensitivityPseudoforest

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

variable {V : Type}








theorem WeightedCover.card_le_two {R : V → V → Prop} {s : Finset V}
    (cover : WeightedCover R s) {v : V} (hv : v ∈ s) : (cover.colors v).card ≤ 2 := by
  rw [cover.size v hv]
  split <;> omega

theorem outgoing_subset {R : V → V → Prop} {s t : Finset V}
    (hst : s ⊆ t) (v : V) : outgoing R s v ⊆ outgoing R t v :=
  Finset.filter_subset_filter _ hst

theorem sum_outgoing_eq_incoming (R : V → V → Prop) (s : Finset V) :
    ∑ v ∈ s, (outgoing R s v).card = ∑ v ∈ s, (incoming R s v).card := by
  simp only [outgoing, incoming, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem incoming_positive_all_one (R : V → V → Prop) (s : Finset V)
    (hout : ∀ v ∈ s, (outgoing R s v).card ≤ 1)
    (hin : ∀ v ∈ s, 1 ≤ (incoming R s v).card) :
    (∀ v ∈ s, (outgoing R s v).card = 1) ∧
      (∀ v ∈ s, (incoming R s v).card = 1) := by
  have hsum := sum_outgoing_eq_incoming R s
  have hle := Finset.sum_le_sum hout
  have hge := Finset.sum_le_sum hin
  simp only [← Finset.card_eq_sum_ones] at hle hge
  constructor
  · intro v hv
    by_contra hne
    have hlt : (outgoing R s v).card < 1 := by have := hout v hv; omega
    have hsumlt := Finset.sum_lt_sum hout ⟨v, hv, hlt⟩
    simp only [← Finset.card_eq_sum_ones] at hsumlt
    omega
  · intro v hv
    by_contra hne
    have hlt : 1 < (incoming R s v).card := by have := hin v hv; omega
    have hsumlt := Finset.sum_lt_sum hin ⟨v, hv, hlt⟩
    simp only [← Finset.card_eq_sum_ones] at hsumlt
    omega

theorem neighbors_card_le (R : V → V → Prop) (s : Finset V) (v : V) :
    (neighbors R s v).card ≤ (outgoing R s v).card + (incoming R s v).card := by
  have heq : neighbors R s v = outgoing R s v ∪ incoming R s v := by
    ext w
    simp only [neighbors, outgoing, incoming, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [heq]
  exact Finset.card_union_le _ _














end
end SensitivityPseudoforest

end

/-!
Three independent palettes for a finite orientation of outdegree at most one.
Sinks receive two colors, all other vertices one. This directly gives the
population-plus-sinks inequality without classifying connected components.
-/
open SensitivityPseudoforest
open scoped Classical BigOperators
set_option autoImplicit false
variable {V : Type}

theorem solution (R : V → V → Prop) (hirr : ∀ v, ¬ R v v) :
    ∀ s : Finset V, (∀ v ∈ s, (outgoing R s v).card ≤ 1) → Nonempty (WeightedCover R s) := by
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih hout
  by_cases hsource : ∃ v ∈ s, ∀ w ∈ s, ¬ R w v
  · obtain ⟨v, hv, hsource⟩ := hsource
    have hout' : ∀ w ∈ s.erase v, (outgoing R (s.erase v) w).card ≤ 1 := by
      intro w hw
      exact (Finset.card_le_card (outgoing_subset (Finset.erase_subset _ _) w)).trans
        (hout w (Finset.mem_of_mem_erase hw))
    obtain ⟨cover⟩ := ih (s.erase v) (Finset.erase_ssubset hv) hout'
    by_cases hsink : IsSink R s v
    · refine ⟨extend_source_cover hv hsource cover {0, 1} ?_ ?_⟩
      · simp [hsink]
      · intro w hw hvw
        exact False.elim (hsink w (Finset.mem_of_mem_erase hw) hvw)
    · have hexists : ∃ w ∈ s, R v w := by
        by_contra h
        exact hsink (fun w hw hr => h ⟨w, hw, hr⟩)
      obtain ⟨w, hw, hvw⟩ := hexists
      have hwv : w ≠ v := by intro h; exact hirr v (h ▸ hvw)
      have hwmem : w ∈ s.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
      have hcard : (cover.colors w).card < (Finset.univ : Finset (Fin 3)).card := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Nat.lt_succ_of_le (cover.card_le_two hwmem)
      obtain ⟨fresh, _, hfresh⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      refine ⟨extend_source_cover hv hsource cover {fresh} ?_ ?_⟩
      · simp [hsink]
      · intro u hu hvu
        have huw : u = w := Finset.card_le_one.mp (hout v hv) u
          (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hu, hvu⟩)
          w
          (Finset.mem_filter.mpr ⟨hw, hvw⟩)
        subst u
        exact Finset.disjoint_singleton_left.mpr hfresh
  · have hin : ∀ v ∈ s, 1 ≤ (incoming R s v).card := by
      intro v hv
      have hexists : ∃ w ∈ s, R w v := by
        by_contra h
        apply hsource
        exact ⟨v, hv, fun w hw hr => h ⟨w, hw, hr⟩⟩
      obtain ⟨w, hw, hwv⟩ := hexists
      exact Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hwv⟩⟩
    obtain ⟨houtone, hinone⟩ := incoming_positive_all_one R s hout hin
    have hdegree : ∀ v ∈ s, (neighbors R s v).card ≤ 2 := by
      intro v hv
      have h := neighbors_card_le R s v
      rw [houtone v hv, hinone v hv] at h
      exact h
    obtain ⟨color, hcolor⟩ := exists_three_coloring R hirr s hdegree
    refine ⟨{ colors := fun v => {color v}, size := ?_, proper := ?_ }⟩
    · intro v hv
      have hnot : ¬ IsSink R s v := by
        intro hsink
        have hnonempty := Finset.one_le_card.mp (Nat.le_of_eq (houtone v hv).symm)
        obtain ⟨w, hw⟩ := hnonempty
        obtain ⟨hw, hr⟩ := Finset.mem_filter.mp hw
        exact hsink w hw hr
      simp [hnot]
    · intro v hv w hw hr
      simpa only [Finset.disjoint_singleton] using hcolor v hv w hw hr
