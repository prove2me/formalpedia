-- Prove2me | solution 1 for Sensitivity213981Formal.MarkedCandidateCaps.exists_markers_outside_first
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:29:26.965987+00:00
-- url     : https://prove2.me/submissions/5643290c-1f6c-4777-801b-5ba855968d10

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
section
/-
Unrestricted marked prefix caps and the outside-first marker choice used in
the exact q2 recurrence. These theorems refer to actual selected-child guards.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MarkedCandidateCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]





/-- Select eligible markers outside T first. This proves the exact correction
    max(0,m-outside) used by the numerical prefix-cap formula. -/
theorem exists_markers_outside_first (T E : Finset V) (m : ℕ) (hm : m ≤  E.card) :
    ∃ M : Finset V, M ⊆ E ∧ M.card = m ∧ (T ∩ M).card ≤  m - (E \ T).card := by
  by_cases hout : m ≤  (E \ T).card
  · obtain ⟨M,hMO,hMc⟩ := Finset.exists_subset_card_eq hout
    refine ⟨M,hMO.trans Finset.sdiff_subset,hMc,?_⟩
    have hdis : Disjoint T M := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvM
      exact (Finset.mem_sdiff.mp (hMO hvM)).2 hvT
    have hempty : T ∩ M = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have houtle : (E \ T).card ≤  m := by omega
    have hsplit := Finset.card_sdiff_add_card_inter E T
    have hneed : m - (E \ T).card ≤  (E ∩ T).card := by omega
    obtain ⟨J,hJI,hJc⟩ := Finset.exists_subset_card_eq hneed
    let O := E \ T
    let M := O ∪ J
    have hME : M ⊆ E := by
      apply Finset.union_subset
      · exact Finset.sdiff_subset
      · exact hJI.trans Finset.inter_subset_left
    have hdis : Disjoint O J := by
      apply Finset.disjoint_left.mpr
      intro v hvO hvJ
      exact (Finset.mem_sdiff.mp hvO).2 (Finset.mem_inter.mp (hJI hvJ)).2
    have hMc : M.card = m := by
      have hc : M.card = O.card + J.card := Finset.card_union_of_disjoint hdis
      dsimp [O] at hc
      omega
    have hsub : T ∩ M ⊆ J := by
      intro v hv
      obtain ⟨hvT,hvM⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvM with hvO | hvJ
      · exact False.elim ((Finset.mem_sdiff.mp hvO).2 hvT)
      · exact hvJ
    refine ⟨M,hME,hMc,?_⟩
    exact (Finset.card_le_card hsub).trans (le_of_eq hJc)



end
end MarkedCandidateCaps






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] [inst : DecidableEq.{1} V] (T E : Finset.{0} V) (m : Nat)
  (hm : @LE.le.{0} Nat instLENat m (@Finset.card.{0} V E)),
  @Exists.{1} (Finset.{0} V) fun (M : Finset.{0} V) =>
    And
      (@LE.le.{0} (Finset.{0} V)
        (@Preorder.toLE.{0} (Finset.{0} V)
          (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
        M E)
      (And (@Eq.{1} Nat (@Finset.card.{0} V M) m)
        (@LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Inter.inter.{0} (Finset.{0} V) (@Finset.instInter.{0} V inst) T M))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
            (@Finset.card.{0} V (@SDiff.sdiff.{0} (Finset.{0} V) (@Finset.instSDiff.{0} V inst) E T))))) := @Sensitivity213981Formal.MarkedCandidateCaps.exists_markers_outside_first
