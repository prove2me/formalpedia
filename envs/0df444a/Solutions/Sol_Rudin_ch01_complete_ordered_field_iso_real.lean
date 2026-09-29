-- Prove2me | solution 1 for Rudin.ch01_complete_ordered_field_iso_real
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-12T21:37:06.517946+00:00
-- url     : https://prove2.me/submissions/d509c9c9-43f8-4030-a41f-79d524a5f786

import Mathlib
import Definitions.Def_Rudin_ch01_order

namespace RudinCh01Solution

open Rudin Set

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The supremum operator built from the least-upper-bound property, with the junk value `0`
for sets that are empty or unbounded above. -/
@[instance_reducible]
noncomputable def supSetOfLUB (hK : HasLeastUpperBoundProperty K) : SupSet K :=
  ⟨fun s => open Classical in
    if h : s.Nonempty ∧ BddAbove s then (hK s h.1 h.2).choose else 0⟩

/-- In an ordered field the whole space is not bounded above. -/
theorem not_bddAbove_univ : ¬ BddAbove (Set.univ : Set K) := by
  rintro ⟨b, hb⟩
  have : b + 1 ≤ b := hb (Set.mem_univ _)
  linarith

omit [IsStrictOrderedRing K] in
theorem sSup_eq_zero_of_not (hK : HasLeastUpperBoundProperty K) (s : Set K)
    (h : ¬ (s.Nonempty ∧ BddAbove s)) :
    letI := supSetOfLUB hK
    sSup s = 0 := by
  letI := supSetOfLUB hK
  show (open Classical in if h : s.Nonempty ∧ BddAbove s then (hK s h.1 h.2).choose else 0) = 0
  rw [dif_neg h]

omit [IsStrictOrderedRing K] in
theorem isLUB_sSup_of (hK : HasLeastUpperBoundProperty K) (s : Set K)
    (hb : BddAbove s) (hne : s.Nonempty) :
    letI := supSetOfLUB hK
    IsLUB s (sSup s) := by
  letI := supSetOfLUB hK
  show IsLUB s (open Classical in
    if h : s.Nonempty ∧ BddAbove s then (hK s h.1 h.2).choose else 0)
  rw [dif_pos ⟨hne, hb⟩]
  exact (hK s hne hb).choose_spec

/-- The conditionally complete linear order structure on an ordered field with the
least-upper-bound property. -/
@[instance_reducible]
noncomputable def ccloOfLUB (hK : HasLeastUpperBoundProperty K) :
    ConditionallyCompleteLinearOrder K :=
  letI := supSetOfLUB hK
  { conditionallyCompleteLatticeOfLatticeOfsSup K (isLUB_sSup_of hK) with
    le_total := le_total
    toDecidableLE := inferInstance
    toDecidableEq := inferInstance
    toDecidableLT := inferInstance
    compare := compare
    compare_eq_compareOfLessAndEq := LinearOrder.compare_eq_compareOfLessAndEq
    csSup_of_not_bddAbove := by
      intro s hs
      rw [sSup_eq_zero_of_not hK s (fun h => hs h.2),
        sSup_eq_zero_of_not hK ∅ (fun h => absurd h.1 (by simp))]
    csInf_of_not_bddBelow := by
      intro s hs
      show sSup (lowerBounds s) = sSup (lowerBounds ∅)
      have h1 : lowerBounds s = (∅ : Set K) := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact hs ⟨x, hx⟩
      have h2 : lowerBounds (∅ : Set K) = Set.univ := by simp
      rw [h1, h2, sSup_eq_zero_of_not hK ∅ (fun h => absurd h.1 (by simp)),
        sSup_eq_zero_of_not hK Set.univ (fun h => not_bddAbove_univ h.2)] }

end RudinCh01Solution

open Rudin ConditionallyCompleteLinearOrderedField in
/-- Rudin, Theorem 1.19 (existence and uniqueness of the real field). -/
theorem solution (K : Type) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (hK : HasLeastUpperBoundProperty K) :
    ∃ e : K ≃+*o ℝ, ∀ e' : K ≃+*o ℝ, e' = e := by
  letI := RudinCh01Solution.ccloOfLUB hK
  exact ⟨inducedOrderRingIso K ℝ, fun e' => Subsingleton.elim _ _⟩
