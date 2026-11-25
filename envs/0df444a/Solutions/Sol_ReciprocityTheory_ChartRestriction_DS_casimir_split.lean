-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:40.608016+00:00
-- url     : https://prove2.me/submissions/a298b689-2de9-4f68-94dd-32fa1b76c5fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (P : Fin n → Fin n → Prop) [DecidableRel P] (hirr : ∀ a, ¬ P a a)
    (hP : ∀ a b, a ≠ b → (P a b ↔ ¬ P b a)) :
    casimir E = ∑ a, E a a * E a a +
      ∑ a, ∑ b ∈ univ.filter (fun b => P a b), (E a a - E b b + 2 • (E b a * E a b)) := by
  classical

  have h1 : casimir E = ∑ a, ∑ b, ((if a = b then E a a * E a a else 0) +
      (if P a b then E a b * E b a else 0) + (if P b a then E a b * E b a else 0)) := by
    unfold casimir
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      simp [hirr]
    · by_cases h : P a b
      · have h' : ¬ P b a := (hP a b hab).1 h
        simp [hab, h, h']
      · have h' : P b a := by
          by_contra h''
          exact h ((hP a b hab).2 h'')
        simp [hab, h, h']

  have comm : ∀ a b, E a b * E b a + E b a * E a b = E a a - E b b + 2 • (E b a * E a b) := by
    intro a b
    have h := hE a b b a
    rw [if_pos rfl, if_pos rfl, sub_eq_iff_eq_add] at h
    rw [h]
    abel
  have h3 : ∑ a, ∑ b, (if P b a then E a b * E b a else 0) =
      ∑ a, ∑ b, (if P a b then E b a * E a b else 0) := Finset.sum_comm
  have h4 : ∑ a, ∑ b, (if a = b then E a a * E a a else 0) = ∑ a, E a a * E a a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  rw [h1]
  simp only [Finset.sum_add_distrib]
  rw [h3, h4, add_assoc]
  congr 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact comm a b
  · simp
end ReciprocityTheory.ChartRestriction.DS
