-- Prove2me | solution 1 for OpenMath.WOWII19.exists_indepIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:32.221892+00:00
-- url     : https://prove2.me/submissions/0fa7a59e-efee-40d5-be4e-04e5e00be3f3

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath.WOWII19
theorem _root_.solution (G : SimpleGraph α) (T : Finset α) :
    ∃ s ⊆ T, (s : Set α).Pairwise (fun x y => ¬ G.Adj x y) ∧ s.card = indepIn G T := by
  classical
  have hne : (T.powerset.filter fun s : Finset α =>
      (s : Set α).Pairwise fun x y => ¬ G.Adj x y).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset T, by simp⟩⟩
  obtain ⟨s, hs, hsup⟩ := exists_mem_eq_sup _ hne card
  obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
  refine ⟨s, mem_powerset.mp hs1, hs2, ?_⟩
  unfold indepIn
  convert hsup.symm
end OpenMath.WOWII19
