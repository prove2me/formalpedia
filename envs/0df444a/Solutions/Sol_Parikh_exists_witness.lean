-- Prove2me | solution 1 for Parikh.exists_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:36.113916+00:00
-- url     : https://prove2.me/submissions/e437744b-0023-4cc2-9816-58af317924f5

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting
public import Theorems.Thm_Parikh_Component_denotation_eq_vadd_closure

set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ W : Witness T, W.denotation = X := by
  classical
  have linear_witness : ∀ X : Set (Vector T), IsLinearSet X →
      ∃ c : Component T, c.denotation = X := by
    rintro X ⟨b, periods, hperiods, rfl⟩
    refine ⟨⟨b, hperiods.toFinset.toList⟩, ?_⟩
    rw [Component.denotation_eq_vadd_closure]
    have hrange : Set.range hperiods.toFinset.toList.get = periods := by
      ext p
      simp only [Set.mem_range, ← List.mem_iff_get, Finset.mem_toList,
        Set.Finite.mem_toFinset]
    simp only [hrange]
  rcases hX with ⟨S, hS, hlinear, rfl⟩
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact ⟨[], by ext v; simp [Witness.denotation]⟩
  | @insert X S hnot hS ih =>
    obtain ⟨c, hc⟩ := linear_witness X (hlinear X (by simp))
    obtain ⟨W, hW⟩ := ih (fun Y hY => hlinear Y (by simp [hY]))
    refine ⟨c :: W, ?_⟩
    have hcons : Witness.denotation (c :: W) = c.denotation ∪ W.denotation := by
      ext v
      simp [Witness.denotation]
    rw [hcons, hc, hW, Set.sUnion_insert]
end Parikh
