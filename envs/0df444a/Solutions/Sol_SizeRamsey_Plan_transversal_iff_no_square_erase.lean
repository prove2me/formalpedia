-- Prove2me | solution 1 for SizeRamsey.Plan.transversal_iff_no_square_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:27.075092+00:00
-- url     : https://prove2.me/submissions/50ca7c2e-c6af-4cf9-91f1-dd83f2ac4bcd

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_val
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_mk

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (D : Finset V) :
    c4Transversal G D ↔ ¬ HasC4 (erase G D) := by
  constructor
  · rintro hS ⟨f, hf⟩
    obtain ⟨i, hi⟩ := hS _ (IsC4Map.erase_val hf)
    exact (f i).2 hi
  · intro h f hf
    by_contra hcon
    push Not at hcon
    exact h ⟨_, IsC4Map.erase_mk hf hcon⟩
end SizeRamsey.Plan
