-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:20.521846+00:00
-- url     : https://prove2.me/submissions/a1ac6a53-4e58-4d42-a92b-a0abb2c3ac6c

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_isC4Map_iff_cyclic

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}
namespace SizeRamsey.Plan
namespace IsC4Map
theorem _root_.solution {G : SimpleGraph V} {f : Fin 4 → V} (hf : IsC4Map G f) (k : Fin 4) :
    IsC4Map G (fun i => f (k - i)) := by
  rw [isC4Map_iff_cyclic] at hf ⊢
  refine ⟨hf.1.comp (sub_right_injective), fun i => ?_⟩
  have := hf.2 (k - (i + 1))
  rw [show k - (i + 1) + 1 = k - i by rw [sub_add_eq_sub_sub, sub_add_cancel]] at this
  exact this.symm
end IsC4Map
end SizeRamsey.Plan
