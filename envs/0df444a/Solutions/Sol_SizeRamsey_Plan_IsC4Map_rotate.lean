-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:19.319683+00:00
-- url     : https://prove2.me/submissions/469a241c-c048-4b75-9270-4ba2346936db

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
    IsC4Map G (fun i => f (i + k)) := by
  rw [isC4Map_iff_cyclic] at hf ⊢
  refine ⟨hf.1.comp (add_left_injective k), fun i => ?_⟩
  have := hf.2 (i + k)
  rwa [add_right_comm] at this
end IsC4Map
end SizeRamsey.Plan
