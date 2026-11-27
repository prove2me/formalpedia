-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.edgeOnSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:56.380347+00:00
-- url     : https://prove2.me/submissions/64e23b59-2e30-41bc-844c-a403be57217f

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_rotate
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_reverse

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
theorem _root_.solution {G : SimpleGraph V} {f : Fin 4 → V} (hf : IsC4Map G f)
    (i : Fin 4) : EdgeOnSquare G (f i) (f (i + 1)) ∧ EdgeOnSquare G (f (i + 1)) (f i) := by
  refine ⟨⟨_, IsC4Map.rotate hf i, by simp, by simp [add_comm]⟩,
    ⟨_, IsC4Map.reverse hf (i + 1), by simp, by simp⟩⟩
end IsC4Map
end SizeRamsey.Plan
