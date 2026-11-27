-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.erase_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:03.356386+00:00
-- url     : https://prove2.me/submissions/89fbf3ae-dbed-47a9-a430-986b31671e3a

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_val

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
theorem _root_.solution {G : SimpleGraph V} {D : Finset V} {f : Fin 4 → {v : V // v ∉ D}}
    (hf : IsC4Map (erase G D) f) : IsC4Map G (fun i => (f i : V)) :=
  IsC4Map.induce_val (s := {v | v ∉ D}) hf
end IsC4Map
end SizeRamsey.Plan
