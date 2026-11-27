-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.erase_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:29.072678+00:00
-- url     : https://prove2.me/submissions/7a990876-b52a-4f0f-83a9-015791feab40

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_mk

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
theorem _root_.solution {G : SimpleGraph V} {D : Finset V} {f : Fin 4 → V}
    (hf : IsC4Map G f) (h : ∀ i, f i ∉ D) :
    IsC4Map (erase G D) (fun i => (⟨f i, h i⟩ : {v : V // v ∉ D})) :=
  IsC4Map.induce_mk (s := {v | v ∉ D}) hf h
end IsC4Map
end SizeRamsey.Plan
