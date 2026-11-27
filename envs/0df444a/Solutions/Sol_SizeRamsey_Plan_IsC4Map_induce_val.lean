-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.induce_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:24.734794+00:00
-- url     : https://prove2.me/submissions/0d7644f7-fe98-4596-97cc-0aee45a53fda

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion

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
theorem _root_.solution {G : SimpleGraph V} {s : Set V} {f : Fin 4 → s}
    (hf : IsC4Map (G.induce s) f) : IsC4Map G (fun i => (f i : V)) := by
  obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
  exact ⟨Subtype.val_injective.comp hinj, h01, h12, h23, h30⟩
end IsC4Map
end SizeRamsey.Plan
