-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.induce_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:01.966599+00:00
-- url     : https://prove2.me/submissions/eacafe8a-a793-4135-8e9c-54102019cae6

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
theorem _root_.solution {G : SimpleGraph V} {s : Set V} {f : Fin 4 → V}
    (hf : IsC4Map G f) (h : ∀ i, f i ∈ s) : IsC4Map (G.induce s) (fun i => ⟨f i, h i⟩) := by
  obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
  exact ⟨fun i j hij => hinj (congrArg Subtype.val hij), h01, h12, h23, h30⟩
end IsC4Map
end SizeRamsey.Plan
