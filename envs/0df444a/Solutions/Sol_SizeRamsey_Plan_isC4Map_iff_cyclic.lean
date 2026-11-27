-- Prove2me | solution 1 for SizeRamsey.Plan.isC4Map_iff_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:18:28.201029+00:00
-- url     : https://prove2.me/submissions/0b5fd5af-04c8-4c4c-8af3-d9ca47b74225

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
theorem _root_.solution {G : SimpleGraph V} {f : Fin 4 → V} :
    IsC4Map G f ↔ Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1)) := by
  constructor
  · rintro ⟨hinj, h01, h12, h23, h30⟩
    refine ⟨hinj, fun i => ?_⟩
    fin_cases i
    exacts [h01, h12, h23, h30]
  · rintro ⟨hinj, h⟩
    exact ⟨hinj, h 0, h 1, h 2, h 3⟩
end SizeRamsey.Plan
