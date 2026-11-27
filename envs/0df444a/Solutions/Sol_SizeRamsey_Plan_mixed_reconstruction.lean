-- Prove2me | solution 1 for SizeRamsey.Plan.mixed_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:59.349993+00:00
-- url     : https://prove2.me/submissions/435548c7-2cd3-45ed-9a94-4e0d03157a4d

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Mixed

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} (G : SimpleGraph V)
    (f : Fin 6 ≃ V)
    (hadj : ∀ i j,
      G.Adj (f i) (f j) ↔ k33MinusEdge.Adj i j) :
    Nonempty (G ≃g k33MinusEdge) := by
  let e : k33MinusEdge ≃g G := {
    toEquiv := f
    map_rel_iff' := by
      intro a b
      exact hadj a b
  }
  exact ⟨e.symm⟩
end SizeRamsey.Plan
