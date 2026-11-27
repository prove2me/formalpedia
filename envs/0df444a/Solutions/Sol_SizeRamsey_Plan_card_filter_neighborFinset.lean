-- Prove2me | solution 1 for SizeRamsey.Plan.card_filter_neighborFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:26.272832+00:00
-- url     : https://prove2.me/submissions/a5760447-87aa-43ad-9976-4d488b914575

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
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (v : V) (p : V → Prop) [DecidablePred p] :
    ((G.neighborFinset v).filter p).card =
      ∑ w ∈ Finset.univ.filter p, if G.Adj v w then 1 else 0 := by
  rw [← Finset.card_filter]
  congr 1
  ext w
  simp [and_comm]
end SizeRamsey.Plan
