-- Prove2me | solution 1 for Shatters.subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:41.157318+00:00
-- url     : https://prove2.me/submissions/00f00434-b6b9-42e0-8cb9-a99792bf72d7

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone

set_option autoImplicit true
@[expose] public section
public section
universe u v
namespace Shatters
theorem _root_.solution {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hS : Shatters X C S) (hTS : T ⊆ S) : Shatters X C T := by
  classical
  intro f
  -- Extend `f` from `T` to `S` by `false` outside `T`.
  let g : ↥S → Bool := fun ⟨x, _⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hc⟩ := hS g
  refine ⟨c, hcC, fun ⟨x, hx⟩ => ?_⟩
  have := hc ⟨x, hTS hx⟩
  simpa only [g, dif_pos hx] using this
end Shatters
