-- Prove2me | solution 1 for SizeRamsey.Plan.equality_square_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:47.633865+00:00
-- url     : https://prove2.me/submissions/ab366440-2065-40c6-ac16-79d41401f0a9

module
public import Definitions.Def_SizeRamsey_Universal
public import Definitions.Def_SizeRamsey_Tightness
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_non_square_edge
public import Theorems.Thm_SizeRamsey_Plan_universal


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (ht : 4 * tau4 G = edgeCount G) :
    SquareSupported G := by
  intro a b hab
  by_contra hns
  obtain ⟨htau, hcount⟩ := tau4_delete_non_square_edge G hab hns
  have hbound := universal (G.deleteEdges {s(a, b)})
  omega
end SizeRamsey.Plan
