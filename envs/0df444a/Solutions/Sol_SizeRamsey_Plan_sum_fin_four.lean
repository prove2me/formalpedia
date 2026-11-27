-- Prove2me | solution 1 for SizeRamsey.Plan.sum_fin_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:03.149671+00:00
-- url     : https://prove2.me/submissions/8128dd3a-4235-49bf-87c9-b9a778e1bbdd

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (c : Fin 4 → ℕ) : ∑ i, c i = c 0 + c 1 + c 2 + c 3 := by
  rw [Finset.sum_fin_eq_sum_range]; simp [Finset.sum_range_succ]
end SizeRamsey.Plan
