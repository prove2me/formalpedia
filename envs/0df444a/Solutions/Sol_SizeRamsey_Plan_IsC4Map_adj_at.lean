-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.adj_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:36.008775+00:00
-- url     : https://prove2.me/submissions/7896c3f4-a117-430a-b052-c45a5d0cbe22

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_isC4Map_iff_cyclic


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
omit [Fintype V]
namespace SizeRamsey.Plan
namespace IsC4Map
theorem _root_.solution {g : Fin 4 → V} (hg : IsC4Map G g) (k : Fin 4) :
    G.Adj (g k) (g (k + 1)) ∧ G.Adj (g (k + 1)) (g (k + 2)) ∧
      G.Adj (g (k + 2)) (g (k + 3)) ∧ G.Adj (g (k + 3)) (g k) := by
  have h := (isC4Map_iff_cyclic.mp hg).2
  refine ⟨h k, ?_, ?_, ?_⟩
  · have := h (k + 1); rwa [add_assoc, show (1 + 1 : Fin 4) = 2 from rfl] at this
  · have := h (k + 2); rwa [add_assoc, show (2 + 1 : Fin 4) = 3 from rfl] at this
  · have := h (k + 3); rwa [add_assoc, show (3 + 1 : Fin 4) = 0 from rfl, add_zero] at this
end IsC4Map
end SizeRamsey.Plan
