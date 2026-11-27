-- Prove2me | solution 1 for SizeRamsey.Plan.IsC4Map.ne_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:36.482344+00:00
-- url     : https://prove2.me/submissions/6b2946de-92d9-4c50-a191-79588044b3d7

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
omit [Fintype V]
namespace SizeRamsey.Plan
namespace IsC4Map
theorem _root_.solution {g : Fin 4 → V} (hg : IsC4Map G g) (k : Fin 4) {a b : Fin 4}
    (h : a ≠ b) : g (k + a) ≠ g (k + b) := fun he => h (add_left_cancel (hg.1 he))
end IsC4Map
end SizeRamsey.Plan
