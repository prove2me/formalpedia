-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.span_mk_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:59.358486+00:00
-- url     : https://prove2.me/submissions/5de2ffa2-04c8-42e9-abf6-2ecad9e17fd0

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    {d : ℕ} (y : Fin d → M) (hy : Submodule.span R (Set.range y) = ⊤) :
    Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (y k) : M ⧸ N)) = ⊤ := by
  rw [show (fun k => (Submodule.Quotient.mk (y k) : M ⧸ N)) = N.mkQ ∘ y from rfl, Set.range_comp,
    ← Submodule.map_span, hy, Submodule.map_top, Submodule.range_mkQ]
end ReciprocityTheory.PGsh.Up
