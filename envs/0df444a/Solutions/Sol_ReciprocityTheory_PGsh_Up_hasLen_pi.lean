-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasLen_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:55.352363+00:00
-- url     : https://prove2.me/submissions/f91ee4f7-54c8-41ed-bb62-c9a706153fbd

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply

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
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal) [Algebra R C] {d : ℕ} (a : Fin d → R) :
    HasLen v R ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {a j} : Submodule R R)))
      (∏ j, v (algebraMap R C (a j))) :=
  ⟨d, a, ⟨Submodule.quotientPi _⟩, rfl⟩
end ReciprocityTheory.PGsh.Up
