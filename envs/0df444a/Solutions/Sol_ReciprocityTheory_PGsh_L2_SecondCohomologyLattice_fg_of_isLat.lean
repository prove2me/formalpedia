-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.fg_of_isLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:46.473803+00:00
-- url     : https://prove2.me/submissions/9462790e-1db0-4e18-9f64-6a63848c7656

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_Lemmata_MiscLemmasL_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open Module
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : M.FG := by
  obtain ⟨B, -, rfl⟩ := h
  exact Submodule.fg_span (Set.finite_range _)
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
