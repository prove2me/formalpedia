-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.exists_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:31.411644+00:00
-- url     : https://prove2.me/submissions/c90dcef9-4d40-4248-bf45-649a324604bf

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {x x' y y' : B.G R} (hx : x = x') (hy : y = y') (u : B.P R x y) :
    ∃ u' : B.P R x' y', HEq u' u := by
  subst hx hy; exact ⟨u, HEq.rfl⟩
end ReciprocityTheory.PGsh.BX
