-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.castFst_heq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:00.03917+00:00
-- url     : https://prove2.me/submissions/7936ec20-8821-4edc-af3b-dc1ab8d58074

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
theorem _root_.solution {x x' y : B.G R} (h : x = x') (u : B.P R x y) : HEq (B.tr1 h u) u := by
  subst h; rfl
end ReciprocityTheory.PGsh.BX
