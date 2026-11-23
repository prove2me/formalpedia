-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.swap_castFst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:53.32906+00:00
-- url     : https://prove2.me/submissions/e87cc169-6bf9-4193-8f82-572e7e50f7b9

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
theorem _root_.solution {x x' y : B.G R} (h : x = x') (u : B.P R x y) :
    B.sw (B.tr1 h u) = B.tr2 h (B.sw u) := by subst h; rfl
end ReciprocityTheory.PGsh.BX
