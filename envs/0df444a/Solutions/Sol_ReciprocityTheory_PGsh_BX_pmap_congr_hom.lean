-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pmap_congr_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:52.943666+00:00
-- url     : https://prove2.me/submissions/d005b143-057e-406b-a4e8-ceabd4eecc5c

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {S : LAlg R₀} {f g : LHom R S} (h : f = g) {x y : B.G R} (u : B.P R x y) :
    HEq (B.pmap f u) (B.pmap g u) := by
  subst h
  exact HEq.rfl
end ReciprocityTheory.PGsh.BX
