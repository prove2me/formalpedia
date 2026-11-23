-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair______56f01b043277
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:14.464729+00:00
-- url     : https://prove2.me/submissions/e095054a-ec75-4049-9a6c-da0a8a42ebf3

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero

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
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution (s : (R : Type u)) : Dp.κ (Dp.σ.1 s * Dp.η) = s :=
  (Dp.decomp_unique (b := Dp.σ.1 s * Dp.η) (r := 0) (s := s) (by simp)).2.symm
end ReciprocityTheory.PGsh.DualPair
