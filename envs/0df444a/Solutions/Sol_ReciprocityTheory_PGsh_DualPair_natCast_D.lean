-- Prove2me | solution 1 for ReciprocityTheory.PGsh.DualPair.natCast_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:33.410176+00:00
-- url     : https://prove2.me/submissions/656e6b15-7cb1-452e-a9c6-589b84bb96d2

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
theorem _root_.solution {N : ℕ} (hN : (N : (R : Type u)) = 0) : (N : (Dp.D : Type u)) = 0 := by
  rw [← map_natCast Dp.σ.1 N, hN, map_zero]
end ReciprocityTheory.PGsh.DualPair
