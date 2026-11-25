-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_fr___2154160be0da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:41:36.829349+00:00
-- url     : https://prove2.me/submissions/c087e807-2db4-45d4-85e4-4caec2310ec4

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair______56f01b043277
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_fr_apply

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
theorem _root_.solution (r : (R : Type u)) : (Dp.fr r).1 Dp.η = Dp.σ.1 r * Dp.η := by
  rw [Dp.fr_apply, Dp.π_η, map_zero, zero_add]
  have h1 : Dp.κ Dp.η = 1 := by
    have h2 := Dp.κ_ση 1
    rwa [map_one, one_mul] at h2
  rw [h1, one_mul]
end ReciprocityTheory.PGsh.DualPair
