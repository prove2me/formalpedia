-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair___comp_fr_8c3b9426a108
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:39.704803+00:00
-- url     : https://prove2.me/submissions/742f7614-0916-4f1e-a1bf-4d054ebc2c8e

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504

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
theorem _root_.solution (r : (R : Type u)) : Dp.π.comp (Dp.fr r) = Dp.π := LHom.ext' (fun b => by
  show Dp.π.1 (Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η) = Dp.π.1 b
  rw [map_add, map_mul, Dp.π_η, mul_zero, add_zero, Dp.sect])
end ReciprocityTheory.PGsh.DualPair
