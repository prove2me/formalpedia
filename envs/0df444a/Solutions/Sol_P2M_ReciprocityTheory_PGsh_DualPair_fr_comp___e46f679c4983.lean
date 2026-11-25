-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair_fr_comp___e46f679c4983
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:46.857157+00:00
-- url     : https://prove2.me/submissions/886b9895-d399-4314-b24b-2eddee3fb222

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
theorem _root_.solution (r : (R : Type u)) : (Dp.fr r).comp Dp.σ = Dp.σ := LHom.ext' (fun x => by
  show Dp.σ.1 (Dp.π.1 (Dp.σ.1 x)) + Dp.σ.1 (Dp.κ (Dp.σ.1 x) * r) * Dp.η = Dp.σ.1 x
  rw [Dp.sect, Dp.κ_σ, zero_mul, map_zero, zero_mul, add_zero])
end ReciprocityTheory.PGsh.DualPair
