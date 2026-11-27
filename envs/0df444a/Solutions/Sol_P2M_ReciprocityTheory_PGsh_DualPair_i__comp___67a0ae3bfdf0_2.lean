-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair_i__comp___67a0ae3bfdf0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:23.221441+00:00
-- url     : https://prove2.me/submissions/c26c3462-4467-42c3-aef2-8bbb83c41140

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc

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
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.DualPair
theorem _root_.solution : Dp.i₂L.comp Dp.σ = Dp.i₁L.comp Dp.σ := LHom.ext' fun r => by
  apply Subtype.ext
  apply Prod.ext
  · show Dp.σ.1 (Dp.π.1 (Dp.σ.1 r)) = Dp.σ.1 r
    rw [Dp.sect]
  · show Dp.σ.1 r = Dp.σ.1 (Dp.π.1 (Dp.σ.1 r))
    rw [Dp.sect]
end ReciprocityTheory.PGsh.DualPair
