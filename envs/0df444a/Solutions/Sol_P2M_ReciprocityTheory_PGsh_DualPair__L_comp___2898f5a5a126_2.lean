-- Prove2me | solution 2 for P2M_ReciprocityTheory_PGsh_DualPair__L_comp___2898f5a5a126
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:16:36.841306+00:00
-- url     : https://prove2.me/submissions/9108c122-eeb0-469b-b3cf-6a3edab046db

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair__A___be3006636bb6

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
theorem _root_.solution (c : (R : Type u)) : (Dp.μL c).comp Dp.σ = Dp.σ :=
  LHom.ext' fun r => Dp.μA_σ c r
end ReciprocityTheory.PGsh.DualPair
