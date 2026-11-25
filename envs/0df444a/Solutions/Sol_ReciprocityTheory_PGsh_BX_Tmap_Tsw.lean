-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.Tmap_Tsw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:09.001368+00:00
-- url     : https://prove2.me/submissions/31833660-3f93-483b-96f9-2162b7619277

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
import Theorems.Thm_ReciprocityTheory_PGsh_BX_tot_ext

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
variable (B : BX R₀)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {R S : LAlg R₀} (f : LHom R S) (t : B.Tot R) :
    B.Tmap f (B.Tsw t) = B.Tsw (B.Tmap f t) :=
  B.tot_ext rfl rfl (heq_of_eq (B.sw_nat f t.2.2).symm)
end ReciprocityTheory.PGsh.BX
