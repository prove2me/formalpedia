-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.Tmap_Tsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:06.375363+00:00
-- url     : https://prove2.me/submissions/e6f2ce6a-ad4a-4af9-81ed-d420a4280137

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
theorem _root_.solution {R S : LAlg R₀} (f : LHom R S) (l : (R : Type u)ˣ) (t : B.Tot R) :
    B.Tmap f (B.Tsmul l t) =
      B.Tsmul (Units.map (f.1 : (R : Type u) →* (S : Type u)) l) (B.Tmap f t) :=
  B.tot_ext rfl rfl (heq_of_eq (B.pmap_smul f l t.2.2))
end ReciprocityTheory.PGsh.BX
