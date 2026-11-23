-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.Tmap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:31.850155+00:00
-- url     : https://prove2.me/submissions/c2235fdd-faca-43a8-968a-370d56e21aef

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
theorem _root_.solution {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) (t : B.Tot R) :
    B.Tmap (g.comp f) t = B.Tmap g (B.Tmap f t) :=
  B.tot_ext (B.map_comp f g t.1) (B.map_comp f g t.2.1) (B.pmap_comp f g t.2.2)
end ReciprocityTheory.PGsh.BX
