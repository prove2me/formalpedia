-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.lhom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:19.740142+00:00
-- url     : https://prove2.me/submissions/af19c6d9-2469-42c8-b87c-37b4a7c74784

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique

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
theorem _root_.solution {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)
end ReciprocityTheory.PGsh.BX
