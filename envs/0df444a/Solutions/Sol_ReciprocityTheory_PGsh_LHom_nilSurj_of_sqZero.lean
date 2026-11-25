-- Prove2me | solution 1 for ReciprocityTheory.PGsh.LHom.nilSurj_of_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:51.078607+00:00
-- url     : https://prove2.me/submissions/38d0b69e-06f7-4fb5-9871-22cf85b0214b

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
namespace ReciprocityTheory.PGsh
namespace LHom
theorem _root_.solution {R S : LAlg R₀} {π : LHom R S} (h : π.SqZero) : π.NilSurj := ⟨h.1, 2, h.2⟩
end LHom
end ReciprocityTheory.PGsh
