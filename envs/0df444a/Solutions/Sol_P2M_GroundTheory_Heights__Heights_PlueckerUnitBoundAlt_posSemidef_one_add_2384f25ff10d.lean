-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_posSemidef_one_add_2384f25ff10d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:19.106085+00:00
-- url     : https://prove2.me/submissions/440c45f8-4a54-4fa1-a683-428d54d2f126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerUnitBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt
namespace GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt
theorem _root_.solution {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    (1 + Z * Zᴴ).PosSemidef :=
  Matrix.PosSemidef.one.add (Matrix.posSemidef_self_mul_conjTranspose Z)
end GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt
