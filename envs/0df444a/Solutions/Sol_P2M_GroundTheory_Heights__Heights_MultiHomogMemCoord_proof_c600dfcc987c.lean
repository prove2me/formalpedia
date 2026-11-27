-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MultiHomogMemCoord_proof_c600dfcc987c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:19.154264+00:00
-- url     : https://prove2.me/submissions/479d499d-a2f3-4240-acba-985e656c751f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PMultiHomogMemCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_eq_613223755b9a

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
open MultiHomogMemCoordinate
namespace GroundTheory.Heights₂.Heights
namespace MultiHomogMemCoord
theorem _root_.solution : MultiHomogMemCoord.Statement := by
  intro K _ ι _ Ω _ y g a hg
  rw [mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one,
    monomial_eq_zero]
end MultiHomogMemCoord
end GroundTheory.Heights₂.Heights
