-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplBoxVolume_proof_173f1293829e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:00.840084+00:00
-- url     : https://prove2.me/submissions/742178fa-ea24-45e9-911c-a4c328d16d84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplBoxVolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplBoxVolume_set_eq_preimage_c34e58dd3381

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
open Matrix
open PSymplBoxVolume
namespace GroundTheory.Heights₂.Heights
namespace SymplBoxVolume
theorem _root_.solution : SymplBoxVolume.Statement := by
  intro ι _ _ A a hA ha
  rw [set_eq_preimage, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])
    , Real.volume_pi_Ioo, LinearMap.det_toLin',
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  ring
end SymplBoxVolume
end GroundTheory.Heights₂.Heights
