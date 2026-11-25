-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_add_const_877e0affda6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:14.673271+00:00
-- url     : https://prove2.me/submissions/70d26832-d26c-4f56-bbad-9e8d5c4941bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob

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
open Finset
open GroundTheory.Heights₂.Heights.KAlt
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    frobDelta (fun a => s + ν a) = frobDelta ν := by
  unfold frobDelta
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast; ring
  · rfl
end GroundTheory.Heights₂.Heights.KAlt
