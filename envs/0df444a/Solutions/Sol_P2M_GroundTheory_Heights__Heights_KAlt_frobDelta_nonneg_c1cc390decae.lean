-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_nonneg_c1cc390decae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:16.618488+00:00
-- url     : https://prove2.me/submissions/5edd6b88-b02e-4af8-95f9-786e8f553b3e

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
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) : 0 ≤ frobDelta ν := by
  unfold frobDelta
  refine prod_nonneg fun a _ => prod_nonneg fun b _ => ?_
  split_ifs with h
  · have h1 : ν b ≤ ν a := hν h.le
    have hab : (a : ℕ) < b := h
    have hb := b.isLt
    have h2 : ν b + (r - 1 - (b : ℕ)) ≤ ν a + (r - 1 - (a : ℕ)) := by omega
    rw [sub_nonneg]
    exact_mod_cast h2
  · exact zero_le_one
end GroundTheory.Heights₂.Heights.KAlt
