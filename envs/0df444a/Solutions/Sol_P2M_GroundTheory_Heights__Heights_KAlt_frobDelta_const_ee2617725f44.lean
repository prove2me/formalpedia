-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_const_ee2617725f44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:53.832494+00:00
-- url     : https://prove2.me/submissions/17458007-4259-456b-94e3-3c91248fe448

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_prod_sub_eq_prod_factorial_80b5f99ca249

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
theorem _root_.solution {r : ℕ} (s : ℕ) :
    frobDelta (fun _ : Fin r => s) = ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) := by
  rw [← prod_sub_eq_prod_factorial r]
  unfold frobDelta
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  split_ifs with h
  · have ha := a.isLt
    have hb := b.isLt
    have hab : (a : ℕ) < b := h
    have : ((s + (r - 1 - (a : ℕ)) : ℕ) : ℚ) + ((a : ℕ) : ℚ) =
        ((s + (r - 1 - (b : ℕ)) : ℕ) : ℚ) + ((b : ℕ) : ℚ) := by
      exact_mod_cast (show s + (r - 1 - (a : ℕ)) + a = s + (r - 1 - (b : ℕ)) + b by omega)
    linarith
  · rfl
end GroundTheory.Heights₂.Heights.KAlt
