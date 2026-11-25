-- Prove2me | solution 1 for P2M_Formalism_ZeroFreeDirichlet_inRegion_mono__5281f592e2e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:48:52.362497+00:00
-- url     : https://prove2.me/submissions/a8b72ea2-5454-4dae-a514-1b8fec7b7636

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_mul_abs_add_two_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at *
  have hL := log_mul_abs_add_two_pos q s.im
  have := div_le_div_of_nonneg_right h hL.le
  linarith
end Formalism.ZeroFreeDirichlet
