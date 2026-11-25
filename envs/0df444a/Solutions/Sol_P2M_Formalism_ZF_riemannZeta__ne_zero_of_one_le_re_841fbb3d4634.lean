-- Prove2me | solution 1 for P2M_Formalism_ZF_riemannZeta__ne_zero_of_one_le_re_841fbb3d4634
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:48:50.572941+00:00
-- url     : https://prove2.me/submissions/2d5cb06e-8ac7-47be-82c8-2f89e78548d6

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  intro h
  by_cases hs1 : s = 1
  · subst hs1
    simp at h
  · have hz := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero] at hz
    exact hz rfl
end Formalism.ZF
