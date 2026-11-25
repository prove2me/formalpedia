-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r24a.quadratic_form_smul_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:58.757267+00:00
-- url     : https://prove2.me/submissions/8443477d-0746-45f1-93e6-8ca221c86219

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_InvNormSmulMemSphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r24a
namespace UpperTheory.Reformulated.B.P6.r24a
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
  ring
end UpperTheory.Reformulated.B.P6.r24a
