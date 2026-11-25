-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r24a.inv_norm_smul_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:54.564602+00:00
-- url     : https://prove2.me/submissions/c6b62ae0-29ee-4b9d-981c-64c53f161015

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
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
end UpperTheory.Reformulated.B.P6.r24a
