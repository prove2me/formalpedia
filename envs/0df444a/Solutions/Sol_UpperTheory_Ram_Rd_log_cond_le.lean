-- Prove2me | solution 1 for UpperTheory.Ram.Rd.log_cond_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:12.081671+00:00
-- url     : https://prove2.me/submissions/491ee3a3-f0f5-462f-a01b-59433680db77

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_log_QS_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Rd
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Ram.Rd
theorem _root_.solution : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * Real.log R.n + Real.log H.q + Real.log H.d := by
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq : (0 : ℝ) < H.q := by exact_mod_cast hyp.1.pos
  have hd : (0 : ℝ) < H.d := by exact_mod_cast hyp.2.1.pos
  have hQ : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  rw [Real.log_mul (mul_pos hQ hq).ne' hd.ne', Real.log_mul hQ.ne' hq.ne']
  linarith [log_QS_le H]
end UpperTheory.Ram.Rd
