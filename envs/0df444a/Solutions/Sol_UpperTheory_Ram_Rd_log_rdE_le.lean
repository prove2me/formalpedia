-- Prove2me | solution 1 for UpperTheory.Ram.Rd.log_rdE_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:44.237626+00:00
-- url     : https://prove2.me/submissions/a3fea382-5493-47a7-9af1-39ffe9ac5404

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_log_QS_le
import Theorems.Thm_UpperTheory_Ram_Rd_rdE_pos
import Theorems.Thm_UpperTheory_Ram_Rd_rdE_le_QS

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
theorem _root_.solution : Real.log H.rdE ≤ 2 * Real.log R.n + (Real.log H.q + Real.log H.d) / 2 := by
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq : (0 : ℝ) < H.q := by exact_mod_cast hyp.1.pos
  have hd : (0 : ℝ) < H.d := by exact_mod_cast hyp.2.1.pos
  have hQ : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hs : 0 < Real.sqrt ((H.q : ℝ) * H.d) := Real.sqrt_pos.2 (mul_pos hq hd)
  have h1 : H.rdE ≤ (H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d) := by
    have := rdE_le_QS H
    nlinarith [mul_pos hQ hs]
  calc Real.log H.rdE ≤ Real.log ((H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d)) := Real.log_le_log (rdE_pos H) h1
    _ = Real.log H.QS + (Real.log H.q + Real.log H.d) / 2 := by
      rw [Real.log_mul hQ.ne' hs.ne', Real.log_sqrt (mul_pos hq hd).le, Real.log_mul hq.ne' hd.ne']
    _ ≤ 2 * Real.log R.n + (Real.log H.q + Real.log H.d) / 2 := by linarith [log_QS_le H]
end UpperTheory.Ram.Rd
