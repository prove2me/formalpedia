-- Prove2me | solution 1 for UpperTheory.Ram.Rd.sqrt_qd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:42.049962+00:00
-- url     : https://prove2.me/submissions/78417779-7d11-4c84-b212-3046c721ddb4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN

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
theorem _root_.solution : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq : (2 : ℝ) ≤ H.q := by exact_mod_cast hyp.1.two_le
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast hyp.2.1.two_le
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [mul_le_mul hq hd (by norm_num) (by linarith)]
end UpperTheory.Ram.Rd
