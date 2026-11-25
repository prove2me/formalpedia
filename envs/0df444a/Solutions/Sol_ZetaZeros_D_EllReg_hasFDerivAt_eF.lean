-- Prove2me | solution 1 for ZetaZeros.D.EllReg.hasFDerivAt_eF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:36.620458+00:00
-- url     : https://prove2.me/submissions/0156aa84-c07d-446b-9a77-276a7092f779

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
import Theorems.Thm_ZetaZeros_D_EllReg_eF_eq_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp
end ZetaZeros.D.EllReg
