-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.contDiff_eF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:12.647192+00:00
-- url     : https://prove2.me/submissions/96aa62ed-c636-4b93-968d-e58c66523005

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose

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
noncomputable section
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  have h1 : ContDiff ℝ ∞ (fun y : E d => ((inner ℝ y ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)
  exact Complex.contDiff_exp.comp ((contDiff_const.mul h1).neg)
end ZetaZeros.D.EllReg.Dec
