-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.integrable_mul_chr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:51.751043+00:00
-- url     : https://prove2.me/submissions/267c0e34-87bf-4f53-ab46-9d86b9b4b91b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_continuous_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_norm_chr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution {g : E n → ℂ} (hg : Integrable g) (hc : Continuous g) (t : ℝ) (β : E n) :
    Integrable fun y => g y * chr t β y :=
  hg.norm.mono' (hc.mul (continuous_chr t β)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [norm_mul, norm_chr, mul_one])
end PositivityTheory.Rg.Sw.WR.Ib
