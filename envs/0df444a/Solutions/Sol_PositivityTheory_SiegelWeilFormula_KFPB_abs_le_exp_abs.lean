-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.abs_le_exp_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:48.722041+00:00
-- url     : https://prove2.me/submissions/7e827688-55d0-480f-88a1-3fc6abcb3311

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrableRexpLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (x : ℝ) : |x| ≤ Real.exp |x| := by
  have := Real.add_one_le_exp |x|
  linarith
end PositivityTheory.SiegelWeilFormula.KFPB
