-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.dl_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:05.048031+00:00
-- url     : https://prove2.me/submissions/de9a8ea2-d7dc-47a8-80a9-515b3fb37f36

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.Delta
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.Delta
theorem _root_.solution (c : ℂ) : dl p q r s (C c) = c • ((1 : Pol p q r 0) ⊗ₜ[ℂ] (1 : Pol p q 0 s)) := by
  rw [dl, aeval_C, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
end PositivityTheory.KReal.Delta
