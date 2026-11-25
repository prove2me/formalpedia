-- Prove2me | solution 1 for P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cc_nonneg_31edcbb41409
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:36.485071+00:00
-- url     : https://prove2.me/submissions/c19d484c-f56a-46fc-a02a-4c042241bdc1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.DirichletSeriesUnbounded₂
variable {W X : Type} (q : W → ℕ) {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (x : ι → X)
namespace PositivityTheory.RgJS.DirichletSeriesUnbounded₂
theorem _root_.solution (p : W × ℕ) : 0 ≤ cc A x p := by
  unfold cc; positivity
end PositivityTheory.RgJS.DirichletSeriesUnbounded₂
