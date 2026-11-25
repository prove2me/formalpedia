-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.cc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:18.470731+00:00
-- url     : https://prove2.me/submissions/5aa2aa7a-3acf-47f2-a3aa-59633a46c24f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler

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
open Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}
namespace PositivityTheory.RgJS.Common0Aux
theorem _root_.solution (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (p : W × ℕ) :
    0 ≤ cc q A u p := by
  unfold cc; positivity
end PositivityTheory.RgJS.Common0Aux
