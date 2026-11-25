-- Prove2me | solution 1 for PositivityTheory.RgJS.EulerProductLogLemmas.x_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:03.613455+00:00
-- url     : https://prove2.me/submissions/e11d4e55-ef3a-495f-8cfb-5c0e804e1743

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound

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
open PositivityTheory.RgJS.EulerProductLogLemmas
variable {W : Type} {A B : Type} [Fintype A] [Fintype B]
namespace PositivityTheory.RgJS.EulerProductLogLemmas
theorem _root_.solution {q : W → ℕ} (s : ℂ) (w : W) : 0 ≤ (q w : ℝ) ^ (1 - s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
end PositivityTheory.RgJS.EulerProductLogLemmas
