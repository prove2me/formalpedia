-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.cpow_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:31.863453+00:00
-- url     : https://prove2.me/submissions/9c2010a9-a89d-4252-8bdc-9da9ad0c2309

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
theorem _root_.solution (q : ℕ) (t : ℝ) : (q : ℂ) ^ (-(t : ℂ)) = (((q : ℝ) ^ (-t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, Complex.ofReal_neg]
end PositivityTheory.RgJS.Common0Aux
