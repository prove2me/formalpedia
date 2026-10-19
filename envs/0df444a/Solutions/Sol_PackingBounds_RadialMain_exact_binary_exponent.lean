-- Prove2me | solution 1 for PackingBounds.RadialMain.exact_binary_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/728ff70b-5656-4e80-97e2-d2d8b2e9d99b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpBinaryLogAsymptotic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped FourierTransform SchwartzMap Topology
open PackingBounds PackingBounds.RadialMain
namespace PackingBounds.RadialMain
theorem _root_.solution :
    Tendsto
      (fun d : ℕ =>
        Real.logb 2 (CohnElkies.linearProgram d) / (d : ℝ))
      atTop
      (nhds (-(1 / 2 : ℝ) *
        Real.logb 2 (2 * Real.pi / Real.exp 1))) := by
  simpa [CohnElkies.SharpBinaryLogAsymptotic,
    CohnElkies.criticalBinaryExponent] using!
    CohnElkies.sharpBinaryLogAsymptotic
end PackingBounds.RadialMain
