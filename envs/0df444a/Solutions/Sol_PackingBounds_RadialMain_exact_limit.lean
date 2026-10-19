-- Prove2me | solution 1 for PackingBounds.RadialMain.exact_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/9f8e2ff1-b26e-4e53-9c86-7d3879af3ec5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpPackingRootAsymptotic

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
        CohnElkies.linearProgram d ^ ((d : ℝ)⁻¹))
      atTop
      (nhds (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) := by
  simpa [CohnElkies.SharpPackingRootAsymptotic,
    CohnElkies.criticalPackingBase] using!
    CohnElkies.sharpPackingRootAsymptotic
end PackingBounds.RadialMain
