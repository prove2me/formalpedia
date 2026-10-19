-- Prove2me | solution 2 for SchwartzMap.reference_basis_fundamental_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:22:12.779841+00:00
-- url     : https://prove2.me/submissions/62312453-cd64-45d1-94f1-37457021f836

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform Real
open MeasureTheory Module
open SchwartzMap
variable {d : ℕ}


theorem solution :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).real
        (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
  have hset : ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) =
      (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 1) := by
    ext x; simp [ZSpan.mem_fundamentalDomain]
  rw [Measure.real, hset, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet, Real.volume_pi_Ico]
  simp

