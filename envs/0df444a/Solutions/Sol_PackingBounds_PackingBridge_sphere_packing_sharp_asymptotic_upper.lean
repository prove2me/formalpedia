-- Prove2me | solution 1 for PackingBounds.PackingBridge.sphere_packing_sharp_asymptotic_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/032641c9-0193-425c-9961-ee11c0278e32

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_manuscriptPackingIsLittleO
import Theorems.Thm_PackingBounds_PackingBridge_sphere_packing_le_radial_linear_program_ennreal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds PackingBounds.PackingBridge
namespace PackingBounds.PackingBridge
theorem _root_.solution :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d →
        SpherePackingConstant d ≤
          ENNReal.ofReal
            ((Real.sqrt (Real.exp 1 / (2 * Real.pi)) + e d) ^ d) := by
  obtain ⟨e, he, hformula⟩ := CohnElkies.exists_manuscriptPackingIsLittleO
  refine ⟨e, he, fun d hd => ?_⟩
  change SpherePackingConstant d ≤
    ENNReal.ofReal ((CohnElkies.criticalPackingBase + e d) ^ d)
  rw [← hformula d hd]
  exact sphere_packing_le_radial_linear_program_ennreal hd
end PackingBounds.PackingBridge
