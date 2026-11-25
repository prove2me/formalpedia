-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.uSer_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:22.648482+00:00
-- url     : https://prove2.me/submissions/d2efa971-76d3-4902-a92c-29b619c27870

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_wpNum_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_wpDen_map
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_wpDen_const__5e7138a2c865

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  have hD : constantCoeff (wpDen (φ g2) (φ g3)) ≠ 0 := by rw [wpDen_const']; exact one_ne_zero
  have hD0 : constantCoeff (wpDen g2 g3) ≠ 0 := by rw [wpDen_const']; exact one_ne_zero
  have h : map φ (wpDen g2 g3)⁻¹ = (wpDen (φ g2) (φ g3))⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hD, ← wpDen_map, ← map_mul,
      PowerSeries.inv_mul_cancel _ hD0, map_one]
  unfold uSer
  rw [map_mul, map_mul, map_X, wpNum_map, h]
end ReciprocityTheory.ChartRestriction.L1
