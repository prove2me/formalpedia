-- Prove2me | solution 1 for PhysicalCostTransfer.selected_state_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/2918c503-50bb-4034-aba3-e38266f05253

import Definitions.Def_SelectedFloorTransfer
import Definitions.Def_PhysicalCostTransfer
import Theorems.Thm_PhysicalCostTransfer_state_all_width_bound
import Theorems.Thm_PhysicalCostTransfer_uniformConstant_nonneg
import Theorems.Thm_PhysicalCostTransfer_uniformConstant_base
import Theorems.Thm_PhysicalCostTransfer_uniformConstant_overhead
import Theorems.Thm_SelectedProfileReal_actual_power_characteristic_lt_one
import Theorems.Thm_SelectedProfileReal_row_valid


set_option autoImplicit true
open PhysicalCostTransfer
open scoped BigOperators
open SelectedProfileCertificate
namespace PhysicalCostTransfer
theorem _root_.solution {S : Type}
    (width : S → ℕ) (volume cost : S → ℝ)
    (child : S → (r : Row) → Fin r.multiplicity → S)
    (B C : ℝ) (hvolume : ∀ s, 0 ≤ volume s)
    (child_width : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      width (child s r j) = r.width * (width s / m))
    (child_volume : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      volume (child s r j) = volume s / W)
    (uniform_base : ∀ s, 0 < width s → width s < m → cost s ≤ B * volume s)
    (physical_recurrence : ∀ s, m ≤ width s → cost s ≤ C * volume s +
      (rows.map (fun r => ∑ j : Fin r.multiplicity, cost (child s r j))).sum) :
    ∀ s, 0 < width s → cost s ≤ selectedConstant B C * volume s *
      (width s : ℝ) ^ (1 - (saving : ℝ)) := by
  apply state_all_width_bound rows (fun r => r.width) (fun r => r.multiplicity) m W
    width volume cost child (1 - (saving : ℝ)) (selectedConstant B C) B C
    SelectedProfileReal.powerCharacteristic
  · norm_num [m]
  · norm_num [W]
  · norm_num [saving]
  · exact uniformConstant_nonneg B C _ SelectedProfileReal.actual_power_characteristic_lt_one
  · exact uniformConstant_base B C _ SelectedProfileReal.actual_power_characteristic_lt_one
  · exact uniformConstant_overhead B C _ SelectedProfileReal.actual_power_characteristic_lt_one
  · exact hvolume
  · intro r hr; exact (SelectedProfileReal.row_valid r hr).1
  · intro r hr; exact (SelectedProfileReal.row_valid r hr).2.1
  · rfl
  · exact SelectedProfileReal.actual_power_characteristic_lt_one
  · exact child_width
  · exact child_volume
  · exact uniform_base
  · exact physical_recurrence
end PhysicalCostTransfer
