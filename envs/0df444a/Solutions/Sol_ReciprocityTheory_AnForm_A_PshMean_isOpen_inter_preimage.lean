-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMean.isOpen_inter_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:32.771259+00:00
-- url     : https://prove2.me/submissions/5bd80de9-9208-47cc-ae9e-04935fe82102

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshMean
theorem _root_.solution {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) (y : ℝ) : IsOpen (φ ⁻¹' Iio y ∩ U) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hxU⟩
  have h := hφ x hxU y hx
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h
  filter_upwards [h, hU.mem_nhds hxU] with x' h1 h2
  exact ⟨h1, h2⟩
end ReciprocityTheory.AnForm.A.PshMean
