-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:16.088951+00:00
-- url     : https://prove2.me/submissions/2db4d1ed-0dee-4a2c-a4c7-6cdcd4c5b5f4

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ p : (k : K) → ι k, (∀ k, z ⟨k, p k⟩ ≠ 0) ∧ ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, p k⟩‖ := by
  have hmax : ∀ k, ∃ i, ∀ j, ‖z ⟨k, j⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun j => ‖z ⟨k, j⟩‖)
  choose p hp using hmax
  refine ⟨p, fun k => ?_, fun k i => hp k i⟩
  obtain ⟨i0, hi0⟩ := hz k
  have h1 : 0 < ‖z ⟨k, i0⟩‖ := norm_pos_iff.mpr hi0
  have h2 := hp k i0
  intro h
  rw [h, norm_zero] at h2
  linarith
end ReciprocityTheory.AnForm.R
