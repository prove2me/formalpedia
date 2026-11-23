-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.sliceChart_symm_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:43.909802+00:00
-- url     : https://prove2.me/submissions/c586aaf9-5bf3-41eb-ad51-857d2bea46fb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]
open Classical
namespace ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
theorem _root_.solution {e : ℕ} (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) (S : Set X) (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S)
    {z : Fin e → ℂ} (hz : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target) :
    ((sliceChart ψ i S hS w0).symm z : X) = ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z) := by
  obtain ⟨w, hw⟩ : ∃ w, w = (sliceChart ψ i S hS w0).symm z := ⟨_, rfl⟩
  rw [← hw]
  have hws : w ∈ (sliceChart ψ i S hS w0).source := by
    rw [hw]
    exact (sliceChart ψ i S hS w0).map_target hz
  have hwz : (sliceChart ψ i S hS w0) w = z := by
    rw [hw]
    exact (sliceChart ψ i S hS w0).right_inv hz
  have hψw : (w : X) ∈ ψ.source := hws
  have h0 : ψ w i = 0 := (hS _ hψw).1 w.2
  have hrem : i.removeNth (ψ w) = z := hwz
  have h2 : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by
    rw [Fin.insertNth_removeNth, Function.update_eq_self_iff, h0]
  rw [hrem] at h2
  rw [h2, ψ.left_inv hψw]
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
