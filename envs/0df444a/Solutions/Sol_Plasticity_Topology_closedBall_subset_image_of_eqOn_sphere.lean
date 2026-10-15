-- Prove2me | solution 1 for Plasticity.Topology.closedBall_subset_image_of_eqOn_sphere
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:36:52.795922+00:00
-- url     : https://prove2.me/submissions/daea7a8b-0906-41fe-9b37-3ee5a781532f

import Theorems.Thm_Plasticity_Ext_NoRetraction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.ContinuousOn

namespace Sol_Plasticity_Topology_closedBall_subset_image_of_eqOn_sphere

end Sol_Plasticity_Topology_closedBall_subset_image_of_eqOn_sphere

open Metric Set Topology in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (g : V → V) (hg : ContinuousOn g (Metric.closedBall (0 : V) 1))
    (hid : ∀ z ∈ Metric.sphere (0 : V) 1, g z = z) :
    Metric.closedBall (0 : V) 1 ⊆ g '' Metric.closedBall (0 : V) 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact fun z hz => ⟨z, hz, Subsingleton.elim _ _⟩
  intro z₀ hz₀
  by_contra hno
  have hz₀1 : ‖z₀‖ < 1 := by
    rcases (mem_closedBall_zero_iff.mp hz₀).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨z₀, hz₀, hid z₀ (mem_sphere_zero_iff_norm.mpr h)⟩ hno
  set s : Set V := closedBall (-z₀) 1 with hs
  have hsc : Convex ℝ s := convex_closedBall _ _
  have hs0 : s ∈ 𝓝 (0 : V) :=
    closedBall_mem_nhds_of_mem (by rw [mem_ball, dist_eq_norm]; simpa using hz₀1)
  have hsb : Bornology.IsVonNBounded ℝ s :=
    NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall
  have hsa : Absorbent ℝ s := absorbent_nhds_zero hs0
  have hcont : Continuous (gauge s) := continuous_gauge hsc hs0
  have hpos : ∀ w : V, w ≠ 0 → 0 < gauge s w := fun w hw => (gauge_pos hsa hsb).2 hw
  have hfront : ∀ w : V, gauge s w = 1 ↔ ‖w + z₀‖ = 1 := by
    intro w
    rw [gauge_eq_one_iff_mem_frontier hsc hs0, hs, frontier_closedBall _ one_ne_zero, mem_sphere,
      dist_eq_norm, sub_neg_eq_add]
  have hne : ∀ z ∈ closedBall (0 : V) 1, g z - z₀ ≠ 0 :=
    fun z hz h => hno ⟨z, hz, sub_eq_zero.mp h⟩
  let r : V → V := fun z => z₀ + (gauge s (g z - z₀))⁻¹ • (g z - z₀)
  have hr : ContinuousOn r (closedBall (0 : V) 1) := by
    apply continuousOn_const.add
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact hcont.comp_continuousOn (hg.sub continuousOn_const)
      · intro z hz
        exact (hpos _ (hne z hz)).ne'
    · exact hg.sub continuousOn_const
  have hmaps : MapsTo r (closedBall (0 : V) 1) (sphere (0 : V) 1) := by
    intro z hz
    have hw := hne z hz
    have hg1 : gauge s ((gauge s (g z - z₀))⁻¹ • (g z - z₀)) = 1 := by
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr (gauge_nonneg _)), smul_eq_mul,
        inv_mul_cancel₀ (hpos _ hw).ne']
    rw [hfront] at hg1
    rw [mem_sphere_zero_iff_norm]
    simpa [r, add_comm] using hg1
  obtain ⟨x, hx, hrx⟩ := Plasticity.Ext.NoRetraction r hr hmaps
  apply hrx
  have hgx := hid x hx
  have h1 : gauge s (x - z₀) = 1 := by
    rw [hfront]
    simpa using mem_sphere_zero_iff_norm.mp hx
  simp [r, hgx, h1]
