-- Prove2me | solution 1 for Plasticity.Ext.NoRetraction
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T18:44:38.604803+00:00
-- url     : https://prove2.me/submissions/56d2b05d-0fe7-4743-9b04-cbaea32c9808

import Theorems.Thm_AGT_brouwer_fixed_point
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.ContinuousOn

namespace Sol_Plasticity_Ext_NoRetraction

end Sol_Plasticity_Ext_NoRetraction

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V] (r : V → V) (hr : ContinuousOn r (Metric.closedBall (0 : V) 1))
    (hmaps : Set.MapsTo r (Metric.closedBall (0 : V) 1) (Metric.sphere (0 : V) 1)) :
    ∃ x ∈ Metric.sphere (0 : V) 1, r x ≠ x := by
  by_contra hcon
  push Not at hcon
  have hg : ContinuousOn (fun x => -r x) (Metric.closedBall (0 : V) 1) := hr.neg
  have hgK : Set.MapsTo (fun x => -r x) (Metric.closedBall (0 : V) 1)
      (Metric.closedBall (0 : V) 1) := by
    intro x hx
    have h1 := hmaps hx
    rw [mem_sphere_zero_iff_norm] at h1
    rw [mem_closedBall_zero_iff, norm_neg, h1]
  obtain ⟨x, hx, hfix⟩ := AGT.brouwer_fixed_point (convex_closedBall (0 : V) 1)
    (isCompact_closedBall (0 : V) 1) ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    (fun x => -r x) hg hgK
  have hrx : r x ∈ Metric.sphere (0 : V) 1 := hmaps hx
  have hxs : x ∈ Metric.sphere (0 : V) 1 := by
    rw [mem_sphere_zero_iff_norm] at hrx ⊢
    rw [← hfix, norm_neg, hrx]
  have hrxx : r x = x := hcon x hxs
  rw [hrxx] at hfix
  have hx0 : x = 0 := by
    have : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← hfix]; exact neg_add_cancel x
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [mem_sphere_zero_iff_norm, hx0, norm_zero] at hxs
  exact zero_ne_one hxs
