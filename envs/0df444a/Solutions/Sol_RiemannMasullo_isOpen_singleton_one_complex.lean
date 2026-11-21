-- Prove2me | solution 1 for RiemannMasullo.isOpen_singleton_one_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:16:41.258314+00:00
-- url     : https://prove2.me/submissions/b35aa929-b893-4b79-90ba-bf72b05ce7ee

module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Definitions.Def_RiemannMasullo_ForMathlib_Topology_Algebra_Group_CompactOpen

set_option autoImplicit false
@[expose] public section
public section
open RiemannMasullo
open Filter
namespace RiemannMasullo
theorem _root_.solution {G : Type*} [Monoid G] [TopologicalSpace G] [CompactSpace G] :
    IsOpen ({1} : Set (G →ₜ* ℂ)) := by
  let V : Set (G →ₜ* ℂ) := {c | Set.MapsTo c Set.univ (Metric.ball 1 1)}
  have hV : IsOpen V := isOpen_induced
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ Metric.isOpen_ball)
  have hVeq : V = {1} := by
    ext c
    rw [Set.mem_singleton_iff]
    refine ⟨fun hc ↦ ?_, ?_⟩
    · obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := G))
        ((c.continuous.sub continuous_const).norm.continuousOn)
      have hbound (y : G) : ‖c y - 1‖ ≤ ‖c x - 1‖ := isMaxOn_univ_iff.mp hx y
      have hclose : ‖c x - 1‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hc (Set.mem_univ x)
      have hfactor : 1 < ‖c x + 1‖ := by
        have h := norm_add_le (c x + 1) (1 - c x)
        have hsum : c x + 1 + (1 - c x) = 2 := by ring
        rw [hsum, norm_sub_rev, Complex.norm_ofNat] at h
        linarith
      -- Squaring would increase the maximum distance from one if it were positive.
      have hsq := hbound (x ^ 2)
      have hsq_factor : c x ^ 2 - 1 = (c x + 1) * (c x - 1) := by ring
      rw [map_pow, hsq_factor, norm_mul] at hsq
      have hzero : ‖c x - 1‖ = 0 := by
        nlinarith [norm_nonneg (c x - 1)]
      ext1 y
      change c y = 1
      exact sub_eq_zero.mp (norm_eq_zero.mp
        (le_antisymm ((hbound y).trans_eq hzero) (norm_nonneg _)))
    · rintro rfl y _
      simp [Metric.mem_ball]
  simpa [hVeq] using hV
end RiemannMasullo
