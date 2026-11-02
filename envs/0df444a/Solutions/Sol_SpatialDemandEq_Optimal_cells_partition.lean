-- Prove2me | solution 1 for SpatialDemandEq.Optimal.cells_partition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:37:31.162093+00:00
-- url     : https://prove2.me/submissions/b5758985-34bd-4425-8f57-480586a204ed

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory
open SpatialDemandEq.Optimal

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (w : Fin K → ℝ) :
    IsPartition ν S (cell S (distFn dst xs) w) ∧
      ∑ k, area ν (cell S (distFn dst xs) w k) = 1 := by
  have hprob := hS.prob
  have hne : Nonempty (Fin K) := ⟨⟨0, hS.K_pos⟩⟩
  set d := distFn dst xs with hd
  have hcont : ∀ k, Continuous (d k) := by
    intro k
    have h := hS.metric.1
    exact h.comp (Continuous.prodMk continuous_id continuous_const)
  have hclosed : ∀ k, IsClosed (cell S d w k) := by
    intro k
    have : cell S d w k = S ∩ ⋂ j, ⋂ (_ : j ≠ k), {x | d k x + w k ≤ d j x + w j} := by
      ext x; simp [cell]
    rw [this]
    exact hS.closed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le ((hcont k).add continuous_const) ((hcont j).add continuous_const))
  have hmeas : ∀ k, MeasurableSet (cell S d w k) := fun k => (hclosed k).measurableSet
  have hsub : ∀ k, cell S d w k ⊆ S := fun k x hx => hx.1
  have hunion : (⋃ k, cell S d w k) = S := by
    apply Set.Subset.antisymm (Set.iUnion_subset hsub)
    intro x hx
    obtain ⟨k, hk⟩ := Finite.exists_min (fun i => d i x + w i)
    exact Set.mem_iUnion.mpr ⟨k, hx, fun j _ => hk j⟩
  have hnull : ∀ j k, j ≠ k → ν (cell S d w j ∩ cell S d w k) = 0 := by
    intro j k hjk
    set f : E n → ℝ := fun x => d j x - d k x
    have hfm : Measurable f := ((hcont j).sub (hcont k)).measurable
    have hsubset : cell S d w j ∩ cell S d w k ⊆ f ⁻¹' {w k - w j} := by
      rintro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      have a := h1 k hjk.symm
      have b := h2 j hjk
      simp only [Set.mem_preimage, Set.mem_singleton_iff, f]
      linarith
    apply measure_mono_null hsubset
    rw [← Measure.map_apply hfm (measurableSet_singleton _)]
    exact hS.regular j k hjk (Real.volume_singleton)
  refine ⟨⟨hmeas, hsub, hunion, hnull⟩, ?_⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint ν) (cell S d w)) := by
    intro j k hjk
    exact hnull j k hjk
  have hU := measure_iUnion₀ hdisj (fun k => (hmeas k).nullMeasurableSet)
  rw [hunion, tsum_fintype] at hU
  have hSone : ν S = 1 := by
    rw [measure_congr (ae_eq_univ.mpr hS.supp), measure_univ]
  unfold area
  rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top _ _), ← hU, hSone]
  simp
