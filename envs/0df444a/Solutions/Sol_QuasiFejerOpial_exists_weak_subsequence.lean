-- Prove2me | solution 1 for QuasiFejerOpial.exists_weak_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:48:53.345696+00:00
-- url     : https://prove2.me/submissions/a63056ae-6466-4e8f-8ec2-6a8202495e9d

import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

/-!
# Weakly convergent subsequences of bounded Hilbert-space sequences

Standard weak sequential compactness, via sequential Banach-Alaoglu and the
Riesz representation theorem. For a possibly nonseparable Hilbert space we
restrict to the separable closed linear span of the sequence and lift weak
convergence using orthogonal projection. No first-countability assumption on
the weak topology of the ambient space is made.
-/
open Filter Topology InnerProductSpace
open ThreeOpSplitting.Convergence

namespace QuasiFejerOpial

universe u

/-- The separable case of Hilbert weak sequential compactness. -/
theorem exists_weak_subsequence_separable {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (x : ℕ → E) (R : ℝ) (hR : ∀ n, ‖x n‖ ≤ R) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ p : E, WeakTendsto (x ∘ r) p := by
  let f : ℕ → WeakDual ℝ E := fun n => StrongDual.toWeakDual (toDual ℝ E (x n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) R := by
    intro n
    simpa [f, Metric.mem_closedBall, dist_zero_right] using hR n
  obtain ⟨w, _, r, hr, hw⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) R) hf
  refine ⟨r, hr, (toDual ℝ E).symm (WeakDual.toStrongDual w), ?_⟩
  intro y
  have h := ((WeakDual.eval_continuous y).tendsto w).comp hw
  have heq : inner ℝ ((toDual ℝ E).symm (WeakDual.toStrongDual w)) y = w y := by
    change (toDual ℝ E ((toDual ℝ E).symm (WeakDual.toStrongDual w))) y = w y
    simp
  change Tendsto (fun k => inner ℝ (x (r k)) y) atTop (𝓝 (w y)) at h
  rw [heq]
  exact h

end QuasiFejerOpial

open QuasiFejerOpial
universe u

/-- Every norm-bounded sequence in a real Hilbert space has a strictly
increasing weakly convergent subsequence, with no separability hypothesis. -/
theorem solution {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : ℕ → E) (R : ℝ) (hR : ∀ n, ‖x n‖ ≤ R) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ p : E, WeakTendsto (x ∘ r) p := by
  let F : Submodule ℝ E := (Submodule.span ℝ (Set.range x)).topologicalClosure
  have hs : TopologicalSpace.IsSeparable (F : Set E) := by
    exact ((Set.countable_range x).isSeparable.span (R := ℝ)).closure
  letI : TopologicalSpace.SeparableSpace F := hs.separableSpace
  have hxF : ∀ n, x n ∈ F := fun n =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let v : ℕ → F := fun n => ⟨x n, hxF n⟩
  have hv : ∀ n, ‖v n‖ ≤ R := hR
  obtain ⟨r, hr, p, hp⟩ := exists_weak_subsequence_separable v R hv
  refine ⟨r, hr, (p : E), ?_⟩
  intro y
  have h := hp (F.orthogonalProjectionOnto y)
  simpa only [Function.comp_apply, v,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using h

