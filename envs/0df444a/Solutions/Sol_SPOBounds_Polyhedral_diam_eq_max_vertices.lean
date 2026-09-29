-- Prove2me | solution 1 for SPOBounds.Polyhedral.diam_eq_max_vertices
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:49:59.254578+00:00
-- url     : https://prove2.me/submissions/fec32141-a451-4c3f-865e-36187161cf67

import Mathlib

namespace SPOBounds.Polyhedral

theorem aux_dmv_diam_range {E : Type*} [NormedAddCommGroup E]
    {K : ℕ} (hK : 0 < K) (v : Fin K → E) :
    ∃ p0 : Fin K × Fin K, Metric.diam (Set.range v) = ‖v p0.1 - v p0.2‖ ∧
      ∀ p : Fin K × Fin K, ‖v p.1 - v p.2‖ ≤ ‖v p0.1 - v p0.2‖ := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨p0, -, hp0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin K × Fin K))
    (fun p : Fin K × Fin K => ‖v p.1 - v p.2‖) Finset.univ_nonempty
  have hmax : ∀ p : Fin K × Fin K, ‖v p.1 - v p.2‖ ≤ ‖v p0.1 - v p0.2‖ :=
    fun p => hp0 p (Finset.mem_univ p)
  refine ⟨p0, le_antisymm ?_ ?_, hmax⟩
  · apply Metric.diam_le_of_forall_dist_le (norm_nonneg _)
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    rw [dist_eq_norm]
    exact hmax (i, j)
  · rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      ⟨p0.1, rfl⟩ ⟨p0.2, rfl⟩

end SPOBounds.Polyhedral

open SPOBounds.Polyhedral

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ} (hK : 0 < K) (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) :
    IsGreatest (Set.range fun p : Fin K × Fin K => ‖v p.1 - v p.2‖) (Metric.diam S) := by
  obtain ⟨p0, hd, hmax⟩ := aux_dmv_diam_range hK v
  have hdS : Metric.diam S = ‖v p0.1 - v p0.2‖ := by
    rw [hS, convexHull_diam, hd]
  refine ⟨⟨p0, hdS.symm⟩, ?_⟩
  rintro r ⟨p, rfl⟩
  rw [hdS]
  exact hmax p
