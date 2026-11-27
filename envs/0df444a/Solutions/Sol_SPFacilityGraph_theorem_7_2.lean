-- Prove2me | solution 1 for SPFacilityGraph.theorem_7_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:57:34.870573+00:00
-- url     : https://prove2.me/submissions/22f4e651-e22b-4e99-8b93-84a1a286f042
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_SPFacilityGraph_lemma_Q_4
import Theorems.Thm_SPFacilityGraph_lemma_Q_1

set_option autoImplicit false

open SPFacilityGraph

theorem solution {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (M : Profile G n → G.Pt) (hM : Function.Surjective M) :
    List.TFAE [IsSP G M, IsSSP G M,
      ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
        IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K] := by
  -- `d_G(t, t) = 0`: the one-point walk has length `0`, and every walk length is `≥ 0`.
  have hdist0 : ∀ t : G.Pt, G.dist t t = 0 := by
    intro t
    unfold MetricGraph.dist
    apply IsLeast.csInf_eq
    refine ⟨⟨[(t : EuclideanSpace ℝ (Fin k))], by simp, by simp, by simp, by simp⟩, ?_⟩
    rintro L ⟨l, -, -, -, rfl⟩
    exact List.sum_nonneg (by
      intro a ha
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
      exact norm_nonneg _)
  tfae_have 1 → 3 := fun hSP => lemma_Q_4 hn G M hSP hM
  tfae_have 3 → 2 := fun ⟨W, K, hK, hA⟩ => lemma_Q_1 G M W K hK hA
  tfae_have 2 → 1 := by
    intro hSSP x i z
    have h := hSSP i (x i) x (x i) z (by rw [hdist0, zero_add])
    simpa [Function.update_eq_self] using h
  tfae_finish
