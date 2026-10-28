-- Prove2me | solution 1 for OptimumBranchings.Polytope.dual_certificate_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T04:27:13.710028+00:00
-- url     : https://prove2.me/submissions/8ee67c37-6e9f-4b0d-9ad0-cbc6d92373e5

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron
import Definitions.Def_OptimumBranchings_Polytope_DualCertificate
import Theorems.Thm_OptimumBranchings_Polytope_branching_vector_mem

namespace OptimumBranchings.Polytope

private lemma sum_front_mul {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (zNode : V → ℝ) (x : E → ℝ) :
    ∑ e : E, zNode (G.front e) * x e =
      ∑ v : V, zNode v * (∑ e ∈ Finset.univ.filter (fun e => G.front e = v), x e) := by
  rw [← Finset.sum_fiberwise Finset.univ G.front (fun e => zNode (G.front e) * x e)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [(Finset.mem_filter.mp he).2]

private lemma sum_edgeSetDual_mul {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (zSet : Finset V → ℝ) (x : E → ℝ) :
    ∑ e : E, edgeSetDual G zSet e * x e =
      ∑ S ∈ Finset.univ.filter (fun S : Finset V => 2 ≤ S.card),
        (∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S), x e) * zSet S := by
  simp only [edgeSetDual, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  by_cases hS : 2 ≤ S.card
  · simp only [hS, true_and, ↓reduceIte, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e _ => by split_ifs <;> ring)
  · simp only [hS, false_and, ↓reduceIte, Finset.sum_const_zero, zero_mul]

private lemma dual_decomp {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (zNode : V → ℝ) (zSet : Finset V → ℝ) (x : E → ℝ) :
    ∑ e : E, (zNode (G.front e) + edgeSetDual G zSet e) * x e =
      (∑ v : V, zNode v * (∑ e ∈ Finset.univ.filter (fun e => G.front e = v), x e)) +
      (∑ S ∈ Finset.univ.filter (fun S : Finset V => 2 ≤ S.card),
        (∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S), x e) * zSet S) := by
  simp only [add_mul, Finset.sum_add_distrib]
  rw [sum_front_mul, sum_edgeSetDual_mul]

private lemma weak_duality {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (c : E → ℝ) (x : E → ℝ)
    (zNode : V → ℝ) (zSet : Finset V → ℝ)
    (hx : x ∈ branchingPolyhedron G) (hz : IsDualFeasible G c zNode zSet) :
    ∑ e, c e * x e ≤ dualObjective zNode zSet := by
  rcases hx with ⟨hx1, hx2, hx3⟩
  rcases hz with ⟨hz1, hz2, hz3⟩
  have hle1 : ∑ e, c e * x e ≤ ∑ e, (zNode (G.front e) + edgeSetDual G zSet e) * x e := by
    refine Finset.sum_le_sum (fun e _ => ?_)
    exact mul_le_mul_of_nonneg_right (hz3 e) (hx1 e)
  rw [dual_decomp] at hle1
  refine le_trans hle1 ?_
  unfold dualObjective
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum (fun v _ => ?_)
    have hv := mul_le_mul_of_nonneg_left (hx2 v) (hz1 v)
    linarith
  · refine Finset.sum_le_sum (fun S hS => ?_)
    have hScard : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
    exact mul_le_mul_of_nonneg_right (hx3 S hScard) (hz2 S hScard)

theorem dual_certificate_optimal_main {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (c : E → ℝ) (B : Finset E) (yNode : V → ℝ)
    (ySet : Finset V → ℝ) (hB : G.IsBranching B)
    (hy : IsDualCertificate G c B yNode ySet) :
    ∑ e, c e * incidenceVector B e = dualObjective yNode ySet ∧
    incidenceVector B ∈ branchingPolyhedron G ∧
    (∀ x ∈ branchingPolyhedron G, ∑ e, c e * x e ≤ ∑ e, c e * incidenceVector B e) ∧
    (∀ (zNode : V → ℝ) (zSet : Finset V → ℝ), IsDualFeasible G c zNode zSet →
      dualObjective yNode ySet ≤ dualObjective zNode zSet) := by
  have hBmem : incidenceVector B ∈ branchingPolyhedron G :=
    OptimumBranchings.Polytope.branching_vector_mem G B hB
  rcases hy with ⟨hyFeas, hyNode, hySet, hyEdge⟩
  have hEq : ∑ e, c e * incidenceVector B e = dualObjective yNode ySet := by
    have h1 : ∑ e, c e * incidenceVector B e =
        ∑ e, (yNode (G.front e) + edgeSetDual G ySet e) * incidenceVector B e := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      unfold incidenceVector
      by_cases he : e ∈ B
      · simp [he, hyEdge e he]
      · simp [he]
    rw [h1, dual_decomp]
    unfold dualObjective
    congr 1
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      by_cases hv : yNode v = 0
      · simp [hv]
      · rw [hyNode v hv, mul_one]
    · refine Finset.sum_congr rfl (fun S hS => ?_)
      have hScard : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
      by_cases hSy : ySet S = 0
      · simp [hSy]
      · rw [hySet S hScard hSy]
  refine ⟨hEq, hBmem, ?_, ?_⟩
  · intro x hx
    rw [hEq]
    exact weak_duality G c x yNode ySet hx hyFeas
  · intro zNode zSet hz
    rw [← hEq]
    exact weak_duality G c (incidenceVector B) zNode zSet hBmem hz

end OptimumBranchings.Polytope

open OptimumBranchings.Polytope in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : OptimumBranchings.Polytope.Graph V E) (c : E → ℝ) (B : Finset E)
    (yNode : V → ℝ) (ySet : Finset V → ℝ) (hB : G.IsBranching B)
    (hy : IsDualCertificate G c B yNode ySet) :
    ∑ e, c e * incidenceVector B e = dualObjective yNode ySet ∧
    incidenceVector B ∈ branchingPolyhedron G ∧
    (∀ x ∈ branchingPolyhedron G, ∑ e, c e * x e ≤ ∑ e, c e * incidenceVector B e) ∧
    (∀ (zNode : V → ℝ) (zSet : Finset V → ℝ), IsDualFeasible G c zNode zSet →
      dualObjective yNode ySet ≤ dualObjective zNode zSet) :=
  OptimumBranchings.Polytope.dual_certificate_optimal_main G c B yNode ySet hB hy
