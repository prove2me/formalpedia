-- Prove2me | solution 1 for SupplyChainTheory.revised_cost_identities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:31:00.13997+00:00
-- url     : https://prove2.me/submissions/e4951ec0-c8c5-47f8-b292-35cf2bd0cef1

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (lam : Fin n → ℝ) :
    (∀ τ : Equiv.Perm (Fin n), tourLength (revisedCost c lam) τ = tourLength c τ + 2 * ∑ i, lam i)
      ∧ (∀ τ : Equiv.Perm (Fin n), IsMinOn (tourLength c) Set.univ τ →
          IsMinOn (tourLength (revisedCost c lam)) Set.univ τ)
      ∧ ∀ (r : Fin n) (G : SimpleGraph (Fin n)), Is1Tree r G →
          graphWeight (revisedCost c lam) G = graphWeight c G + ∑ i, G.degree i * lam i := by
  -- (a) Each node is left once and entered once along a tour.
  have ha : ∀ τ : Equiv.Perm (Fin n),
      tourLength (revisedCost c lam) τ = tourLength c τ + 2 * ∑ i, lam i := by
    intro τ
    simp only [tourLength, revisedCost, Finset.sum_add_distrib]
    have h1 : ∑ k, lam (τ k) = ∑ i, lam i := Equiv.sum_comp τ lam
    have h2 : ∑ k, lam (τ (finRotate n k)) = ∑ i, lam i :=
      Equiv.sum_comp (τ * finRotate n) lam
    rw [h1, h2]; ring
  refine ⟨ha, ?_, ?_⟩
  · -- (b) The revised tour length differs from the original by a constant.
    intro τ hτ x _
    rw [Set.mem_ofPred_eq, ha, ha]
    have := hτ (Set.mem_univ x)
    simp only [Set.mem_ofPred_eq] at this
    linarith
  · -- (c) Each edge `{i, j}` contributes `λᵢ + λⱼ`; summing over edges counts `λᵥ` once per
    -- incident edge, i.e. `deg v` times.
    intro r G _
    have hedge : ∀ e : Sym2 (Fin n), ¬ e.IsDiag →
        edgeCost (revisedCost c lam) e
          = edgeCost c e + ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), lam v := by
      intro e he
      induction e using Sym2.ind with
      | h i j =>
        have hij : i ≠ j := by simpa using he
        have hf : Finset.univ.filter (fun v => v ∈ s(i, j)) = {i, j} := by
          ext v; simp
        rw [hf, Finset.sum_pair hij]
        simp only [edgeCost, Sym2.lift_mk, revisedCost]
        ring
    have hdeg : ∑ i, (G.degree i : ℝ) * lam i
        = ∑ e ∈ G.edgeFinset, ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), lam v := by
      calc ∑ i, (G.degree i : ℝ) * lam i
          = ∑ i, ∑ e ∈ G.incidenceFinset i, lam i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_const, G.card_incidenceFinset_eq_degree, nsmul_eq_mul]
        _ = ∑ e ∈ G.edgeFinset, ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), lam v := by
            refine Finset.sum_comm' (fun i e => ?_)
            simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, and_comm]
    simp only [graphWeight]
    rw [hdeg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e he => hedge e ?_)
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
