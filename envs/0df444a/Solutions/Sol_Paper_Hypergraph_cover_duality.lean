-- Prove2me | solution 1 for Paper.Hypergraph.cover_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:19.365807+00:00
-- url     : https://prove2.me/submissions/f201a31f-2149-4eba-8a4c-63712b157095

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_coverCost_support
import Theorems.Thm_Paper_Hypergraph_modular_le_coverCost

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ} (_hx : H.UnitDemand x) :
    ∃ w, H.ModularWeight w ∧ H.coverCost x = ∑ v ∈ H.vertices, w v * x v ∧
      ∀ w', H.ModularWeight w' → (∑ v ∈ H.vertices, w' v * x v) ≤ H.coverCost x := by
  obtain ⟨g, hgx, hg⟩ := H.coverCost_support x
  let w : ℕ → ℝ := fun v => g (Pi.single v 1)
  have hw0 : ∀ v, 0 ≤ w v := by
    intro v
    have hz : H.coverCost (-Pi.single v 1) = 0 := by
      apply H.coverCost_eq_zero_of_nonpos
      intro u hu
      simp only [Pi.neg_apply, Pi.single_apply]
      split_ifs <;> norm_num
    have hh := hg (-Pi.single v 1)
    rw [hz, map_neg] at hh
    dsimp [w]
    linarith
  have hsum (S : Finset ℕ) (z : ℕ → ℝ) :
      g (∑ v ∈ S, z v • Pi.single v (1 : ℝ)) = ∑ v ∈ S, z v * w v := by
    simp [map_sum, map_smul, smul_eq_mul, w]
  have hsingle (S : Finset ℕ) (z : ℕ → ℝ) (u : ℕ) :
      (∑ v ∈ S, z v • Pi.single v (1 : ℝ)) u = if u ∈ S then z u else 0 := by
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hwE : ∀ e ∈ H.edges, ∑ v ∈ H.edge e, w v ≤ 1 := by
    intro e he
    have heq : (∑ v ∈ H.edge e, (1 : ℝ) • Pi.single v (1 : ℝ)) = indicator (H.edge e) := by
      ext u
      exact hsingle (H.edge e) (fun _ => 1) u
    have hcover : H.Cover (indicator (H.edge e)) (Pi.single e 1) := by
      refine ⟨?_, ?_⟩
      · intro f hf
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · intro v hv
        by_cases hve : v ∈ H.edge e
        · simp [indicator, hve, Pi.single_apply, he]
        · simp only [indicator, if_neg hve]
          apply sum_nonneg
          intro f hf
          simp only [Pi.single_apply]
          split_ifs <;> norm_num
    have hc : H.setCoverCost (H.edge e) ≤ 1 := by
      simpa [setCoverCost, Pi.single_apply, he] using H.coverCost_le hcover
    have hh := (hg (indicator (H.edge e))).trans hc
    rw [← heq, hsum] at hh
    simpa using hh
  have hrepr : g x = ∑ v ∈ H.vertices, x v * w v := by
    let z := ∑ v ∈ H.vertices, x v • Pi.single v (1 : ℝ)
    have hz : ∀ v ∈ H.vertices, (x - z) v = 0 := by
      intro v hv
      simp [Pi.sub_apply, z, hsingle, hv]
    have hpos := hg (x - z)
    have hneg := hg (-(x - z))
    rw [H.coverCost_eq_zero_of_nonpos (fun v hv => le_of_eq (hz v hv))] at hpos
    rw [H.coverCost_eq_zero_of_nonpos (by intro v hv; simp [hz v hv]), map_neg] at hneg
    have heq : g (x - z) = 0 := by linarith
    rw [map_sub] at heq
    exact (sub_eq_zero.mp heq).trans (hsum _ _)
  refine ⟨w, ⟨hw0, hwE⟩, ?_, fun w' hw' => H.modular_le_coverCost hw' x⟩
  rw [← hgx, hrepr]
  apply sum_congr rfl
  intro v hv
  exact mul_comm _ _
end Paper.Hypergraph
