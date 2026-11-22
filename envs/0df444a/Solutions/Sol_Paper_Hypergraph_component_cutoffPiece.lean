-- Prove2me | solution 1 for Paper.Hypergraph.component_cutoffPiece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:29.64159+00:00
-- url     : https://prove2.me/submissions/4d70bd4a-76f5-49a6-a169-f79e2cee1df5

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_RoundingCutoff
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
import Theorems.Thm_Paper_Hypergraph_edgeVolume_mono
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj
import Theorems.Thm_Paper_Hypergraph_roundingBall_volume_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {φ r C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (hr : r < 1) (hC : 0 ≤ C) {Q : Finset ℕ} (hQ : Q ⊆ H.vertices)
    {c : ℕ} (hc : c ∈ Q)
    (hball : ∀ v, (H.induce Q).primal.Reachable c v → (H.induce Q).vertexDistance x c v ≤ r) :
    Nonempty (H.CutoffPiece γ x Q (φ / (1 - r) * ∑ e ∈ H.edges, γ e) C) := by
  have hcJ : c ∈ (H.induce Q).vertices := mem_inter.mpr ⟨hQ hc, hc⟩
  obtain ⟨P, hP, hcP⟩ := (H.induce Q).exists_component_of_mem hcJ
  have hPV := mem_powerset.mp (mem_filter.mp hP).1
  have hPQ : P ⊆ Q := fun v hv => (mem_inter.mp (hPV hv)).2
  have hPB : P ⊆ H.roundingBall x Q c r := by
    intro v hv
    exact mem_filter.mpr ⟨hPV hv,
      hball v (((H.induce Q).component_mem_iff_reachable hP hcP (hPV hv)).mp hv)⟩
  refine ⟨{
    piece := P
    separator := ∅
    nonempty := ⟨c, hcP⟩
    piece_subset := hPQ
    separator_subset := empty_subset _
    disjoint := by simp
    support := empty_subset _
    separated := ?_
    volume_le := (H.edgeVolume_mono hγ hPB).trans (H.roundingBall_volume_le hγ hx Q hcJ hr)
    cost_le := ?_ }⟩
  · intro e he
    by_contra hn
    obtain ⟨hu, hv⟩ := not_or.mp hn
    obtain ⟨u, hue, huP⟩ := not_disjoint_iff.mp hu
    obtain ⟨v, hve, hvQ⟩ := not_disjoint_iff.mp hv
    have hv := mem_sdiff.mp hvQ
    have hnP : v ∉ P := by simpa using hv.2
    have huv : u ≠ v := by intro h; subst v; exact hnP huP
    have hadj := (H.primal_induce_adj Q (hPQ huP) hv.1).mpr ⟨huv, e, he, hue, hve⟩
    exact hnP (((H.induce Q).component_mem_iff_reachable hP huP
      (mem_inter.mpr ⟨hQ hv.1, hv.1⟩)).mpr hadj.reachable)
  · have hz : H.setCoverCost ∅ = 0 := H.coverCost_eq_zero_of_nonpos
      (fun v hv => by simp [indicator])
    rw [hz]
    exact mul_nonneg hC (H.coverCost_nonneg _)
end Paper.Hypergraph
