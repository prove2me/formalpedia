-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:55.540243+00:00
-- url     : https://prove2.me/submissions/336b694c-59b1-4ebd-ad45-57b847682d48

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_cover_exists
import Theorems.Thm_Paper_Hypergraph_le_coverCost
import Theorems.Thm_Paper_Hypergraph_cover_cap

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) :
    ∃ y, H.Cover x y ∧ (∀ e ∈ H.edges, y e ≤ 1) ∧
      H.coverCost x = ∑ e ∈ H.edges, y e := by
  let E := {e // e ∈ H.edges}
  let extend : (E → ℝ) → ℕ → ℝ := fun z e => if he : e ∈ H.edges then z ⟨e, he⟩ else 0
  have hext (e : ℕ) : Continuous (fun z : E → ℝ => extend z e) := by
    dsimp [extend]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  let K : Set (E → ℝ) := Set.Icc 0 1 ∩ {z | H.Cover x (extend z)}
  have hclosed : IsClosed {z : E → ℝ | H.Cover x (extend z)} := by
    unfold Cover
    simp only [Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter
    · exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        isClosed_le continuous_const (hext e)
    · exact isClosed_iInter fun v => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_finsetSum _ (fun e _ => hext e))
  have hcompact : IsCompact K := isCompact_Icc.inter_right hclosed
  have hmem (y : ℕ → ℝ) (hy : H.Cover x y) :
      (fun e : E => min (y e) 1) ∈ K := by
    have heq : ∀ e ∈ H.edges,
        extend (fun e : E => min (y e) 1) e = min (y e) 1 := by
      intro e he
      simp [extend, he]
    refine ⟨⟨fun e => le_min (hy.1 e e.property) (by norm_num),
      fun _ => min_le_right _ _⟩, ?_⟩
    refine ⟨fun e he => by rw [heq e he]; exact le_min (hy.1 e he) (by norm_num), ?_⟩
    intro v hv
    convert (H.cover_cap hx hy).2 v hv using 1
    apply sum_congr rfl
    intro e he
    exact heq e (mem_filter.mp he).1
  obtain ⟨y0, hy0⟩ := H.cover_exists x
  have hcont : Continuous (fun z : E → ℝ => ∑ e ∈ H.edges, extend z e) :=
    continuous_finsetSum _ (fun e _ => hext e)
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn ⟨_, hmem y0 hy0⟩ hcont.continuousOn
  refine ⟨extend z, hz.2, ?_, le_antisymm (H.coverCost_le hz.2) ?_⟩
  · intro e he
    simpa [extend, he] using hz.1.2 ⟨e, he⟩
  · apply H.le_coverCost
    intro y hy
    calc
      (∑ e ∈ H.edges, extend z e) ≤
          ∑ e ∈ H.edges, extend (fun e : E => min (y e) 1) e := hmin (hmem y hy)
      _ ≤ ∑ e ∈ H.edges, y e := by
        apply sum_le_sum
        intro e he
        simpa [extend, he] using min_le_left (y e) 1
end Paper.Hypergraph
