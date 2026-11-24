-- Prove2me | solution 1 for SensitivityGraphPopulation.quadratic_independence_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:52.088635+00:00
-- url     : https://prove2.me/submissions/803f33e5-a7c1-4646-8ae1-ba19ce4d0123

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GraphPopulationBounds
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SimpleGraph
end SimpleGraph

section


/-! The quadratic population inequality from an actual independence cap. -/

namespace SensitivityGraphPopulation

noncomputable section
open scoped Classical
open SimpleGraph
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {V : Type} [Fintype V]



theorem edgeFinset_card_eq (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card = edgeCount G := by
  simp only [edgeFinset, Set.toFinset_card, edgeCount, Nat.card_eq_fintype_card]

theorem complement_edge_partition (G : SimpleGraph V) :
    edgeCount G + edgeCount Gᶜ = (Fintype.card V).choose 2 := by
  have hset : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    rw [← edgeFinset_sup]
    exact edgeFinset_inj.mpr sup_compl_eq_top
  have hcard := Finset.card_union_of_disjoint (disjoint_edgeFinset.mpr
    (show Disjoint G Gᶜ from disjoint_compl_right))
  rw [hset] at hcard
  have htop := card_edgeFinset_top_eq_card_choose_two (V := V)
  simp only [edgeFinset_card_eq] at hcard htop
  exact hcard.symm.trans htop



theorem cliqueFree_edge_bound (G : SimpleGraph V) (alpha : ℕ) (hpos : 0 < alpha)
    (hfree : G.CliqueFree (alpha + 1)) :
    2 * alpha * edgeCount G ≤ (alpha - 1) * Fintype.card V ^ 2 := by
  obtain ⟨H, hdec, hmax⟩ := exists_isTuranMaximal (V := V) hpos
  letI := hdec
  have hbound := hmax.2 hfree
  have hiso := hmax.nonempty_iso_turanGraph.some.card_edgeFinset_eq
  rw [hiso] at hbound
  have hscaled := Nat.mul_le_mul_left (2 * alpha) hbound
  have hturan := mul_card_edgeFinset_turanGraph_le (n := Fintype.card V) (r := alpha)
  simp only [edgeFinset_card_eq] at hscaled hturan
  exact hscaled.trans hturan





end
end SensitivityGraphPopulation

end

/-! The quadratic population inequality from an actual independence cap. -/
open SensitivityGraphPopulation
open scoped Classical
open SimpleGraph
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {V : Type} [Fintype V]

theorem solution (G : SimpleGraph V) (alpha : ℕ)
    (hpos : 0 < alpha)
    (hind : ∀ vertices : Finset V, G.IsIndepSet vertices → vertices.card ≤ alpha) :
    Fintype.card V ^ 2 ≤ alpha * (Fintype.card V + 2 * edgeCount G) := by
  have hfree : Gᶜ.CliqueFree (alpha + 1) := by
    intro vertices hclique
    have hbound := hind vertices ((isClique_compl (G := G)).mp hclique.1)
    rw [hclique.2] at hbound
    omega
  have hbound := cliqueFree_edge_bound Gᶜ alpha hpos hfree
  have hpart := complement_edge_partition G
  have hn := twice_choose_two (Fintype.card V)
  have hfactor : alpha - 1 + 1 = alpha := Nat.sub_add_cancel hpos
  have htotal : alpha * (Fintype.card V +
      2 * (edgeCount G + edgeCount Gᶜ)) = alpha * Fintype.card V ^ 2 := by
    rw [hpart, hn]
  have hcancel : Fintype.card V ^ 2 + 2 * alpha * edgeCount Gᶜ ≤
      alpha * (Fintype.card V + 2 * edgeCount G) + 2 * alpha * edgeCount Gᶜ := by
    calc
      _ ≤ Fintype.card V ^ 2 + (alpha - 1) * Fintype.card V ^ 2 :=
        Nat.add_le_add_left hbound _
      _ = (alpha - 1 + 1) * Fintype.card V ^ 2 := by ring
      _ = alpha * Fintype.card V ^ 2 := by rw [hfactor]
      _ = alpha * (Fintype.card V + 2 * edgeCount G) +
          2 * alpha * edgeCount Gᶜ := by rw [← htotal]; ring
  exact Nat.le_of_add_le_add_right hcancel
