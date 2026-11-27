-- Prove2me | solution 1 for SizeRamsey.Proof.equality_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:38:09.59661+00:00
-- url     : https://prove2.me/submissions/4dc41427-c944-4281-97cd-25db809360f8

module
public import Definitions.Def_SizeRamsey_Equality_DegreeFour
public import Definitions.Def_SizeRamsey_Equality_Mixed
public import Definitions.Def_SizeRamsey_Equality_Cubic
public import Definitions.Def_SizeRamsey_Equality_TwoRegular
public import Definitions.Def_SizeRamsey_Equality
public import Theorems.Thm_SizeRamsey_Plan_classification_of_step
public import Theorems.Thm_SizeRamsey_Plan_classified_tight
public import Theorems.Thm_SizeRamsey_Plan_degree_two_three_cases
public import Theorems.Thm_SizeRamsey_Plan_equality_cubic_impossible
public import Theorems.Thm_SizeRamsey_Plan_equality_degree_four_case
public import Theorems.Thm_SizeRamsey_Plan_equality_max_degree_le_four
public import Theorems.Thm_SizeRamsey_Plan_equality_min_degree
public import Theorems.Thm_SizeRamsey_Plan_equality_mixed_degree_case
public import Theorems.Thm_SizeRamsey_Plan_equality_two_regular_case


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Proof
namespace SizeRamsey.Proof
theorem _root_.solution
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected)
    (hpos : 0 < edgeCount G)
    (hle : edgeCount G ≤ 16) :
    4 * tau4 G = edgeCount G ↔
      Nonempty (G ≃g SimpleGraph.cycleGraph 4) ∨
      Nonempty (G ≃g wheel5) ∨
      Nonempty (G ≃g k33MinusEdge) ∨
      Nonempty (G ≃g octahedron) := by
  classical
  refine ⟨?_, Plan.classified_tight G⟩
  intro ht
  apply Plan.classification_of_step (G := G) _ hconn hpos hle ht
  intro W inst H hc hp hm ht ih
  by_cases hfour : ∃ v, H.degree v = 4
  · exact Plan.equality_degree_four_case H hc hp hm ht ih hfour
  · have hthree : ∀ v, H.degree v ≤ 3 := by
      intro v; have := Plan.equality_max_degree_le_four H ht v; have : H.degree v ≠ 4 := fun hv => hfour ⟨v, hv⟩; omega
    have hcases : ∀ v, H.degree v = 2 ∨ H.degree v = 3 := by intro v; have := Plan.equality_min_degree H hc hp ht v; have := hthree v; omega
    rcases Plan.degree_two_three_cases H hc hcases with htwo | hthree' | hmixed
    · exact Or.inl (Plan.equality_two_regular_case H hc hp ht htwo)
    · exact (Plan.equality_cubic_impossible H hc hp hm ht ih hthree').elim
    · exact Or.inr (Or.inr (Or.inl (Plan.equality_mixed_degree_case H hc hp hm ht ih hthree hmixed)))
end SizeRamsey.Proof
