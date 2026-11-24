-- Prove2me | solution 1 for SensitivityGraphPopulation.integral_independence_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:12.605505+00:00
-- url     : https://prove2.me/submissions/c3ef1482-c3bf-4c3b-bd19-80864d75e967

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GraphPopulationBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
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









end
end SensitivityGraphPopulation

end

section


/-! The exact integral Turán lower edge count used by the source population tables. -/
namespace SensitivityGraphPopulation

noncomputable section
open scoped Classical
open SimpleGraph
set_option autoImplicit false



theorem choose_two_add (n m : ℕ) :
    (n + m).choose 2 = n.choose 2 + m.choose 2 + n * m := by
  have hn := twice_choose_two n
  have hm := twice_choose_two m
  have hnm := twice_choose_two (n + m)
  nlinarith

theorem minimumEdges_add (n alpha : ℕ) (hpos : 0 < alpha) :
    minimumEdges (n + alpha) alpha = minimumEdges n alpha + n := by
  unfold minimumEdges
  rw [Nat.add_div_right _ hpos, Nat.add_mod_right, Nat.choose_succ_succ' _ 1,
    Nat.choose_one_right]
  have hdiv := Nat.mod_add_div n alpha
  nlinarith only [hdiv]

theorem minimumEdges_turan_partition (alpha : ℕ) (hpos : 0 < alpha) :
    ∀ n, minimumEdges n alpha + edgeCount (turanGraph n alpha) = n.choose 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < alpha
    · have htop : turanGraph n alpha = ⊤ := turanGraph_eq_top.mpr (Or.inr hsmall.le)
      have htopCard : edgeCount (turanGraph n alpha) = n.choose 2 := by
        rw [htop]
        simpa only [edgeFinset_card_eq, Fintype.card_fin] using
          card_edgeFinset_top_eq_card_choose_two (V := Fin n)
      simp only [minimumEdges, Nat.div_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall,
        Nat.choose_zero_succ, Nat.mul_zero, Nat.zero_add, htopCard]
    · let before := n - alpha
      have hn : n = before + alpha := by omega
      have hbefore : before < n := by omega
      have hp := ih before hbefore
      have he := card_edgeFinset_turanGraph_add (n := before) (r := alpha)
      simp only [edgeFinset_card_eq] at he
      rw [hn, minimumEdges_add before alpha hpos, he, choose_two_add]
      have hfactor : alpha - 1 + 1 = alpha := Nat.sub_add_cancel hpos
      have hmul := congrArg (fun a => before * a) hfactor
      nlinarith only [hp, hmul]






end
end SensitivityGraphPopulation

end

/-! The exact integral Turán lower edge count used by the source population tables. -/
open SensitivityGraphPopulation
open scoped Classical
open SimpleGraph
set_option autoImplicit false

theorem solution {V : Type} [Fintype V]
    (G : SimpleGraph V) (alpha : ℕ) (hpos : 0 < alpha)
    (hind : ∀ vertices : Finset V, G.IsIndepSet vertices → vertices.card ≤ alpha) :
    minimumEdges (Fintype.card V) alpha ≤ edgeCount G := by
  have hfree : Gᶜ.CliqueFree (alpha + 1) := by
    intro vertices hclique
    have hbound := hind vertices ((isClique_compl (G := G)).mp hclique.1)
    rw [hclique.2] at hbound
    omega
  obtain ⟨H, hdec, hmax⟩ := exists_isTuranMaximal (V := V) hpos
  letI := hdec
  have hbound := hmax.2 hfree
  have hiso := hmax.nonempty_iso_turanGraph.some.card_edgeFinset_eq
  rw [hiso] at hbound
  simp only [edgeFinset_card_eq] at hbound
  have hgraph := complement_edge_partition G
  have hturan := minimumEdges_turan_partition alpha hpos (Fintype.card V)
  omega
