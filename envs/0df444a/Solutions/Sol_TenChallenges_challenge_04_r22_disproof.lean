-- Prove2me | solution 1 for TenChallenges.challenge_04_r22_disproof
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T21:51:39.808987+00:00
-- url     : https://prove2.me/submissions/145d898a-ef84-4909-bc7c-9a5c166e5bc6

import Definitions.Def_TenChallenges_Challenge_04
import Theorems.Thm_OAI_SidorenkoCounterexample_main
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option linter.style.haveILetI false

open SimpleGraph

namespace TenChallenges.Challenge04R22Disproof

abbrev Pattern := OAI.SidorenkoCounterexample.PatternVertex
abbrev H := OAI.SidorenkoCounterexample.H

lemma density_agrees {W V : Type} [Fintype W] [Fintype V]
    (F : SimpleGraph W) (G : SimpleGraph V) :
    _root_.homDensity F G = OAI.SidorenkoCounterexample.homDensity F G := by
  simp only [_root_.homDensity, OAI.SidorenkoCounterexample.homDensity,
    OAI.SidorenkoCounterexample.homCount, Nat.card_eq_fintype_card]

lemma edge_density_agrees {V : Type} [Fintype V] (G : SimpleGraph V) :
    _root_.homDensity (completeGraph (Fin 2)) G =
      OAI.SidorenkoCounterexample.edgeDensity G := by
  classical
  unfold _root_.homDensity OAI.SidorenkoCounterexample.edgeDensity
  rw [Fintype.card_fin, Nat.card_eq_fintype_card (α := V)]
  congr 1
  norm_cast
  trans Nat.card G.Dart
  · apply Nat.card_congr
    refine { toFun := fun f => ⟨(f.1 0, f.1 1), f.2 (by decide)⟩
             invFun := fun d => ⟨fun i => if i = 0 then d.fst else d.snd, ?_⟩
             left_inv := fun f => Subtype.ext (funext fun i => by fin_cases i <;> rfl)
             right_inv := fun d => by cases d; rfl }
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [d.adj, d.adj.symm]
  · simpa only [Nat.card_eq_fintype_card, G.edgeFinset_card]
      using G.dart_card_eq_twice_card_edges

set_option maxRecDepth 10000 in
lemma pattern_edges : Nat.card H.edgeSet = 66 := by
  let : DecidableRel H.Adj := fun x y => match x, y with
    | .inl i, .inr j => inferInstanceAs (Decidable (i ∈ OAI.SidorenkoCounterexample.faces j))
    | .inr j, .inl i => inferInstanceAs (Decidable (i ∈ OAI.SidorenkoCounterexample.faces j))
    | .inl _, .inl _ => isFalse id
    | .inr _, .inr _ => isFalse id
  rw [Nat.card_eq_fintype_card, H.card_edgeSet]
  decide

lemma pattern_bipartite_bounded_22 : BipartiteBoundedBy H 22 := by
  refine ⟨Set.range (Sum.inl : Fin 13 → Pattern),
    Set.range (Sum.inr : Fin 22 → Pattern), ?_, Set.range_inl_union_range_inr, ?_, ?_⟩
  · constructor
    · simp [Set.disjoint_left]
    · intro a b hab
      cases a <;> cases b <;>
        simp_all [H, OAI.SidorenkoCounterexample.H, OAI.SidorenkoCounterexample.incidence]
  · rw [Set.ncard_range_of_injective Sum.inl_injective]
    simp
  · rw [Set.ncard_range_of_injective Sum.inr_injective]
    simp

set_option maxRecDepth 10000 in
theorem canonical_counterexample :
    ∃ n : ℕ, 0 < n ∧ ∃ G : SimpleGraph (Fin n), ¬ SidorenkoFor H G := by
  obtain ⟨n, hn, G, _, hviol⟩ := OAI.SidorenkoCounterexample.main
  refine ⟨n, hn, G, ?_⟩
  rw [SidorenkoFor, edge_density_agrees, density_agrees, pattern_edges, not_le]
  exact hviol

theorem not_statement_04_22 : ¬ TenChallenges.statement_04 22 := by
  intro hall
  obtain ⟨n, hn, G, hbad⟩ := canonical_counterexample
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hbad (hall H G pattern_bipartite_bounded_22)

end TenChallenges.Challenge04R22Disproof

/-- Refutation of the exact `r = 22` Sidorenko benchmark statement (`statement_04 22`). -/
theorem solution : ¬ TenChallenges.statement_04 22 :=
  TenChallenges.Challenge04R22Disproof.not_statement_04_22
