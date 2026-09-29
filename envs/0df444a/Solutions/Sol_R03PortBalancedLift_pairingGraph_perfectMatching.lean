-- Prove2me | solution 1 for R03PortBalancedLift.pairingGraph_perfectMatching
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:52:26.724586+00:00
-- url     : https://prove2.me/submissions/62e8ecd9-b73e-40ad-a0d4-f88d1e221b4d

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v

namespace R03PortBalancedLift

open CubicP3Partition

universe u v

variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]

noncomputable section
open scoped Classical

lemma contractedRelation_symm (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) {p q : P} {i j : Fin 2} :
    contractedRelation G pair p i q j ↔
      contractedRelation G pair q j p i := by
  constructor
  · intro h
    exact ⟨h.1.symm, (G.adj_comm _ _).mp h.2⟩
  · intro h
    exact ⟨h.1.symm, (G.adj_comm _ _).mp h.2⟩

lemma contractedRelation_no_quotient_loop (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) (p : P) (i j : Fin 2) :
    ¬ contractedRelation G pair p i p j := by
  intro h
  exact h.1 rfl

lemma portFlip_zero : portFlip (0 : Fin 2) = 1 := by simp [portFlip]
lemma portFlip_one : portFlip (1 : Fin 2) = 0 := by simp [portFlip]

lemma portFlip_ne (p : Fin 2) : portFlip p ≠ p := by
  fin_cases p <;> simp [portFlip]

lemma portFlip_injective : Function.Injective portFlip := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;> simp [portFlip] at hpq ⊢

lemma portFlip_eq_iff {p q : Fin 2} :
    portFlip p = q ↔ p ≠ q := by
  fin_cases p <;> fin_cases q <;> simp [portFlip]

lemma portFlip_portFlip (p : Fin 2) : portFlip (portFlip p) = p := by
  fin_cases p <;> simp [portFlip]

lemma pairingGraph_adj_iff (pair : (P × Fin 2) ≃ V)
    (p : P) (b : Fin 2) (w : V) :
    (pairingGraph pair).Adj (pair (p, b)) w ↔
      w = pair (p, portFlip b) := by
  fin_cases b
  · constructor
    · rintro ⟨q, h | h⟩
      · have hp := pair.injective h.1
        have hq : p = q := congrArg Prod.fst hp
        simpa [hq, portFlip] using h.2
      · have hp := pair.injective h.1
        exact False.elim (Fin.zero_ne_one (congrArg Prod.snd hp))
    · intro h
      exact ⟨p, Or.inl ⟨rfl, h⟩⟩
  · constructor
    · rintro ⟨q, h | h⟩
      · have hp := pair.injective h.1
        exact False.elim (Fin.zero_ne_one (congrArg Prod.snd hp).symm)
      · have hp := pair.injective h.1
        have hq : p = q := congrArg Prod.fst hp
        simpa [hq, portFlip] using h.2
    · intro h
      exact ⟨p, Or.inr ⟨rfl, h⟩⟩

lemma pairingGraph_degree (pair : (P × Fin 2) ≃ V)
    (p : P) (b : Fin 2) :
    degree (pairingGraph pair) (pair (p, b)) = 1 := by
  let e : {w : V // (pairingGraph pair).Adj (pair (p, b)) w} ≃ Fin 1 :=
    {
      toFun := fun _ => 0
      invFun := fun _ =>
        ⟨pair (p, portFlip b), (pairingGraph_adj_iff pair p b _).2 rfl⟩
      left_inv := by
        intro w
        apply Subtype.ext
        exact (pairingGraph_adj_iff pair p b w.1).mp w.2 |>.symm
      right_inv := by
        intro x
        fin_cases x
        rfl
    }
  change Nat.card {w : V // (pairingGraph pair).Adj (pair (p, b)) w} = 1
  rw [Nat.card_congr e]
  simp


end
end R03PortBalancedLift

open R03PortBalancedLift
open CubicP3Partition
universe u v
variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]
open scoped Classical
theorem solution
    (G : SimpleGraph V) (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))) :
    PerfectMatching G (pairingGraph pair) := by
  constructor
  · intro u v huv
    rcases huv with ⟨p, h | h⟩
    · simpa [h.1, h.2] using pair_edge p
    · simpa [h.1, h.2] using (G.adj_comm _ _).mp (pair_edge p)
  · intro v
    obtain ⟨⟨p, b⟩, rfl⟩ := pair.surjective v
    exact pairingGraph_degree pair p b
