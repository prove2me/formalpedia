-- Prove2me | solution 1 for R03SP06Arithmetic.cubic_three_dvd_implies_six_dvd
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:11.488236+00:00
-- url     : https://prove2.me/submissions/441ba639-be34-4416-ae8a-3bceaefb4874

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only arithmetic bridge: cubicity forces even order, so the frozen
root's 3-divisibility entails the six-divisibility used in the cited source's
z1 notation.  This does not prove the P3-factor theorem.
-/

namespace R03SP06Arithmetic

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

/-- A finite cubic simple graph has even order. -/
theorem cubic_order_even {G : SimpleGraph V} (hC : Cubic G) :
    2 ∣ Fintype.card V := by
  classical
  have hdegree : ∀ v : V, G.degree v = 3 := by
    intro v
    change (G.neighborFinset v).card = 3
    have hcard : (G.neighborFinset v).card =
        Nat.card {w : V // G.Adj v w} := by
      change (G.neighborFinset v).card = Nat.card (G.neighborSet v)
      rw [Nat.card_coe_set_eq]
      symm
      simpa [SimpleGraph.neighborFinset] using
        (Set.ncard_eq_toFinset_card' (G.neighborSet v))
    exact hcard.trans (hC v)
  have hsum : ∑ v, G.degree v = 3 * Fintype.card V := by
    calc
      ∑ v, G.degree v = ∑ v : V, 3 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hdegree v
      _ = 3 * Fintype.card V := by simp [Nat.mul_comm]
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hparity : (3 * Fintype.card V) % 2 = 0 := by
    calc
      (3 * Fintype.card V) % 2 = (∑ v, G.degree v) % 2 := by
        rw [hsum]
      _ = (2 * G.edgeFinset.card) % 2 := by
        exact congrArg (fun n : Nat => n % 2) hhand
      _ = 0 := by omega
  omega


end R03SP06Arithmetic

open R03SP06Arithmetic
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution {G : SimpleGraph V}
    (hC : Cubic G) (h3 : 3 ∣ Fintype.card V) :
    6 ∣ Fintype.card V := by
  obtain ⟨a, ha⟩ := cubic_order_even hC
  obtain ⟨b, hb⟩ := h3
  have h3a : 3 ∣ a := by
    apply (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 3 2)).mp
    rw [← ha, hb]
    exact ⟨b, by omega⟩
  obtain ⟨c, hc⟩ := h3a
  refine ⟨c, ?_⟩
  omega

