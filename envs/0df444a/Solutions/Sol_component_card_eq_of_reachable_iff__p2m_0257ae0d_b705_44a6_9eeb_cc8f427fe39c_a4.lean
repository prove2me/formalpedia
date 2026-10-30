-- Prove2me | solution 1 for component_card_eq_of_reachable_iff__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:33.749816+00:00
-- url     : https://prove2.me/submissions/c623bf76-ac28-4d82-b50f-c52416382b01

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

open SimpleGraph

theorem solution
    {V : Type} (F K : SimpleGraph V)
    (hReach : ∀ u v, F.Reachable u v ↔ K.Reachable u v) :
    Nat.card F.ConnectedComponent = Nat.card K.ConnectedComponent := by
  exact Nat.card_congr (Quot.congr (Equiv.refl V) hReach)