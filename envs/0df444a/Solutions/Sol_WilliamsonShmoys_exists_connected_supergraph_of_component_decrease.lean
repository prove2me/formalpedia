-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_supergraph_of_component_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:26:39.062001+00:00
-- url     : https://prove2.me/submissions/5909c959-ed54-4db1-9a35-7c0fb3846e8c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V -> Prop)
    (H : SimpleGraph V)
    (hH : P H)
    (hstep : forall G : SimpleGraph V, H <= G -> P G -> Not G.Connected ->
      exists K : SimpleGraph V, G <= K /\ P K /\
        Nat.card K.ConnectedComponent < Nat.card G.ConnectedComponent) :
    exists K : SimpleGraph V, H <= K /\ K.Connected /\ P K := by
  have descend : forall n : Nat, forall G : SimpleGraph V, H <= G -> P G ->
      Nat.card G.ConnectedComponent = n ->
      exists K : SimpleGraph V, H <= K /\ K.Connected /\ P K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hHG hPG hcard
      by_cases hconn : G.Connected
      case pos =>
        exact Exists.intro G (And.intro hHG (And.intro hconn hPG))
      case neg =>
        apply Exists.elim (hstep G hHG hPG hconn)
        intro K hK
        have hGK : G <= K := hK.1
        have hPK : P K := hK.2.1
        have hlt : Nat.card K.ConnectedComponent < Nat.card G.ConnectedComponent := hK.2.2
        have hlt' : Nat.card K.ConnectedComponent < n := by omega
        exact ih _ hlt' K (le_trans hHG hGK) hPK rfl
  exact descend (Nat.card H.ConnectedComponent) H le_rfl hH rfl
