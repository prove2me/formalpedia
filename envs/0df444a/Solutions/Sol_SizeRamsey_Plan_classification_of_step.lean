-- Prove2me | solution 1 for SizeRamsey.Plan.classification_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:36.568785+00:00
-- url     : https://prove2.me/submissions/e440875d-5c38-4d24-b41e-8e15c2d82f50

module
public import Definitions.Def_SizeRamsey_Equality_DegreeFour
public import Definitions.Def_SizeRamsey_Equality_Mixed
public import Definitions.Def_SizeRamsey_Equality_Cubic
public import Definitions.Def_SizeRamsey_Equality_TwoRegular
public import Definitions.Def_SizeRamsey_Equality

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    (step : ∀ {V : Type u} [Fintype V]
      (G : SimpleGraph V),
      G.Connected → 0 < edgeCount G →
      edgeCount G ≤ 16 →
      Tight G → SmallerClassified G → Classified G)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (hm : edgeCount G ≤ 16)
    (ht : Tight G) :
    Classified G := by
  have aux : ∀ n, ∀ {W : Type u} [Fintype W]
      (H : SimpleGraph W),
      edgeCount H = n → H.Connected →
      0 < edgeCount H → edgeCount H ≤ 16 →
      Tight H → Classified H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W inst H he hconn hpos hcap htight
      apply step H hconn hpos hcap htight
      intro X instX K kc kp klt kt
      have kn : edgeCount K < n := by omega
      exact ih (edgeCount K) kn K rfl kc kp
        (by omega) kt
  exact aux (edgeCount G) G rfl hc hp hm ht
end SizeRamsey.Plan
