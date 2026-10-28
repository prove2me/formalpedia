-- Prove2me | solution 1 for ProxADMMLC.Conv.eq_2_10
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:18.289205+00:00
-- url     : https://prove2.me/submissions/7da6575e-96ec-4adc-b36b-d6ed557401e2

import Definitions.Def_ProxADMMLC_Conv_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
open ProxADMMLC.Conv
open scoped BigOperators

theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (Γ p : ℝ) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    (∀ x ∈ box ℓ u, ∀ (y : E m) (z : E n), dval f A b Γ p xs y z ≤ K f A b Γ p x z y) ∧
      ∀ (y : E m) (z : E n), dval f A b Γ p xs y z ≤ Mval f p xst z := by
  constructor
  · intro x hx y z
    exact (hxs y z).2 x hx
  · intro y z
    have hfeas : A (xst z) = b := (hxst z).1.2
    have hmin := (hxs y z).2 (xst z) (hxst z).1.1
    simpa [dval,K,hfeas,Mval] using hmin

#print axioms solution



