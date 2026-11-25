-- Prove2me | solution 1 for QuarticPairing.isBigO_neg_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:36:51.898572+00:00
-- url     : https://prove2.me/submissions/63035487-8192-44e1-bc44-a62fa46441c2

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended

set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {κ : ℂ} (hκ : ‖κ‖ = 1) {f : ℕ → ℂ} {u : ℕ → ℝ}
    (h : f =O[atTop] u) : (fun X => -κ * starRingEnd ℂ (f X)) =O[atTop] u := by
  refine IsBigO.of_norm_left ?_
  have : (fun X => ‖-κ * starRingEnd ℂ (f X)‖) = fun X => ‖f X‖ :=
    funext fun X => by rw [norm_mul, norm_neg, hκ, one_mul, Complex.norm_conj]
  rw [this]; exact h.norm_left
end QuarticPairing
