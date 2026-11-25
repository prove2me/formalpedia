-- Prove2me | solution 1 for QuarticPairing.pointwise_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:23.028653+00:00
-- url     : https://prove2.me/submissions/3f0cd818-6be8-4105-b405-5eafc4010e85

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_term_pairing


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g :=
  term_pairing hκ h
end QuarticPairing
