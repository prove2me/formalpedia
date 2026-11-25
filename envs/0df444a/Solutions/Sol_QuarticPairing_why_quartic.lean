-- Prove2me | solution 1 for QuarticPairing.why_quartic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:31.949787+00:00
-- url     : https://prove2.me/submissions/cb2dfe98-a01a-43f7-a80c-59e232053577

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_conj_eq_pow_mul


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ :=
  conj_eq_pow_mul hk hg h
end QuarticPairing
