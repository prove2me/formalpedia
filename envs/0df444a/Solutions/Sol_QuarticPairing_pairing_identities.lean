-- Prove2me | solution 1 for QuarticPairing.pairing_identities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:46.166417+00:00
-- url     : https://prove2.me/submissions/1c6ad7a6-6005-47a9-86e1-942583b5167a

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_twistedAvg_pairing


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) :=
  twistedAvg_pairing χ χ₃ g w s hκ hχ h12 k
end QuarticPairing
