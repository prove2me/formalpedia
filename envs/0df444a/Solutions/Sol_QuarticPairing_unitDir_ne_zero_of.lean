-- Prove2me | solution 1 for QuarticPairing.unitDir_ne_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:26.861555+00:00
-- url     : https://prove2.me/submissions/ad852664-80ff-443b-8914-0d32ae063230

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {g κ : ℂ} {c : GaussianInt} (hg : g ≠ 0) (h : g ^ 2 = -κ * unitDir c) :
    unitDir c ≠ 0 := by
  intro h0; simp [h0] at h; exact hg h
end QuarticPairing
