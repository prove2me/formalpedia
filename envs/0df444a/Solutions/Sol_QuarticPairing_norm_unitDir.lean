-- Prove2me | solution 1 for QuarticPairing.norm_unitDir
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:36:30.276806+00:00
-- url     : https://prove2.me/submissions/8c440d3e-a62a-4631-b485-ca9a7eb00386

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_toComplex_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {c : GaussianInt} (hc : c ≠ 0) : ‖unitDir c‖ = 1 := by
  rw [unitDir, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.2 (toComplex_ne_zero hc))]
end QuarticPairing
