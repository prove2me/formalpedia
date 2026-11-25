-- Prove2me | solution 1 for QuarticPairing.norm_unitDir_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:33.646931+00:00
-- url     : https://prove2.me/submissions/6dadf5a5-01f9-4be3-a288-5040ba88679d

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_norm_unitDir
public import Theorems.Thm_QuarticPairing_unitDir_zero

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (c : GaussianInt) : ‖unitDir c‖ ≤ 1 := by
  by_cases hc : c = 0
  · subst hc; simp [unitDir_zero]
  · rw [norm_unitDir hc]
end QuarticPairing
