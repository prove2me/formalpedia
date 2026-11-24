-- Prove2me | solution 1 for Psi.deltaAux_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:31:39.067905+00:00
-- url     : https://prove2.me/submissions/0f8fc56b-078a-440f-819f-77f951e4a6e4

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List ℕ) (acc : ℕ) :
    deltaAux r acc = (deltaAux r 0).map (· + acc) := by
  induction r generalizing acc with
  | nil => simp [deltaAux]
  | cons x xs ih =>
    conv_lhs => rw [deltaAux, ih (acc + x)]
    conv_rhs => rw [deltaAux, zero_add, List.map_cons, ih x, List.map_map]
    refine List.cons.injEq _ _ _ _ |>.mpr ⟨by omega, ?_⟩
    apply List.map_congr_left; intro y _; simp only [Function.comp_apply]; omega
end Psi
