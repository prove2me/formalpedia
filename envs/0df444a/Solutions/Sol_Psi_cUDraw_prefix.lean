-- Prove2me | solution 1 for Psi.cUDraw_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:56:40.949406+00:00
-- url     : https://prove2.me/submissions/5850d45e-59aa-4a69-a3d2-7146aca803c5

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) :
    π = (List.replicate (cUDraw π) [true, false]).flatten ++ π.drop (2 * cUDraw π) := by
  fun_induction cUDraw π with
  | case1 r ih1 =>
      rw [List.replicate_add, List.flatten_append]
      simp only [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [show 2 * (1 + cUDraw r) = 2 * cUDraw r + 1 + 1 from by ring,
        List.drop_succ_cons, List.drop_succ_cons, List.append_assoc, ← ih1]; rfl
  | case2 x hx => simp
end Psi
