-- Prove2me | solution 1 for Psi.fUD_drop_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:04:45.557029+00:00
-- url     : https://prove2.me/submissions/c9228b57-a7da-4538-b049-01e408f965ab

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_fUD_len

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    (List.replicate n [true, false]).flatten.drop (2 * n - 1) = [false] := by
  have hsplit : (List.replicate n [true, false]).flatten
      = (List.replicate (n - 1) [true, false]).flatten ++ [true, false] := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega, List.replicate_add]
    simp [List.flatten_append]
  rw [hsplit, List.drop_append, fUD_len,
    List.drop_eq_nil_of_le (by rw [fUD_len]; omega), List.nil_append,
    show 2 * n - 1 - 2 * (n - 1) = 1 from by omega]; rfl
end Psi
