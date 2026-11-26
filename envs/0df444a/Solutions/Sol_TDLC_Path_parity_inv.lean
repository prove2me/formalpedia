-- Prove2me | solution 1 for TDLC.Path.parity_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:05.418382+00:00
-- url     : https://prove2.me/submissions/13823c4e-a099-4b18-ba67-6c39cfde3296


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_bxor_comm
import Theorems.Thm_TDLC_Path_parity_lEmbed
import Theorems.Thm_TDLC_Path_parity_concat
attribute [local simp] TDLC.Path.parity_lEmbed
attribute [local simp] TDLC.Path.parity_concat

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
namespace Path
theorem _root_.solution {A : Type u} {x y : A} (p : Path x y) :
    Path.parity (Path.inv p) = Path.parity p := by
  induction p with
  | nil => rfl
  | seq s p ih =>
      rw [Path.inv, Path.parity_concat, ih, Path.parity_lEmbed]
      exact bxor_comm _ _
end Path
end TDLC
