-- Prove2me | solution 1 for P2M_Combinatorics_Line_exists_mono_of_ack_le__0a26130f3292
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:22.065203+00:00
-- url     : https://prove2.me/submissions/86c033fc-1db6-486b-964d-48eff347665b

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_Ackermann
public import Definitions.Def_ShelahHalesJewett_Solution
public import Theorems.Thm_Combinatorics_Line_exists_mono_of_ack_le
public import Theorems.Thm_Combinatorics_Subspace_compLine_apply
attribute [local simp] Combinatorics.Subspace.compLine_apply



set_option autoImplicit true
@[expose] public section
public section
open Combinatorics Combinatorics.Line
namespace Combinatorics.Line
theorem _root_.solution {k r n : ℕ} (hk : 0 < k) (hn : ack 5 (2 * k + r) ≤ n)
    (C : (Fin n → Fin k) → Fin r) : ∃ l : Line (Fin k) (Fin n), l.IsMono C := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact exists_mono_of_ack_le (by simpa using hn) C
end Combinatorics.Line
