-- Prove2me | solution 1 for SemigroupBetti.GenData.pos_of_two_le_ncomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:29.85653+00:00
-- url     : https://prove2.me/submissions/ebd49d27-81b4-4130-88af-9397dfd1167c

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_ncomp_zero

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (h : 2 ≤ G.ncomp d) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [ncomp_zero] at h; omega
  · exact hd
end SemigroupBetti.GenData
