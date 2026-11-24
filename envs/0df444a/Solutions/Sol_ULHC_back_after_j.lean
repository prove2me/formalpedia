-- Prove2me | solution 1 for ULHC.back_after_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:39:00.113563+00:00
-- url     : https://prove2.me/submissions/6285c801-c37b-44ec-aada-47d87230f57a

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_front_after
import Theorems.Thm_ULHC_back_cellJ_succ


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ k + 1) :
    back (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [back_cellJ_succ, front_after hk hpat (by omega)]; omega
end ULHC
