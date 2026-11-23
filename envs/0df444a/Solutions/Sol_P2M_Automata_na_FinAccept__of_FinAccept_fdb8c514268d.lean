-- Prove2me | solution 1 for P2M_Automata_na_FinAccept__of_FinAccept_fdb8c514268d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:42.609389+00:00
-- url     : https://prove2.me/submissions/609d592a-2371-4d4b-992d-92c345502249

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Theorems.Thm_P2M_Automata_na_FinRun__of_FinRun_8f693dc0996c

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A}
    (h : M.FinAccept acc n as) : M.FinAccept' acc n (fun k ↦ as k) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (fun k ↦ ss k)
  constructor
  · exact na_FinRun'_of_FinRun h_run
  simpa
end Automata
