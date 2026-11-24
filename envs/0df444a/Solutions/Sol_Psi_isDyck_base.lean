-- Prove2me | solution 1 for Psi.isDyck_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:09:03.642888+00:00
-- url     : https://prove2.me/submissions/72b4204b-af13-47d7-a876-482106ec7240

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_validFrom_append
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_runHeight_replicate_true
import Theorems.Thm_Psi_runHeight_replicate_false
import Theorems.Thm_Psi_validFrom_replicate_true
import Theorems.Thm_Psi_validFrom_replicate_false
import Theorems.Thm_Psi_runHeight_flatten_UD
import Theorems.Thm_Psi_validFrom_flatten_UD

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l k : ℕ) :
    IsDyck ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) := by
  rw [IsDyck, isDyckAux_iff]
  refine ⟨?_, ?_⟩
  · rw [validFrom_append, validFrom_append]
    refine ⟨⟨validFrom_flatten_UD _ 0 le_rfl, ?_⟩, ?_⟩
    · rw [runHeight_flatten_UD]; exact validFrom_replicate_true _ _
    · rw [runHeight_append, runHeight_flatten_UD, runHeight_replicate_true]
      apply validFrom_replicate_false; push_cast; omega
  · rw [runHeight_append, runHeight_append, runHeight_flatten_UD, runHeight_replicate_true,
      runHeight_replicate_false]; push_cast; ring
end Psi
