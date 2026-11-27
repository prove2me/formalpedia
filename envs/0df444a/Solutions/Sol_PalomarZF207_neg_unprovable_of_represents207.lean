-- Prove2me | solution 1 for PalomarZF207.neg_unprovable_of_represents207
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T00:04:45.797169+00:00
-- url     : https://prove2.me/submissions/b918fe18-7100-4269-822c-f0c7875df185
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement
import Definitions.Def_palomar_zf207_internal_prov
import Theorems.Thm_PalomarZF207_nd_sound
import Theorems.Thm_PalomarZF207_zf_consistent_has_provC1_model
import Theorems.Thm_PalomarZF207_internal_provC1_implies_linkedHalts

open PalomarZF207

theorem solution (H : Formula) (hH : Represents207 H) : Consistent → ¬ Provable (Neg H) := by
  intro hCon hNegH
  obtain ⟨V, E, hNe, hMod, hProvC1⟩ := PalomarZF207.zf_consistent_has_provC1_model hCon
  have hHalts : PalomarZF207History.InternalLinkedHalts E :=
    PalomarZF207.internal_provC1_implies_linkedHalts V E hNe hMod hProvC1
  let s : Nat → V := fun _ => Classical.choice hNe
  have hEvalH : eval E H s := (hH.2 V E hNe hMod s).mpr hHalts
  have hEvalNegH : eval E (Neg H) s := PalomarZF207.nd_sound (Neg H) hNegH V E hNe hMod s
  exact hEvalNegH hEvalH
