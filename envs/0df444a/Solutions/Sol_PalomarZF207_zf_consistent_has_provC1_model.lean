-- Prove2me | solution 1 for PalomarZF207.zf_consistent_has_provC1_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T00:04:40.342807+00:00
-- url     : https://prove2.me/submissions/d91dbd94-403b-48f4-b451-308b76fe1c85
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_internal_prov
import Theorems.Thm_PalomarZF207_henkin_model_of_not_provable_neg
import Theorems.Thm_PalomarZF207_godel2_from_hbl
import Theorems.Thm_PalomarZF207_provC_hbl_box_exists

open PalomarZF207

theorem solution :
    Consistent → ∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E ∧ PalomarZF207Internal.InternalProvC1 E := by
  intro hCon
  obtain ⟨Box, hCl, hBot, hD1, hD2, hD3, hDiag⟩ := PalomarZF207.provC_hbl_box_exists
  have hNotNeg : ¬ Provable (Neg (Box .bot)) :=
    PalomarZF207.godel2_from_hbl Box hCl hD1 hD2 hD3 hDiag hCon
  have hClBot : Closed (Box .bot) := hCl .bot trivial
  obtain ⟨V, E, hNe, hMod, hEval⟩ :=
    PalomarZF207.henkin_model_of_not_provable_neg (Box .bot) hClBot hNotNeg
  exact ⟨V, E, hNe, hMod, (hBot V E hNe hMod (fun _ => Classical.choice hNe)).mp (hEval _)⟩
