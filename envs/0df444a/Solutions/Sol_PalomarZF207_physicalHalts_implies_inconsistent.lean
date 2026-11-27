-- Prove2me | solution 1 for PalomarZF207.physicalHalts_implies_inconsistent
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:22:10.113041+00:00
-- url     : https://prove2.me/submissions/79ccb0bd-d103-4e2e-aedd-311bd419cdf2

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement
import Definitions.Def_palomar_zf207_physical
import Theorems.Thm_PalomarZF207_henkin_completeness
import Theorems.Thm_PalomarZF207_calc_not_provC_one
import Theorems.Thm_PalomarZF207_physicalHalts_implies_provC_one

open PalomarZF207

theorem solution : PhysicalHalts207 → ¬ Consistent := fun hHalt hCons =>
  PalomarZF207.calc_not_provC_one
    (PalomarZF207.henkin_completeness hCons)
    (PalomarZF207.physicalHalts_implies_provC_one hHalt)
