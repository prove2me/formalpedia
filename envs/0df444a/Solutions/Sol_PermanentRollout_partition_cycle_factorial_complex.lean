-- Prove2me | solution 1 for PermanentRollout.partition_cycle_factorial_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/182ce24d-2c36-4401-a7d4-686b448e1a98

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partition_cycle_factorial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (rows : Finset (Fin t)) :
    (∑ partition : Finpartition rows,
      ∏ block ∈ partition.parts,
        ((block.card - 1).factorial : ℂ)) =
      (rows.card.factorial : ℂ) := by
  exact_mod_cast partition_cycle_factorial rows
end PermanentRollout
