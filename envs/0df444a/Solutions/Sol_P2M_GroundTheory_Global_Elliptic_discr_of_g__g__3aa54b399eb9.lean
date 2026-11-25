-- Prove2me | solution 1 for P2M_GroundTheory_Global_Elliptic_discr_of_g__g__3aa54b399eb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:14.114954+00:00
-- url     : https://prove2.me/submissions/5438608f-2a86-4f01-892a-d44bc6730cec

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L L' : PeriodPair} {t : ℂ} (h₂ : L'.g₂ = t ^ 4 * L.g₂)
    (h₃ : L'.g₃ = t ^ 6 * L.g₃) : discr L' = t ^ 12 * discr L := by
  rw [discr, discr, h₂, h₃]
  ring
end GroundTheory.Global.Elliptic
