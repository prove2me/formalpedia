-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_zero_mem_ballU_14f16944d72d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:51.138486+00:00
-- url     : https://prove2.me/submissions/b0e5a8fa-2c5e-444a-b230-5e1187f9d5a5

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {r : ℝ} (hr : 0 < r) : (0 : lieU P Q) ∈ ballU P Q r := by
  show ∑ i, ∑ j, ‖((0 : lieU P Q) : MM P Q) i j‖ < r
  simpa using hr
end Formalism.BasicNotions.Examples₂.CD
