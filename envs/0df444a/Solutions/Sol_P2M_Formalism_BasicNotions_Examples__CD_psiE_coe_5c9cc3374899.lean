-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_psiE_coe_5c9cc3374899
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:47.535607+00:00
-- url     : https://prove2.me/submissions/f3809266-61e1-4ce4-9947-042db5420a57

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
theorem _root_.solution : ⇑(psiE P Q) = fun ab : lieU P Q × lieU P Q =>
    entries ((ab.1 : MM P Q) + Complex.I • (ab.2 : MM P Q)) := by
  funext ab
  rfl
end Formalism.BasicNotions.Examples₂.CD
