-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_ballU_pos_9cb43a7a02ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:00.898575+00:00
-- url     : https://prove2.me/submissions/822b1fb0-67ea-41d9-a96b-5c4d7bb01a8d

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_zero_mem_ballU_14f16944d72d

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
theorem _root_.solution (lam : Measure (lieU P Q)) [lam.IsAddHaarMeasure] {r : ℝ} (hr : 0 < r) :
    0 < lam (ballU P Q r) :=
  (isOpen_ballU P Q r).measure_pos lam ⟨0, zero_mem_ballU P Q hr⟩
end Formalism.BasicNotions.Examples₂.CD
