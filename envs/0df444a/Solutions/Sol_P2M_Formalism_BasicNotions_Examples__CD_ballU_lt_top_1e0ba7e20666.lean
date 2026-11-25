-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_ballU_lt_top_1e0ba7e20666
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:59.81643+00:00
-- url     : https://prove2.me/submissions/669eff57-d376-4ede-9974-b9bc40f93d12

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_entry_le_sum_6938a3ded12d

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
theorem _root_.solution (lam : Measure (lieU P Q)) [lam.IsAddHaarMeasure] (r : ℝ) :
    lam (ballU P Q r) < ⊤ := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin P ⊕ Fin Q =>
      Set.pi Set.univ fun _ : Fin P ⊕ Fin Q => Metric.closedBall (0 : ℂ) r : Set (MM P Q)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 r
  have hK := (isClosed_lieU P Q).isClosedEmbedding_subtypeVal.isCompact_preimage hbox
  refine lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top
  intro X hX i _ j _
  rw [mem_closedBall_zero_iff]
  exact (entry_le_sum P Q X i j).trans (le_of_lt hX)
end Formalism.BasicNotions.Examples₂.CD
