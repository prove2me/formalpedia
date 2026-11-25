-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanFubini_measurePreserving_consEquiv_fe40b3b8d4c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:35.339981+00:00
-- url     : https://prove2.me/submissions/0a7f4795-88e7-4ae4-817b-867c566f822b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanFubini
namespace GroundTheory.Heights₂.Heights.SphereMeanFubini
theorem _root_.solution {n : ℕ} (k : ℕ) :
    MeasurePreserving (consEquiv (n := n) k) volume volume :=
  (measurePreserving_piCongrLeft (fun _ : Fin (k + 1) × Fin n => (volume : Measure ℂ))
    (groupSplit k n)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ (Fin k × Fin n) => (volume : Measure ℂ)))
end GroundTheory.Heights₂.Heights.SphereMeanFubini
