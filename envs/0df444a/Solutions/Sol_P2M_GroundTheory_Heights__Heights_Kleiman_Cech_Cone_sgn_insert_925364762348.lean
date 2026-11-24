-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_insert_925364762348
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:07.001334+00:00
-- url     : https://prove2.me/submissions/5b46dd44-7414-4d51-adda-4d167c09d76e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
theorem _root_.solution {a b : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) :
    Cech.sgn (insert a A) b = Cech.sgn A b * (if a < b then -1 else 1) := by
  unfold Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), pow_succ]
  · rw [mul_one]
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
