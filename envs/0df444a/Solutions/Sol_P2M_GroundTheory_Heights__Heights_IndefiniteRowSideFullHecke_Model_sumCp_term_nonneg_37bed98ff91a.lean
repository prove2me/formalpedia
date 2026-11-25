-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_sumCp_term_nonneg_37bed98ff91a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:12:09.165796+00:00
-- url     : https://prove2.me/submissions/b6e5e3f3-8e3e-4ad2-b539-fb7031e24153

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_CpEqPrimeWeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_cp_nonneg_18587f44450a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution (d : ℤ) {p : ℕ} (hp : p.Prime) :
    0 ≤ (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p :=
  mul_nonneg (add_nonneg (cp_nonneg hp) (by positivity))
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
