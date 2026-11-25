-- Prove2me | solution 1 for PI.GalTorsConj.W.pInj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:33:46.564378+00:00
-- url     : https://prove2.me/submissions/c58115c9-b208-47ec-a27d-22a842e251ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
import Theorems.Thm_PI_GalTorsConj_W_neg_pair
import Theorems.Thm_Formalism_L2_Th1_F_pDerivZero
import Theorems.Thm_Formalism_L2_Th1_F_pInjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w) (hy : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    z - w ∈ L.lattice := by
  rcases (pInjective L z w hz hw).1 hx with h | h
  · exact h
  · have h1 := (neg_pair L h).2
    have h0 : L.derivWeierstrassP z = 0 := by linear_combination (hy + h1) / 2
    have h2 : 2 * z ∈ L.lattice := (pDerivZero L z hz).1 h0
    have e : z - w = 2 * z - (z + w) := by ring
    rw [e]
    exact L.lattice.sub_mem h2 h
end PI.GalTorsConj.W
