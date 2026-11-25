-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_F_hasCMByIsogeny_of__5413287b0bf6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:09.498792+00:00
-- url     : https://prove2.me/submissions/006e3419-efc2-41f0-afdb-691e7346b5f6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
import Theorems.Thm_Formalism_L2_Th1_F_has_cm_stable
import Theorems.Thm_Formalism_L2_Th1_F_hasCMByIsogeny_of
import Theorems.Thm_Formalism_L2_Th1_F_kerRepsCard
import Theorems.Thm_Formalism_L2_Th1_F_kerRepsExist
import Theorems.Thm_Formalism_L2_Th1_F_quasiPeriodConstIsogeny


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (hf : IsogenyFormulaInstance) : HasCMByIsogeny :=
  hasCMByIsogeny_of has_cm_stable kerRepsExist kerRepsCard hf quasiPeriodConstIsogeny
end Formalism.L2.Th1.F
