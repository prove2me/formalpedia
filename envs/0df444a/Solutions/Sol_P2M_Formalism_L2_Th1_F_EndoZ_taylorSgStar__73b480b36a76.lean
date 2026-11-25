-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_F_EndoZ_taylorSgStar__73b480b36a76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:42.267846+00:00
-- url     : https://prove2.me/submissions/2c423a21-bf82-4008-84c0-c632f4432d4d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_sigmaEntire
import Theorems.Thm_Formalism_L2_Th1_F_taylorSgStar_of
import Theorems.Thm_Formalism_L2_Th1_F_taylorSigma_of
import Theorems.Thm_Formalism_L2_Th1_F_taylor_deriv
import Theorems.Thm_Formalism_L2_Th1_F_taylor_exp
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring
import Theorems.Thm_P2M_Formalism_L2_Th1_F_taylorSgStar__of_8dcab6c5c93b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution : TaylorSgStar' :=
  taylorSgStar'_of (taylorSgStar_of (taylorSigma_of taylor_ring taylor_deriv)
    taylor_ring taylor_exp sigmaEntire)
end Formalism.L2.Th1.F.EndoZ
