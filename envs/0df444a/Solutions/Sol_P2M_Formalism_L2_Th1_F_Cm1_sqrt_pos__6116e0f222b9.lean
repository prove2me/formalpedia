-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_F_Cm1_sqrt_pos__6116e0f222b9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:11.957707+00:00
-- url     : https://prove2.me/submissions/30ae2114-6f0a-4d4f-b9b1-54c7a886fe13

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Cm1
namespace Formalism.L2.Th1.F.Cm1
theorem _root_.solution (d : ℕ) (hd : 0 < d) : 0 < Real.sqrt d :=
  Real.sqrt_pos.mpr (by exact_mod_cast hd)
end Formalism.L2.Th1.F.Cm1
