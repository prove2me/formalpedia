-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____81bf5efe9be8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:22.539674+00:00
-- url     : https://prove2.me/submissions/3dd1e7ad-3f81-4c03-ba7b-8ffe4943516e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
namespace Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
theorem _root_.solution (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  simpa [wEta] using this
end Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
