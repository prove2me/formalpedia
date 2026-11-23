-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_A_Univ___injective_04fee711be81
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:14.740809+00:00
-- url     : https://prove2.me/submissions/1a1319af-1b08-4d31-b687-5c8a2245800e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Univ
namespace Formalism.L2.Th1.A.Univ
theorem _root_.solution : Function.Injective ι := IsFractionRing.injective Univ.Z Univ.K₀
end Formalism.L2.Th1.A.Univ
