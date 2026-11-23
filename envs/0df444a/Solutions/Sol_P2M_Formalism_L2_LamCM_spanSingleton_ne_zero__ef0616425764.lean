-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:48.779528+00:00
-- url     : https://prove2.me/submissions/94d8658a-f001-4e08-8ddf-41bb441ed9e4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {x : K} (hx : x ≠ 0) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
  rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
end Formalism.L2.LamCM
