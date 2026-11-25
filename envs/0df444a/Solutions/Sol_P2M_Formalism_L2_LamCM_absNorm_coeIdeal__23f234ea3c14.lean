-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_absNorm_coeIdeal__23f234ea3c14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:21.300798+00:00
-- url     : https://prove2.me/submissions/ef619812-251a-4834-82af-fcc8503f8d48

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero

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
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution {F : Type} [Field F] [NumberField F] (J : Ideal (𝓞 F)) :
    FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.absNorm J : ℚ) := FractionalIdeal.coeIdeal_absNorm J
end Formalism.L2.LamCM
