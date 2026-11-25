-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Jx7_t_ProductLemma__cbaa48e0fe14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:12.842799+00:00
-- url     : https://prove2.me/submissions/2cab283c-df71-4df4-8761-9092d91f23bb

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_ProductLemma
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_SchurProduct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_ProductDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : ProductLemma := t_ProductLemma t_SchurProduct t_ProductDomination
end Formalism.FourierDecayAlt.P.Jx7
