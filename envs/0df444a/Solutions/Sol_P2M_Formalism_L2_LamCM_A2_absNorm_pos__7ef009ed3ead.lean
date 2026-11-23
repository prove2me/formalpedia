-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.807238+00:00
-- url     : https://prove2.me/submissions/840a05cc-75a6-4cc6-b471-9e357565278e

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

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
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (h : I ≠ 0) : 0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I) (fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e.symm))
end Formalism.L2.LamCM.A2
