-- Prove2me | solution 1 for UpperTheory.Mu.mu_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:46.649537+00:00
-- url     : https://prove2.me/submissions/eee6d298-697b-4cfa-bde7-9dddef63358a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
import Theorems.Thm_UpperTheory_prod_cmType_eq_norm_and_weightCongruence_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.BasicNotions
open UpperTheory UpperTheory.Mu
variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)
namespace UpperTheory.Mu
theorem _root_.solution : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := (UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one R H ι eT).2
end UpperTheory.Mu
