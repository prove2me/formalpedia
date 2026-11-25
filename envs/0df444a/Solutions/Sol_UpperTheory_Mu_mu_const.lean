-- Prove2me | solution 1 for UpperTheory.Mu.mu_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:05.74219+00:00
-- url     : https://prove2.me/submissions/149b2675-46af-4af3-8ccd-c5fa2083bb67

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
import Theorems.Thm_UpperTheory_Mu_mu_one
import Theorems.Thm_UpperTheory_MU_const


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
theorem _root_.solution (c : ℤ) : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => c) := (mu_one H eT).const c
end UpperTheory.Mu
