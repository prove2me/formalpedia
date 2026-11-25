-- Prove2me | solution 1 for UpperTheory.Mu.muq_of_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:46.991645+00:00
-- url     : https://prove2.me/submissions/356bf2a2-d964-4067-97ea-358b634c8775

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
import Theorems.Thm_UpperTheory_Mu_mu_const

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
theorem _root_.solution {e : ι → ℚ} (c : ℤ) (he : ∀ τ, e τ = c) : MUQ (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) e :=
  ⟨fun _ => c, he, mu_const H eT c⟩
end UpperTheory.Mu
