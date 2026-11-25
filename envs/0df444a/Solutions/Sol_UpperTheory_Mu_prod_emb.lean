-- Prove2me | solution 1 for UpperTheory.Mu.prod_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:08:11.634729+00:00
-- url     : https://prove2.me/submissions/492bdcf8-2ddc-4a73-ae5b-372d7dd311a2

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
import Theorems.Thm_UpperTheory_Mu_prod_emb_zpow
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Formalism.BasicNotions
open UpperTheory UpperTheory.Mu
variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)
namespace UpperTheory.Mu
theorem _root_.solution {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z = 1 := by
  simpa using prod_emb_zpow H eT hz 1
end UpperTheory.Mu
