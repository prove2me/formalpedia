-- Prove2me | solution 1 for UpperTheory.Mu.exists_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:40.49351+00:00
-- url     : https://prove2.me/submissions/d54426a8-68fd-4b77-8d65-e9d3528b89fa

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
import Theorems.Thm_UpperTheory_exists_shift_weightCongruence_lt_torsionOrder


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
theorem _root_.solution [DecidableEq ι] (a : ι → ℤ) (τ₀ : ι) : ∃ s : ℕ, s < Units.torsionOrder H.E ∧
    MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun τ => a τ + if τ = τ₀ then (s : ℤ) else 0) :=
  UpperTheory.exists_shift_weightCongruence_lt_torsionOrder H.E ℂ ι _ a τ₀
end UpperTheory.Mu
