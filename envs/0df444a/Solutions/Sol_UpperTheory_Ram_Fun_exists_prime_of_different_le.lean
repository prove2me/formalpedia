-- Prove2me | solution 1 for UpperTheory.Ram.Fun.exists_prime_of_different_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:33.023226+00:00
-- url     : https://prove2.me/submissions/26782af7-d64b-491e-86cb-ce56d93b96c4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Theorems.Thm_UpperTheory_Reformulated_B_Qj12_exists_prime_of_different_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Ram.Fun
theorem _root_.solution (v : HeightOneSpectrum (𝓞 H.F)) (hle : differentIdeal ℤ (𝓞 H.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ H.QS * H.q * H.d ∧ (p : 𝓞 H.F) ∈ v.asIdeal :=
  by apply _root_.UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le <;> assumption
end UpperTheory.Ram.Fun
