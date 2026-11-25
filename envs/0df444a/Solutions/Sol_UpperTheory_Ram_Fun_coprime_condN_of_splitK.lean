-- Prove2me | solution 1 for UpperTheory.Ram.Fun.coprime_condN_of_splitK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:10.830183+00:00
-- url     : https://prove2.me/submissions/11dd396b-981f-4328-a12c-68fe59deecc9

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
import Theorems.Thm_Formalism_BasicNotions_not_dvd_of_splitK


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h : H.cls p = .splitK) : Nat.Coprime p (H.QS * H.q * H.d) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_of_splitK hp h)
end UpperTheory.Ram.Fun
