-- Prove2me | solution 1 for UpperTheory.Host.muQ_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:56:52.199924+00:00
-- url     : https://prove2.me/submissions/85c34ca4-e4cf-4ba1-84c1-1c63b8a33c35

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_MuParallel
import Theorems.Thm_UpperTheory_Host_mu_one
import Theorems.Thm_UpperTheory_MU_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.Host
open Formalism.BasicNotions NumberField
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Host
theorem _root_.solution [Fintype R.Psi] {e : R.Psi → ℚ} {c : ℤ} (h : ∀ g, e g = c) :
    UpperTheory.MUQ (fun g : R.Psi => H.emb (g : R.GG)) e :=
  ⟨fun _ => c, h, (mu_one H).const c⟩
end UpperTheory.Host
