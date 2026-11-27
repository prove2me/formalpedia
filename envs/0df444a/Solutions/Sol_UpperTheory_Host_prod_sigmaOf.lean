-- Prove2me | solution 1 for UpperTheory.Host.prod_sigmaOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:38:46.031612+00:00
-- url     : https://prove2.me/submissions/ee94f2a3-198a-4ef3-949c-0367c3f3aab5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_MuParallel
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_HC_HostAx_hostE_isGalois


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
theorem _root_.solution [Fintype R.Psi] (x : H.E) :
    ∏ g : R.Psi, H.sigmaOf (g : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.hostE_isGalois
  rw [Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_equiv (psiEquiv H) _ _ fun g => rfl
end UpperTheory.Host
