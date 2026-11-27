-- Prove2me | solution 1 for UpperTheory.Host.mu_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:41:40.429241+00:00
-- url     : https://prove2.me/submissions/251c38ed-ce05-4f44-8c66-0fd189b24c4e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_MuParallel
import Theorems.Thm_UpperTheory_Host_prod_sigmaOf
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
noncomputable section
open UpperTheory UpperTheory.Host
open Formalism.BasicNotions NumberField
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Host
theorem _root_.solution [Fintype R.Psi] : UpperTheory.MU (fun g : R.Psi => H.emb (g : R.GG)) (fun _ => 1) := by
  intro z hz
  have h1 : ∀ g : R.Psi, H.emb (g : R.GG) z ^ (1 : ℤ) = H.φ₀ (H.sigmaOf (g : R.GG) z) := fun g => zpow_one _
  simp only [h1]
  rw [← map_prod, prod_sigmaOf, H.der.norm_mu z hz, map_one, map_one]
end UpperTheory.Host
