-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__adelic_theta_conj_c64eb5f92f34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:33.370534+00:00
-- url     : https://prove2.me/submissions/1c5cb714-dd8c-45fc-bf90-1af53f297817

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
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
open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : H.conj (adelTheta H) = 1 - adelTheta H := by
  unfold adelTheta
  first
  | (rw [map_div₀, map_add, map_one, adel_conj_bE, map_ofNat]; ring)
  | (simp [adel_conj_bE]; ring)
end Formalism.BasicNotions.Examples₂
