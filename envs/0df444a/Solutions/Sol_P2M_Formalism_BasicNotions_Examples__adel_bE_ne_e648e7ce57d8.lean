-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__adel_bE_ne_e648e7ce57d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:42.59992+00:00
-- url     : https://prove2.me/submissions/da9be1f7-24ca-41cd-853c-b82625542fcd

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : (H.sqd : H.E) ≠ 0 := by
  intro h
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  have h2 := H.sqd_sq
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h2
  exact hd.ne_zero h2
end Formalism.BasicNotions.Examples₂
