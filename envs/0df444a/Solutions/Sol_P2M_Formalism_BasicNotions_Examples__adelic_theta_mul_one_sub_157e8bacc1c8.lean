-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__adelic_theta_mul_one_sub_157e8bacc1c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:34.885789+00:00
-- url     : https://prove2.me/submissions/dd33777c-43b8-4402-b4ac-5d58b665800d

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
theorem _root_.solution : adelTheta H * (1 - adelTheta H) = ((adelNd H : ℤ) : H.E) := by
  have h4 := congrArg (Int.cast : ℤ → H.E) (adelNd_spec H)
  push_cast at h4
  have hs := H.sqd_sq
  unfold adelTheta
  linear_combination (-1/4 : H.E) * hs - (1/4 : H.E) * h4
end Formalism.BasicNotions.Examples₂
