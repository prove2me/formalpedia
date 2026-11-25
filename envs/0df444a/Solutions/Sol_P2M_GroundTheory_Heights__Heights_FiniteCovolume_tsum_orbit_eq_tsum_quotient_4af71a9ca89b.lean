-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_tsum_orbit_eq_tsum_quotient_4af71a9ca89b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:30.788033+00:00
-- url     : https://prove2.me/submissions/df2a2e14-c6ec-4abc-95eb-faf303661a10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {G X : Type*} [Group G] [MulAction G X] (b : X) (o : Set X)
    (ho : MulAction.orbit G b = o) (K : Subgroup G) (hK : MulAction.stabilizer G b = K)
    (f : X → ℝ≥0∞) : ∑' p : o, f p = ∑' q : G ⧸ K, f ((Quotient.out q : G) • b) := by
  subst ho hK
  rw [← (MulAction.orbitEquivQuotientStabilizer G b).symm.tsum_eq]
  refine tsum_congr fun q => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.orbitEquivQuotientStabilizer_symm_apply]
end GroundTheory.Heights₂.Heights.FiniteCovolume
