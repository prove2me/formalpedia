-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ord_pow_irreducible_of_dvr_6fdea97bf37d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:35:41.501721+00:00
-- url     : https://prove2.me/submissions/54f26d6f-e977-4cb1-aa11-3846683d26ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : Ring.ord R (ϖ ^ e) = e := by
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp
end GroundTheory.Heights₂.Heights
