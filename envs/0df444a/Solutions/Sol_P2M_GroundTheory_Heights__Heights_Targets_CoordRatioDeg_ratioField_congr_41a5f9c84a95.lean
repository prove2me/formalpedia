-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_congr_41a5f9c84a95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:00.920106+00:00
-- url     : https://prove2.me/submissions/7b940905-4cfd-4a32-bea7-f862630c7852

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordRatioDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
namespace GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
theorem _root_.solution {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by
  unfold ratioField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, h p q hpq⟩
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, (h p q hpq).symm⟩
end GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
