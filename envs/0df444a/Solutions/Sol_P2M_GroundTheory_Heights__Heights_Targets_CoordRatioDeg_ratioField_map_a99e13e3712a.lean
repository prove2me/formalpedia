-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_map_a99e13e3712a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:02.509961+00:00
-- url     : https://prove2.me/submissions/cd95367e-79a8-4b30-a8e2-4b2de2136cab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordRatioDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
namespace GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
theorem _root_.solution {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by
  rw [ratioField, IntermediateField.adjoin_map, ratioField]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp⟩
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp⟩
end GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg
