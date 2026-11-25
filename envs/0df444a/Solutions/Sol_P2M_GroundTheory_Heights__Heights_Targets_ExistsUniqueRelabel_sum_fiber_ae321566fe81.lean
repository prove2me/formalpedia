-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sum_fiber_ae321566fe81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:10.694631+00:00
-- url     : https://prove2.me/submissions/d4cadbd9-6817-4607-806e-faea4557b996

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution {M : Type*} [AddCommMonoid M] [DecidableEq K] (g : (Σ k, ι k) → M) (k : K) :
    ∑ i, g ⟨k, i⟩ = ∑ p : Σ k, ι k, if p.1 = k then g p else 0 := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
