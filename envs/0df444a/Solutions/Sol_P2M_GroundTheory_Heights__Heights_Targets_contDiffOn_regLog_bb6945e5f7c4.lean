-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_contDiffOn_regLog_bb6945e5f7c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:33.236798+00:00
-- url     : https://prove2.me/submissions/f7df9e6b-3513-4723-9dff-4f1b5fce1dba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_normSq_nonneg_5767a13ad4c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_contDiff_evalC_435b0b7923c5

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {A : HermLine ι} (hA : IsSmoothHerm A) (s : MRing ι) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (regLog A s ε) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hN : ContDiffOn ℝ ∞ (normSq A s) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have h1 := (((contDiff_norm_sq ℝ).comp (contDiff_evalC s)).contDiffOn (s := {z : (Σ k, ι k) → ℂ |
      ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})).div (hA.pow 2) fun z hz => pow_ne_zero _ (A.pos z hz).ne'
    exact h1.congr fun z _ => by simp only [normSq, div_pow]; rfl
  exact ((hN.add contDiffOn_const).log fun z _ =>
    (add_pos_of_nonneg_of_pos (normSq_nonneg A s z) hε).ne').div_const 2
end GroundTheory.Heights₂.Heights.Targets
