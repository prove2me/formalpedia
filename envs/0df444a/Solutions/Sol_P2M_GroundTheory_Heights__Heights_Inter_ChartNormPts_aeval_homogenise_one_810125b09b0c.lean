-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_one_810125b09b0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:35.247078+00:00
-- url     : https://prove2.me/submissions/1f5fec82-243e-437a-b275-a20c0db2c871

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartNormPtsA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.ChartNormPts
variable {P : Type*} {Q : Type*} [Fintype Q] {V : Type*}
namespace GroundTheory.Heights₂.Heights.Inter.ChartNormPts
theorem _root_.solution {R : Type*} [CommRing R] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (z : V → R) (hz : ∀ q, z (g q) = 1) :
    aeval z (homogenise v f g F) =
      eval₂ (aeval (z ∘ v) : MvPolynomial P ℤ →ₐ[ℤ] R).toRingHom (fun q => z (f q)) F := by
  rw [aeval_homogenise, eval₂_eq']
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [hz]
end GroundTheory.Heights₂.Heights.Inter.ChartNormPts
