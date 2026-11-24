-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_eval_chartSection_a507f7e3a7e7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:29.237776+00:00
-- url     : https://prove2.me/submissions/97a4f07f-b18f-4710-9c4f-9fdb7176a07e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn PBlk fsLine Xc)
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRing ι)
    (x : Fin m → ℂ) :
    eval x (chartSection σ i s) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) s) := by
  show eval₂Hom (RingHom.id ℂ) x _ = _
  rw [chartSection, eval₂Hom_bind₁]
  simp only [eval₂Hom_X']
  rfl
end GroundTheory.Heights₂.Heights.Targets
