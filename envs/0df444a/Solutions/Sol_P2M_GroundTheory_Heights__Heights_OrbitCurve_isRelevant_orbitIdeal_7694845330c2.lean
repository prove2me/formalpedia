-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_isRelevant_orbitIdeal_7694845330c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:29.891902+00:00
-- url     : https://prove2.me/submissions/e2641ea6-bc23-4590-979d-a9c8f14aa1aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    Geo.IsRelevant (ι := blockIdx n) (orbitIdeal x) := by
  obtain ⟨c, hc⟩ := exists_chart hx
  refine fun k ↦ ⟨c k, fun h ↦ ?_⟩
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X] at h
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) h
end GroundTheory.Heights₂.Heights.OrbitCurve
