-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_eval_liftPoly_7a6b03adb6c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:15.368412+00:00
-- url     : https://prove2.me/submissions/c89fee84-5410-41ea-ba72-369f3f39deb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.SegreChartZeroSet
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreChartZeroSet
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ)
    (f : MRing ι) :
    eval x (liftPoly σ i f) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) := by
  rw [liftPoly, hom_eval₂, eval_map]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp [chartLift]
end GroundTheory.Heights₂.Heights.SegreChartZeroSet
