-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_maDens_congr_germ_60dfe05ed1fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:34.635249+00:00
-- url     : https://prove2.me/submissions/8d7dc267-17f3-40c4-95b6-bb12b1cd4754

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution {F G : Fin m → (Fin m → ℂ) → ℝ} {y : Fin m → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 y] G k) : ReciprocityTheory.AnForm.maDens F y = ReciprocityTheory.AnForm.maDens G y := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) y = fderiv ℝ (fderiv ℝ (G k)) y :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) y) = fun k => ReciprocityTheory.AnForm.hessC (G k) y := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
