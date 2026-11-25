-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hessC_const_smul_8db5d30f5530
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:13.037696+00:00
-- url     : https://prove2.me/submissions/9e059d0c-bd88-4a97-a8da-65cd0a0a74bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PlaneIdealTwoOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {D : ℕ} (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.hessC (c • φ) z = (c : ℂ) • ReciprocityTheory.AnForm.hessC φ z := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (0 : ℝ) • φ = fun _ => (0 : ℝ) := by funext x; simp
    ext i j
    simp [ReciprocityTheory.AnForm.hessC, h0]
  have := invertibleOfNonzero hc
  have h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ := by
    funext x
    exact fderiv_const_smul_of_invertible c
  have h2 : fderiv ℝ (fderiv ℝ (c • φ)) z = c • fderiv ℝ (fderiv ℝ φ) z := by
    rw [h1]
    exact fderiv_const_smul_of_invertible (f := fderiv ℝ φ) c
  ext i j
  simp only [ReciprocityTheory.AnForm.hessC, h2, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
