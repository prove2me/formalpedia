-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_window_d6119a75072f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:30.00462+00:00
-- url     : https://prove2.me/submissions/01120bf5-6b5e-4b70-abca-f64c29cc9c48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_eq_finsum_1e4201e1d6ff

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
open GroundTheory.Heights₂.Heights.StokesOffDiscriminant
variable {n D : ℕ}
open Classical
namespace GroundTheory.Heights₂.Heights.StokesOffDiscriminant
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ} {y : Fin D → ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (h : ∀ x, sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0) :
    sheetSum J A H y = V.indicator (fun y => H (s y) s) y := by
  rw [sheetSum_eq_finsum, finsum_congr h]
  by_cases hyV : y ∈ V
  · rw [Set.indicator_of_mem hyV, finsum_eq_single _ (s y) fun x hx => if_neg fun hc => hx hc.2]
    simp [hyV]
  · rw [Set.indicator_of_notMem hyV]
    simp [hyV]
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
