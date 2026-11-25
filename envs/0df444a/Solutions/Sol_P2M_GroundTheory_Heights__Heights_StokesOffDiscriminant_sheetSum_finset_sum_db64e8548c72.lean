-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetSum_finset_sum_db64e8548c72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:27.368709+00:00
-- url     : https://prove2.me/submissions/d91be115-cb24-4537-bb82-5c8fe5f953d1

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
namespace GroundTheory.Heights₂.Heights.StokesOffDiscriminant
theorem _root_.solution {ι : Type*} (t : Finset ι) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin D) (Fin n) ℂ} {y : Fin D → ℂ}
    (H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ)
    (K : ι → (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ)
    (hH : ∀ x ∈ fibre J A y, ∀ s', IsSheetAt J A x s' → H x s' = ∑ i ∈ t, K i x s')
    (hfin : ∀ i ∈ t, (Function.support (sheetTerm J A (K i) y)).Finite) :
    sheetSum J A H y = ∑ i ∈ t, sheetSum J A (K i) y := by
  simp only [sheetSum_eq_finsum]
  rw [← finsum_sum_comm t (fun x i => sheetTerm J A (K i) y x) hfin]
  refine finsum_congr fun x => ?_
  unfold sheetTerm
  by_cases hx : x ∈ fibre J A y
  · simp only [Set.indicator_of_mem hx]
    split_ifs with hex
    · exact hH x hx _ hex.choose_spec
    · simp
  · simp [Set.indicator_of_notMem hx]
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
