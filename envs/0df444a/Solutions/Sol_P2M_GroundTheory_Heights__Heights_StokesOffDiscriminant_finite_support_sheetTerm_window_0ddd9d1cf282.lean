-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_finite_support_sheetTerm_window_0ddd9d1cf282
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:21.089906+00:00
-- url     : https://prove2.me/submissions/517d2c05-80d5-40b1-acf2-ae85430c2a2c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow

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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin D) (Fin n) ℂ} {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ}
    {y : Fin D → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (h : ∀ x, sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0) :
    (Function.support (sheetTerm J A H y)).Finite := by
  refine (Set.finite_singleton (s y)).subset fun x hx => ?_
  rw [Function.mem_support, h x] at hx
  split_ifs at hx with hc
  · exact hc.2
  · exact absurd rfl hx
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
