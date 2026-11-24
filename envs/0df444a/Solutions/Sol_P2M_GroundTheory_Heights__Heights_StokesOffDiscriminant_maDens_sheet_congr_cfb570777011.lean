-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:47.359991+00:00
-- url     : https://prove2.me/submissions/dab2b287-ec9e-48f0-bdfd-10c83573bdcd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_maDens_congr_germ


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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    (Ψ : Fin D → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ} {s s' : (Fin D → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (hs' : IsSheetAt J A x s') :
    ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s') (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s) (A *ᵥ x) :=
  ReciprocityTheory.AnForm.M.PLAux.maDens_congr_germ fun k =>
    (SheetSumMeasurable.sheet_eventuallyEq hs hs').fun_comp (Ψ k)
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
