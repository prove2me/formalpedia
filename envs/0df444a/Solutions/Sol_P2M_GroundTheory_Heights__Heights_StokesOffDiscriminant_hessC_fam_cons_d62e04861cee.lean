-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_hessC_fam_cons_d62e04861cee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:24.956487+00:00
-- url     : https://prove2.me/submissions/bb434d3a-91c6-4175-9fb7-d3b16ea4b39f

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
namespace GroundTheory.Heights₂.Heights.StokesOffDiscriminant
theorem _root_.solution {m : ℕ} (f : (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ)
    (z : Fin (m + 1) → ℂ) :
    (fun k => ReciprocityTheory.AnForm.hessC ((Fin.cons f φ : Fin (m + 1) → (Fin (m + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (ReciprocityTheory.AnForm.hessC f z) (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
