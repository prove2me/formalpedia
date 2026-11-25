-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_cons_add_84a6f63f8f9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:29.557801+00:00
-- url     : https://prove2.me/submissions/8c487c6f-b436-48eb-af03-9e33844e3dbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_hessC_fam_cons_d62e04861cee
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


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
theorem _root_.solution {m : ℕ} (f g : (Fin (m + 1) → ℂ) → ℝ) (φ : Fin m → (Fin (m + 1) → ℂ) → ℝ)
    (z : Fin (m + 1) → ℂ) (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    ReciprocityTheory.AnForm.maDens (Fin.cons (fun w => f w + g w) φ) z =
      ReciprocityTheory.AnForm.maDens (Fin.cons f φ) z + ReciprocityTheory.AnForm.maDens (Fin.cons g φ) z := by
  unfold ReciprocityTheory.AnForm.maDens
  rw [hessC_fam_cons, hessC_fam_cons, hessC_fam_cons, ReciprocityTheory.AnForm.A.hessC_add f g z hf hg,
    ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum,
    ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum]
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re]
  ring
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
