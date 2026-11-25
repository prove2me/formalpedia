-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_eq_zero_of_notMem_tsupport_2109f7bfe5df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:23.771525+00:00
-- url     : https://prove2.me/submissions/67f40cec-f671-4f24-9a68-ca4815b4f881

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_fam_comp_6096efaf6c1c
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_maDens_cons_eq_zero


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
theorem _root_.solution {m : ℕ} (f : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) {s : (Fin (m + 1) → ℂ) → Fin n → ℂ} {y : Fin (m + 1) → ℂ}
    (hs : ContinuousAt s y) (hy : s y ∉ tsupport f) :
    ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s) y = 0 := by
  rw [fam_comp]
  apply ReciprocityTheory.AnForm.M.PLAux.maDens_cons_eq_zero
  filter_upwards [hs.preimage_mem_nhds ((isClosed_tsupport f).isOpen_compl.mem_nhds hy)] with w hw
  exact image_eq_zero_of_notMem_tsupport (f := f) (x := s w) hw
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
