-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.maDens_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:46.332899+00:00
-- url     : https://prove2.me/submissions/2b5a8fac-85f8-4f25-834d-bbc0cdab80b7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_maDens_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution (f : (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) (h : f =ᶠ[𝓝 z] 0) :
    ReciprocityTheory.AnForm.maDens ![f] z = 0 := by
  rw [maDens_one]
  simp only [Matrix.cons_val_zero]
  have hH : ReciprocityTheory.AnForm.hessC f z = ReciprocityTheory.AnForm.hessC (0 : (Fin 1 → ℂ) → ℝ) z := by
    have hF : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ (0 : (Fin 1 → ℂ) → ℝ)) z :=
      h.fderiv.fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [hF]
  rw [hH]
  simp [ReciprocityTheory.AnForm.hessC]
end ReciprocityTheory.AnForm.M.PLC
