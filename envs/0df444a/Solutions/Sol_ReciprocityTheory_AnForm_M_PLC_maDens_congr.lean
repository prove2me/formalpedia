-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.maDens_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:03.493388+00:00
-- url     : https://prove2.me/submissions/8761c8e9-5b74-4125-97f1-c81e3e27a6c5

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
theorem _root_.solution {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) : ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have hF : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z := (h k).fderiv.fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [hF]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]
end ReciprocityTheory.AnForm.M.PLC
