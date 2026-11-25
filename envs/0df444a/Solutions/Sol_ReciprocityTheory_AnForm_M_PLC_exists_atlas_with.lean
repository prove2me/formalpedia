-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.exists_atlas_with
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:27.208777+00:00
-- url     : https://prove2.me/submissions/4473a1ed-a952-4724-be93-5b902073b325

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
import Theorems.Thm_ReciprocityTheory_AnForm_M_atlasOfCompat
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_compat_chart


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
theorem _root_.solution (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hψ : IsCompatChart A ψ) : ∃ B : FinHolAtlas e X, A.Compatible B ∧ ∃ j, B.chart j = ψ := by
  obtain ⟨B, hB, hall, -⟩ := atlasOfCompat A
    (Fin.cons ψ A.chart : Fin (A.n + 1) → OpenPartialHomeomorph X (Fin e → ℂ))
    (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hψ
      · simpa using pa_compat_chart A j)
    (fun x => by
      obtain ⟨j, hj⟩ := A.cover x
      exact ⟨j.succ, by simpa using hj⟩)
  obtain ⟨j, hj⟩ := hall 0
  exact ⟨B, hB, j, by simpa using hj⟩
end ReciprocityTheory.AnForm.M.PLC
