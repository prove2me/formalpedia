-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.isCompatChart_trans_cle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:45.265+00:00
-- url     : https://prove2.me/submissions/204a9b65-1d9d-4090-a5b0-4cd74f0efe1d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (i : Fin A.n) (L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) :
    IsCompatChart A ((A.chart i).trans L.toHomeomorph.toOpenPartialHomeomorph) := by
  intro j
  constructor
  · intro x hx
    have hx' : x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source := ⟨hx.1, hx.2.1⟩
    exact (L.toContinuousLinearMap.analyticAt _).comp (A.holo j i x hx')
  · intro x hx
    have hx' : L.symm x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source := ⟨hx.1.2, hx.2⟩
    exact (A.holo i j (L.symm x) hx').comp (L.symm.toContinuousLinearMap.analyticAt x)
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
