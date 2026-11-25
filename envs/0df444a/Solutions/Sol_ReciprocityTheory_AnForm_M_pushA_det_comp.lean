-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_det_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:05.856589+00:00
-- url     : https://prove2.me/submissions/4e561e3f-8783-4ddd-aa6a-f08cbfdd0283

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter

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
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (f g : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    LinearMap.det ((f.comp g : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
        LinearMap.det (g : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  exact LinearMap.det_comp (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) (g : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
end ReciprocityTheory.AnForm.M
