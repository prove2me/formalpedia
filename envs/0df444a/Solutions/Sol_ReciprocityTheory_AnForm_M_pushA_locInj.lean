-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_locInj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:14.363848+00:00
-- url     : https://prove2.me/submissions/9ee0e079-da64-4279-ae5d-757bbafab661

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
theorem _root_.solution {τ : (Fin e → ℂ) → (Fin e → ℂ)} {z : Fin e → ℂ} (hτ : AnalyticAt ℂ τ z)
    (hd : LinearMap.det (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ Set.InjOn τ W := by
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hd).toContinuousLinearEquiv
  have hL : (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ τ z := by
    ext v : 1
    simp [L]
  have hs : HasStrictFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z := hL ▸ hτ.hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph τ).source, (hs.toOpenPartialHomeomorph τ).open_source,
    hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  have := (hs.toOpenPartialHomeomorph τ).injOn
  simpa using this
end ReciprocityTheory.AnForm.M
