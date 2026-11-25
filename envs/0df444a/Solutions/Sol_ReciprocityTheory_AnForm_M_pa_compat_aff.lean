-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pa_compat_aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:42.594627+00:00
-- url     : https://prove2.me/submissions/0c29b8fe-0164-4064-b878-7dba27e9c3f8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_aff_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩
  have hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z :=
    by fun_prop
  exact AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv
end ReciprocityTheory.AnForm.M
