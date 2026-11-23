-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_db_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:11.515853+00:00
-- url     : https://prove2.me/submissions/953eddea-e000-4d94-82c8-1c1ab8a96e09

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    db n z j f x = db n z j g x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm he.2
      | (have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)
         rwa [e.left_inv he.2] at hc')
    have hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact ht.eventually h
    unfold wdb
    rw [hfg.fderiv_eq]
  · simp only [db, dif_neg hc]
end ReciprocityTheory.L2DbarEstimates.F
