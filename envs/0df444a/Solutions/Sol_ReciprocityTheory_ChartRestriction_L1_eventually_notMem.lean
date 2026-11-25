-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.eventually_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:15.763626+00:00
-- url     : https://prove2.me/submissions/ff8455a1-9659-45dd-8f15-86a6a191aef3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) {α : ℂ} (hα : α ≠ 0) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ≠ 0 ∧ α * z ∉ L.lattice := by
  have h1 : Filter.Tendsto (fun z : ℂ => α * z) (nhds 0) (nhds 0) := by
    have : ContinuousAt (fun z : ℂ => α * z) 0 := by fun_prop
    simpa [ContinuousAt] using this
  have h2 := h1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h2] with z hz hz0
  refine ⟨hz0, fun hm => hz ⟨hm, ?_⟩⟩
  simpa [hα] using hz0
end ReciprocityTheory.ChartRestriction.L1
