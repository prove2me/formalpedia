-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isKHWVec_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:01.803603+00:00
-- url     : https://prove2.me/submissions/1e7a22dd-562a-4414-b8be-8d31e28bbce0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ : Fin n → ℝ} {v w : M} (hv : IsKHWVec ε E μ v)
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (v - w) := by
  refine ⟨fun a => ?_, fun a b h he => ?_⟩
  · rw [map_sub, hv.1 a, hw.1 a, smul_sub]
  · rw [map_sub, hv.2 a b h he, hw.2 a b h he, sub_zero]
end ReciprocityTheory.ChartRestriction.DS
