-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uRepHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:20.674129+00:00
-- url     : https://prove2.me/submissions/cbf54159-22ce-4d11-a154-bda2eeaf6c63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_URepHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_urepHom_toMK_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_urepHom_toMK_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_urepHom_mem_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution : URepHomStatement := by
  intro n ε H _ _ _ σ hσ
  have hmem : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  refine ⟨{ toFun := fun k => ⟨σ (toMK k), urepHom_mem_unitary hσ k⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_, fun k => rfl⟩
  · apply Subtype.ext
    show σ (toMK (1 : KG ε)) = 1
    rw [urepHom_toMK_one, hσ.1.1]
  · intro k k'
    apply Subtype.ext
    show σ (toMK (k * k')) = σ (toMK k) * σ (toMK k')
    rw [urepHom_toMK_mul]
    exact hσ.1.2 _ (hmem k) _ (hmem k')
  · have hc : Continuous (fun k : KG ε => toMK k) := by
      fun_prop
    have hop : Continuous (fun k : KG ε => σ (toMK k)) := by
      refine continuous_clm_apply.2 fun v => ?_
      exact (hσ.2.2 v).comp_continuous hc hmem
    exact Continuous.subtype_mk hop _
end ReciprocityTheory.ChartRestriction.DS.HW
