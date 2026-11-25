-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_le_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:34.083347+00:00
-- url     : https://prove2.me/submissions/f0c436a2-26ec-4da3-9103-98396f4b2643

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : Submodule ℂ M} (hVT : V ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) (k : ℕ) : layer ε E V k ≤ T := by
  induction k with
  | zero => exact hVT
  | succ k ih =>
    show layer ε E V k ⊔ _ ≤ T
    refine sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact hT a b v (ih hv)
end ReciprocityTheory.ChartRestriction.DS
