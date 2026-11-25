-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.khw_weight_eq_of_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:07.065681+00:00
-- url     : https://prove2.me/submissions/c8fc94dc-b6bc-48c7-a259-462037711317

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrPs_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirr_eq_of_ps

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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V)
    (hu0 : u ≠ 0) {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) : ν = Λ := by
  obtain ⟨-, -, -, w, hw, hw0, hwΛ⟩ := id hV
  exact kirr_eq_of_ps fun k =>
    le_antisymm (kirrPs_le hA hV hw hw0 hwΛ hu hu0 hν.1 k) (kirrPs_le hA hV hu hu0 hν hw hw0 hwΛ.1 k)
end ReciprocityTheory.ChartRestriction.DS
