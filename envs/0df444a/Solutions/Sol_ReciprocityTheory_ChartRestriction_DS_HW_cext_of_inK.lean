-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.cext_of_inK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:25:53.283236+00:00
-- url     : https://prove2.me/submissions/42c150af-3a05-4eb3-b6e7-5cb048b139a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_cpart_bdPart_of_inK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : cext ε A X = A X := by
  obtain ⟨h1, h2⟩ := cpart_bdPart_of_inK ε hX
  have h0 : A 0 = 0 := by
    have := (hA X X 0 hX hX).2
    simpa using this
  unfold cext
  rw [h1, h2, h0, smul_zero, add_zero]
end ReciprocityTheory.ChartRestriction.DS.HW
