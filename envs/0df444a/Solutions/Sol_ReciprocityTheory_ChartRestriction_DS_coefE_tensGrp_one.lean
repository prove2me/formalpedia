-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefE_tensGrp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:44.296657+00:00
-- url     : https://prove2.me/submissions/39dfec2d-ffdb-4004-b7e5-ab9baab897df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul

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
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (w : Fin n → H) :
    coefTG dual σ 1 w = w := by
  ext c
  cases dual <;> simp [coefTG, coefAm, hσ.1.1, Matrix.one_apply]
end ReciprocityTheory.ChartRestriction.DS
