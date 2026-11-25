-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefLam_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:57.544457+00:00
-- url     : https://prove2.me/submissions/2472af24-f5f4-44b6-87ef-b568bacba538

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
theorem _root_.solution (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f u : Fin n → H) :
    coefLam dual σ g f u = ∑ c, inner ℂ (f c) (coefTG dual σ g u c) := by
  simp [coefLam, coefTG, inner_sum, inner_smul_right]
end ReciprocityTheory.ChartRestriction.DS
