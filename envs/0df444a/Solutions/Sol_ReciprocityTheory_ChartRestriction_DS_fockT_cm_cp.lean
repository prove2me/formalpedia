-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fockT_cm_cp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:27.9363+00:00
-- url     : https://prove2.me/submissions/a135b616-13dd-427d-9c29-48e1f917dd38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA

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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) {ε : Fin n → Bool}
    {j b u v : Fin n} (hjb : ¬(ε j = true ∧ ε b = false)) (huv : ε u = true ∧ ε v = false) (y : W) :
    cm j b (cp u v y) = -(cp u v (cm j b y)) := by
  have h3 := (hC j b u v).2.2
  have hne : ¬(j = u ∧ b = v) := by
    rintro ⟨rfl, rfl⟩
    exact hjb huv
  rw [if_neg hne] at h3
  have h := LinearMap.congr_fun h3 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h
end ReciprocityTheory.ChartRestriction.DS
