-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fockT_cm_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:48.173947+00:00
-- url     : https://prove2.me/submissions/1bc20cea-3d18-48a9-9439-dfbb07ea6cca

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
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (j b w z : Fin n) (y : W) :
    cm j b (cm w z y) = -(cm w z (cm j b y)) := by
  have h := LinearMap.congr_fun (hC j b w z).2.1 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h
end ReciprocityTheory.ChartRestriction.DS
