-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ite_end_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:38.474853+00:00
-- url     : https://prove2.me/submissions/2d9bbac9-bad0-4843-867b-1ee170b90cbe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (p : Prop) [Decidable p] (A : Module.End ℂ (Fin n → M)) (f : Fin n → M) (x : Fin n) :
    (if p then A else 0) f x = if p then A f x else 0 := by
  split_ifs <;> rfl
end ReciprocityTheory.ChartRestriction.DS
