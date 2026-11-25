-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tset_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:30.612082+00:00
-- url     : https://prove2.me/submissions/3c3babb7-d7c5-47b4-abdf-98b60a1669ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : Matrix (Fin n) (Fin n) ℂ} (hu : k * kᴴ = 1) (s b : Fin n) :
    ∑ d, k s d * star (k b d) = if s = b then 1 else 0 := by
  have h := congrFun (congrFun hu s) b
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply] using h
end ReciprocityTheory.ChartRestriction.DS
