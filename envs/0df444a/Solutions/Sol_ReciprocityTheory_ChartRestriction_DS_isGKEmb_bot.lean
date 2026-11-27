-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isGKEmb_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:30:59.319967+00:00
-- url     : https://prove2.me/submissions/62e2dcc1-ebbf-4df3-a84c-bb62767b7357

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Submodule ℂ H}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S : Submodule ℂ D) : IsGKEmb dual ε σ E S ⊥ 0 := by
  refine ⟨fun x _ => by simp, fun x hx _ => (Submodule.mem_bot ℂ).1 hx, fun a b x _ => by simp, ?_⟩
  intro k _ x _ x' _ _
  funext c
  simp [kDiag]
end ReciprocityTheory.ChartRestriction.DS
