-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tensSub_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:17.978021+00:00
-- url     : https://prove2.me/submissions/db78f307-3f37-4f9e-afbe-6bf53942ce37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_genSub_E

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} (dual : Bool) (a b : Fin n) :
    ∀ f ∈ tensSub (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) := by
  intro f hf
  rw [tset_mem] at hf ⊢
  intro c
  have hE : ∀ x y v, v ∈ genSub E V → E x y v ∈ genSub E V := fun x y v hv => tset_genSub_E E V x y hv
  cases dual
  · show ((E a b).comp (coordV c) + (if c = a then coordV b else 0) : (Fin n → D) →ₗ[ℂ] D) f ∈ genSub E V
    split_ifs
    · rw [LinearMap.add_apply, LinearMap.comp_apply]
      exact Submodule.add_mem _ (hE a b _ (hf c)) (hf b)
    · rw [LinearMap.add_apply, LinearMap.zero_apply, add_zero, LinearMap.comp_apply]
      exact hE a b _ (hf c)
  · show ((E a b).comp (coordV c) - (if c = b then coordV a else 0) : (Fin n → D) →ₗ[ℂ] D) f ∈ genSub E V
    split_ifs
    · rw [LinearMap.sub_apply, LinearMap.comp_apply]
      exact Submodule.sub_mem _ (hE a b _ (hf c)) (hf a)
    · rw [LinearMap.sub_apply, LinearMap.zero_apply, sub_zero, LinearMap.comp_apply]
      exact hE a b _ (hf c)
end ReciprocityTheory.ChartRestriction.DS
