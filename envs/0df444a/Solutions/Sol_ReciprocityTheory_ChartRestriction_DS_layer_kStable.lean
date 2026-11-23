-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_kStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:47.421331+00:00
-- url     : https://prove2.me/submissions/b318d0c4-418b-451b-be3d-4426dbf3facd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_layer_succ_nc

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε E (layer ε E V k) := by
  induction k with
  | zero => exact hV
  | succ k ih =>
    intro a b hab
    have key : layer ε E V (k + 1) ≤ (layer ε E V (k + 1)).comap (E a b) := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun v hv => layer_le_succ k (ih a b hab v hv))
        (iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_)
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      rw [Submodule.mem_comap, Submodule.mem_comap]
      have h := congrArg (fun f : Module.End ℂ M => f v) (hE a b c d)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      have h2 : E a b (E c d v) = E c d (E a b v) +
          ((if b = c then E a d else 0) v - (if d = a then E c b else 0) v) := by
        rw [← h]
        abel
      rw [h2]
      refine Submodule.add_mem _ (apply_mem_layer_succ_nc hcd (ih a b hab v hv))
        (Submodule.sub_mem _ ?_ ?_)
      · split_ifs with hbc
        · exact apply_mem_layer_succ_nc (fun h' => hcd (by rw [← hbc, ← hab, h'])) hv
        · simp
      · split_ifs with hda
        · exact apply_mem_layer_succ_nc (fun h' => hcd (by rw [hda, hab]; exact h')) hv
        · simp
    intro v hv
    exact key hv
end ReciprocityTheory.ChartRestriction.DS
