-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerateLayer_nodup_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:35.158582+00:00
-- url     : https://prove2.me/submissions/d0596fea-8fdd-44ff-9231-939dcae2b047

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L k : ℕ) : (enumerateLayer L k).Nodup := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerateLayer]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · rw [enumerateLayer, if_pos hk]
            apply (ih (k + 1)).append
            · exact (ih k).map (fun _ _ h => Nat.add_left_cancel h)
            · intro m hm hn
              have hb := ((mem_enumerateLayer L (k + 1) m).mp hm).1
              obtain ⟨n, _, he⟩ := List.mem_map.mp hn
              omega
          · simp [enumerateLayer, hk]
end ThreeSum.SubsetAddress
