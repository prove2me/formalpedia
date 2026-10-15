-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerateLayer_nodup
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:45:36.248311+00:00
-- url     : https://prove2.me/submissions/e974f623-98cd-4539-ac13-93006051abc0

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators



















































































































































































theorem enumerateLayer_nodup_sourceProof (L k : ℕ) : (enumerateLayer L k).Nodup := by
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

end


theorem solution : ∀ (L k : Nat), @List.Nodup.{0} Nat (ThreeSum.SubsetAddress.enumerateLayer L k) := by
  exact @ThreeSum.SubsetAddress.enumerateLayer_nodup_sourceProof

#print axioms solution
