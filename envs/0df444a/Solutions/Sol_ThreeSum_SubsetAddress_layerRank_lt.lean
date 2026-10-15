-- Prove2me | solution 1 for ThreeSum.SubsetAddress.layerRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:48:09.458981+00:00
-- url     : https://prove2.me/submissions/d968ba2d-b7c8-4e89-93e1-fe5033007f19

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




























































































theorem layerRank_lt_sourceProof {L k m : ℕ} (hm : IsMask L k m) : layerRank L k m < L.choose k := by
  induction L generalizing k m with
  | zero =>
      have hk := hm.le_width
      have : k = 0 := by omega
      simp [this, layerRank]
  | succ L ih =>
      by_cases hc : m < 2 ^ L
      · simpa only [layerRank, if_pos hc] using
          (ih (hm.low hc)).trans_le (Nat.choose_le_succ L k)
      · obtain ⟨hk, hr⟩ := hm.high (Nat.le_of_not_gt hc)
        have hb := ih hr
        rw [layerRank, if_neg hc, Nat.choose_succ_left L k hk]
        omega



























































































































































































































































































































































end ThreeSum.SubsetAddress

end


theorem solution : ∀ {L k m : Nat},
  ThreeSum.SubsetAddress.IsMask L k m → @LT.lt.{0} Nat instLTNat (ThreeSum.SubsetAddress.layerRank L k m) (L.choose k) := by
  exact @ThreeSum.SubsetAddress.layerRank_lt_sourceProof

#print axioms solution
