-- Prove2me | solution 1 for ThreeSum.SubsetAddress.layerRank_injective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:59.788163+00:00
-- url     : https://prove2.me/submissions/8a487f3c-710c-4a3d-8654-05dbd8ce321e

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
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


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











































































































theorem layerRank_injective_sourceProof {L k m n : ℕ} (hm : IsMask L k m) (hn : IsMask L k n)
    (he : layerRank L k m = layerRank L k n) : m = n := by
  induction L generalizing k m n with
  | zero =>
      have hm' := hm.1
      have hn' := hn.1
      simp only [pow_zero] at hm' hn'
      omega
  | succ L ih =>
      by_cases hc : m < 2 ^ L <;> by_cases hd : n < 2 ^ L
      · apply ih (hm.low hc) (hn.low hd)
        simpa only [layerRank, if_pos hc, if_pos hd] using he
      · have hb := layerRank_lt (hm.low hc)
        simp only [layerRank, if_pos hc, if_neg hd] at he
        omega
      · have hb := layerRank_lt (hn.low hd)
        simp only [layerRank, if_neg hc, if_pos hd] at he
        omega
      · have hr := (hm.high (Nat.le_of_not_gt hc)).2
        have hs := (hn.high (Nat.le_of_not_gt hd)).2
        have hrest : layerRank L (k - 1) (m - 2 ^ L) =
            layerRank L (k - 1) (n - 2 ^ L) := by
          simpa only [layerRank, if_neg hc, if_neg hd, Nat.add_left_cancel_iff] using he
        have hi := ih hr hs hrest
        omega

































































































































































































































































































































end ThreeSum.SubsetAddress

end


theorem solution : ∀ {L k m n : Nat},
  ThreeSum.SubsetAddress.IsMask L k m →
    ThreeSum.SubsetAddress.IsMask L k n →
      @Eq.{1} Nat (ThreeSum.SubsetAddress.layerRank L k m) (ThreeSum.SubsetAddress.layerRank L k n) → @Eq.{1} Nat m n := by
  exact @ThreeSum.SubsetAddress.layerRank_injective_sourceProof

#print axioms solution
