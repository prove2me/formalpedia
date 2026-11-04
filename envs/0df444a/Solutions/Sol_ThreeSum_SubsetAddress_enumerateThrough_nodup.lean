-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerateThrough_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:55.882882+00:00
-- url     : https://prove2.me/submissions/9f327144-bfc6-4dd8-9022-acaeb36ceb63

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
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer
import Definitions.Def_WeightedCache3SUM_Alias_40fc3f0c4241d47a
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateThrough

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L k : ℕ) : (enumerateThrough L k).Nodup := by
  induction k with
  | zero => exact enumerateLayer_nodup L 0
  | succ k ih =>
      apply ih.append (enumerateLayer_nodup L (k + 1))
      intro m hm hn
      have ht := (mem_enumerateThrough L k m).mp hm
      have hk := (mem_enumerateLayer L (k + 1) m).mp hn
      have hw := hk.2
      omega
end ThreeSum.SubsetAddress
