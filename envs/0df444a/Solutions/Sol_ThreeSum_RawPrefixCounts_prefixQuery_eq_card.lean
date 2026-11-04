-- Prove2me | solution 1 for ThreeSum.RawPrefixCounts.prefixQuery_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:52.01935+00:00
-- url     : https://prove2.me/submissions/2926f59d-672c-404c-acc3-540856991332

import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawPrefixCounts
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding RawIncidences RawReporting
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawPrefixCounts
theorem _root_.solution {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :
    prefixQuery I w k pre = (prefixItems I w k pre).card := by
  simp only [prefixQuery, Reporting.mass, Subset.fiberMass, prefixItems,
    Finset.sum_const, smul_eq_mul, mul_one]
end ThreeSum.RawPrefixCounts
