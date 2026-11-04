-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.values_bounded_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:37.032169+00:00
-- url     : https://prove2.me/submissions/09ecd872-4e09-4b36-9380-f107341d7f15

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}
namespace ThreeSum.RadixKeyLists
theorem _root_.solution (p U : ℕ) (base : List ℤ)
    (hbase : ∀ x ∈ base, |x| ≤ (U : ℤ)) (j : ℕ) :
    ∀ z ∈ values (p : ℤ) base j, |z| ≤ ((U*(p+1)^j : ℕ) : ℤ) := by
  induction j with
  | zero =>
    intro z hz
    have hz0 : z=0 := by simpa only [values,List.mem_singleton] using hz
    subst z
    simp
  | succ j ih =>
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    have hkey := hbase a ha
    have htail := ih y hy
    have hpow : 1 ≤ (p+1)^j := one_le_pow₀ (by omega)
    have hU : (U : ℤ) ≤ ((U*(p+1)^j : ℕ) : ℤ) := by
      exact_mod_cast (Nat.le_mul_of_pos_right U (by omega : 0 < (p+1)^j))
    calc
      |a+(p : ℤ)*y| ≤ |a|+(p : ℤ)*|y| := by
        simpa only [abs_mul,Int.abs_natCast] using abs_add_le a ((p : ℤ)*y)
      _ ≤ (U : ℤ)+(p : ℤ)*((U*(p+1)^j : ℕ) : ℤ) :=
        add_le_add hkey (mul_le_mul_of_nonneg_left htail (Int.natCast_nonneg _))
      _ ≤ ((U*(p+1)^j : ℕ) : ℤ)+(p : ℤ)*((U*(p+1)^j : ℕ) : ℤ) :=
        add_le_add hU le_rfl
      _ = ((U*(p+1)^(j+1) : ℕ) : ℤ) := by push_cast; rw [pow_succ]; ring
end ThreeSum.RadixKeyLists
