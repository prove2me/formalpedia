-- Prove2me | solution 1 for SensitivityMacroPartitionModel.clusterCounts_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:24.008028+00:00
-- url     : https://prove2.me/submissions/163d0345-b0e1-49ab-b2ee-7e62eca54019

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel

section


/-! Every partition of a finite indexed head set is represented by choosing
its least index in each class. The finite search may enumerate all functions
whose value at index i is at most i; no canonicality test is needed for
completeness. -/
namespace SensitivityMacroPartitionModel

open scoped BigOperators
set_option autoImplicit false



























noncomputable section
open scoped Classical













theorem macro_least {n : ℕ} {M : Type} (cluster : Fin n → M) (i : Fin n) :
    cluster (least cluster i) = cluster i := by
  have hm : least cluster i ∈ fiber cluster i := Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hm).2













theorem le_groupCap {n : ℕ} (p : Partition n) (residual : Fin n → ℕ)
    (k : Fin n) (c : ℕ) (hempty : (members p k) = ∅ → c = 0)
    (hle : ∀ i ∈ members p k, c ≤ residual i) : c ≤ groupCap p residual k := by
  unfold groupCap
  split_ifs with h
  · obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp (Finset.min'_mem ((members p k).image residual) (h.image residual))
    exact heq ▸ hle i hi
  · rw [hempty (Finset.not_nonempty_iff_eq_empty.mp h)]





end
end SensitivityMacroPartitionModel

end

/-! The counts attached to a cluster are kept once for pricing and once per
guard head for the uncompressed incidence budget. The finite product of
bounded counts includes every actual assignment. -/
open SensitivityMacroPartitionModel
open scoped Classical BigOperators
set_option autoImplicit false
variable {n : ℕ} {M : Type}

theorem solution (cluster : Fin n → M) (G : Finset (Fin n)) (amount : M → ℕ)
    (residual : Fin n → ℕ) (hbound : ∀ i, amount (cluster i) ≤ residual i) (k : Fin n) :
    clusterCounts cluster G amount k ≤ groupCap (representative cluster) residual k := by
  unfold clusterCounts
  split_ifs with h
  · obtain ⟨j,hj,hjk⟩ := Finset.mem_image.mp h
    apply le_groupCap
    · intro hempty
      have hm : j ∈ members (representative cluster) k := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjk⟩
      rw [hempty] at hm
      exact (Finset.notMem_empty _ hm).elim
    · intro i hi
      have hir : least cluster i = k := (Finset.mem_filter.mp hi).2
      have hc : cluster k = cluster i := by
        rw [← hir]
        exact macro_least cluster i
      rw [hc]
      exact hbound i
  · exact Nat.zero_le _
