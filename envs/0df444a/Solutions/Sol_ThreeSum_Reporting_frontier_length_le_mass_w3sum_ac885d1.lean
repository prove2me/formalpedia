-- Prove2me | solution 1 for ThreeSum.Reporting.frontier_length_le_mass_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:15.845119+00:00
-- url     : https://prove2.me/submissions/9cd44ccf-d4db-4fe1-b9a3-4087141e88bf

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting
import Theorems.Thm_ThreeSum_Reporting_mass_pos_iff
import Definitions.Def_WeightedCache3SUM_Alias_c2dccdb99e31a4aa
import Definitions.Def_WeightedCache3SUM_Alias_491c605e29e6bd9c
import Theorems.Thm_ThreeSum_Subset_positive_fibers_le_mass


set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]
namespace ThreeSum.Reporting
theorem _root_.solution (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hc : ∀ k, (children k).Nodup) (hk : k ≤ J) :
    (frontier children query k).length ≤ ∑ i ∈ I, weight i := by
  classical
  let labels := I.image fun i => (word i).take k
  have heq : (frontier children query k).toFinset =
      labels.filter (fun pre => 0 < mass I word weight k pre) := by
    ext pre
    rw [List.mem_toFinset, mem_frontier_iff I word weight children query J k
      hlen hchildren hquery hk, mem_filter]
    constructor
    · intro h
      obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight k pre).mp h
      exact ⟨mem_image.mpr ⟨i, hi, hpre⟩, h⟩
    · exact And.right
  have hcount := Subset.positive_fibers_le_mass I labels
    (fun i => (word i).take k) weight (fun i hi => mem_image.mpr ⟨i, hi, rfl⟩)
  change (labels.filter (fun pre => 0 < mass I word weight k pre)).card ≤ _ at hcount
  rw [← heq, List.toFinset_card_of_nodup (frontier_nodup children query hc k)] at hcount
  exact hcount
end ThreeSum.Reporting
