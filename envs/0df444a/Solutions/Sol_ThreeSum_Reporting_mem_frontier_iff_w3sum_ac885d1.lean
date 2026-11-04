-- Prove2me | solution 1 for ThreeSum.Reporting.mem_frontier_iff_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:18.615486+00:00
-- url     : https://prove2.me/submissions/592af4b0-1bfb-44ef-9822-3b4a73de4940

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting
import Theorems.Thm_ThreeSum_Reporting_mass_pos_iff

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
    (hk : k ≤ J) (pre : List α) :
    pre ∈ frontier children query k ↔ 0 < mass I word weight k pre := by
  induction k generalizing pre with
  | zero =>
      constructor
      · intro hp
        simp only [frontier] at hp
        split at hp
        · have heq := List.mem_singleton.mp hp
          subst pre
          simpa only [hquery 0 (by omega) []] using ‹0 < query 0 []›
        · cases hp
      · intro hm
        obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight 0 pre).mp hm
        have heq : pre = [] := by simpa using hpre.symm
        rw [heq] at hm ⊢
        simp [frontier, hquery 0 (by omega) [], hm]
  | succ k ih =>
      constructor
      · intro hp
        have hpos := (List.mem_filter.mp hp).2
        simpa only [decide_eq_true_eq, hquery (k + 1) hk pre] using hpos
      · intro hm
        obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight (k + 1) pre).mp hm
        have hj : k < J := by omega
        have hlenk : k < (word i).length := by rw [hlen i hi]; exact hj
        have hparentMass : 0 < mass I word weight k ((word i).take k) :=
          (mass_pos_iff I word weight k _).mpr ⟨i, hi, rfl, hw⟩
        have hparent := (ih (by omega) ((word i).take k)).mpr hparentMass
        apply List.mem_filter.mpr
        constructor
        · apply List.mem_flatMap.mpr
          refine ⟨(word i).take k, hparent, ?_⟩
          apply List.mem_map.mpr
          exact ⟨(word i)[k], hchildren i hi k hj,
            (List.take_append_getElem hlenk).trans hpre⟩
        · simpa only [decide_eq_true_eq, hquery (k + 1) hk pre] using hm
end ThreeSum.Reporting
