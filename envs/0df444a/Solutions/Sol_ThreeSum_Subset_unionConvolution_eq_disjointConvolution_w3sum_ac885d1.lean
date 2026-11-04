-- Prove2me | solution 1 for ThreeSum.Subset.unionConvolution_eq_disjointConvolution_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:22.018678+00:00
-- url     : https://prove2.me/submissions/07e0365a-b880-4855-96fc-62318b34d3d6

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
import Theorems.Thm_ThreeSum_Subset_disjoint_of_union_card

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (f g : Finset α → ℤ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    unionConvolution f g q = disjointConvolution f g q := by
  unfold unionConvolution disjointConvolution
  apply Finset.sum_congr rfl
  intro s hs
  have hsq := Finset.mem_powerset.mp hs
  by_cases hfs : f s = 0
  · simp [hfs]
  have hcompl : q \ s ∈ q.powerset :=
    Finset.mem_powerset.mpr Finset.sdiff_subset
  rw [Finset.sum_eq_single (q \ s)]
  · have hU : s ∪ (q \ s) = q := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hx | ⟨hx, _⟩)
        · exact hsq hx
        · exact hx
      · intro hx
        by_cases hxs : x ∈ s
        · exact Or.inl hxs
        · exact Or.inr ⟨hx, hxs⟩
    simp only [hU, ite_true]
  · intro v hv hne
    by_cases hu : s ∪ v = q
    · by_cases hgv : g v = 0
      · simp [hgv]
      have hd : Disjoint s v := disjoint_of_union_card hu (by rw [hf s hfs, hg v hgv]; exact hq)
      have he : v = q \ s := by
        ext x
        simp only [Finset.mem_sdiff]
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · rw [← hu]
            exact Finset.mem_union_right s hx
          · intro hxs
            exact Finset.disjoint_left.mp hd hxs hx
        · rintro ⟨hxq, hxs⟩
          rw [← hu] at hxq
          exact (Finset.mem_union.mp hxq).resolve_left hxs
      exact False.elim (hne he)
    · simp only [hu, ite_false]
  · intro h
    exact False.elim (h hcompl)
end ThreeSum.Subset
