-- Prove2me | solution 1 for ThreeSum.Subset.forced_prefix_identity_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:43.988663+00:00
-- url     : https://prove2.me/submissions/ae84840e-76fa-4cb4-b0fd-19cd75594a68

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
import Theorems.Thm_ThreeSum_Subset_mobius_congr
import Theorems.Thm_ThreeSum_Subset_mobius_zeta_product
import Definitions.Def_WeightedCache3SUM_Alias_645fa0f53a5987d6
import Theorems.Thm_ThreeSum_Subset_forcedInput_cardinality
import Theorems.Thm_ThreeSum_Subset_zeta_forcedInput

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (f g : Finset α → ℤ) (prefix₁ prefix₂ suffix q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hd₁ : Disjoint prefix₁ suffix) (hd₂ : Disjoint prefix₂ suffix)
    (hqs : q ⊆ suffix)
    (hq : q.card = (a - prefix₁.card) + (b - prefix₂.card)) :
    mobius (fun t => partialZeta suffix f (prefix₁ ∪ t) *
      partialZeta suffix g (prefix₂ ∪ t)) q =
    ∑ x ∈ q.powerset, f (prefix₁ ∪ x) * g (prefix₂ ∪ (q \ x)) := by
  let f' := forcedInput f prefix₁ suffix
  let g' := forcedInput g prefix₂ suffix
  have hprod := mobius_zeta_product f' g' q
  rw [unionConvolution_eq_disjointConvolution f' g' q
    (a - prefix₁.card) (b - prefix₂.card)
    (forcedInput_cardinality f prefix₁ suffix a hf hd₁)
    (forcedInput_cardinality g prefix₂ suffix b hg hd₂) hq] at hprod
  calc
    _ = mobius (fun t => zeta f' t * zeta g' t) q := by
      apply mobius_congr
      intro t ht
      rw [zeta_forcedInput f prefix₁ suffix t hd₁ (ht.trans hqs),
        zeta_forcedInput g prefix₂ suffix t hd₂ (ht.trans hqs)]
    _ = disjointConvolution f' g' q := hprod
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxs := (Finset.mem_powerset.mp hx).trans hqs
      have hds : q \ x ⊆ suffix := Finset.sdiff_subset.trans hqs
      simp only [f', g', forcedInput, hxs, hds, ite_true]
end ThreeSum.Subset
