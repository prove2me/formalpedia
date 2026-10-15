-- Prove2me | solution 1 for ThreeSum.Subset.unionConvolution_eq_disjointConvolution
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:06.241122+00:00
-- url     : https://prove2.me/submissions/47618294-ab98-4f96-bb87-f7610b2129ea

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]



























































































































































/-- If the input sizes add to the output size, an exact union is disjoint. -/
theorem disjoint_of_union_card {s v q : Finset α}
    (hu : s ∪ v = q) (hc : q.card = s.card + v.card) : Disjoint s v := by
  apply Finset.card_union_eq_card_add_card.mp
  simpa only [hu] using hc





theorem unionConvolution_eq_disjointConvolution_sourceProof
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









































/-! ## Stored partial zeta stages -/































































































































































































/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

end

universe u_1

theorem solution : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f g : Finset.{u_1} α → Int) (q : Finset.{u_1} α) (a b : Nat),
  (∀ (s : Finset.{u_1} α),
      @Ne.{1} Int (f s) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α s) a) →
    (∀ (v : Finset.{u_1} α),
        @Ne.{1} Int (g v) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq.{1} Nat (@Finset.card.{u_1} α v) b) →
      @Eq.{1} Nat (@Finset.card.{u_1} α q) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b) →
        @Eq.{1} Int (@ThreeSum.Subset.unionConvolution.{u_1} α inst f g q)
          (@ThreeSum.Subset.disjointConvolution.{u_1} α inst f g q) := by
  exact @ThreeSum.Subset.unionConvolution_eq_disjointConvolution_sourceProof

#print axioms solution
