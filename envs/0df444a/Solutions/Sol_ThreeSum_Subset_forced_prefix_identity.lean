-- Prove2me | solution 1 for ThreeSum.Subset.forced_prefix_identity
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:30:52.849328+00:00
-- url     : https://prove2.me/submissions/f7267a58-2af6-4ff5-90de-ae9297672a32

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
import Theorems.Thm_ThreeSum_Subset_mobius_zeta
import Theorems.Thm_ThreeSum_Subset_partialZeta_forced_prefix
import Theorems.Thm_ThreeSum_Subset_unionConvolution_eq_disjointConvolution


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














theorem mobius_congr (q : Finset α) {f g : Finset α → ℤ}
    (h : ∀ s ⊆ q, f s = g s) : mobius f q = mobius g q := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finset.mem_powerset.mp hs)]
























































private theorem powerset_subset_of_subset {u q : Finset α} (h : u ⊆ q) :
    u.powerset ⊆ q.powerset := by
  intro s hs
  exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hs).trans h)

private theorem unionConvolution_extend (f g : Finset α → ℤ)
    {u q : Finset α} (hu : u ⊆ q) :
    unionConvolution f g u =
      ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
        if s ∪ v = u then f s * g v else 0 := by
  have hp := powerset_subset_of_subset hu
  unfold unionConvolution
  calc
    _ = ∑ s ∈ u.powerset, ∑ v ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_subset hp
      intro v hv hvu
      have hne : s ∪ v ≠ u := by
        intro he
        apply hvu
        apply Finset.mem_powerset.mpr
        rw [← he]
        exact Finset.subset_union_right
      simp only [hne, ite_false]
    _ = _ := by
      apply Finset.sum_subset hp
      intro s hs hsu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : s ∪ v ≠ u := by
        intro he
        apply hsu
        apply Finset.mem_powerset.mpr
        rw [← he]
        exact Finset.subset_union_left
      simp only [hne, ite_false]

theorem zeta_unionConvolution (f g : Finset α → ℤ) (q : Finset α) :
    zeta (unionConvolution f g) q = zeta f q * zeta g q := by
  unfold zeta
  calc
    _ = ∑ u ∈ q.powerset, ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact unionConvolution_extend f g (Finset.mem_powerset.mp hu)
    _ = ∑ s ∈ q.powerset, ∑ v ∈ q.powerset, ∑ u ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
    _ = ∑ s ∈ q.powerset, ∑ v ∈ q.powerset, f s * g v := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      have huv : s ∪ v ∈ q.powerset :=
        Finset.mem_powerset.mpr
          (Finset.union_subset (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp hv))
      rw [Finset.sum_eq_single (s ∪ v)]
      · simp
      · intro u hu hne
        simp only [Ne.symm hne, ite_false]
      · intro h
        exact False.elim (h huv)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The signed product of two ordinary zeta transforms counts exact unions. -/
theorem mobius_zeta_product (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun t => zeta f t * zeta g t) q = unionConvolution f g q := by
  have heq : (fun t => zeta f t * zeta g t) = zeta (unionConvolution f g) := by
    funext t
    exact (zeta_unionConvolution f g t).symm
  rw [heq, mobius_zeta]





































































































/-! ## Stored partial zeta stages -/































































































































theorem forcedInput_cardinality
    (f : Finset α → ℤ) (pre suffix : Finset α) (a : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hd : Disjoint pre suffix) :
    ∀ x, forcedInput f pre suffix x ≠ 0 → x.card = a - pre.card := by
  intro x hx
  have hxs : x ⊆ suffix := by
    by_contra h
    apply hx
    simp only [forcedInput, h, ite_false]
  have hfx : f (pre ∪ x) ≠ 0 := by
    simpa only [forcedInput, hxs, ite_true] using hx
  have hdx : Disjoint pre x := by
    apply Finset.disjoint_left.mpr
    intro b hbp hbx
    exact Finset.disjoint_left.mp hd hbp (hxs hbx)
  have hc := hf (pre ∪ x) hfx
  rw [Finset.card_union_of_disjoint hdx] at hc
  omega

theorem zeta_forcedInput
    (f : Finset α → ℤ) (pre suffix t : Finset α)
    (hd : Disjoint pre suffix) (ht : t ⊆ suffix) :
    zeta (forcedInput f pre suffix) t =
      partialZeta suffix f (pre ∪ t) := by
  rw [partialZeta_forced_prefix f suffix pre t hd ht]
  apply Finset.sum_congr rfl
  intro x hx
  have hxs := (Finset.mem_powerset.mp hx).trans ht
  simp only [forcedInput, hxs, ite_true]

/-- The restricted count used by a reporting query is obtained from the already
stored partial-zeta stages.  No extra restricted transform is postulated. -/
theorem forced_prefix_identity_sourceProof
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

/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

end

universe u_1

theorem solution : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f g : Finset.{u_1} α → Int)
  (prefix₁ prefix₂ suffix q : Finset.{u_1} α) (a b : Nat),
  (∀ (s : Finset.{u_1} α),
      @Ne.{1} Int (f s) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α s) a) →
    (∀ (v : Finset.{u_1} α),
        @Ne.{1} Int (g v) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq.{1} Nat (@Finset.card.{u_1} α v) b) →
      @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) prefix₁
          suffix →
        @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) prefix₂
            suffix →
          @LE.le.{u_1} (Finset.{u_1} α)
              (@Preorder.toLE.{u_1} (Finset.{u_1} α)
                (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
              q suffix →
            @Eq.{1} Nat (@Finset.card.{u_1} α q)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a (@Finset.card.{u_1} α prefix₁))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b (@Finset.card.{u_1} α prefix₂))) →
              @Eq.{1} Int
                (@ThreeSum.Subset.mobius.{u_1} α
                  (fun (t : Finset.{u_1} α) =>
                    @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                      (@ThreeSum.Subset.partialZeta.{u_1} α inst suffix f
                        (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₁ t))
                      (@ThreeSum.Subset.partialZeta.{u_1} α inst suffix g
                        (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₂ t)))
                  q)
                (∑ x ∈ @Finset.powerset.{u_1} α q,
                  @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (f (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₁ x))
                    (g
                      (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₂
                        (@SDiff.sdiff.{u_1} (Finset.{u_1} α) (@Finset.instSDiff.{u_1} α inst) q x)))) := by
  exact @ThreeSum.Subset.forced_prefix_identity_sourceProof

#print axioms solution
