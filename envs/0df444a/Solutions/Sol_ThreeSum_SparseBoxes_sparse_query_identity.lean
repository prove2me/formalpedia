-- Prove2me | solution 1 for ThreeSum.SparseBoxes.sparse_query_identity
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:53:43.854324+00:00
-- url     : https://prove2.me/submissions/d2099e83-ad8c-443f-872d-e0330a9c4a8d

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes

open scoped BigOperators

variable {α : Type*} [LinearOrder α]













theorem largest_spec (t : ℕ) (m : Finset α) (h : t ≤ m.card) :
    IsLargest t m (largest t m) := by
  induction t generalizing m with
  | zero => simp [largest, IsLargest]
  | succ t ih =>
      have hm : m.Nonempty := Finset.card_pos.mp (by omega)
      let a := m.max' hm
      have ha : a ∈ m := Finset.max'_mem m hm
      have hcard : (m.erase a).card = m.card - 1 := Finset.card_erase_of_mem ha
      have ht : t ≤ (m.erase a).card := by omega
      obtain ⟨hsub, hsize, horder⟩ := ih (m.erase a) ht
      have hnot : a ∉ largest t (m.erase a) := by
        intro hx
        exact Finset.notMem_erase a m (hsub hx)
      simp only [largest, dif_pos hm]
      change IsLargest (t + 1) m (insert a (largest t (m.erase a)))
      refine ⟨Finset.insert_subset ha (hsub.trans (Finset.erase_subset a m)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot, hsize]
      · intro u hu x hx hnx
        have hxa : x ≠ a := by
          intro he
          apply hnx
          simp [he]
        have hxe : x ∈ m.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        rcases Finset.mem_insert.mp hu with hua | hut
        · subst u
          exact Finset.lt_max'_of_mem_erase_max' m hm hxe
        · apply horder u hut x hxe
          intro hxt
          exact hnx (Finset.mem_insert_of_mem hxt)

theorem IsLargest.unique {t : ℕ} {m u v : Finset α}
    (hu : IsLargest t m u) (hv : IsLargest t m v) : u = v := by
  obtain ⟨hum, huc, huo⟩ := hu
  obtain ⟨hvm, hvc, hvo⟩ := hv
  apply Finset.eq_of_subset_of_card_le
  · intro a hau
    by_contra hav
    have hex : ∃ b ∈ v, b ∉ u := by
      by_contra hn
      push Not at hn
      have he : v = u := Finset.eq_of_subset_of_card_le hn (by omega)
      exact hav (he.symm ▸ hau)
    obtain ⟨b, hbv, hbu⟩ := hex
    exact (lt_asymm (huo a hau b (hvm hbv) hbu)) (hvo b hbv a (hum hau) hav)
  · omega

























theorem queryBox_iff_separator (q u leaf : Finset α) (huq : u ⊆ q) :
    QueryBox q u leaf ↔
      leaf ⊆ q ∧ u ⊆ q \ leaf ∧
        ∀ a ∈ u, ∀ x ∈ q \ leaf, x ∉ u → x < a := by
  constructor
  · rintro ⟨hleaf, hrequired⟩
    refine ⟨hleaf.trans Finset.sdiff_subset, ?_, ?_⟩
    · intro a hau
      refine Finset.mem_sdiff.mpr ⟨huq hau, ?_⟩
      intro hal
      exact (Finset.mem_sdiff.mp (hleaf hal)).2 hau
    · intro a hau x hxm hxu
      have hxf : x ∈ q \ u :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxm).1, hxu⟩
      have hxFree : x ∈ queryFree q u := by
        by_contra hn
        have hxl := hrequired (Finset.mem_sdiff.mpr ⟨hxf, hn⟩)
        exact (Finset.mem_sdiff.mp hxm).2 hxl
      exact (Finset.mem_filter.mp hxFree).2 a hau
  · rintro ⟨hlq, hum, ho⟩
    refine ⟨?_, ?_⟩
    · intro x hxl
      refine Finset.mem_sdiff.mpr ⟨hlq hxl, ?_⟩
      intro hxu
      exact (Finset.mem_sdiff.mp (hum hxu)).2 hxl
    · intro x hx
      obtain ⟨hxf, hxn⟩ := Finset.mem_sdiff.mp hx
      by_contra hxl
      apply hxn
      apply Finset.mem_filter.mpr
      refine ⟨hxf, ?_⟩
      intro a hau
      exact ho a hau x
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxf).1, hxl⟩)
        (Finset.mem_sdiff.mp hxf).2

theorem queryBox_iff_isLargest (q u leaf : Finset α) (t : ℕ)
    (huq : u ⊆ q) (huc : u.card = t) (hlq : leaf ⊆ q) :
    QueryBox q u leaf ↔ IsLargest t (q \ leaf) u := by
  rw [queryBox_iff_separator q u leaf huq]
  simp only [IsLargest, huc, true_and, and_true]
  exact and_iff_right hlq

/-- Every leaf with at least `t` missing coordinates belongs to exactly one
query box, namely the one indexed by its largest `t` missing coordinates. -/
theorem queryBox_partition (q leaf : Finset α) (t : ℕ) (hlq : leaf ⊆ q)
    (ht : t ≤ (q \ leaf).card) :
    ∃! u, u ∈ q.powersetCard t ∧ QueryBox q u leaf := by
  let u := largest t (q \ leaf)
  have hs := largest_spec t (q \ leaf) ht
  have huq : u ⊆ q := hs.1.trans Finset.sdiff_subset
  refine ⟨u, ⟨Finset.mem_powersetCard.mpr ⟨huq, hs.2.1⟩, ?_⟩, ?_⟩
  · exact (queryBox_iff_isLargest q u leaf t huq hs.2.1 hlq).mpr hs
  · intro v hv
    obtain ⟨hvq, hvc⟩ := Finset.mem_powersetCard.mp hv.1
    exact IsLargest.unique
      ((queryBox_iff_isLargest q v leaf t hvq hvc hlq).mp hv.2) hs

/-- Leaves with fewer than `t` missing coordinates occur in no query box. -/
theorem no_queryBox_of_few_missing (q leaf u : Finset α) (t : ℕ)
    (hu : u ∈ q.powersetCard t) (hsmall : (q \ leaf).card < t) :
    ¬ QueryBox q u leaf := by
  intro hb
  obtain ⟨huq, huc⟩ := Finset.mem_powersetCard.mp hu
  have hsub := ((queryBox_iff_separator q u leaf huq).mp hb).2.1
  have hc := Finset.card_le_card hsub
  omega

/-! ## Canonical free prefixes and the finite preprocessing family -/








































































































































































/-! ## The exact addition recurrence and query sum -/













theorem boxSum_extend (ambient flags free : Finset α) (weight : Finset α → ℤ)
    (hf : flags ⊆ ambient) :
    boxSum flags free weight =
      ∑ leaf ∈ ambient.powerset,
        if BoxMember flags free leaf then weight leaf else 0 := by
  unfold boxSum
  calc
    _ = ∑ leaf ∈ flags.powerset,
          if BoxMember flags free leaf then weight leaf else 0 := by
      apply Finset.sum_congr rfl
      intro leaf hl
      simp only [BoxMember, Finset.mem_powerset.mp hl, true_and]
    _ = _ := by
      apply Finset.sum_subset
      · intro leaf hl
        exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hl).trans hf)
      · intro leaf hl hnl
        have hn : ¬ BoxMember flags free leaf := by
          intro h
          exact hnl (Finset.mem_powerset.mpr h.1)
        simp only [hn, ite_false]



















































































































private theorem query_fiber_sum (q leaf : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) (hl : leaf ∈ q.powerset) :
    (∑ u ∈ q.powersetCard t, if QueryBox q u leaf then weight leaf else 0) =
      if (q \ leaf).card < t then 0 else weight leaf := by
  by_cases hs : (q \ leaf).card < t
  · simp only [hs, ite_true]
    apply Finset.sum_eq_zero
    intro u hu
    simp only [no_queryBox_of_few_missing q leaf u t hu hs, ite_false]
  · have ht : t ≤ (q \ leaf).card := by omega
    obtain ⟨u, hu, huniq⟩ := queryBox_partition q leaf t (Finset.mem_powerset.mp hl) ht
    rw [Finset.sum_eq_single u]
    · simp [hu.2, hs]
    · intro v hv hvn
      have hn : ¬ QueryBox q v leaf := by
        intro hb
        exact hvn (huniq v ⟨hv, hb⟩)
      simp only [hn, ite_false]
    · intro h
      exact False.elim (h hu.1)

/-- The full query partition as an exact signed-sum identity: explicit leaves
with fewer than `t` missing positions, plus one lookup per `t`-subset. -/
theorem sparse_query_identity_sourceProof (q : Finset α) (t : ℕ) (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ q.powerset with (q \ leaf).card < t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by
  have hboxes :
      (∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight) =
      ∑ leaf ∈ q.powerset, if (q \ leaf).card < t then 0 else weight leaf := by
    calc
      _ = ∑ u ∈ q.powersetCard t, ∑ leaf ∈ q.powerset,
            if QueryBox q u leaf then weight leaf else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact boxSum_extend q (q \ u) (queryFree q u) weight Finset.sdiff_subset
      _ = ∑ leaf ∈ q.powerset, ∑ u ∈ q.powersetCard t,
            if QueryBox q u leaf then weight leaf else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro leaf hl
        exact query_fiber_sum q leaf t weight hl
  rw [hboxes, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf hl
  by_cases h : (q \ leaf).card < t <;> simp [h]

/-! ## Number of query accesses -/
































































end ThreeSum.SparseBoxes

end

universe u_1

theorem solution : ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] (q : Finset.{u_1} α) (t : Nat) (weight : Finset.{u_1} α → Int),
  @Eq.{1} Int (∑ leaf ∈ @Finset.powerset.{u_1} α q, weight leaf)
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
      (∑ leaf ∈ @Finset.powerset.{u_1} α q with
        @LT.lt.{0} Nat instLTNat
          (@Finset.card.{u_1} α
            (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
              (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q leaf))
          t,
        weight leaf)
      (∑ u ∈ @Finset.powersetCard.{u_1} α t q,
        @ThreeSum.SparseBoxes.boxSum.{u_1} α inst
          (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
            (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q u)
          (@ThreeSum.SparseBoxes.queryFree.{u_1} α inst q u) weight)) := by
  exact @ThreeSum.SparseBoxes.sparse_query_identity_sourceProof

#print axioms solution
