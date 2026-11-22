-- Prove2me | solution 1 for TenChallenges.challenge_10_fiveFibrePieces
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:26:30.019892+00:00
-- url     : https://prove2.me/submissions/7bc96411-0c02-45c0-855f-f7fbb086fbdd

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sum

set_option autoImplicit false

universe u v

namespace TenChallenges.Continuation.ProtectedPaths

def opponentsIn {V : Type*} (G : SimpleGraph V) (c : V → Bool) (D : Set V) (v : V) : Set V :=
  {w | w ∈ D ∧ G.Adj v w ∧ c w ≠ c v}

end TenChallenges.Continuation.ProtectedPaths

/-! # Counting protections supported on a finite separator -/


namespace TenChallenges.Continuation.SeparatorCapacity

variable {V I : Type*}

open Classical in
/-- The labels whose entire support remains in the boundary. -/
noncomputable def retained (labels : Finset I) (support : I → Finset V)
    (boundary : Finset V) : Finset I :=
  labels.filter fun i => support i ⊆ boundary

open Classical in
/-- Retained labels giving a distinct witness at the specified vertex. -/
noncomputable def incident (labels : Finset I) (support : I → Finset V)
    (boundary : Finset V) (v : V) : Finset I :=
  (retained labels support boundary).filter fun i => v ∈ support i

/-- If each nonempty subset has a vertex incident to at most its capacity of
retained labels, the total number of nonempty-supported labels is bounded
by the sum of capacities. Supports may have any size, and distinct labels
may have the same support. -/
theorem card_le_sum_capacity (boundary : Finset V) (labels : Finset I)
    (support : I → Finset V) (capacity : V → ℕ)
    (hlabels : ∀ i ∈ labels, (support i).Nonempty ∧ support i ⊆ boundary)
    (hsmall : ∀ U ⊆ boundary, U.Nonempty →
      ∃ v ∈ U, (incident labels support U v).card ≤ capacity v) :
    labels.card ≤ ∑ v ∈ boundary, capacity v := by
  classical
  have bound (U : Finset V) : U ⊆ boundary →
      (retained labels support U).card ≤ ∑ v ∈ U, capacity v := by
    induction U using Finset.strongInductionOn with | _ U ih => _
    intro hU
    by_cases hn : U.Nonempty
    · obtain ⟨v, hv, hcap⟩ := hsmall U hU hn
      let R := retained labels support U
      have hrem : R.filter (fun i => v ∉ support i) =
          retained labels support (U.erase v) := by
        ext i
        simp only [R, retained, Finset.mem_filter, Finset.subset_erase, and_assoc]
      have hpart := Finset.card_filter_add_card_filter_not (s := R) (fun i => v ∈ support i)
      change (incident labels support U v).card + _ = _ at hpart
      rw [hrem] at hpart
      have hprev := ih (U.erase v) (Finset.erase_ssubset hv)
        ((Finset.erase_subset v U).trans hU)
      rw [← Finset.sum_erase_add U capacity hv, ← hpart]
      exact (Nat.add_le_add hcap hprev).trans_eq (Nat.add_comm _ _)
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hn
      have hnone : retained labels support ∅ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hil, hsub⟩ := Finset.mem_filter.mp hi
        obtain ⟨v, hv⟩ := (hlabels i hil).1
        exact Finset.notMem_empty v (hsub hv)
      simp [hnone]
  have hfull : retained labels support boundary = labels :=
    Finset.filter_eq_self.mpr fun i hi => (hlabels i hi).2
  simpa only [hfull] using bound boundary (Finset.Subset.refl _)

/-- Excess labels force a nonempty sub-boundary where every vertex has
strictly more distinct witnesses than its capacity. -/
theorem exists_supported_of_sum_lt_card (boundary : Finset V) (labels : Finset I)
    (support : I → Finset V) (capacity : V → ℕ)
    (hlabels : ∀ i ∈ labels, (support i).Nonempty ∧ support i ⊆ boundary)
    (hexcess : (∑ v ∈ boundary, capacity v) < labels.card) :
    ∃ U ⊆ boundary, U.Nonempty ∧
      ∀ v ∈ U, capacity v < (incident labels support U v).card := by
  classical
  by_contra! hn
  exact (not_lt_of_ge (card_le_sum_capacity boundary labels support capacity hlabels hn)) hexcess

open ProtectedPaths (opponentsIn)

/-- Enough labels produce a protected extension. Each label supplies one
distinct opponent to each member of its support. It can also carry an
infinite piece already supported by that boundary and the prescribed set. -/
theorem exists_protected_extension (G : SimpleGraph V) (c : V → Bool)
    (S C : Set V) (q : V → ℕ) (F : Finset V) (labels : Finset I)
    (support : I → Finset V) (piece : I → Set V) (pick : V → I → V)
    (hF : (F : Set V) ⊆ C) (hC : ∀ i ∈ labels, piece i ⊆ C)
    (hsupport : ∀ i ∈ labels, (support i).Nonempty ∧ support i ⊆ F)
    (hpiece : ∀ i ∈ labels, ∀ x ∈ piece i,
      (q x : ℕ∞) ≤ (opponentsIn G c (S ∪ (support i : Set V) ∪ piece i) x).encard)
    (hpick : ∀ i ∈ labels, ∀ v ∈ support i,
      pick v i ∈ opponentsIn G c (S ∪ (support i : Set V) ∪ piece i) v)
    (hdistinct : ∀ v, Set.InjOn (pick v) {i | i ∈ labels ∧ v ∈ support i})
    (hexcess : (∑ v ∈ F, (q v - 1)) < labels.card) :
    ∃ D : Set V, D.Nonempty ∧ D ⊆ C ∧
      ∀ v ∈ D, (q v : ℕ∞) ≤ (opponentsIn G c (S ∪ D) v).encard := by
  classical
  obtain ⟨U, hUF, hUne, hcore⟩ :=
    exists_supported_of_sum_lt_card F labels support (fun v => q v - 1) hsupport hexcess
  let L := retained labels support U
  let D := (U : Set V) ∪ ⋃ i ∈ L, piece i
  have liveInfo {i : I} (hi : i ∈ L) : i ∈ labels ∧ support i ⊆ U := Finset.mem_filter.mp hi
  have inside {i : I} (hi : i ∈ L) : S ∪ (support i : Set V) ∪ piece i ⊆ S ∪ D := by
    intro x hx
    rcases hx with (hs | hb) | hp
    · exact Or.inl hs
    · exact Or.inr (Or.inl ((liveInfo hi).2 hb))
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hp⟩))
  obtain ⟨v₀, hv₀⟩ := hUne
  refine ⟨D, ⟨v₀, Or.inl hv₀⟩, ?_, ?_⟩
  · intro v hv
    rcases hv with hu | hp
    · exact hF (hUF hu)
    · obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.mp hp
      exact hC i (liveInfo hi).1 hvi
  · intro v hv
    rcases hv with hu | hp
    · let A := incident labels support U v
      have info {i : I} (hi : i ∈ A) : i ∈ L ∧ v ∈ support i := Finset.mem_filter.mp hi
      have hm : Set.MapsTo (pick v) (A : Set I) (opponentsIn G c (S ∪ D) v) := by
        intro i hi
        obtain ⟨hl, hvs⟩ := info hi
        have hw := hpick i (liveInfo hl).1 v hvs
        exact ⟨inside hl hw.1, hw.2⟩
      have hj : Set.InjOn (pick v) (A : Set I) := by
        intro i hi j hj heq
        exact hdistinct v (show i ∈ labels ∧ v ∈ support i from
          ⟨(liveInfo (info hi).1).1, (info hi).2⟩)
          (show j ∈ labels ∧ v ∈ support j from ⟨(liveInfo (info hj).1).1, (info hj).2⟩) heq
      have hq : q v ≤ A.card := by
        have h := hcore v hu
        change q v - 1 < A.card at h
        omega
      exact (ENat.natCast_le_natCast.mpr hq).trans (by
        simpa only [Set.encard_coe_eq_coe_finsetCard] using Set.encard_le_encard_of_injOn hm hj)
    · obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.mp hp
      exact (hpiece i (liveInfo hi).1 v hvi).trans (Set.encard_le_encard
        (fun _ hw => ⟨inside hi hw.1, hw.2⟩))

end TenChallenges.Continuation.SeparatorCapacity

/-! # Crossing edges and disjoint pieces at a finite separator -/


namespace TenChallenges.Continuation.SeparatorCapacity

open ProtectedPaths (opponentsIn)

variable {V I : Type*}

/-- Each oriented crossing edge counts once, and each independently supported
piece counts once. The counted edges run from colour false to colour true. -/
theorem exists_extension_of_edges_and_pieces (G : SimpleGraph V) (c : V → Bool)
    (S C : Set V) (q : V → ℕ) (F : Finset V) (E : Finset (V × V)) (L : Finset I)
    (P : I → Set V) (hF : (F : Set V) ⊆ C)
    (hedges : ∀ e ∈ E, e.1 ∈ F ∧ e.2 ∈ F ∧ G.Adj e.1 e.2 ∧ c e.1 = false ∧ c e.2 = true)
    (hP : ∀ i ∈ L, (P i).Nonempty ∧ P i ⊆ C ∧ Disjoint (P i) (F : Set V))
    (hdis : (L : Set I).PairwiseDisjoint P)
    (hquota : ∀ i ∈ L, ∀ x ∈ P i, (q x : ℕ∞) ≤
      (opponentsIn G c (S ∪ (F : Set V) ∪ P i) x).encard)
    (hexcess : (∑ v ∈ F, (q v - 1)) < E.card + L.card) :
    ∃ D : Set V, D.Nonempty ∧ D ⊆ C ∧
      ∀ x ∈ D, (q x : ℕ∞) ≤ (opponentsIn G c (S ∪ D) x).encard := by
  classical
  let deps (i : I) := F.filter fun v => (opponentsIn G c (P i) v).Nonempty
  have trimmed {i : I} (hi : i ∈ L) {x : V} (hx : x ∈ P i) :
      (q x : ℕ∞) ≤ (opponentsIn G c (S ∪ (deps i : Set V) ∪ P i) x).encard := by
    refine (hquota i hi x hx).trans (Set.encard_le_encard ?_)
    intro w hw
    refine ⟨?_, hw.2⟩
    rcases hw.1 with (hs | hf) | hp
    · exact Or.inl (Or.inl hs)
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hf, ⟨x, hx, hw.2.1.symm, hw.2.2.symm⟩⟩))
    · exact Or.inr hp
  by_cases hn : ∀ i ∈ L, (deps i).Nonempty
  case neg =>
    push Not at hn
    obtain ⟨i, hi, hempty⟩ := hn
    refine ⟨P i, (hP i hi).1, (hP i hi).2.1, fun x hx => ?_⟩
    simpa [hempty] using trimmed hi hx
  let supp : (V × V) ⊕ I → Finset V := Sum.elim (fun e => {e.1, e.2}) deps
  let piece : (V × V) ⊕ I → Set V := Sum.elim (fun _ => ∅) P
  let fromPiece (v : V) (i : I) := if h : (opponentsIn G c (P i) v).Nonempty then h.choose else v
  have hpick {i : I} {v : V} (hv : v ∈ deps i) : fromPiece v i ∈ opponentsIn G c (P i) v := by
    have h : (opponentsIn G c (P i) v).Nonempty := (Finset.mem_filter.mp hv).2
    simpa only [fromPiece, dif_pos h] using h.choose_spec
  let other (v : V) (e : V × V) := if c v then e.1 else e.2
  let pick (v : V) : (V × V) ⊕ I → V := Sum.elim (other v) (fromPiece v)
  have edgeInfo {v : V} {e : V × V} (he : e ∈ E) (hv : v ∈ supp (.inl e)) :
      (if c v then (other v e, v) else (v, other v e)) = e ∧
      other v e ∈ F ∧ G.Adj v (other v e) ∧ c (other v e) ≠ c v := by
    obtain ⟨h₁, h₂, ha, h₀, ht⟩ := hedges e he
    change v ∈ ({e.1, e.2} : Finset V) at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simpa [h₀, ht, other] using (show e.2 ∈ F ∧ G.Adj e.1 e.2 from ⟨h₂, ha⟩)
    · obtain rfl := Finset.mem_singleton.mp hv
      simpa [h₀, ht, other] using (show e.1 ∈ F ∧ G.Adj e.2 e.1 from ⟨h₁, ha.symm⟩)
  apply exists_protected_extension G c S C q F (E.disjSum L) supp piece pick hF
  · rintro (e | i) hi
    · exact Set.empty_subset _
    · exact (hP i (Finset.inr_mem_disjSum.mp hi)).2.1
  · rintro (e | i) hi
    · obtain ⟨h₁, h₂, _⟩ := hedges e (Finset.inl_mem_disjSum.mp hi)
      exact ⟨⟨e.1, Finset.mem_insert_self ..⟩, Finset.insert_subset h₁ (Finset.singleton_subset_iff.mpr h₂)⟩
    · exact ⟨hn i (Finset.inr_mem_disjSum.mp hi), Finset.filter_subset ..⟩
  · rintro (e | i) hi x hx
    · exact False.elim hx
    · exact trimmed (Finset.inr_mem_disjSum.mp hi) hx
  · rintro (e | i) hi v hv
    · have hh := edgeInfo (Finset.inl_mem_disjSum.mp hi) hv
      have hmem : other v e ∈ ({e.1, e.2} : Finset V) := by
        cases hc : c v <;> simp [other, hc]
      exact ⟨Or.inl (Or.inr hmem), hh.2.2⟩
    · have hh := hpick hv
      exact ⟨Or.inr hh.1, hh.2⟩
  · rintro v (e | i) hi (e' | j) hj heq
    · have h₁ := (edgeInfo (Finset.inl_mem_disjSum.mp hi.1) hi.2).1
      have h₂ := (edgeInfo (Finset.inl_mem_disjSum.mp hj.1) hj.2).1
      change other v e = other v e' at heq
      rw [heq, h₂] at h₁
      exact congrArg Sum.inl h₁.symm
    · change other v e = fromPiece v j at heq
      have hf := (edgeInfo (Finset.inl_mem_disjSum.mp hi.1) hi.2).2.1
      exact False.elim (Set.disjoint_left.mp (hP j (Finset.inr_mem_disjSum.mp hj.1)).2.2
        (hpick hj.2).1 (heq ▸ hf))
    · change fromPiece v i = other v e' at heq
      have hf := (edgeInfo (Finset.inl_mem_disjSum.mp hj.1) hj.2).2.1
      exact False.elim (Set.disjoint_left.mp (hP i (Finset.inr_mem_disjSum.mp hi.1)).2.2
        (hpick hi.2).1 (heq.symm ▸ hf))
    · change fromPiece v i = fromPiece v j at heq
      apply congrArg Sum.inr
      by_contra hne
      exact Set.disjoint_left.mp (hdis (Finset.inr_mem_disjSum.mp hi.1)
        (Finset.inr_mem_disjSum.mp hj.1) hne) (hpick hi.2).1 (heq.symm ▸ (hpick hj.2).1)
  · simpa only [Finset.card_disjSum] using hexcess

end TenChallenges.Continuation.SeparatorCapacity

/-! # Disjoint supported pieces beyond a set of common neighbours -/


namespace TenChallenges.Continuation.SeparatorCapacity

open ProtectedPaths (opponentsIn)

variable {V I : Type*}

/-- The common sites may be infinite. Each has quota at most one more than
the number of anchors. More disjoint individually supported pieces than the
total anchor capacity yield a protected extension with the chosen colours. -/
theorem exists_extension_beyond_common_sites (G : SimpleGraph V) (c : V → Bool)
    (S C Y : Set V) (q : V → ℕ) (B : Finset V) (L : Finset I) (P : I → Set V)
    (hB : (B : Set V) ⊆ C) (hY : Y ⊆ C)
    (hzero : ∀ b ∈ B, c b = false) (hone : ∀ y ∈ Y, c y = true)
    (hAdj : ∀ b ∈ B, ∀ y ∈ Y, G.Adj b y)
    (hYq : ∀ y ∈ Y, q y ≤ B.card + 1)
    (hP : ∀ i ∈ L, (P i).Nonempty ∧ P i ⊆ C ∧ Disjoint (P i) ((B : Set V) ∪ Y))
    (hdis : (L : Set I).PairwiseDisjoint P)
    (hquota : ∀ i ∈ L, ∀ x ∈ P i, (q x : ℕ∞) ≤
      (opponentsIn G c (S ∪ ((B : Set V) ∪ Y) ∪ P i) x).encard)
    (hcount : (∑ b ∈ B, (q b - 1)) < L.card) :
    ∃ D : Set V, D.Nonempty ∧ D ⊆ C ∧
      ∀ x ∈ D, (q x : ℕ∞) ≤ (opponentsIn G c (S ∪ D) x).encard := by
  classical
  let active : Set V := {y | y ∈ Y ∧ ∃ i ∈ L, (opponentsIn G c (P i) y).Nonempty}
  have trimmed {i : I} (hi : i ∈ L) {x : V} (hx : x ∈ P i) :
      (q x : ℕ∞) ≤ (opponentsIn G c (S ∪ ((B : Set V) ∪ active) ∪ P i) x).encard := by
    refine (hquota i hi x hx).trans (Set.encard_le_encard ?_)
    intro y hy
    refine ⟨?_, hy.2⟩
    rcases hy.1 with (hs | (hb | hsite)) | hp
    · exact Or.inl (Or.inl hs)
    · exact Or.inl (Or.inr (Or.inl hb))
    · exact Or.inl (Or.inr (Or.inr ⟨hsite, i, hi, x, hx, hy.2.1.symm, hy.2.2.symm⟩))
    · exact Or.inr hp
  by_cases hfin : active.Finite
  · let A := hfin.toFinset
    have hA {v : V} : v ∈ A ↔ v ∈ active := hfin.mem_toFinset
    have hBA : Disjoint B A := Finset.disjoint_left.mpr fun v hv ha =>
      Bool.noConfusion ((hzero v hv).symm.trans (hone v (hA.mp ha).1))
    apply exists_extension_of_edges_and_pieces G c S C q (B ∪ A) (B ×ˢ A) L P
    · intro v hv
      exact (Finset.mem_union.mp hv).elim (fun hb => hB hb) (fun ha => hY (hA.mp ha).1)
    · intro e he
      obtain ⟨hb, ha⟩ := Finset.mem_product.mp he
      have hy := (hA.mp ha).1
      exact ⟨Finset.mem_union_left _ hb, Finset.mem_union_right _ ha,
        hAdj _ hb _ hy, hzero _ hb, hone _ hy⟩
    · intro i hi
      refine ⟨(hP i hi).1, (hP i hi).2.1, (hP i hi).2.2.mono_right ?_⟩
      intro v hv
      exact (Finset.mem_union.mp hv).elim Or.inl (fun ha => Or.inr (hA.mp ha).1)
    · exact hdis
    · intro i hi x hx
      simpa only [Finset.coe_union, A, hfin.coe_toFinset] using trimmed hi hx
    · have hsum : (∑ y ∈ A, (q y - 1)) ≤ A.card * B.card := by
        calc
          _ ≤ ∑ _y ∈ A, B.card := Finset.sum_le_sum fun y hy =>
            Nat.sub_le_of_le_add (hYq y (hA.mp hy).1)
          _ = _ := by simp
      rw [Finset.sum_union hBA, Finset.card_product, Nat.mul_comm B.card A.card]
      omega
  · let D : Set V := ((B : Set V) ∪ active) ∪ ⋃ i ∈ L, P i
    have hDC : D ⊆ C := by
      rintro x ((hb | hy) | hp)
      · exact hB hb
      · exact hY hy.1
      · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hp
        exact (hP i hi).2.1 hxi
    have hactive : active.Infinite := hfin
    obtain ⟨y₀, hy₀⟩ := hactive.nonempty
    refine ⟨D, ⟨y₀, Or.inl (Or.inr hy₀)⟩, hDC, ?_⟩
    rintro v ((hb | hy) | hp)
    · have hinf : (opponentsIn G c (S ∪ D) v).Infinite := hactive.mono fun y hs =>
        ⟨Or.inr (Or.inl (Or.inr hs)), hAdj v hb y hs.1, by rw [hone y hs.1, hzero v hb]; decide⟩
      rw [Set.encard_eq_top_iff.mpr hinf]
      exact le_top
    · obtain ⟨hyY, i, hi, x, hx⟩ := hy
      have hxB : x ∉ B := fun hb => Set.disjoint_left.mp (hP i hi).2.2 hx.1 (Or.inl hb)
      have hsub : ((insert x B : Finset V) : Set V) ⊆ opponentsIn G c (S ∪ D) v := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hbw
        · exact ⟨Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hx.1⟩)), hx.2⟩
        · exact ⟨Or.inr (Or.inl (Or.inl hbw)), (hAdj w hbw v hyY).symm,
            by rw [hzero w hbw, hone v hyY]; decide⟩
      exact (ENat.natCast_le_natCast.mpr (hYq v hyY)).trans (by
        simpa only [Set.encard_coe_eq_coe_finsetCard, Finset.card_insert_of_notMem hxB] using
          Set.encard_le_encard hsub)
    · obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.mp hp
      refine (trimmed hi hvi).trans (Set.encard_le_encard ?_)
      intro w hw
      refine ⟨?_, hw.2⟩
      rcases hw.1 with (hs | hb) | hpi
      · exact Or.inl hs
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hpi⟩))

/-- At quota three, five disjoint pieces suffice for a pair of anchors.
The common-neighbour set and the individual pieces can all be infinite. -/
theorem exists_extension_of_five_pieces_at_pair (G : SimpleGraph V) (c : V → Bool)
    (S C Y : Set V) (q : V → ℕ) (a b : V) (hab : a ≠ b)
    (L : Finset I) (P : I → Set V) (ha : a ∈ C) (hb : b ∈ C) (hY : Y ⊆ C)
    (hca : c a = false) (hcb : c b = false) (hone : ∀ y ∈ Y, c y = true)
    (hAdj : ∀ y ∈ Y, G.Adj a y ∧ G.Adj b y)
    (hqa : q a ≤ 3) (hqb : q b ≤ 3) (hYq : ∀ y ∈ Y, q y ≤ 3)
    (hP : ∀ i ∈ L, (P i).Nonempty ∧ P i ⊆ C ∧ Disjoint (P i) ({a, b} ∪ Y))
    (hdis : (L : Set I).PairwiseDisjoint P)
    (hquota : ∀ i ∈ L, ∀ x ∈ P i, (q x : ℕ∞) ≤
      (opponentsIn G c (S ∪ ({a, b} ∪ Y) ∪ P i) x).encard)
    (hcount : 5 ≤ L.card) :
    ∃ D : Set V, D.Nonempty ∧ D ⊆ C ∧
      ∀ x ∈ D, (q x : ℕ∞) ≤ (opponentsIn G c (S ∪ D) x).encard := by
  classical
  let B : Finset V := {a, b}
  have hB : (B : Set V) = {a, b} := by simp [B]
  have hCard : B.card = 2 := by simp [B, hab]
  apply exists_extension_beyond_common_sites G c S C Y q B L P
  · rw [hB]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | h
    · exact ha
    · exact (Set.mem_singleton_iff.mp h).symm ▸ hb
  · exact hY
  · intro x hx
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain rfl | rfl := hx <;> assumption
  · exact hone
  · intro h hh y hy
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hh
    obtain rfl | rfl := hh
    · exact (hAdj y hy).1
    · exact (hAdj y hy).2
  · simpa only [hCard] using hYq
  · simpa only [hB] using hP
  · exact hdis
  · simpa only [hB] using hquota
  · simp [B, hab]
    omega

end TenChallenges.Continuation.SeparatorCapacity

theorem solution {V : Type u} {I : Type v} (G : SimpleGraph V) (c : V → Bool)
    (S C Y : Set V) (q : V → ℕ) (a b : V) (hab : a ≠ b)
    (L : Finset I) (P : I → Set V) (ha : a ∈ C) (hb : b ∈ C) (hY : Y ⊆ C)
    (hca : c a = false) (hcb : c b = false) (hone : ∀ y ∈ Y, c y = true)
    (hAdj : ∀ y ∈ Y, G.Adj a y ∧ G.Adj b y)
    (hqa : q a ≤ 3) (hqb : q b ≤ 3) (hYq : ∀ y ∈ Y, q y ≤ 3)
    (hP : ∀ i ∈ L, (P i).Nonempty ∧ P i ⊆ C ∧ Disjoint (P i) ({a, b} ∪ Y))
    (hdis : (L : Set I).PairwiseDisjoint P)
    (hquota : ∀ i ∈ L, ∀ x ∈ P i, (q x : ℕ∞) ≤
      {w | w ∈ S ∪ ({a, b} ∪ Y) ∪ P i ∧ G.Adj x w ∧ c w ≠ c x}.encard)
    (hcount : 5 ≤ L.card) :
    ∃ D : Set V, D.Nonempty ∧ D ⊆ C ∧
      ∀ x ∈ D, (q x : ℕ∞) ≤ {w | w ∈ S ∪ D ∧ G.Adj x w ∧ c w ≠ c x}.encard :=
  TenChallenges.Continuation.SeparatorCapacity.exists_extension_of_five_pieces_at_pair G c S C Y q a b hab L P ha hb hY hca hcb hone hAdj hqa hqb hYq hP hdis hquota hcount

#print axioms solution
