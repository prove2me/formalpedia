-- Prove2me | solution 1 for PosetMarginals.Chains.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:47:46.306032+00:00
-- url     : https://prove2.me/submissions/e39c5ad2-f709-4098-9987-76bfe5ca2189

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical PosetMarginals.Chains

namespace PMC

section Splice

variable {α : Type*} [PartialOrder α] [Fintype α]

lemma mem_maxChains {C : Finset α} : C ∈ maxChains α ↔ IsMaxChain (· ≤ ·) (C : Set α) := by
  simp [maxChains]

lemma chain_total {C : Finset α} (hC : C ∈ maxChains α) {a b : α} (ha : a ∈ C) (hb : b ∈ C) :
    a ≤ b ∨ b ≤ a := by
  rcases eq_or_ne a b with rfl | hab
  · exact Or.inl le_rfl
  · exact (mem_maxChains.1 hC).1 ha hb hab

lemma mem_of_comparable {C : Finset α} (hC : C ∈ maxChains α) {z : α}
    (hz : ∀ b ∈ C, z ≤ b ∨ b ≤ z) : z ∈ C := by
  have h := mem_maxChains.1 hC
  by_contra hzC
  have hch : IsChain (· ≤ ·) (insert z (C : Set α)) :=
    h.1.insert (fun b hb _ => hz b hb)
  have := h.2 hch (Set.subset_insert _ _)
  have hzin : z ∈ insert z (C : Set α) := Set.mem_insert _ _
  rw [← this] at hzin
  exact hzC hzin

lemma mem_splice {C1 C2 : Finset α} {x z : α} :
    z ∈ splice C1 C2 x ↔ (z ∈ C1 ∧ z ≤ x) ∨ (z ∈ C2 ∧ x ≤ z) := by
  simp [splice]

lemma splice_mem {C1 C2 : Finset α} (h1 : C1 ∈ maxChains α) (h2 : C2 ∈ maxChains α) {x : α}
    (hx1 : x ∈ C1) (hx2 : x ∈ C2) : splice C1 C2 x ∈ maxChains α := by
  rw [mem_maxChains]
  constructor
  · intro a ha b hb _
    simp only [Finset.mem_coe, mem_splice] at ha hb
    rcases ha with ⟨ha1, hax⟩ | ⟨ha2, hxa⟩ <;> rcases hb with ⟨hb1, hbx⟩ | ⟨hb2, hxb⟩
    · exact chain_total h1 ha1 hb1
    · exact Or.inl (hax.trans hxb)
    · exact Or.inr (hbx.trans hxa)
    · exact chain_total h2 ha2 hb2
  · intro t ht hst
    apply Set.Subset.antisymm hst
    intro z hz
    have hcomp : ∀ b ∈ splice C1 C2 x, z ≤ b ∨ b ≤ z := by
      intro b hb
      rcases eq_or_ne z b with rfl | hne
      · exact Or.inl le_rfl
      · exact ht hz (hst (Finset.mem_coe.2 hb)) hne
    have hxs : x ∈ splice C1 C2 x := mem_splice.2 (Or.inl ⟨hx1, le_rfl⟩)
    rcases hcomp x hxs with hzx | hxz
    · have : z ∈ C1 := by
        apply mem_of_comparable h1
        intro b hb
        rcases chain_total h1 hb hx1 with hbx | hxb
        · exact hcomp b (mem_splice.2 (Or.inl ⟨hb, hbx⟩))
        · exact Or.inl (hzx.trans hxb)
      exact Finset.mem_coe.2 (mem_splice.2 (Or.inl ⟨this, hzx⟩))
    · have : z ∈ C2 := by
        apply mem_of_comparable h2
        intro b hb
        rcases chain_total h2 hb hx2 with hbx | hxb
        · exact Or.inr (hbx.trans hxz)
        · exact hcomp b (mem_splice.2 (Or.inr ⟨hb, hxb⟩))
      exact Finset.mem_coe.2 (mem_splice.2 (Or.inr ⟨this, hxz⟩))

lemma sum_lower_upper (f : α → ℝ) (A B : Finset α) (x : α) (hxA : x ∈ A) (hxB : x ∈ B)
    (hA : ∀ z ∈ A, z ≤ x) (hB : ∀ z ∈ B, x ≤ z) :
    ∑ z ∈ A ∪ B, f z = ∑ z ∈ A, f z + ∑ z ∈ B, f z - f x := by
  have hi : A ∩ B = {x} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm (hA z h1) (hB z h2)
    · rintro rfl; exact ⟨hxA, hxB⟩
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  rw [hi, Finset.sum_singleton] at this
  linarith

lemma sum_chain_split (f : α → ℝ) {C : Finset α} (hC : C ∈ maxChains α) {x : α} (hx : x ∈ C) :
    ∑ z ∈ C, f z = ∑ z ∈ C.filter (· ≤ x), f z + ∑ z ∈ C.filter (x ≤ ·), f z - f x := by
  rw [← sum_lower_upper f _ _ x (by simp [hx]) (by simp [hx]) (by simp) (by simp)]
  congr 1
  ext z
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hz
    rcases chain_total hC hz hx with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz

lemma sum_splice_one (f : α → ℝ) (C1 C2 : Finset α) {x : α} (hx1 : x ∈ C1) (hx2 : x ∈ C2) :
    ∑ z ∈ splice C1 C2 x, f z =
      ∑ z ∈ C1.filter (· ≤ x), f z + ∑ z ∈ C2.filter (x ≤ ·), f z - f x := by
  unfold splice
  exact sum_lower_upper f _ _ x (by simp [hx1]) (by simp [hx2]) (by simp) (by simp)

lemma sum_splice (f : α → ℝ) {C1 C2 : Finset α} (h1 : C1 ∈ maxChains α)
    (h2 : C2 ∈ maxChains α) {x : α} (hx1 : x ∈ C1) (hx2 : x ∈ C2) :
    ∑ z ∈ splice C1 C2 x, f z + ∑ z ∈ splice C2 C1 x, f z =
      ∑ z ∈ C1, f z + ∑ z ∈ C2, f z := by
  rw [sum_splice_one f C1 C2 hx1 hx2, sum_splice_one f C2 C1 hx2 hx1,
    sum_chain_split f h1 hx1, sum_chain_split f h2 hx2]
  ring

lemma relGen_lt {C' : Finset (Finset α)} {x y : α} (h : relGen C' x y) (hne : x ≠ y) :
    x < y := by
  rcases h with h | ⟨C, _, _, _, hlt⟩
  · exact absurd h hne
  · exact hlt

/-- Lemma 2, first half: the generated relation is a partial order. -/
lemma isPosetOn_of {X' : Finset α} {C' : Finset (Finset α)} (hC' : C' ⊆ maxChains α)
    (h : PreservesDecomp X' C') : IsPosetOn X' C' := by
  refine ⟨fun x _ => Or.inl rfl, fun x _ y _ hxy hyx => ?_, fun x hx y hy z hz hxy hyz => ?_⟩
  · by_contra hne
    exact lt_asymm (relGen_lt hxy hne) (relGen_lt hyx (Ne.symm hne))
  · rcases hxy with rfl | ⟨C1, hC1, hx1, hy1, hlt1⟩
    · exact hyz
    rcases hyz with rfl | ⟨C2, hC2, hy2, hz2, hlt2⟩
    · exact Or.inr ⟨C1, hC1, hx1, hy1, hlt1⟩
    have hy : y ∈ C1 ∩ C2 ∩ X' := by simp [hy1, hy2, hy]
    refine Or.inr ⟨splice C1 C2 y, (h C1 hC1 C2 hC2 y hy).1, ?_, ?_, hlt1.trans hlt2⟩
    · exact mem_splice.2 (Or.inl ⟨hx1, hlt1.le⟩)
    · exact mem_splice.2 (Or.inr ⟨hz2, hlt2.le⟩)

lemma exists_min_of_chain {C : Finset α} (hC : C ∈ maxChains α) (X : Finset α)
    (hne : (C ∩ X).Nonempty) : ∃ m ∈ C ∩ X, ∀ y ∈ C ∩ X, m ≤ y := by
  obtain ⟨m, hm⟩ := Finset.exists_minimal hne
  refine ⟨m, hm.1, fun y hy => ?_⟩
  rcases chain_total hC (Finset.mem_inter.1 hm.1).1 (Finset.mem_inter.1 hy).1 with h | h
  · exact h
  · exact hm.2 hy h

end Splice

section L2

variable {α : Type*} [PartialOrder α] [Fintype α]

lemma relGen_pair {C' : Finset (Finset α)} {a b : α} (h : relGen C' a b ∨ relGen C' b a)
    (hne : a ≠ b) : ∃ E ∈ C', a ∈ E ∧ b ∈ E ∧ (a < b ∨ b < a) := by
  rcases h with (h | ⟨E, hE, ha, hb, hlt⟩) | (h | ⟨E, hE, hb, ha, hlt⟩)
  · exact absurd h hne
  · exact ⟨E, hE, ha, hb, Or.inl hlt⟩
  · exact absurd h.symm hne
  · exact ⟨E, hE, ha, hb, Or.inr hlt⟩

lemma glue {X' : Finset α} {C' : Finset (Finset α)} (hC' : C' ⊆ maxChains α)
    (h : PreservesDecomp X' C') :
    ∀ n, ∀ T : Finset α, T.card = n → T ⊆ X' → IsChain (relGen C') (T : Set α) →
      2 ≤ T.card → ∃ D ∈ C', T ⊆ D := by
  intro n
  induction n with
  | zero => intro T hT _ _ h2; omega
  | succ n ih =>
    intro T hT hTX hch h2
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨a, ha⟩ := Finset.exists_maximal hTne
    have haT := ha.1
    -- every other element of T lies below a, on a common chain
    have below : ∀ t ∈ T, t ≠ a → ∃ E ∈ C', t ∈ E ∧ a ∈ E ∧ t < a := by
      intro t ht hta
      obtain ⟨E, hE, htE, haE, hlt⟩ := relGen_pair (hch ht haT hta) hta
      rcases hlt with hlt | hlt
      · exact ⟨E, hE, htE, haE, hlt⟩
      · exact absurd (ha.2 ht hlt.le) (not_le_of_gt hlt)
    set T' := T.erase a with hT'
    have hcard' : T'.card = n := by rw [Finset.card_erase_of_mem haT]; omega
    by_cases h1 : T'.card = 1
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
      have hbT : b ∈ T' := by rw [hb]; simp
      have hbT' := Finset.mem_erase.1 hbT
      obtain ⟨E, hE, hbE, haE, _⟩ := below b hbT'.2 hbT'.1
      refine ⟨E, hE, fun t ht => ?_⟩
      by_cases hta : t = a
      · rw [hta]; exact haE
      · have : t ∈ T' := Finset.mem_erase.2 ⟨hta, ht⟩
        rw [hb, Finset.mem_singleton] at this
        rw [this]; exact hbE
    · have h2' : 2 ≤ T'.card := by
        have : 1 ≤ T'.card := by omega
        omega
      obtain ⟨D', hD', hT'D'⟩ := ih T' hcard' ((Finset.erase_subset a T).trans hTX)
        (hch.mono (by simp [hT'])) h2'
      have hT'ne : T'.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨b, hb⟩ := Finset.exists_maximal hT'ne
      have hbT' := Finset.mem_erase.1 hb.1
      have hle : ∀ t ∈ T', t ≤ b := by
        intro t ht
        rcases eq_or_ne t b with rfl | htb
        · exact le_rfl
        have ht' := Finset.mem_erase.1 ht
        obtain ⟨E, _, _, _, hlt⟩ := relGen_pair (hch ht'.2 hbT'.2 htb) htb
        rcases hlt with hlt | hlt
        · exact hlt.le
        · exact absurd (hb.2 ht hlt.le) (not_le_of_gt hlt)
      obtain ⟨E, hE, hbE, haE, hba⟩ := below b hbT'.2 hbT'.1
      have hbX : b ∈ X' := hTX hbT'.2
      have hsp := (h D' hD' E hE b (by simp [hT'D' hb.1, hbE, hbX])).1
      refine ⟨splice D' E b, hsp, fun t ht => ?_⟩
      by_cases hta : t = a
      · rw [hta]; exact mem_splice.2 (Or.inr ⟨haE, hba.le⟩)
      · have htT' : t ∈ T' := Finset.mem_erase.2 ⟨hta, ht⟩
        exact mem_splice.2 (Or.inl ⟨hT'D' htT', hle t htT'⟩)

end L2

end PMC

open PMC in
theorem solution {α : Type*} [PartialOrder α] [Fintype α]
    (X' : Finset α) (C' : Finset (Finset α))
    (hC' : C' ⊆ maxChains α) (h : PreservesDecomp X' C') :
    IsPosetOn X' C' ∧
      ∀ C : Finset α, IsMaxChainOf X' C' C → 2 ≤ C.card →
        ∃ D ∈ C', C = D ∩ X' := by
  refine ⟨isPosetOn_of hC' h, fun C hC h2 => ?_⟩
  obtain ⟨hCX, hch, hmax⟩ := hC
  obtain ⟨D, hD, hCD⟩ := glue hC' h _ C rfl hCX hch h2
  refine ⟨D, hD, (hmax (D ∩ X') Finset.inter_subset_right ?_ ?_).symm⟩
  · intro a ha b hb hne
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at ha hb
    rcases chain_total (hC' hD) ha.1 hb.1 with hab | hba
    · exact Or.inl (Or.inr ⟨D, hD, ha.1, hb.1, lt_of_le_of_ne hab hne⟩)
    · exact Or.inr (Or.inr ⟨D, hD, hb.1, ha.1, lt_of_le_of_ne hba (Ne.symm hne)⟩)
  · intro x hx
    exact Finset.mem_inter.2 ⟨hCD hx, hCX hx⟩
