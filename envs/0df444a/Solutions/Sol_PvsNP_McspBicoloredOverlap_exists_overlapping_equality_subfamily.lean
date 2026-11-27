-- Prove2me | solution 1 for PvsNP.McspBicoloredOverlap.exists_overlapping_equality_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T04:52:45.817691+00:00
-- url     : https://prove2.me/submissions/c15e0185-7693-49de-bef7-5717503c90c6

import Mathlib

set_option autoImplicit false

namespace PvsNP.McspBicoloredOverlap

open Finset

private def goodGraph {α : Type*} (accept : α → α → Prop) : SimpleGraph α where
  Adj a b := a ≠ b ∧ ¬ accept a b ∧ ¬ accept b a
  symm := ⟨fun _ _ ⟨hne, hab, hba⟩ => ⟨Ne.symm hne, hba, hab⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- From all accepted diagonals and at most B accepted ordered pairs, extract a set on which
acceptance is exactly equality. The denominator counts accepted ordered pairs in either orientation,
with their common diagonal counted only once. -/
theorem exists_equality_subfamily
    {α : Type*} [Fintype α] (accept : α → α → Prop) [DecidableRel accept]
    (B : ℕ) (hdiag : ∀ a, accept a a)
    (hcap : (univ.filter (fun ab : α × α => accept ab.1 ab.2)).card ≤ B) :
    ∃ s : Finset α,
      (∀ a ∈ s, ∀ b ∈ s, accept a b ↔ a = b) ∧
      (Fintype.card α)^2 + Fintype.card α * s.card ≤ (2 * B) * s.card := by
  classical
  let G := goodGraph accept
  let n := Fintype.card α
  let r := G.cliqueNum
  let other := (univ : Finset (α × α)).filter (fun ab => ¬ G.Adj ab.1 ab.2)
  let diag := (univ : Finset α).image (fun a => (a, a))
  let off := (univ : Finset (α × α)).filter (fun ab => ab.1 ≠ ab.2 ∧ accept ab.1 ab.2)
  have hf : G.CliqueFree (r + 1) := by
    intro t ht
    have h := ht.isClique.card_le_cliqueNum
    rw [ht.card_eq] at h
    exact Nat.not_succ_le_self _ h
  have hturan : 2 * r * G.edgeFinset.card ≤ (r - 1) * n ^ 2 := by
    apply le_trans (Nat.mul_le_mul_left (2 * r) hf.card_edgeFinset_le)
    rw [← SimpleGraph.card_edgeFinset_turanGraph]
    exact SimpleGraph.mul_card_edgeFinset_turanGraph_le
  have hdiag_card : diag.card = n := by
    exact card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hunion : diag ∪ off = univ.filter (fun ab : α × α => accept ab.1 ab.2) := by
    ext ⟨a, b⟩
    by_cases hab : a = b
    · subst b
      simp [diag, hdiag]
    · simp [diag, off, hab]
  have hdisjoint : Disjoint diag off := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ ha hb
    have hab : a = b := by simpa [diag] using ha
    exact (mem_filter.mp hb).2.1 hab
  have hoff : n + off.card ≤ B := by
    rw [← hdiag_card, ← card_union_of_disjoint hdisjoint, hunion]
    exact hcap
  have hother_subset : other ⊆ diag ∪ off ∪ off.image Prod.swap := by
    rintro ⟨a, b⟩ h
    have hbad := (mem_filter.mp h).2
    change ¬ (a ≠ b ∧ ¬ accept a b ∧ ¬ accept b a) at hbad
    by_cases hab : a = b
    · subst b
      simp [diag]
    · by_cases hp : accept a b
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hab, hp⟩))
      · have hq : accept b a := by
          by_contra hn
          exact hbad ⟨hab, hp, hn⟩
        exact mem_union_right _ (mem_image.mpr
          ⟨(b, a), mem_filter.mpr ⟨mem_univ _, Ne.symm hab, hq⟩, rfl⟩)
  have hother : other.card + n ≤ 2 * B := by
    have h1 := card_le_card hother_subset
    have h2 := card_union_le (diag ∪ off) (off.image Prod.swap)
    have h3 := card_union_le diag off
    have h4 : (off.image Prod.swap).card ≤ off.card := card_image_le
    omega
  have hsplit : 2 * G.edgeFinset.card + other.card = n ^ 2 := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (α × α)))
      (fun ab => G.Adj ab.1 ab.2)
    rw [← G.two_mul_card_edgeFinset] at h
    simpa [other, n, sq] using h
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  refine ⟨s, ?_, ?_⟩
  · intro a ha b hb
    constructor
    · intro hab
      by_contra hne
      have hgood := hs.isClique ha hb hne
      exact hgood.2.1 hab
    · rintro rfl
      exact hdiag a
  · change n ^ 2 + n * s.card ≤ (2 * B) * s.card
    rw [hs.card_eq]
    change n ^ 2 + n * r ≤ (2 * B) * r
    by_cases hr : r = 0
    · have hn : n = 0 := by
        by_contra hn
        obtain ⟨a⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
        have ha : G.IsClique ({a} : Finset α) := by simp
        have h := ha.card_le_cliqueNum
        simp only [card_singleton] at h
        change 1 ≤ r at h
        omega
      simp [hn, hr]
    · have hsucc : r - 1 + 1 = r := by omega
      have hbound : n ^ 2 ≤ r * other.card := by
        have heq := congrArg (fun x => r * x) hsplit
        have hsuccMul := congrArg (fun x => x * n ^ 2) hsucc
        simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at heq hsuccMul
        have hco : r * (2 * G.edgeFinset.card) = 2 * r * G.edgeFinset.card := by ring
        rw [hco] at heq
        omega
      have hg := Nat.mul_le_mul_right r hother
      rw [Nat.add_mul] at hg
      calc
        n ^ 2 + n * r ≤ r * other.card + n * r := Nat.add_le_add_right hbound _
        _ ≤ (2 * B) * r := by simpa only [Nat.mul_comm r other.card] using hg

/-- Put two independently chosen blocks on either side of a shared middle block. -/
def patched {α β : Type*} (left right : α → List β) (gap : List β) (a b : α) : List β :=
  left a ++ gap ++ right b

/-- Every cut inside the shared block realizes the same mixed input. -/
theorem splice_eq_patched {α β : Type*} (left right : α → List β) (gap : List β)
    (len : ℕ) (hleft : ∀ a, (left a).length = len) (a b : α) (cut : ℕ)
    (hlo : len ≤ cut) (hhi : cut ≤ len + gap.length) :
    (patched left right gap a a).take cut ++ (patched left right gap b b).drop cut =
      patched left right gap a b := by
  have htake : ∀ x : α, (patched left right gap x x).take cut =
      left x ++ gap.take (cut - len) := by
    intro x
    unfold patched
    rw [List.take_append_of_le_length (by simpa [hleft] using hhi),
      List.take_append, List.take_of_length_le (by rwa [hleft]), hleft]
  have hdrop : ∀ x : α, (patched left right gap x x).drop cut =
      gap.drop (cut - len) ++ right x := by
    intro x
    unfold patched
    rw [List.append_assoc, List.drop_append,
      List.drop_eq_nil_of_le (by rwa [hleft]), List.nil_append, hleft,
      List.drop_append, Nat.sub_eq_zero_of_le (by omega : cut - len ≤ gap.length),
      List.drop_zero]
  rw [htake, hdrop, patched]
  simp only [List.append_assoc, ← List.append_assoc (gap.take (cut - len)),
    List.take_append_drop]

/-- Accepted diagonal tables are reusable at every cut in the common middle block. The accepted
mixed tables may be covered by any decoder, including a bounded-size circuit decoder. -/
theorem exists_overlapping_equality_subfamily
    {α β σ : Type*} [Fintype α] [Fintype σ] (left right : α → List β)
    (gap : List β) (len : ℕ) (hleft : ∀ a, (left a).length = len)
    (hleft_inj : Function.Injective left) (hright_inj : Function.Injective right)
    (accept : List β → Prop) [DecidablePred accept] (decode : σ → List β)
    (hdiag : ∀ a, accept (left a ++ gap ++ right a))
    (hcover : ∀ a b, accept (left a ++ gap ++ right b) →
      ∃ code, decode code = left a ++ gap ++ right b) :
    ∃ s : Finset α,
      (Fintype.card α)^2 + Fintype.card α * s.card ≤ (2 * Fintype.card σ) * s.card ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ cut, len ≤ cut → cut ≤ len + gap.length →
        (accept ((left a ++ gap ++ right a).take cut ++
          (left b ++ gap ++ right b).drop cut) ↔ a = b) := by
  classical
  have hinj : Function.Injective (fun ab : α × α => patched left right gap ab.1 ab.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have first (x y : α) : (patched left right gap x y).take len = left x := by
      unfold patched
      rw [← hleft x, List.append_assoc, List.take_append_length]
    have last (x y : α) : (patched left right gap x y).drop (len + gap.length) =
        right y := by
      unfold patched
      rw [← hleft x, ← List.length_append, List.drop_append_length]
    have hac := congrArg (fun w : List β => w.take len) h
    have hbd := congrArg (fun w : List β => w.drop (len + gap.length)) h
    change (patched left right gap a b).take len =
      (patched left right gap c d).take len at hac
    change (patched left right gap a b).drop (len + gap.length) =
      (patched left right gap c d).drop (len + gap.length) at hbd
    rw [first, first] at hac
    rw [last, last] at hbd
    exact Prod.ext (hleft_inj hac) (hright_inj hbd)
  let A (a b : α) : Prop := accept (patched left right gap a b)
  let : DecidableRel A := fun a b => inferInstanceAs (Decidable (accept _))
  let s₀ := (univ : Finset (α × α)).filter (fun ab => A ab.1 ab.2)
  have hcap : s₀.card ≤ Fintype.card σ := by
    calc
      s₀.card = (s₀.image (fun ab => patched left right gap ab.1 ab.2)).card :=
        (card_image_of_injective _ hinj).symm
      _ ≤ ((univ : Finset σ).image decode).card := by
        apply card_le_card
        intro v hv
        obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.mp hv
        obtain ⟨code, hcode⟩ := hcover a b (mem_filter.mp hp).2
        exact mem_image.mpr ⟨code, mem_univ _, hcode⟩
      _ ≤ Fintype.card σ := by
        rw [← card_univ]
        exact card_image_le
  obtain ⟨s, h, hs⟩ := exists_equality_subfamily A _ hdiag hcap
  refine ⟨s, hs, ?_⟩
  intro a ha b hb cut hlo hhi
  change (accept ((patched left right gap a a).take cut ++
    (patched left right gap b b).drop cut) ↔ a = b)
  rw [splice_eq_patched left right gap len hleft a b cut hlo hhi]
  exact h a ha b hb

end PvsNP.McspBicoloredOverlap

#print axioms PvsNP.McspBicoloredOverlap.exists_overlapping_equality_subfamily


theorem solution
    {α β σ : Type*} [Fintype α] [Fintype σ] (left right : α → List β)
    (gap : List β) (len : ℕ) (hleft : ∀ a, (left a).length = len)
    (hleft_inj : Function.Injective left) (hright_inj : Function.Injective right)
    (accept : List β → Prop) [DecidablePred accept] (decode : σ → List β)
    (hdiag : ∀ a, accept (left a ++ gap ++ right a))
    (hcover : ∀ a b, accept (left a ++ gap ++ right b) →
      ∃ code, decode code = left a ++ gap ++ right b) :
    ∃ s : Finset α,
      (Fintype.card α)^2 + Fintype.card α * s.card ≤ (2 * Fintype.card σ) * s.card ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ cut, len ≤ cut → cut ≤ len + gap.length →
        (accept ((left a ++ gap ++ right a).take cut ++
          (left b ++ gap ++ right b).drop cut) ↔ a = b) := by
  exact PvsNP.McspBicoloredOverlap.exists_overlapping_equality_subfamily
    left right gap len hleft hleft_inj hright_inj accept decode hdiag hcover

#print axioms solution
