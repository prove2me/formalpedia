-- Prove2me | solution 1 for RoundRobinEq.SubmodularEF1.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T03:39:16.202846+00:00
-- url     : https://prove2.me/submissions/8275dda6-629e-4300-a59a-108dbebe3276

/- Allocation discrepancy under one changed ranking. Original result:
Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser, Round-Robin Beyond
Additive Agents, arXiv:2301.13652v1, Lemma 4.6, printed p.19.
mikedeng1 supplied the formal model; statement approval is not proof review.
Alexander Richard Towell directed the campaign. OpenAI Codex constructed and
checked this proof with Lean/Mathlib. No earlier platform proof is reused;
no mathematical novelty or independent human review is claimed. -/
import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)

namespace AllocationDiscrepancy

variable {M : Type} [Fintype M] [DecidableEq M]

def advance (l : List M) (A : Finset M) : Finset M :=
  match l.find? (fun x => decide (x ∉ A)) with
  | none => A
  | some x => insert x A

lemma subset_advance (l : List M) (A : Finset M) : A ⊆ advance l A := by
  unfold advance
  split <;> simp

lemma advance_cases (l : List M) (A : Finset M) :
    advance l A = A ∨ ∃ x, advance l A = insert x A := by
  unfold advance
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

lemma insert_exchange (A B : Finset M) (a b : M) (ha : a ∈ B \ A) :
    (insert b B \ insert a A).card ≤ (B \ A).card := by
  have hsub : insert b B \ insert a A ⊆ insert b ((B \ A).erase a) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase] at hx ⊢
    aesop
  calc
    (insert b B \ insert a A).card ≤ (insert b ((B \ A).erase a)).card :=
      Finset.card_le_card hsub
    _ ≤ ((B \ A).erase a).card + 1 := Finset.card_insert_le _ _
    _ = (B \ A).card := Finset.card_erase_add_one ha

lemma same_ranking (l : List M) (A B : Finset M) :
    (advance l B \ advance l A).card ≤ (B \ A).card := by
  induction l with
  | nil => simp [advance]
  | cons x l ih =>
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
    · simpa [advance, List.find?_cons, hxA, hxB] using ih
    · have hA : advance (x :: l) A = advance l A := by
        simp [advance, List.find?_cons, hxA]
      have hB : advance (x :: l) B = insert x B := by
        simp [advance, List.find?_cons, hxB]
      rw [hA, hB]
      apply Finset.card_le_card
      intro y hy
      have hmono := subset_advance l A
      simp only [Finset.mem_sdiff, Finset.mem_insert] at hy ⊢
      rcases hy.1 with rfl | hyB
      · exact False.elim (hy.2 (hmono hxA))
      · exact ⟨hyB, fun hyA => hy.2 (hmono hyA)⟩
    · have hA : advance (x :: l) A = insert x A := by
        simp [advance, List.find?_cons, hxA]
      have hB : advance (x :: l) B = advance l B := by
        simp [advance, List.find?_cons, hxB]
      rw [hA, hB]
      rcases advance_cases l B with h | ⟨b, h⟩
      · rw [h]
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_sdiff, Finset.mem_insert] at hy ⊢
        aesop
      · rw [h]
        exact insert_exchange A B x b (Finset.mem_sdiff.mpr ⟨hxB, hxA⟩)
    · simp only [advance, List.find?_cons, hxA, hxB, not_false_eq_true,
        decide_true, Bool.true_eq, if_true]
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_sdiff, Finset.mem_insert] at hy ⊢
      aesop

lemma arbitrary_rankings (l l' : List M) (A B : Finset M) :
    (advance l' B \ advance l A).card ≤ (B \ A).card + 1 := by
  have hmono := subset_advance l A
  rcases advance_cases l' B with h | ⟨b, h⟩
  · rw [h]
    apply (Finset.card_le_card (show B \ advance l A ⊆ B \ A by
      intro x hx
      obtain ⟨hxB, hxA⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxB, fun h => hxA (hmono h)⟩)).trans
    omega
  · rw [h]
    apply (Finset.card_le_card (show insert b B \ advance l A ⊆ insert b (B \ A) by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_insert] at hx ⊢
      rcases hx.1 with rfl | hxB
      · exact Or.inl rfl
      · exact Or.inr ⟨hxB, fun hxA => hx.2 (hmono hxA)⟩)).trans
    exact Finset.card_insert_le _ _

lemma alloc_succ {n : ℕ} [NeZero n] (σ : Fin n → List M) (t : ℕ) :
    allocBefore σ (t + 1) = advance (σ (agentAt n t)) (allocBefore σ t) := by
  simp only [allocBefore, top, advance, Finset.mem_sdiff, Finset.mem_univ, true_and]
  cases (σ (agentAt n t)).find? (fun x => decide (x ∉ allocBefore σ t)) <;> rfl

lemma discrepancy_count {n : ℕ} [NeZero n] (σ : Fin n → List M)
    (i : Fin n) (τ : List M) (t : ℕ) :
    (allocBefore (Function.update σ i τ) t \ allocBefore σ t).card ≤
      Nat.count (fun s => agentAt n s = i) t := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    rw [alloc_succ, alloc_succ, Nat.count_succ]
    by_cases h : agentAt n t = i
    · simp only [h, Function.update_self, if_true]
      exact (arbitrary_rankings (σ i) τ (allocBefore σ t)
        (allocBefore (Function.update σ i τ) t)).trans (Nat.add_le_add_right ih 1)
    · simp only [Function.update_of_ne h, h, if_false, Nat.add_zero]
      exact (same_ranking (σ (agentAt n t)) (allocBefore σ t)
        (allocBefore (Function.update σ i τ) t)).trans ih

lemma count_before {n : ℕ} [NeZero n] (i : Fin n) (r : ℕ) :
    Nat.count (fun s => agentAt n s = i) (r * n + i.val) ≤ r := by
  rw [Nat.count_eq_card_filter_range]
  have hmod (s : ℕ) (hs : agentAt n s = i) : s % n = i.val := by
    simpa [agentAt] using congrArg Fin.val hs
  have hdecomp (s : ℕ) (hs : agentAt n s = i) : s / n * n + i.val = s := by
    simpa [hmod s hs, Nat.mul_comm] using Nat.div_add_mod s n
  calc
    ((Finset.range (r * n + i.val)).filter (fun s => agentAt n s = i)).card ≤
        (Finset.range r).card := by
      apply Finset.card_le_card_of_injOn (fun s : ℕ => s / n)
      · intro s hs
        obtain ⟨hlt, hsi⟩ := Finset.mem_filter.mp hs
        have ht := Finset.mem_range.mp hlt
        have hd := hdecomp s hsi
        have hmul : s / n * n < r * n := by omega
        exact Finset.mem_range.mpr ((Nat.mul_lt_mul_right (NeZero.pos n)).mp hmul)
      · intro s hs t ht hst
        obtain ⟨_, hsi⟩ := Finset.mem_filter.mp hs
        obtain ⟨_, hti⟩ := Finset.mem_filter.mp ht
        have hs' := hdecomp s hsi
        have ht' := hdecomp t hti
        change s / n = t / n at hst
        rw [hst] at hs'
        omega
    _ = r := Finset.card_range r

end AllocationDiscrepancy

theorem solution {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (r : ℕ) (hr : r < k) :
    (allocBefore (Function.update σ i τ) (r * n + i.val) \ allocBefore σ (r * n + i.val)).card
      ≤ r := by
  exact (AllocationDiscrepancy.discrepancy_count σ i τ _).trans
    (AllocationDiscrepancy.count_before i r)

#print axioms solution
