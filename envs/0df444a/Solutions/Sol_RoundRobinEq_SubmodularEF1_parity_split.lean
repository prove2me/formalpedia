-- Prove2me | solution 1 for RoundRobinEq.SubmodularEF1.parity_split
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T05:48:58.940669+00:00
-- url     : https://prove2.me/submissions/ad5ae84d-c395-43c5-a430-dbd3667b82d6

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting
/- Parity splitting for the submodular Round-Robin fairness proof.
Original mathematics: Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser,
arXiv:2301.13652v1, p.20. Platform formulation: mikedeng1.
Reuses the complete accepted Lemma4.7 proof under AcceptedWindow, submission
773ba286-6626-4338-9b8a-b35f10ea2ddc, SHA256
6138b263cc370b1cd4b4ef2ea1bf5a5d620dc4ff31be582b904ac0319fad43df.
Original attribution retained. Alexander Richard Towell directed the campaign;
OpenAI Codex substantially constructed and checked the formalization.
No mathematical novelty or independent human review claimed. -/

namespace AcceptedWindow
/-
Per-agent allocation-window bound, 23 October 2026.
Original result: Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser,
Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, Lemma 4.7, p.19.
PDF SHA256 f4c69869cd4fa69f8472f42d0e4490fbda4ccf70dfaf17d028e0e5b45c7ffadf.
Platform statement and definitions: mikedeng1.
Reuses the complete accepted Lemma 4.6 proof (target
305d619e-2e51-4d19-a823-47c63a485c4a, submission
8275dda6-629e-4300-a59a-108dbebe3276, SHA256
eb4c7357a6321cb47dc3e3f9483ca4bd1dabe69416d698d3168d2c1f76594983),
wrapped in ReusedDiscrepancy with its original attribution preserved below.
The new lemmas prove allocation monotonicity, freshness of picks, equality of
initial prefixes before the deviating agent moves, and a per-agent r-pick bound
on every length-rn interval. The target follows by adding that bound to the
accepted discrepancy estimate. Ranking completeness is not needed by these
stronger combinatorial helper lemmas.
Alexander Richard Towell directed the campaign and verification standards;
OpenAI Codex constructed and checked this formalization with Lean/Mathlib.
No mathematical novelty or independent human proof review is claimed.
-/
/- Allocation discrepancy under one changed ranking. Original result:
Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser, Round-Robin Beyond
Additive Agents, arXiv:2301.13652v1, Lemma 4.6, printed p.19.
mikedeng1 supplied the formal model; statement approval is not proof review.
Alexander Richard Towell directed the campaign. OpenAI Codex constructed and
checked this proof with Lean/Mathlib. No earlier platform proof is reused;
no mathematical novelty or independent human review is claimed. -/

namespace ReusedDiscrepancy

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

end ReusedDiscrepancy

open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)
open ReusedDiscrepancy.AllocationDiscrepancy

namespace AllocationWindow

variable {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]

lemma alloc_mono (σ : Fin n → List M) : Monotone (allocBefore σ) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [alloc_succ]
  exact subset_advance _ _

lemma pick_fresh (σ : Fin n → List M) (t : ℕ) (g : M)
    (h : pick σ t = some g) : g ∉ allocBefore σ t := by
  unfold pick top at h
  simpa using List.find?_some h

lemma pick_mem_next (σ : Fin n → List M) (t : ℕ) (g : M)
    (h : pick σ t = some g) : g ∈ allocBefore σ (t+1) := by
  change g ∈ (match pick σ t with
    | some x => insert x (allocBefore σ t)
    | none => allocBefore σ t)
  rw [h]
  simp

lemma initial_same (σ : Fin n → List M) (i : Fin n) (τ : List M)
    (t : ℕ) (ht : t ≤ i.val) :
    allocBefore (Function.update σ i τ) t = allocBefore σ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [alloc_succ, alloc_succ, ih (by omega)]
    have hne : agentAt n t ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      have htn : t < n := by omega
      simp only [agentAt, Nat.mod_eq_of_lt htn] at hv
      omega
    rw [Function.update_of_ne hne]

lemma window_step_count (i j : Fin n) (r : ℕ) :
    ((Finset.Ico i.val (r*n+i.val)).filter (fun t => agentAt n t = j)).card ≤ r := by
  have hp : Function.Periodic (fun t => agentAt n t = j) (r*n) := by
    intro t
    have he : agentAt n (t+r*n) = agentAt n t := by
      apply Fin.ext
      simp [agentAt, Nat.add_mod]
    exact congrArg (fun a : Fin n => a = j) he
  have he := Nat.filter_Ico_card_eq_of_periodic i.val (r*n)
    (fun t => agentAt n t = j) hp
  rw [Nat.add_comm i.val] at he
  rw [he]
  exact (Nat.count_monotone _ (Nat.le_add_right (r*n) j.val)).trans
    (count_before j r)

lemma bundle_window_bound (σ : Fin n → List M) (i j : Fin n) (r : ℕ) :
    (roundRobin σ j ∩ (allocBefore σ (r*n+i.val) \ allocBefore σ i.val)).card ≤ r := by
  let T := (Finset.Ico i.val (r*n+i.val)).filter (fun t => agentAt n t = j)
  have hsub : roundRobin σ j ∩ (allocBefore σ (r*n+i.val) \ allocBefore σ i.val) ⊆
      T.biUnion (fun t => (pick σ t).toFinset) := by
    intro g hg
    obtain ⟨hgA,hgd⟩ := Finset.mem_inter.mp hg
    obtain ⟨hgb,hga⟩ := Finset.mem_sdiff.mp hgd
    obtain ⟨t,ht,hg⟩ := Finset.mem_biUnion.mp hgA
    obtain ⟨htm,htj⟩ := Finset.mem_filter.mp ht
    have hpick : pick σ t = some g := by simpa using hg
    have hlo : i.val ≤ t := by
      by_contra h
      have hta : t+1 ≤ i.val := by omega
      exact hga (alloc_mono σ hta (pick_mem_next σ t g hpick))
    have hhi : t < r*n+i.val := by
      by_contra h
      exact pick_fresh σ t g hpick (alloc_mono σ (by omega) hgb)
    apply Finset.mem_biUnion.mpr
    exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo,hhi⟩,htj⟩,hg⟩
  calc
    _ ≤ (T.biUnion (fun t => (pick σ t).toFinset)).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, (pick σ t).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ T, 1 := by
      apply Finset.sum_le_sum
      intro t ht
      cases pick σ t <;> simp
    _ = T.card := by simp
    _ ≤ r := window_step_count i j r

end AllocationWindow

#print axioms AllocationWindow.bundle_window_bound


theorem solution {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (j : Fin n) (r : ℕ) (hr : r < k) :
    (roundRobin σ j ∩
        (allocBefore (Function.update σ i τ) (r * n + i.val) \
          allocBefore (Function.update σ i τ) i.val)).card ≤ 2 * r := by
  have hinit := AllocationWindow.initial_same σ i τ i.val le_rfl
  rw [hinit]
  have hsub : roundRobin σ j ∩
      (allocBefore (Function.update σ i τ) (r*n+i.val) \ allocBefore σ i.val) ⊆
      (roundRobin σ j ∩ (allocBefore σ (r*n+i.val) \ allocBefore σ i.val)) ∪
        (allocBefore (Function.update σ i τ) (r*n+i.val) \ allocBefore σ (r*n+i.val)) := by
    intro g hg
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union] at hg ⊢
    by_cases h : g ∈ allocBefore σ (r*n+i.val)
    · exact Or.inl ⟨hg.1,h,hg.2.2⟩
    · exact Or.inr ⟨hg.2.1,h⟩
  calc
    _ ≤ ((roundRobin σ j ∩ (allocBefore σ (r*n+i.val) \ allocBefore σ i.val)) ∪
        (allocBefore (Function.update σ i τ) (r*n+i.val) \ allocBefore σ (r*n+i.val))).card :=
      Finset.card_le_card hsub
    _ ≤ (roundRobin σ j ∩ (allocBefore σ (r*n+i.val) \ allocBefore σ i.val)).card +
        (allocBefore (Function.update σ i τ) (r*n+i.val) \ allocBefore σ (r*n+i.val)).card :=
      Finset.card_union_le _ _
    _ ≤ r+r := Nat.add_le_add (AllocationWindow.bundle_window_bound σ i j r)
      ((discrepancy_count σ i τ _).trans (count_before i r))
    _ = 2*r := by omega

#print axioms solution

end AcceptedWindow

open RoundRobinEq.SubmodularEF1

namespace ParityWindow

lemma count_even (m : ℕ) : ((Finset.range m).filter (fun a => a % 2 = 0)).card = (m+1)/2 := by
  have h := Nat.count_modEq_card (b := m) (r := 2) (by decide) 0
  rw [Nat.count_eq_card_filter_range] at h
  have he : (Finset.range m).filter (fun a => a ≡ 0 [MOD 2]) =
      (Finset.range m).filter (fun a => a % 2 = 0) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_range, Nat.ModEq, Nat.zero_mod, Nat.reduceMod]
  rw [he] at h
  norm_num only [Nat.zero_mod] at h
  rw [h]
  split_ifs <;> omega

lemma count_odd (m : ℕ) : ((Finset.range m).filter (fun a => a % 2 = 1)).card = m/2 := by
  have h := Nat.count_modEq_card (b := m) (r := 2) (by decide) 1
  rw [Nat.count_eq_card_filter_range] at h
  have he : (Finset.range m).filter (fun a => a ≡ 1 [MOD 2]) =
      (Finset.range m).filter (fun a => a % 2 = 1) := by
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_range, Nat.ModEq, Nat.zero_mod, Nat.reduceMod]
  rw [he] at h
  norm_num only [Nat.reduceMod] at h
  rw [h]
  split_ifs <;> omega

lemma interval_count (a b c : ℕ) (hab : a ≤ b) :
    ((Finset.Ico a b).filter (fun x => x % 2 = c)).card =
      ((Finset.range b).filter (fun x => x % 2 = c)).card -
      ((Finset.range a).filter (fun x => x % 2 = c)).card := by
  have hset : (Finset.Ico a b).filter (fun x => x % 2 = c) =
      ((Finset.range b).filter (fun x => x % 2 = c)) \
      ((Finset.range a).filter (fun x => x % 2 = c)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]
    omega
  rw [hset, Finset.card_sdiff_of_subset]
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hab, hx.2⟩

lemma interval_balanced (a b : ℕ) (hab : a ≤ b) :
    |((((Finset.Ico a b).filter (fun x => x % 2 = 0)).card : ℤ) -
      (((Finset.Ico a b).filter (fun x => x % 2 = 1)).card : ℤ))| ≤ 1 := by
  rw [interval_count a b 0 hab, interval_count a b 1 hab, count_even, count_even, count_odd, count_odd]
  apply abs_le.mpr
  omega

lemma convex_balanced (S : Finset ℕ)
    (hconv : ∀ a ∈ S, ∀ c ∈ S, ∀ b, a ≤ b → b ≤ c → b ∈ S) :
    |(((S.filter (fun x => x % 2 = 0)).card : ℤ) -
      ((S.filter (fun x => x % 2 = 1)).card : ℤ))| ≤ 1 := by
  by_cases hS : S.Nonempty
  · have hset : S = Finset.Ico (S.min' hS) (S.max' hS + 1) := by
      ext b
      constructor
      · intro hb
        exact Finset.mem_Ico.mpr ⟨S.min'_le b hb, by have := S.le_max' b hb; omega⟩
      · intro hb
        obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hb
        exact hconv _ (S.min'_mem hS) _ (S.max'_mem hS) b hlo (by omega)
    rw [hset]
    apply interval_balanced
    have h := S.min'_le _ (S.max'_mem hS)
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

lemma enum_parity {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (σ' : Fin n → List M) (A : Finset M) (k : ℕ) (y : ℕ → M)
    (hy : IsTimeOrderedEnum σ' A k y) (lo hi : ℕ) :
    let D := allocBefore σ' hi \ allocBefore σ' lo
    |((Yone y k ∩ D).card : ℤ) - ((Ytwo y k ∩ D).card : ℤ)| ≤ 1 ∧
      (Yone y k ∩ D).card + (Ytwo y k ∩ D).card ≤ (A ∩ D).card := by
  let D := allocBefore σ' hi \ allocBefore σ' lo
  let S := (Finset.range k).filter (fun a => 0 < a ∧ y a ∈ D)
  have hS (a : ℕ) : a ∈ S ↔ a < k ∧ 0 < a ∧
      y a ∈ allocBefore σ' hi ∧ y a ∉ allocBefore σ' lo := by
    simp [S, D, Finset.mem_sdiff]
  have hconv : ∀ a ∈ S, ∀ c ∈ S, ∀ b, a ≤ b → b ≤ c → b ∈ S := by
    intro a ha c hc b hab hbc
    obtain ⟨hak,ha0,hahi,halo⟩ := (hS a).mp ha
    obtain ⟨hck,hc0,hchi,hclo⟩ := (hS c).mp hc
    apply (hS b).mpr
    refine ⟨by omega, by omega, ?_, ?_⟩
    · by_cases he : b = c
      · simpa [he] using hchi
      · exact hy.2.2 b c (by omega) hck hi hchi
    · intro hblo
      by_cases he : a = b
      · exact halo (by simpa [he] using hblo)
      · exact halo (hy.2.2 a b (by omega) (by omega) lo hblo)
  have hsub : S ⊆ Finset.range k := Finset.filter_subset _ _
  have he : Yone y k ∩ D = (S.filter (fun a => a % 2 = 0)).image y := by
    ext g
    simp only [Yone, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, S]
    constructor
    · rintro ⟨⟨a, ⟨hak,ha2,hae⟩, rfl⟩, had⟩
      exact ⟨a, ⟨⟨hak,by omega,had⟩,hae⟩,rfl⟩
    · rintro ⟨a, ⟨⟨hak,ha0,had⟩,hae⟩, rfl⟩
      exact ⟨⟨a,⟨hak,by omega,hae⟩,rfl⟩,had⟩
  have ho : Ytwo y k ∩ D = (S.filter (fun a => a % 2 = 1)).image y := by
    ext g
    simp only [Ytwo, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, S]
    constructor
    · rintro ⟨⟨a, ⟨hak,hao⟩, rfl⟩, had⟩
      exact ⟨a, ⟨⟨hak,by omega,had⟩,hao⟩,rfl⟩
    · rintro ⟨a, ⟨⟨hak,ha0,had⟩,hao⟩, rfl⟩
      exact ⟨⟨a,⟨hak,hao⟩,rfl⟩,had⟩
  have hce : (Yone y k ∩ D).card = (S.filter (fun a => a % 2 = 0)).card := by
    rw [he, Finset.card_image_of_injOn]
    exact hy.2.1.mono (fun a ha => hsub (Finset.mem_filter.mp ha).1)
  have hco : (Ytwo y k ∩ D).card = (S.filter (fun a => a % 2 = 1)).card := by
    rw [ho, Finset.card_image_of_injOn]
    exact hy.2.1.mono (fun a ha => hsub (Finset.mem_filter.mp ha).1)
  have hsplit : (S.filter (fun a => a % 2 = 0)).card +
      (S.filter (fun a => a % 2 = 1)).card = S.card := by
    have hneg : S.filter (fun a => a % 2 = 1) = S.filter (fun a => ¬a % 2 = 0) := by
      apply Finset.filter_congr
      intro a ha
      omega
    rw [hneg]
    exact Finset.card_filter_add_card_filter_not _
  have hsize : S.card ≤ (A ∩ D).card := by
    have himage : S.image y ⊆ A ∩ D := by
      intro g hg
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
      apply Finset.mem_inter.mpr
      constructor
      · rw [← hy.1]
        exact Finset.mem_image.mpr ⟨a,hsub ha,rfl⟩
      · exact (Finset.mem_filter.mp ha).2.2
    have hc : (S.image y).card = S.card := Finset.card_image_of_injOn (hy.2.1.mono hsub)
    rw [← hc]
    exact Finset.card_le_card himage
  change |((Yone y k ∩ D).card : ℤ) - ((Ytwo y k ∩ D).card : ℤ)| ≤ 1 ∧ _
  rw [hce, hco]
  exact ⟨convex_balanced S hconv, by rw [hsplit]; exact hsize⟩

end ParityWindow

theorem solution {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (j : Fin n) (hji : j ≠ i)
    (y : ℕ → M) (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y)
    (r : ℕ) (hr : r < k) :
    let D := allocBefore (Function.update σ i τ) (r * n + i.val) \
      allocBefore (Function.update σ i τ) i.val
    |((Yone y k ∩ D).card : ℤ) - ((Ytwo y k ∩ D).card : ℤ)| ≤ 1 ∧
      (Yone y k ∩ D).card ≤ r ∧ (Ytwo y k ∩ D).card ≤ r := by
  have hbal := ParityWindow.enum_parity (Function.update σ i τ) (roundRobin σ j) k y hy
    i.val (r*n+i.val)
  have htotal := AcceptedWindow.solution k hm σ hσ i τ hτ j r hr
  dsimp only at hbal ⊢
  obtain ⟨habs, hsize⟩ := hbal
  refine ⟨habs, ?_, ?_⟩ <;> have hab := abs_le.mp habs <;> omega

#print axioms solution
