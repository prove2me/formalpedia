-- Prove2me | solution 1 for RoundRobinEq.SubmodularEF1.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T09:41:44.777611+00:00
-- url     : https://prove2.me/submissions/c9f1e777-8bd1-4318-9515-fa89bacdee20

/-
Full submodular Round-Robin fairness root, 23October2026.
The original theorem is due to Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser.
The checked predecessor bodies and their notices follow. New work constructs an
adaptive greedy allocation schedule and proves its full chronological history is
an implementing ranking; this discharges the earlier conditional reduction.
Alexander Richard Towell stewards this work; OpenAI Codex developed and checked
these formalizations. No mathematical novelty or independent human review claimed.
-/
/-
Closing factor3/alpha value bound for Round-Robin submodular fairness.
Original source: Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser,
Round-Robin Beyond Additive Agents, arXiv:2301.13652v1 pp.20-21.
Alexander Richard Towell (queelius), substantial OpenAI Codex assistance,
23 October 2026. New work constructs Algorithm3 orderings, proves picks exist,
enumerates the final greedy bundle, and sums diminishing marginals by telescoping.
Actual accepted inequality(2) body: submission2b1a0a70-bdbf-458e-b66a-4978598900a1,
SHA2564285f07979b6c0bfb858b3b87f0479ae361d2b0c8dd8240274cab73550b7e130.
Actual accepted marginal-sum characterization body: submission5225f278-5f41-4b2a-95fd-074aab99d004,
SHA25682d42cf98e62cd96e948f253dee0029d49b0a3841f7686bb4a605d7d43373f76.
The characterization is due to Nemhauser, Wolsey and Fisher(1978), as reproduced
in the inspected paper's Theorem2.1 p.5; the1978 original was not inspected.
Inherited parity, window and discrepancy attribution is retained below.
mikedeng1 supplied the platform definitions. No mathematical novelty or
independent human proof review claimed. A greedy response and time enumeration
remain hypotheses, exactly as in this target; this is not the full fairness root.
-/
/-
Greedy-response marginal inequality (2), Amanatidis, Birmpas, Lazos, Leonardi
and Reiffenhäuser, Round-Robin Beyond Additive Agents, arXiv:2301.13652v1 p.20.
Formalization by Alexander Richard Towell (queelius), substantial OpenAI Codex
assistance, 23 October 2026. New work: initial exclusion, exact bundle-prefix
identity, injectivity of Algorithm3 enumeration and allocation contradiction.
Reuses actual accepted parity proof, submission ad5ae84d-c395-43c5-a430-dbd3667b82d6,
SHA256 6316f7622391b5794bd2a3d6c9a49c21415f0cf0b7968fbadd3af455b0083e08,
including its previously accepted window and discrepancy proofs. Notices retained.
No mathematical novelty or independent human review claimed.
-/
import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace AcceptedClosing
/- Parity splitting for the submodular Round-Robin fairness proof.
Original mathematics: Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser,
arXiv:2301.13652v1, p.20. Platform formulation: mikedeng1.
Reuses the complete accepted Lemma4.7 proof under AcceptedWindow, submission
773ba286-6626-4338-9b8a-b35f10ea2ddc, SHA256
6138b263cc370b1cd4b4ef2ea1bf5a5d620dc4ff31be582b904ac0319fad43df.
Original attribution retained. Alexander Richard Towell directed the campaign;
OpenAI Codex substantially constructed and checked the formalization.
No mathematical novelty or independent human review claimed. -/

namespace CheckedInequality
namespace AcceptedParity

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

end AcceptedParity

open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)
open AcceptedParity.AcceptedWindow.AllocationWindow

namespace GreedyComparison
variable {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]

lemma initial_card (σ : Fin n → List M) (i j : Fin n) :
    (roundRobin σ j ∩ allocBefore σ i.val).card ≤ 1 := by
  have hsub : roundRobin σ j ∩ allocBefore σ i.val ⊆ (pick σ j.val).toFinset := by
    intro g hg
    obtain ⟨hgA,hgb⟩ := Finset.mem_inter.mp hg
    obtain ⟨t,ht,hg⟩ := Finset.mem_biUnion.mp hgA
    obtain ⟨_,htj⟩ := Finset.mem_filter.mp ht
    have hpick : pick σ t = some g := by simpa using hg
    have hti : t < i.val := by
      by_contra h
      exact pick_fresh σ t g hpick (alloc_mono σ (by omega) hgb)
    have htn : t < n := lt_trans hti i.isLt
    have ht : t = j.val := by
      simpa only [agentAt, Nat.mod_eq_of_lt htn] using congrArg Fin.val htj
    simpa [ht] using hg
  apply (Finset.card_le_card hsub).trans
  cases pick σ j.val <;> simp

lemma parity_index (y : ℕ → M) (k : ℕ) (Y : Finset M)
    (hY : Y = Yone y k ∨ Y = Ytwo y k) {g : M} (hg : g ∈ Y) :
    ∃ a < k, 0 < a ∧ y a = g := by
  rcases hY with rfl | rfl
  · obtain ⟨a,ha,hag⟩ := Finset.mem_image.mp hg
    obtain ⟨hak,ha2,hae⟩ := Finset.mem_filter.mp ha
    exact ⟨a,Finset.mem_range.mp hak,by omega,hag⟩
  · obtain ⟨a,ha,hag⟩ := Finset.mem_image.mp hg
    obtain ⟨hak,hao⟩ := Finset.mem_filter.mp ha
    exact ⟨a,Finset.mem_range.mp hak,by omega,hag⟩

lemma parity_size (y : ℕ → M) (k : ℕ) (Y : Finset M)
    (hY : Y = Yone y k ∨ Y = Ytwo y k) : Y.card ≤ k := by
  have hs : Y ⊆ (Finset.range k).image y := by
    intro g hg
    obtain ⟨a,ha,_,rfl⟩ := parity_index y k Y hY hg
    exact Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr ha,rfl⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans (by simp))

lemma parity_not_initial (σ : Fin n → List M) (i j : Fin n) (τ : List M)
    (y : ℕ → M) (k : ℕ)
    (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y)
    (Y : Finset M) (hY : Y = Yone y k ∨ Y = Ytwo y k) :
    ∀ g ∈ Y, g ∉ allocBefore (Function.update σ i τ) i.val := by
  intro g hg hgi
  obtain ⟨a,hak,ha0,rfl⟩ := parity_index y k Y hY hg
  have h0i := hy.2.2 0 a ha0 hak i.val hgi
  have hmem (b : ℕ) (hb : b < k) : y b ∈ roundRobin σ j := by
    rw [← hy.1]
    exact Finset.mem_image.mpr ⟨b,Finset.mem_range.mpr hb,rfl⟩
  have he := initial_same σ i τ i.val le_rfl
  rw [he] at hgi h0i
  have eq := Finset.card_le_one.mp (initial_card σ i j) (y 0)
    (Finset.mem_inter.mpr ⟨hmem 0 (by omega),h0i⟩) (y a)
    (Finset.mem_inter.mpr ⟨hmem a hak,hgi⟩)
  have ha := hy.2.1 (Finset.mem_range.mpr (by omega : 0 < k))
    (Finset.mem_range.mpr hak) eq
  omega

lemma bundle_prefix (σ : Fin n → List M) (i : Fin n) (x : ℕ → M) (k r : ℕ)
    (hr : r ≤ k) (hx : ∀ a < k, pick σ (a*n+i.val) = some (x a)) :
    bundleBefore σ i (r*n+i.val) = (Finset.range r).image x := by
  ext g
  constructor
  · intro hg
    obtain ⟨t,ht,hg⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨htr,hti⟩ := Finset.mem_filter.mp ht
    have htr' := Finset.mem_range.mp htr
    have hmod : t % n = i.val := by simpa [agentAt] using congrArg Fin.val hti
    have hd : t / n * n + i.val = t := by
      simpa [hmod, Nat.mul_comm] using Nat.div_add_mod t n
    have hqr : t/n < r := by
      apply (Nat.mul_lt_mul_right (NeZero.pos n)).mp
      omega
    have hp := hx (t/n) (lt_of_lt_of_le hqr hr)
    rw [hd] at hp
    have he : x (t/n) = g := by simpa [hp, eq_comm] using hg
    exact Finset.mem_image.mpr ⟨t/n,Finset.mem_range.mpr hqr,he⟩
  · intro hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    have har := Finset.mem_range.mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨a*n+i.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,?_⟩,?_⟩
    · have h := Nat.mul_lt_mul_of_pos_right har (NeZero.pos n)
      omega
    · apply Fin.ext
      simp [agentAt, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    · simp [hx a (lt_of_lt_of_le har hr)]

lemma alg3_injective (vi : Finset M → ℝ) (x : ℕ → M) (Y : Finset M) (y' : ℕ → M)
    (hy' : IsAlg3Order vi x Y y') : Set.InjOn y' (Finset.range Y.card : Set ℕ) := by
  apply Finset.card_image_iff.mp
  rw [hy'.1,Finset.card_range]

end GreedyComparison

open GreedyComparison

theorem solution {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i j : Fin n) (hji : j ≠ i) (vi : Finset M → ℝ)
    (τ : List M) (hτ : IsGreedyResponse vi σ i τ)
    (x : ℕ → M) (hx : ∀ r < k, pick (Function.update σ i τ) (r*n+i.val) = some (x r))
    (y : ℕ → M) (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y)
    (Y : Finset M) (hY : Y = Yone y k ∨ Y = Ytwo y k)
    (y' : ℕ → M) (hy' : IsAlg3Order vi x Y y') :
    ∀ r < Y.card,
      marginal vi {y' r} ((Finset.range r).image x) ≤
        marginal vi {x r} ((Finset.range r).image x) := by
  intro r hr
  have hrk : r < k := lt_of_lt_of_le hr (parity_size y k Y hY)
  have htm : r*n+i.val < Fintype.card M := by
    rw [hm]
    have h := Nat.mul_le_mul_right n (show r+1 ≤ k by omega)
    nlinarith [i.isLt]
  have hai : agentAt n (r*n+i.val) = i := by
    apply Fin.ext
    simp [agentAt, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have hb := bundle_prefix (Function.update σ i τ) i x k r hrk.le hx
  let D := allocBefore (Function.update σ i τ) (r*n+i.val) \
    allocBefore (Function.update σ i τ) i.val
  have hcount : (Y ∩ D).card ≤ r := by
    have h := AcceptedParity.solution k hm σ hσ i τ hτ.1 j hji y hy r hrk
    rcases hY with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hsub : (Finset.range (r+1)).image y' ⊆ Y ∩ D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    have har : a ≤ r := by simpa using Finset.mem_range.mp ha
    have haY : a < Y.card := lt_of_le_of_lt har hr
    have hyY : y' a ∈ Y := by
      rw [← hy'.1]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr haY,rfl⟩
    have hgalloc : y' a ∈ allocBefore (Function.update σ i τ) (r*n+i.val) := by
      by_contra hg
      have hgreedy := hτ.2 (r*n+i.val) htm hai (x r) (hx r hrk) (y' a) hg
      rw [hb] at hgreedy
      exact (not_lt_of_ge ((hy'.2 r hr a har).trans hgreedy)) hlt
    exact Finset.mem_inter.mpr ⟨hyY,Finset.mem_sdiff.mpr
      ⟨hgalloc,parity_not_initial σ i j τ y k hy Y hY _ hyY⟩⟩
  have hinj := (alg3_injective vi x Y y' hy').mono
    (show (Finset.range (r+1) : Set ℕ) ⊆ (Finset.range Y.card : Set ℕ) by
      intro a ha
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha) (by omega)))
  have hcard : ((Finset.range (r+1)).image y').card = r+1 := by
    rw [Finset.card_image_of_injOn hinj,Finset.card_range]
  have hc := (Finset.card_le_card hsub).trans hcount
  rw [hcard] at hc
  omega

#print axioms solution

end CheckedInequality

namespace AcceptedMarginalSum
open RoundRobinEq.SubmodularEF1
namespace MarginalSumProof

variable {M : Type} [Fintype M] [DecidableEq M] (v : Finset M → ℝ)

lemma union_bound (hsub : IsSubmodular v) (S U : Finset M) :
    v (S ∪ U) ≤ v S + ∑ g ∈ U, marginal v {g} S := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert x U hx ih =>
    rw [Finset.sum_insert hx]
    by_cases hxS : x ∈ S
    · have heq : S ∪ insert x U = S ∪ U := by ext a; simp; aesop
      have hmarg : marginal v {x} S = 0 := by simp [marginal, hxS]
      simpa [heq, hmarg] using ih
    · have hxSU : x ∉ S ∪ U := by simp [hxS, hx]
      have h := hsub S (S ∪ U) x Finset.subset_union_left hxSU
      have heq : S ∪ insert x U = insert x (S ∪ U) := by ext a; simp
      rw [heq]
      simp only [marginal, Finset.singleton_union] at h ih ⊢
      linarith

lemma one_step (h : ∀ S T : Finset M,
    v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S)
    (S : Finset M) (x g : M) (hx : x ∉ S) (hg : g ∉ S) (hxg : x ≠ g) :
    marginal v {g} (insert x S) ≤ marginal v {g} S := by
  have hpair := h S (insert x (insert g S))
  have hdiff : insert x (insert g S) \ S = {x, g} := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hdiff] at hpair
  simp only [Finset.sum_insert (show x ∉ ({g} : Finset M) by simpa using hxg),
    Finset.sum_singleton, marginal, Finset.singleton_union] at hpair ⊢
  rw [Finset.insert_comm] at hpair
  linarith

lemma diminishing (h : ∀ S T : Finset M,
    v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S)
    (S U : Finset M) (g : M) (hg : g ∉ S ∪ U) :
    marginal v {g} (S ∪ U) ≤ marginal v {g} S := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert x U hx ih =>
    have hgU : g ∉ S ∪ U := by intro hmem; apply hg; simpa only [Finset.mem_union,
      Finset.mem_insert] using (show g ∈ S ∪ insert x U from Finset.mem_union.mpr
        ((Finset.mem_union.mp hmem).imp_right (fun h => Finset.mem_insert_of_mem h)))
    have ih' := ih hgU
    have heq : S ∪ insert x U = insert x (S ∪ U) := by ext a; simp
    rw [heq]
    by_cases hxSU : x ∈ S ∪ U
    · simpa [Finset.insert_eq_of_mem hxSU] using ih'
    · have hxg : x ≠ g := by intro he; subst x; apply hg; simp
      exact (one_step v h (S ∪ U) x g hxSU hgU hxg).trans ih'

end MarginalSumProof

theorem solution {M : Type} [Fintype M] [DecidableEq M] (v : Finset M → ℝ)
    (hv : ∀ S, 0 ≤ v S) :
    (IsNonDecreasing v ∧ IsSubmodular v) ↔
      ∀ S T : Finset M, v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S := by
  constructor
  · rintro ⟨hmono, hsub⟩ S T
    have hle := hmono T (S ∪ (T \ S)) (by intro x hx; simp; aesop)
    exact hle.trans (MarginalSumProof.union_bound v hsub S (T \ S))
  · intro h
    constructor
    · intro S T hST
      have h' := h T S
      simpa [Finset.sdiff_eq_empty_iff_subset.mpr hST] using h'
    · intro S T g hST hg
      have hg' : g ∉ S ∪ (T \ S) := by simpa [Finset.union_sdiff_of_subset hST] using hg
      simpa [Finset.union_sdiff_of_subset hST] using
        MarginalSumProof.diminishing v h S (T \ S) g hg'

#print axioms solution

end AcceptedMarginalSum

open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)
open CheckedInequality.AcceptedParity.AcceptedWindow.AllocationWindow
namespace ClosingSupport
variable {M : Type} [Fintype M] [DecidableEq M]

lemma alg3_exists [Nonempty M] (v : Finset M → ℝ) (x : ℕ → M) (Y : Finset M) :
    ∃ y', IsAlg3Order v x Y y' := by
  classical
  refine Finset.strongInductionOn Y ?_
  intro Y ih
  by_cases hY : Y = ∅
  · subst Y
    exact ⟨fun _ => Classical.ofNonempty, by simp [IsAlg3Order]⟩
  obtain ⟨a,ha,hmin⟩ := Y.exists_min_image
    (fun a => marginal v {a} ((Finset.range (Y.card-1)).image x))
    (Finset.nonempty_iff_ne_empty.mpr hY)
  obtain ⟨z,hz⟩ := ih (Y.erase a) (Finset.erase_ssubset ha)
  have hcard := Finset.card_erase_add_one ha
  let y' := fun r => if r < (Y.erase a).card then z r else a
  have hpre : (Finset.range (Y.erase a).card).image y' = (Finset.range (Y.erase a).card).image z := by
    apply Finset.image_congr
    intro b hb
    simp only [y', if_pos (Finset.mem_range.mp hb)]
  have himage : (Finset.range Y.card).image y' = Y := by
    rw [← hcard, Finset.range_add_one, Finset.image_insert, hpre, hz.1]
    simp [y', Finset.insert_erase ha]
  refine ⟨y',himage,?_⟩
  intro r hr t htr
  by_cases hrc : r < (Y.erase a).card
  · have htc : t < (Y.erase a).card := lt_of_le_of_lt htr hrc
    simpa [y',hrc,htc] using hz.2 r hrc t htr
  · have he : r = Y.card-1 := by omega
    have hyY : y' t ∈ Y := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨t,Finset.mem_range.mpr (lt_of_le_of_lt htr hr),rfl⟩
    have hyr : y' r = a := if_neg hrc
    rw [hyr,he]
    exact hmin (y' t) hyY

lemma alloc_card {n : ℕ} [NeZero n] (σ : Fin n → List M) (t : ℕ) :
    (allocBefore σ t).card ≤ t := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    change (match pick σ t with
      | some g => insert g (allocBefore σ t)
      | none => allocBefore σ t).card ≤ t+1
    cases pick σ t with
    | none => exact ih.trans (by omega)
    | some g => exact (Finset.card_insert_le _ _).trans (by omega)

lemma pick_exists {n : ℕ} [NeZero n] (σ : Fin n → List M)
    (hσ : ∀ i, IsRanking (σ i)) (t : ℕ) (ht : t < Fintype.card M) :
    ∃ g, pick σ t = some g := by
  cases hp : pick σ t with
  | some g => exact ⟨g,rfl⟩
  | none =>
    exfalso
    have he : allocBefore σ t = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro g
      unfold pick top at hp
      have hh := List.find?_eq_none.mp hp g ((hσ (agentAt n t)).2 g)
      simpa using hh
    have hc := alloc_card σ t
    rw [he,Finset.card_univ] at hc
    omega

lemma response_sequence [Nonempty M] {n : ℕ} [NeZero n]
    (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i)) (i : Fin n)
    (k : ℕ) (hm : Fintype.card M = k*n) :
    ∃ x : ℕ → M, ∀ r < k, pick σ (r*n+i.val) = some (x r) := by
  have he (r : ℕ) (hr : r < k) : ∃ g, pick σ (r*n+i.val) = some g := by
    apply pick_exists σ hσ
    rw [hm]
    have h := Nat.mul_le_mul_right n (show r+1 ≤ k by omega)
    nlinarith [i.isLt]
  let x := fun r => if h : r < k then Classical.choose (he r h) else Classical.ofNonempty
  refine ⟨x,?_⟩
  intro r hr
  simpa only [x, dif_pos hr] using Classical.choose_spec (he r hr)

lemma marginal_nonneg (v : Finset M → ℝ) (hv : IsNonDecreasing v) (g : M) (S : Finset M) :
    0 ≤ marginal v {g} S := by
  unfold marginal
  exact sub_nonneg.mpr (hv S ({g} ∪ S) Finset.subset_union_right)

lemma marginal_prefix_le (v : Finset M → ℝ) (hv : IsNonDecreasing v) (hs : IsSubmodular v)
    (S T : Finset M) (hST : S ⊆ T) (g : M) : marginal v {g} T ≤ marginal v {g} S := by
  by_cases hg : g ∈ T
  · simpa [marginal, hg] using marginal_nonneg v hv g S
  · exact hs S T g hST hg

lemma telescoping (v : Finset M → ℝ) (x : ℕ → M) (r : ℕ) :
    (∑ a ∈ Finset.range r, marginal v {x a} ((Finset.range a).image x)) =
      v ((Finset.range r).image x) - v ∅ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_add_one, Finset.image_insert]
    simp only [marginal, Finset.singleton_union]
    ring

lemma sum_comparison (v : Finset M → ℝ) (hv : IsValuation v) (hs : IsSubmodular v)
    (x : ℕ → M) (k : ℕ) (Y : Finset M) (hY : Y.card ≤ k) (y' : ℕ → M)
    (hy' : IsAlg3Order v x Y y')
    (hcomp : ∀ r < Y.card, marginal v {y' r} ((Finset.range r).image x) ≤
      marginal v {x r} ((Finset.range r).image x)) :
    (∑ g ∈ Y, marginal v {g} ((Finset.range k).image x)) ≤
      v ((Finset.range k).image x) := by
  have hinj := CheckedInequality.GreedyComparison.alg3_injective v x Y y' hy'
  calc
    _ = ∑ a ∈ Finset.range Y.card, marginal v {y' a} ((Finset.range k).image x) := by
      conv_lhs => rw [← hy'.1]
      rw [Finset.sum_image]
      exact fun a ha b hb he => hinj ha hb he
    _ ≤ ∑ a ∈ Finset.range Y.card, marginal v {x a} ((Finset.range a).image x) := by
      apply Finset.sum_le_sum
      intro a ha
      have har := Finset.mem_range.mp ha
      apply (marginal_prefix_le v hv.2 hs _ _ ?_ (y' a)).trans (hcomp a har)
      exact Finset.image_subset_image (Finset.range_mono (le_trans har.le hY))
    _ = v ((Finset.range Y.card).image x) := by rw [telescoping,hv.1,sub_zero]
    _ ≤ v ((Finset.range k).image x) := hv.2 _ _
      (Finset.image_subset_image (Finset.range_mono hY))

end ClosingSupport
#print axioms ClosingSupport.sum_comparison
#print axioms ClosingSupport.alg3_exists

namespace ClosingSupport
variable {M : Type} [Fintype M] [DecidableEq M]

lemma final_bundle {n : ℕ} [NeZero n] (σ : Fin n → List M) (i : Fin n)
    (x : ℕ → M) (k : ℕ) (hm : Fintype.card M = k*n)
    (hx : ∀ a < k, pick σ (a*n+i.val) = some (x a)) :
    roundRobin σ i = (Finset.range k).image x := by
  ext g
  constructor
  · intro hg
    obtain ⟨t,ht,hg⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨htm,hti⟩ := Finset.mem_filter.mp ht
    have htm' := Finset.mem_range.mp htm
    rw [hm] at htm'
    have hmod : t % n = i.val := by simpa [agentAt] using congrArg Fin.val hti
    have hd : t / n * n + i.val = t := by
      simpa [hmod, Nat.mul_comm] using Nat.div_add_mod t n
    have hq : t/n < k := by
      apply (Nat.mul_lt_mul_right (NeZero.pos n)).mp
      omega
    have hp := hx (t/n) hq
    rw [hd] at hp
    exact Finset.mem_image.mpr ⟨t/n,Finset.mem_range.mpr hq,by simpa [hp,eq_comm] using hg⟩
  · intro hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    have hak := Finset.mem_range.mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨a*n+i.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,?_⟩,?_⟩
    · rw [hm]
      have h := Nat.mul_le_mul_right n (show a+1 ≤ k by omega)
      nlinarith [i.isLt]
    · apply Fin.ext
      simp [agentAt,Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
    · simp [hx a hak]

lemma parity_cover {n : ℕ} [NeZero n] (σ : Fin n → List M) (A : Finset M)
    (y : ℕ → M) (k : ℕ) (hy : IsTimeOrderedEnum σ A k y) :
    A.erase (y 0) = Yone y k ∪ Ytwo y k := by
  ext g
  constructor
  · intro hg
    obtain ⟨hne,hgA⟩ := Finset.mem_erase.mp hg
    rw [← hy.1] at hgA
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hgA
    have hak := Finset.mem_range.mp ha
    have ha0 : 0 < a := by
      by_contra h
      have he0 : a = 0 := by omega
      exact hne (congrArg y he0)
    by_cases he : a % 2 = 0
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨a,Finset.mem_filter.mpr ⟨ha,by omega,he⟩,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a,Finset.mem_filter.mpr ⟨ha,by omega⟩,rfl⟩)
  · intro hg
    have hex : ∃ a < k, 0 < a ∧ y a = g := by
      rcases Finset.mem_union.mp hg with hg | hg
      · exact CheckedInequality.GreedyComparison.parity_index y k _ (Or.inl rfl) hg
      · exact CheckedInequality.GreedyComparison.parity_index y k _ (Or.inr rfl) hg
    obtain ⟨a,hak,ha0,rfl⟩ := hex
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have h := hy.2.1 (Finset.mem_range.mpr hak) (Finset.mem_range.mpr (by omega : 0 < k)) he
      omega
    · rw [← hy.1]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr hak,rfl⟩

end ClosingSupport
open ClosingSupport

theorem solution {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k*n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ) (hv : ∀ i, IsValuation (v i)) (hsub : ∀ i, IsSubmodular (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ)
    (i j : Fin n) (hji : j ≠ i) (τ : List M) (hτ : IsGreedyResponse (v i) σ i τ)
    (y : ℕ → M) (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y) :
    v i ((roundRobin σ j).erase (y 0)) ≤ 3/α * v i (roundRobin σ i) := by
  classical
  letI : Nonempty M := ⟨y 0⟩
  have hσ' : ∀ ℓ, IsRanking ((Function.update σ i τ) ℓ) := by
    intro ℓ
    by_cases he : ℓ = i
    · subst ℓ; simpa using hτ.1
    · simpa [Function.update_of_ne he] using hσ.1 ℓ
  obtain ⟨x,hx⟩ := response_sequence (Function.update σ i τ) hσ' i k hm
  let S := (Finset.range k).image x
  have hS := final_bundle (Function.update σ i τ) i x k hm hx
  have hbound (Y : Finset M) (hY : Y = Yone y k ∨ Y = Ytwo y k) :
      (∑ g ∈ Y, marginal (v i) {g} S) ≤ v i S := by
    obtain ⟨y',hy'⟩ := alg3_exists (v i) x Y
    exact sum_comparison (v i) (hv i) (hsub i) x k Y
      (CheckedInequality.GreedyComparison.parity_size y k Y hY) y' hy'
      (CheckedInequality.solution k hm σ hσ.1 i j hji (v i) τ hτ x hx y hy Y hY y' hy')
  have h1 := hbound (Yone y k) (Or.inl rfl)
  have h2 := hbound (Ytwo y k) (Or.inr rfl)
  have hunion := AcceptedMarginalSum.MarginalSumProof.union_bound (v i) (hsub i) S
    (Yone y k ∪ Ytwo y k)
  have hmono := (hv i).2 (Yone y k ∪ Ytwo y k) (S ∪ (Yone y k ∪ Ytwo y k))
    Finset.subset_union_right
  have hsum : (∑ g ∈ Yone y k ∪ Ytwo y k, marginal (v i) {g} S) +
      (∑ g ∈ Yone y k ∩ Ytwo y k, marginal (v i) {g} S) =
      (∑ g ∈ Yone y k, marginal (v i) {g} S) +
      (∑ g ∈ Ytwo y k, marginal (v i) {g} S) := Finset.sum_union_inter
  have hnn : 0 ≤ ∑ g ∈ Yone y k ∩ Ytwo y k, marginal (v i) {g} S :=
    Finset.sum_nonneg (fun g _ => marginal_nonneg (v i) (hv i).2 g S)
  have htotal : v i ((roundRobin σ j).erase (y 0)) ≤ 3 * v i S := by
    rw [parity_cover (Function.update σ i τ) (roundRobin σ j) y k hy]
    linarith
  have hpne := hσ.2 i τ hτ.1
  rw [hS] at hpne
  have hval : v i S ≤ v i (roundRobin σ i) / α := (le_div_iff₀ hα).mpr (by nlinarith)
  calc
    _ ≤ 3 * v i S := htotal
    _ ≤ 3 * (v i (roundRobin σ i) / α) := mul_le_mul_of_nonneg_left hval (by norm_num)
    _ = _ := by ring

#print axioms solution

end AcceptedClosing
open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)
open AcceptedClosing.CheckedInequality.AcceptedParity.AcceptedWindow.AllocationWindow

namespace RootAssembly
variable {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]

lemma mem_alloc_iff (σ : Fin n → List M) (g : M) (t : ℕ) :
    g ∈ allocBefore σ t ↔ ∃ s < t, pick σ s = some g := by
  constructor
  · intro hg
    induction t with
    | zero => simpa [allocBefore] using hg
    | succ t ih =>
      change g ∈ (match pick σ t with
        | some a => insert a (allocBefore σ t)
        | none => allocBefore σ t) at hg
      cases hp : pick σ t with
      | none =>
        rw [hp] at hg
        obtain ⟨s,hs,hp⟩ := ih hg
        exact ⟨s,by omega,hp⟩
      | some a =>
        rw [hp] at hg
        rcases Finset.mem_insert.mp hg with he | hg
        · subst a; exact ⟨t,by omega,hp⟩
        · obtain ⟨s,hs,hp⟩ := ih hg
          exact ⟨s,by omega,hp⟩
  · rintro ⟨s,hs,hp⟩
    exact alloc_mono σ (by omega : s+1 ≤ t) (pick_mem_next σ s g hp)

lemma pick_time_unique (σ : Fin n → List M) (s t : ℕ) (g : M)
    (hs : pick σ s = some g) (ht : pick σ t = some g) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (pick_fresh σ t g ht ((mem_alloc_iff σ g t).mpr ⟨s,h,hs⟩))
  · exact h
  · exact False.elim (pick_fresh σ s g hs ((mem_alloc_iff σ g s).mpr ⟨t,h,ht⟩))

lemma alloc_card_eq (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : ℕ) (ht : t ≤ Fintype.card M) : (allocBefore σ t).card = t := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    have ht' : t < Fintype.card M := by omega
    obtain ⟨g,hg⟩ := AcceptedClosing.ClosingSupport.pick_exists σ hσ t ht'
    change (match pick σ t with
      | some a => insert a (allocBefore σ t)
      | none => allocBefore σ t).card = t+1
    rw [hg,Finset.card_insert_of_notMem (pick_fresh σ t g hg),ih (by omega)]

lemma time_enum_exists [Nonempty M] (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (A : Finset M) (k : ℕ) (hcard : A.card = k) :
    ∃ y : ℕ → M, IsTimeOrderedEnum σ A k y := by
  classical
  have hall : allocBefore σ (Fintype.card M) = Finset.univ :=
    Finset.eq_univ_of_card _ (alloc_card_eq σ hσ _ le_rfl)
  have hex : ∀ g : M, ∃ t < Fintype.card M, pick σ t = some g := by
    intro g
    apply (mem_alloc_iff σ g _).mp
    rw [hall]; exact Finset.mem_univ g
  let time : M → ℕ := fun g => Classical.choose (hex g)
  have htime : ∀ g, time g < Fintype.card M ∧ pick σ (time g) = some g :=
    fun g => Classical.choose_spec (hex g)
  have hinj : Function.Injective time := by
    intro a b hab
    have ha := (htime a).2
    rw [hab,(htime b).2] at ha
    exact (Option.some.inj ha).symm
  have hbefore : ∀ g t, g ∈ allocBefore σ t ↔ time g < t := by
    intro g t
    constructor
    · intro hg
      obtain ⟨s,hs,hsg⟩ := (mem_alloc_iff σ g t).mp hg
      have he := pick_time_unique σ s (time g) g hsg (htime g).2
      omega
    · intro h; exact (mem_alloc_iff σ g t).mpr ⟨time g,h,(htime g).2⟩
  let R : M → M → Prop := fun a b => time a ≤ time b
  letI : DecidableRel R := fun a b => inferInstanceAs (Decidable (time a ≤ time b))
  letI : IsTrans M R := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  letI : Std.Antisymm R := ⟨fun _ _ h1 h2 => hinj (le_antisymm h1 h2)⟩
  letI : Std.Total R := ⟨fun _ _ => le_total _ _⟩
  let l := A.sort R
  have hlen : l.length = k := (Finset.length_sort R).trans hcard
  let y : ℕ → M := fun a => if h : a < k then l.get ⟨a,by omega⟩ else Classical.ofNonempty
  refine ⟨y,?_,?_,?_⟩
  · ext g
    constructor
    · rintro hg
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
      have hak := Finset.mem_range.mp ha
      simp only [y,dif_pos hak]
      exact (Finset.mem_sort R).mp (List.get_mem _ _)
    · intro hg
      have hgl : g ∈ l := (Finset.mem_sort R).mpr hg
      obtain ⟨a,ha⟩ := List.mem_iff_get.mp hgl
      have hak : a.val < k := by simpa [hlen] using a.isLt
      exact Finset.mem_image.mpr ⟨a.val,Finset.mem_range.mpr hak,by simpa only [y,dif_pos hak] using ha⟩
  · intro a ha b hb he
    have hak := Finset.mem_range.mp ha
    have hbk := Finset.mem_range.mp hb
    simp only [y,dif_pos hak,dif_pos hbk] at he
    have hi := (Finset.sort_nodup A R).injective_get he
    exact congrArg Fin.val hi
  · intro a b hab hbk t hbt
    have hak : a < k := by omega
    have hsorted := (Finset.pairwise_sort A R).rel_get_of_lt
      (show (⟨a,by omega⟩ : Fin l.length) < ⟨b,by omega⟩ from hab)
    have hkey : time (y a) ≤ time (y b) := by
      simpa only [y,dif_pos hak,dif_pos hbk] using hsorted
    exact (hbefore _ _).mpr (lt_of_le_of_lt hkey ((hbefore _ _).mp hbt))

lemma bundle_card [Nonempty M] (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (i : Fin n) (k : ℕ) (hm : Fintype.card M = k*n) : (roundRobin σ i).card = k := by
  obtain ⟨x,hx⟩ := AcceptedClosing.ClosingSupport.response_sequence σ hσ i k hm
  rw [AcceptedClosing.ClosingSupport.final_bundle σ i x k hm hx]
  rw [Finset.card_image_of_injOn,Finset.card_range]
  intro a ha b hb he
  have hab : a*n+i.val = b*n+i.val := pick_time_unique σ _ _ (x a)
    (hx a (Finset.mem_range.mp ha)) (by rw [he]; exact hx b (Finset.mem_range.mp hb))
  have hn := NeZero.pos n
  nlinarith

lemma conditional_root (k : ℕ) (hm : Fintype.card M = k*n)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ) (hv : ∀ i, IsValuation (v i)) (hsub : ∀ i, IsSubmodular (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ)
    (hgreedy : ∀ i, ∃ τ, IsGreedyResponse (v i) σ i τ) :
    IsApproxEF1 (α/3) v (roundRobin σ) := by
  classical
  intro i j hAj
  letI : Nonempty M := ⟨hAj.choose⟩
  by_cases hji : j = i
  · subst j
    obtain ⟨g,hg⟩ := hAj
    refine ⟨g,hg,?_⟩
    have hmono := (hv i).2 _ _ (Finset.erase_subset g (roundRobin σ i))
    have hnonneg : 0 ≤ v i ((roundRobin σ i).erase g) := by
      have hh := (hv i).2 ∅ ((roundRobin σ i).erase g) (Finset.empty_subset _)
      rw [(hv i).1] at hh; exact hh
    nlinarith
  · obtain ⟨τ,hτ⟩ := hgreedy i
    have hσ' : ∀ ℓ, IsRanking ((Function.update σ i τ) ℓ) := by
      intro ℓ
      by_cases h : ℓ = i
      · subst ℓ; simpa using hτ.1
      · simpa [Function.update_of_ne h] using hσ.1 ℓ
    have hcard := bundle_card σ hσ.1 j k hm
    obtain ⟨y,hy⟩ := time_enum_exists (Function.update σ i τ) hσ' (roundRobin σ j) k hcard
    have hk : 0 < k := by rw [← hcard]; exact Finset.card_pos.mpr hAj
    have hy0 : y 0 ∈ roundRobin σ j := by
      rw [← hy.1]; exact Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr hk,rfl⟩
    refine ⟨y 0,hy0,?_⟩
    have hclose := AcceptedClosing.solution k hm α hα hα1 v hv hsub σ hσ i j hji τ hτ y hy
    have hmultiply := mul_le_mul_of_nonneg_left hclose hα.le
    field_simp [ne_of_gt hα] at hmultiply
    nlinarith

end RootAssembly

theorem conditional_solution : ∀ {n : ℕ} [inst : NeZero n] {M : Type} [inst_1 : Fintype M] [inst_2 : DecidableEq M] (k : ℕ),
  Fintype.card M = k * n →
    ∀ (α : ℝ),
      OfNat.ofNat 0 < α →
        α ≤ OfNat.ofNat 1 →
          ∀ (v : Fin n → Finset M → ℝ),
            (∀ (i : Fin n), RoundRobinEq.SubmodularEF1.IsValuation (v i)) →
              (∀ (i : Fin n), RoundRobinEq.SubmodularEF1.IsSubmodular (v i)) →
                ∀ (σ : Fin n → List M),
                  RoundRobinEq.SubmodularEF1.IsApproxPNE α v σ →
                    (∀ (i : Fin n), ∃ (τ : List M), RoundRobinEq.SubmodularEF1.IsGreedyResponse (v i) σ i τ) →
                      RoundRobinEq.SubmodularEF1.IsApproxEF1 (α / OfNat.ofNat 3) v
                        (RoundRobinEq.SubmodularEF1.roundRobin σ) := @RootAssembly.conditional_root

open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)
namespace GreedyExistence
variable {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]

lemma choice_exists (vi : Finset M → ℝ) (σ : Fin n → List M)
    (hσ : ∀ j, IsRanking (σ j)) (i : Fin n) (A B : Finset M) (t : ℕ)
    (hA : (Finset.univ \ A).Nonempty) :
    ∃ g : M, g ∉ A ∧
      (agentAt n t = i → ∀ h : M, h ∉ A → marginal vi {h} B ≤ marginal vi {g} B) ∧
      (agentAt n t ≠ i → top (σ (agentAt n t)) (Finset.univ \ A) = some g) := by
  classical
  by_cases hi : agentAt n t = i
  · obtain ⟨g,hg,hmax⟩ := (Finset.univ \ A).exists_max_image (fun g => marginal vi {g} B) hA
    refine ⟨g,(Finset.mem_sdiff.mp hg).2,?_,by simp [hi]⟩
    intro _ h hh
    exact hmax h (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hh⟩)
  · cases hg : top (σ (agentAt n t)) (Finset.univ \ A) with
    | some g =>
      have hmem : g ∈ Finset.univ \ A := by
        have hh := List.find?_some hg
        simpa only [decide_eq_true_eq] using hh
      exact ⟨g,(Finset.mem_sdiff.mp hmem).2,by simp [hi],fun _ => rfl⟩
    | none =>
      obtain ⟨g,hgmem⟩ := hA
      have hh := List.find?_eq_none.mp hg g ((hσ (agentAt n t)).2 g)
      simp [hgmem] at hh

noncomputable def choose [Nonempty M] (vi : Finset M → ℝ) (σ : Fin n → List M)
    (hσ : ∀ j, IsRanking (σ j)) (i : Fin n) (A B : Finset M) (t : ℕ) : M :=
  if hA : (Finset.univ \ A).Nonempty then Classical.choose (choice_exists vi σ hσ i A B t hA)
  else Classical.ofNonempty

lemma choose_spec [Nonempty M] (vi : Finset M → ℝ) (σ : Fin n → List M)
    (hσ : ∀ j, IsRanking (σ j)) (i : Fin n) (A B : Finset M) (t : ℕ)
    (hA : (Finset.univ \ A).Nonempty) :
    let g := choose vi σ hσ i A B t
    g ∉ A ∧ (agentAt n t = i → ∀ h : M, h ∉ A → marginal vi {h} B ≤ marginal vi {g} B) ∧
      (agentAt n t ≠ i → top (σ (agentAt n t)) (Finset.univ \ A) = some g) := by
  simpa only [choose,dif_pos hA] using Classical.choose_spec (choice_exists vi σ hσ i A B t hA)

noncomputable def state [Nonempty M] (vi : Finset M → ℝ) (σ : Fin n → List M)
    (hσ : ∀ j, IsRanking (σ j)) (i : Fin n) : ℕ → Finset M × Finset M
  | 0 => (∅,∅)
  | t+1 =>
    let S := state vi σ hσ i t
    let g := choose vi σ hσ i S.1 S.2 t
    (insert g S.1, if agentAt n t = i then insert g S.2 else S.2)

noncomputable def dynPick [Nonempty M] (vi : Finset M → ℝ) (σ : Fin n → List M)
    (hσ : ∀ j, IsRanking (σ j)) (i : Fin n) (t : ℕ) : M :=
  choose vi σ hσ i (state vi σ hσ i t).1 (state vi σ hσ i t).2 t

section Nonempty
variable [Nonempty M] (vi : Finset M → ℝ) (σ : Fin n → List M)
  (hσ : ∀ j, IsRanking (σ j)) (i : Fin n)

lemma first_image (t : ℕ) :
    (state vi σ hσ i t).1 = (Finset.range t).image (dynPick vi σ hσ i) := by
  induction t with
  | zero => simp [state]
  | succ t ih =>
    rw [Finset.range_add_one,Finset.image_insert]
    change insert (dynPick vi σ hσ i t) (state vi σ hσ i t).1 = _
    rw [ih]

lemma second_image (t : ℕ) :
    (state vi σ hσ i t).2 = ((Finset.range t).filter (fun s => agentAt n s = i)).image (dynPick vi σ hσ i) := by
  induction t with
  | zero => simp [state]
  | succ t ih =>
    rw [Finset.range_add_one,Finset.filter_insert]
    change (if agentAt n t = i then insert (dynPick vi σ hσ i t) (state vi σ hσ i t).2 else (state vi σ hσ i t).2) = _
    by_cases hi : agentAt n t = i
    · simp only [hi,if_pos,Finset.image_insert,ih]
    · simp [hi,ih]

lemma first_card (t : ℕ) (ht : t ≤ Fintype.card M) : (state vi σ hσ i t).1.card = t := by
  induction t with
  | zero => simp [state]
  | succ t ih =>
    have hc := ih (by omega)
    have hA : (Finset.univ \ (state vi σ hσ i t).1).Nonempty := by
      apply Finset.sdiff_nonempty.mpr
      intro hsub
      have hh := Finset.card_le_card hsub
      rw [Finset.card_univ,hc] at hh
      omega
    have hs := choose_spec vi σ hσ i (state vi σ hσ i t).1 (state vi σ hσ i t).2 t hA
    change (insert (dynPick vi σ hσ i t) (state vi σ hσ i t).1).card = t+1
    rw [Finset.card_insert_of_notMem (show dynPick vi σ hσ i t ∉ (state vi σ hσ i t).1 from hs.1),hc]

lemma step_spec (t : ℕ) (ht : t < Fintype.card M) :
    let g := dynPick vi σ hσ i t
    g ∉ (state vi σ hσ i t).1 ∧
      (agentAt n t = i → ∀ h : M, h ∉ (state vi σ hσ i t).1 →
        marginal vi {h} (state vi σ hσ i t).2 ≤ marginal vi {g} (state vi σ hσ i t).2) ∧
      (agentAt n t ≠ i → top (σ (agentAt n t)) (Finset.univ \ (state vi σ hσ i t).1) = some g) := by
  apply choose_spec
  apply Finset.sdiff_nonempty.mpr
  intro hsub
  have hh := Finset.card_le_card hsub
  rw [Finset.card_univ,first_card vi σ hσ i t ht.le] at hh
  omega

lemma picks_injective : Function.Injective (fun t : Fin (Fintype.card M) => dynPick vi σ hσ i t) := by
  intro a b he
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hab | hba
  · have hf := (step_spec vi σ hσ i b b.isLt).1
    apply hf
    rw [first_image]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr hab,he⟩
  · have hf := (step_spec vi σ hσ i a a.isLt).1
    apply hf
    rw [first_image]
    exact Finset.mem_image.mpr ⟨b,Finset.mem_range.mpr hba,he.symm⟩

noncomputable def ranking : List M := List.ofFn (fun t : Fin (Fintype.card M) => dynPick vi σ hσ i t)

lemma ranking_valid : IsRanking (ranking vi σ hσ i) := by
  constructor
  · exact List.nodup_ofFn.mpr (picks_injective vi σ hσ i)
  · intro g
    have hsurj := (Fintype.bijective_iff_injective_and_card (f := fun t : Fin (Fintype.card M) => dynPick vi σ hσ i t)).mpr ⟨picks_injective vi σ hσ i,by simp⟩
    obtain ⟨t,ht⟩ := hsurj.2 g
    exact List.mem_ofFn.mpr ⟨t,ht⟩

lemma ranking_top (t : ℕ) (ht : t < Fintype.card M) :
    top (ranking vi σ hσ i) (Finset.univ \ (state vi σ hσ i t).1) = some (dynPick vi σ hσ i t) := by
  apply List.find?_ofFn_eq_some.mpr
  constructor
  · simpa using (step_spec vi σ hσ i t ht).1
  · refine ⟨⟨t,ht⟩,rfl,?_⟩
    intro j hj
    have hmem : dynPick vi σ hσ i j ∈ (state vi σ hσ i t).1 := by
      rw [first_image]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩
    simpa using hmem

end Nonempty
end GreedyExistence

open RoundRobinEq.SubmodularEF1
open RoundRobinEq.CancelableBluff (agentAt)
namespace GreedyExistence
variable {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
section Nonempty
variable [Nonempty M] (vi : Finset M → ℝ) (σ : Fin n → List M)
  (hσ : ∀ j, IsRanking (σ j)) (i : Fin n)

lemma prefix_alloc (σ' : Fin n → List M) (t : ℕ)
    (h : ∀ s < t, pick σ' s = some (dynPick vi σ hσ i s)) :
    allocBefore σ' t = (state vi σ hσ i t).1 := by
  ext g
  rw [RootAssembly.mem_alloc_iff,first_image,Finset.mem_image]
  constructor
  · rintro ⟨s,hs,hp⟩
    exact ⟨s,Finset.mem_range.mpr hs,Option.some.inj ((h s hs).symm.trans hp)⟩
  · rintro ⟨s,hs,he⟩
    exact ⟨s,Finset.mem_range.mp hs,(h s (Finset.mem_range.mp hs)).trans (congrArg some he)⟩

lemma prefix_bundle (σ' : Fin n → List M) (t : ℕ)
    (h : ∀ s < t, pick σ' s = some (dynPick vi σ hσ i s)) :
    bundleBefore σ' i t = (state vi σ hσ i t).2 := by
  rw [second_image]
  ext g
  constructor
  · intro hg
    obtain ⟨s,hs,hg⟩ := Finset.mem_biUnion.mp hg
    have hst := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hp : pick σ' s = some g := by simpa using hg
    exact Finset.mem_image.mpr ⟨s,hs,Option.some.inj ((h s hst).symm.trans hp)⟩
  · intro hg
    obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hg
    apply Finset.mem_biUnion.mpr
    refine ⟨s,hs,?_⟩
    have hst := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    simp [h s hst,he]

lemma follows (t : ℕ) (ht : t < Fintype.card M) :
    pick (Function.update σ i (ranking vi σ hσ i)) t = some (dynPick vi σ hσ i t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have hprev : ∀ s < t, pick (Function.update σ i (ranking vi σ hσ i)) s = some (dynPick vi σ hσ i s) := by
      intro s hs
      exact ih s hs (lt_trans hs ht)
    have halloc := prefix_alloc vi σ hσ i (Function.update σ i (ranking vi σ hσ i)) t hprev
    unfold pick
    rw [halloc]
    by_cases hai : agentAt n t = i
    · simpa [hai] using ranking_top vi σ hσ i t ht
    · rw [Function.update_of_ne hai]
      exact (step_spec vi σ hσ i t ht).2.2 hai

lemma greedy_ranking : IsGreedyResponse vi σ i (ranking vi σ hσ i) := by
  refine ⟨ranking_valid vi σ hσ i,?_⟩
  intro t ht hai g hpg h hh
  have hprev : ∀ s < t, pick (Function.update σ i (ranking vi σ hσ i)) s = some (dynPick vi σ hσ i s) := by
    intro s hs
    exact follows vi σ hσ i s (lt_trans hs ht)
  have ha := prefix_alloc vi σ hσ i (Function.update σ i (ranking vi σ hσ i)) t hprev
  have hb := prefix_bundle vi σ hσ i (Function.update σ i (ranking vi σ hσ i)) t hprev
  have hg : dynPick vi σ hσ i t = g := Option.some.inj ((follows vi σ hσ i t ht).symm.trans hpg)
  rw [ha] at hh
  rw [hb,← hg]
  exact (step_spec vi σ hσ i t ht).2.1 hai h hh

end Nonempty

lemma exists_greedy (vi : Finset M → ℝ) (σ : Fin n → List M)
    (hσ : ∀ j, IsRanking (σ j)) (i : Fin n) : ∃ τ, IsGreedyResponse vi σ i τ := by
  classical
  by_cases he : Fintype.card M = 0
  · letI : IsEmpty M := Fintype.card_eq_zero_iff.mp he
    exact ⟨[],by simp [IsGreedyResponse,IsRanking,he]⟩
  · letI : Nonempty M := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero he)
    exact ⟨ranking vi σ hσ i,greedy_ranking vi σ hσ i⟩

end GreedyExistence

/-- Complete Theorem4.4, with greedy-response existence constructed above. -/
theorem solution {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ) (hv : ∀ i, IsValuation (v i)) (hsub : ∀ i, IsSubmodular (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ) :
    IsApproxEF1 (α / 3) v (roundRobin σ) := by
  apply RootAssembly.conditional_root k hm α hα hα1 v hv hsub σ hσ
  intro i
  exact GreedyExistence.exists_greedy (v i) σ hσ.1 i
