-- Prove2me | solution 1 for SinkReset.Plan.transposition_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:55.820778+00:00
-- url     : https://prove2.me/submissions/f419a885-f167-4a59-9b6c-27e19ccf08e6

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
private theorem pot_perm {n : ℕ} (weight : Fin n → ℕ) (g : Fin n → Fin n) (hg : Function.Injective g)
    (p : Fin n) (hle : ∀ q, q ≠ p → weight q ≤ weight (g q)) (hp : weight p ≤ weight (g p) + 1)
    (S : Finset (Fin n)) :
    ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image g, weight q + 1 := by
  classical
  rw [Finset.sum_image (fun x _ y _ h => hg h)]
  calc ∑ q ∈ S, weight q ≤ ∑ q ∈ S, (weight (g q) + if q = p then 1 else 0) :=
        Finset.sum_le_sum fun q _ => by
          by_cases h : q = p
          · subst h; simpa using hp
          · simpa [h] using hle q h
    _ = ∑ q ∈ S, weight (g q) + ∑ q ∈ S, (if q = p then 1 else 0) := Finset.sum_add_distrib
    _ ≤ ∑ q ∈ S, weight (g q) + 1 := by
        refine Nat.add_le_add_left ?_ _
        rw [Finset.sum_ite_eq']
        split_ifs <;> simp
private theorem pot_kill {n : ℕ} (weight : Fin n → ℕ) (g : Fin n → Fin n) (p : Fin n)
    (hfix : ∀ q, q ≠ p → g q = q) (hp : weight p ≤ 1) (S : Finset (Fin n)) :
    ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image g, weight q + 1 := by
  classical
  have hsub : S.erase p ⊆ S.image g := fun q hq => by
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_image.2 ⟨q, hq, hfix q hqp⟩
  have h1 := Finset.sum_le_sum_of_subset (f := weight) hsub
  by_cases hpS : p ∈ S
  · rw [← Finset.add_sum_erase S weight hpS]; omega
  · rw [Finset.erase_eq_of_notMem hpS] at h1; omega
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Letter n) (ha : a ∈ (transposition n).letters) (S : Finset (Fin n)) :
    potential Fin.val S ≤ potential Fin.val (S.image a) + 1 := by
  have h1 : (1 : Fin n).val = 1 := by
    show 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  unfold potential
  rcases ha with h | ⟨i, j, hi, hj, rfl⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    refine pot_kill _ (kill 1) 1 (fun q hq => ?_) (by rw [h1]) S
    simp [kill, hq]
  · refine pot_perm _ _ (Equiv.injective _) j (fun q hq => ?_) ?_ S
    · by_cases hqi : q = i
      · subst hqi; simp [Equiv.swap_apply_left]; omega
      · simp [Equiv.swap_apply_of_ne_of_ne hqi hq]
    · simp [Equiv.swap_apply_right]; omega
end SinkReset.Plan
