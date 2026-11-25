-- Prove2me | solution 1 for SinkReset.Plan.path_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:14.678006+00:00
-- url     : https://prove2.me/submissions/67616bb2-3318-4e29-979a-d056c57e7875

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_wins_of_rank
public import Theorems.Thm_SinkReset_Plan_path_action
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
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
theorem _root_.solution {n k : ℕ} [NeZero n] (hk : 1 ≤ k) :
    (path n).IsAk k ∧
    (∃ w, (path n).IsReset w ∧ w.length = n - 1) ∧
    ∀ w, (path n).IsReset w → n - 1 ≤ w.length := by
  have hpred : predecessor n ∈ (path n).letters := rfl
  have hwr : (path n).IsWord (List.replicate (n - 1) (predecessor n)) := by
    intro a ha
    rw [List.mem_replicate] at ha
    rw [ha.2]; exact hpred
  refine ⟨?_, ⟨List.replicate (n - 1) (predecessor n), ⟨hwr, fun q => ?_⟩, by simp⟩, ?_⟩
  · refine wins_of_rank _ (fun S => ∑ q ∈ S, q.val) (fun S hS => ?_) Finset.univ
    refine ⟨predecessor n, hpred, fun u hu hlen => ?_⟩
    have hu' : (path n).IsWord (predecessor n :: u) := (word_cons _).2 ⟨hpred, hu⟩
    obtain ⟨q₀, hq₀⟩ := hS
    have hq₀' : q₀ ∈ S.erase 0 := hq₀
    calc ∑ x ∈ S.image (act (predecessor n :: u)), x.val ≤ ∑ q ∈ S, (act (predecessor n :: u) q).val :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ < ∑ q ∈ S, q.val := by
          refine Finset.sum_lt_sum (fun q _ => by rw [path_action _ hu']; omega)
            ⟨q₀, (Finset.mem_erase.1 hq₀').2, ?_⟩
          rw [path_action _ hu']
          have : q₀.val ≠ 0 := fun h => (Finset.mem_erase.1 hq₀').1 (Fin.ext (by simpa using h))
          simp only [List.length_cons]
          omega
  · apply Fin.ext
    have := q.isLt
    rw [path_action _ hwr, List.length_replicate]
    simp only [Fin.val_zero]
    omega
  · rintro w ⟨hw, hw0⟩
    have := path_action w hw ⟨n - 1, by have := NeZero.ne n; omega⟩
    rw [hw0] at this
    simp at this
    omega
end SinkReset.Plan
