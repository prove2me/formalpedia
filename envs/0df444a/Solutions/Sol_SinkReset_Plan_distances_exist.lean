-- Prove2me | solution 1 for SinkReset.Plan.distances_exist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:35.835969+00:00
-- url     : https://prove2.me/submissions/904182f6-a7e3-4db9-8edc-4874a958fb63

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem dist_exists {n : ℕ} [NeZero n] (A : Automaton n) (h : ∀ q, ∃ w, A.IsWord w ∧ act w q = 0) :
    ∃ d : Fin n → ℕ, ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length := by
  classical
  have hP : ∀ q, ∃ ℓ, ∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = ℓ := fun q => by
    obtain ⟨w, hw, hw0⟩ := h q
    exact ⟨_, w, hw, hw0, rfl⟩
  refine ⟨fun q => Nat.find (hP q), fun q => ⟨Nat.find_spec (hP q), fun w hw hw0 => ?_⟩⟩
  exact Nat.find_min' (hP q) ⟨w, hw, hw0, rfl⟩
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
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (h : ∃ w, A.IsReset w) :
    ∃ d, Distances A d := by
  obtain ⟨w, hw, hw0⟩ := h
  exact dist_exists A fun q => ⟨w, hw, hw0 q⟩
end SinkReset.Plan
