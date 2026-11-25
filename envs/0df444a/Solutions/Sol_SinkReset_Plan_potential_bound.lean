-- Prove2me | solution 1 for SinkReset.Plan.potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:52.505396+00:00
-- url     : https://prove2.me/submissions/6ed4fc24-0b2f-4c53-947d-7e615e0142fc

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem act_nil (q : Fin n) : act ([] : List (Letter n)) q = q := rfl
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
private theorem potential_bound' {n : ℕ} [NeZero n] (A : Automaton n) (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image a, weight q + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    ∑ q, weight q ≤ w.length := by
  classical
  have key : ∀ (w : List (Letter n)), A.IsWord w → ∀ S : Finset (Fin n),
      ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image (act w), weight q + w.length := by
    intro w
    induction w with
    | nil =>
      intro _ S
      have : S.image (act ([] : List (Letter n))) = S := by ext; simp [act_nil]
      rw [this]; simp
    | cons a w ih =>
      intro hw S
      rw [word_cons] at hw
      have h1 := hstep a hw.1 S
      have h2 := ih hw.2 (S.image a)
      rw [Finset.image_image] at h2
      have : (act w ∘ a) = act (a :: w) := rfl
      rw [this] at h2
      simp only [List.length_cons]
      omega
  have := key w hw.1 Finset.univ
  have h0 : ∑ q ∈ Finset.univ.image (act w), weight q = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hx
    rw [hw.2 q, hzero]
  omega
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
theorem _root_.solution {n : ℕ} [NeZero n] (A : Automaton n)
    (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      potential weight S ≤ potential weight (S.image a) + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    potential weight Finset.univ ≤ w.length :=
  potential_bound' A weight hzero hstep w hw
end SinkReset.Plan
