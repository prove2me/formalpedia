-- Prove2me | solution 1 for SinkReset.Plan.wins_pull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:26.77587+00:00
-- url     : https://prove2.me/submissions/87ff3ce9-7a75-41c7-93b2-12af60d70509

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_lift_word
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
private theorem pull_act (φ : Fin m → Fin n)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    (u : List (Letter n)) (hu : A.IsWord u) (q : Fin m) :
    φ (act (u.map τ) q) = act u (φ q) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have ha : a ∈ A.letters := hu a List.mem_cons_self
    change φ (act (u.map τ) (τ a q)) = act u (a (φ q))
    rw [ih (fun c hc => hu c (List.mem_cons_of_mem _ hc)), hcomm a ha]
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
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
namespace SinkReset.Plan
theorem _root_.solution
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin m → Fin n) (hzero : ∀ q, φ q = 0 ↔ q = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    {k : ℕ} (S : Finset (Fin m)) (h : A.AliceWins k (S.image φ)) :
    B.AliceWins k S := by
  suffices H : ∀ X, A.AliceWins k X → ∀ S : Finset (Fin m), S.image φ ⊆ X → B.AliceWins k S from
    H _ h S subset_rfl
  intro X hX
  induction hX with
  | reset X hX =>
    intro S hS
    exact .reset S fun q hq => (hzero q).1 (hX _ (hS (Finset.mem_image_of_mem _ hq)))
  | step X a ha _ ih =>
    intro S hS
    refine .step _ (τ a) ((hletters _).2 ⟨a, ha, rfl⟩) fun v hv hlen => ?_
    obtain ⟨u, hu, rfl, hlen'⟩ := lift_word A B τ hletters v hv
    have hu' : A.IsWord (a :: u) := fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ha
      · exact hu c hc
    refine ih u hu (hlen' ▸ hlen) _ ?_
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨q, ⟨p, hp, rfl⟩, rfl⟩ := hx
    have := pull_act A τ φ hcomm (a :: u) hu' p
    simp only [List.map_cons] at this
    rw [this]
    exact Finset.mem_image_of_mem _ (hS (Finset.mem_image_of_mem _ hp))
end SinkReset.Plan
