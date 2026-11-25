-- Prove2me | solution 1 for SinkReset.Plan.wins_push
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:21.99702+00:00
-- url     : https://prove2.me/submissions/d6856cd0-5f51-4d4e-adbf-686dcea7582d

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
private theorem push_act (φ : Fin n → Fin m)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    (u : List (Letter n)) (hu : A.IsWord u) (q : Fin n) :
    φ (act u q) = act (u.map τ) (φ q) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have ha : a ∈ A.letters := hu a List.mem_cons_self
    change φ (act u (a q)) = act (u.map τ) (τ a (φ q))
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
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin n → Fin m) (hzero : φ 0 = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    {k : ℕ} {S : Finset (Fin n)} (h : A.AliceWins k S) :
    B.AliceWins k (S.image φ) := by
  induction h with
  | reset S hS =>
    refine .reset _ fun q hq => ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    rw [hS p hp, hzero]
  | step S a ha _ ih =>
    refine .step _ (τ a) ((hletters _).2 ⟨a, ha, rfl⟩) fun v hv hlen => ?_
    obtain ⟨u, hu, rfl, hlen'⟩ := lift_word A B τ hletters v hv
    have hu' : A.IsWord (a :: u) := fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ha
      · exact hu c hc
    have key := ih u hu (hlen' ▸ hlen)
    rw [Finset.image_image] at key ⊢
    convert key using 2
    funext q
    simp only [Function.comp]
    rw [push_act A τ φ hcomm (a :: u) hu' q]
    rfl
end SinkReset.Plan
