-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.shortest_distance_preserved_if_path_survives
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:06:03.883204+00:00
-- url     : https://prove2.me/submissions/db027e15-e666-4f94-aebd-8438c31a7951

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem walk_mono {α : Type} {arc arc' : α → α → Prop}
    (hsub : ∀ a b, arc' a b → arc a b) {n : ℕ} {a b : α}
    (hw : WalkLength arc' n a b) : WalkLength arc n a b := by
  induction hw with
  | zero => exact WalkLength.zero _
  | step hab hw ih => exact WalkLength.step (hsub _ _ hab) ih

theorem solution {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (G G' : Instance Γ V)
    (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (root target : Literal V) (n : ℕ)
    (hd : implicationDistance rep G root target = some n)
    (hw : WalkLength (implicationArc rep G') n root target) :
    implicationDistance rep G' root target = some n := by
  have hr' : ∃ m, WalkLength (implicationArc rep G') m root target := ⟨n,hw⟩
  have hr : ∃ m, WalkLength (implicationArc rep G) m root target := ⟨n,walk_mono hsub hw⟩
  have hn : Nat.find hr = n := by simpa [implicationDistance,hr] using hd
  have hle1 : Nat.find hr' ≤ n := Nat.find_min' hr' hw
  have hle2 : n ≤ Nat.find hr' := by
    rw [← hn]
    exact Nat.find_min' hr (walk_mono hsub (Nat.find_spec hr'))
  have heq : Nat.find hr' = n := Nat.le_antisymm hle1 hle2
  simp [implicationDistance,hr',heq]
