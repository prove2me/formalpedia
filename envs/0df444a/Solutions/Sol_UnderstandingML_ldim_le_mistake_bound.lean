-- Prove2me | solution 1 for UnderstandingML.ldim_le_mistake_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:31:51.753735+00:00
-- url     : https://prove2.me/submissions/82a3b6ac-85af-4edf-9ec6-85ad9d2a0ed6


import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section Adversary

variable {X : Type*}

theorem take_ofFn_eq {α : Type*} {n : ℕ} (f : Fin n → α) (t : ℕ) (ht : t ≤ n) :
    (List.ofFn f).take t = List.ofFn (fun j : Fin t ↦ f ⟨j, lt_of_lt_of_le j.2 ht⟩) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp

/-- The adversary of Lemma 21.6 walking down a tree `v`: the state after `n` rounds is the
path `(y₁, …, yₙ)` taken so far together with the history `((x₁, y₁), …, (xₙ, yₙ))`, where
`xₜ` is the node at the current path and `yₜ` is the opposite of `A`'s prediction. -/
noncomputable def advState (A : OnlineAlg X Bool) (v : List Bool → X) :
    ℕ → List Bool × List (X × Bool)
  | 0 => ([], [])
  | n + 1 =>
    ((advState A v n).1 ++ [!(A (advState A v n).2 (v (advState A v n).1))],
      (advState A v n).2 ++
        [(v (advState A v n).1, !(A (advState A v n).2 (v (advState A v n).1)))])

/-- The adversarial label at round `n`: the opposite of the algorithm's prediction. -/
noncomputable def advLabel (A : OnlineAlg X Bool) (v : List Bool → X) (n : ℕ) : Bool :=
  !(A (advState A v n).2 (v (advState A v n).1))

theorem advState_fst (A : OnlineAlg X Bool) (v : List Bool → X) (n : ℕ) :
    (advState A v n).1 = List.ofFn (fun j : Fin n ↦ advLabel A v j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    rfl

theorem advState_snd (A : OnlineAlg X Bool) (v : List Bool → X) (n : ℕ) :
    (advState A v n).2 =
      List.ofFn (fun j : Fin n ↦ (v (advState A v j).1, advLabel A v j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    rfl

/-- Every tree of depth `d` shattered by `H` forces `d` mistakes on any algorithm. -/
theorem le_mistakeBound_of_shatters (H : Set (X → Bool)) (A : OnlineAlg X Bool) (d : ℕ)
    (v : List Bool → X) (hv : ShattersTree H d v) : (d : ℕ∞) ≤ mistakeBound A H := by
  obtain ⟨h, hH, hh⟩ := hv (fun t ↦ advLabel A v t)
  have hh' : ∀ t : Fin d, h (v (advState A v t).1) = advLabel A v t := by
    intro t
    rw [advState_fst]
    exact hh t
  set x : Fin d → X := fun t ↦ v (advState A v t).1 with hx
  have hmis : mistakes A (fun t ↦ (x t, h (x t))) = d := by
    unfold mistakes
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro t _
    have hhist : history (fun t ↦ (x t, h (x t))) t = (advState A v t).2 := by
      unfold history
      rw [take_ofFn_eq _ t (le_of_lt t.2), advState_snd]
      congr 1
      funext j
      simp only [hx]
      rw [hh' ⟨j, lt_trans j.2 t.2⟩]
    simp only
    rw [hhist, hh' t]
    unfold advLabel
    simp [hx]
  calc (d : ℕ∞) = (mistakes A (fun t ↦ (x t, h (x t))) : ℕ∞) := by rw [hmis]
    _ ≤ mistakeBound A H := by
      unfold mistakeBound
      exact le_iSup_of_le d (le_iSup_of_le x (le_iSup_of_le h (le_iSup_of_le hH le_rfl)))

theorem ldim_le_mistake_bound_main {X : Type*} (H : Set (X → Bool)) (A : OnlineAlg X Bool) :
    ldim H ≤ mistakeBound A H := by
  unfold ldim
  refine iSup₂_le fun d hd ↦ ?_
  obtain ⟨v, hv⟩ := hd
  exact le_mistakeBound_of_shatters H A d v hv

end Adversary

end UnderstandingML

open UnderstandingML

theorem solution {X : Type*} (H : Set (X → Bool)) (A : OnlineAlg X Bool) :
    ldim H ≤ mistakeBound A H := by
  apply UnderstandingML.ldim_le_mistake_bound_main <;> assumption
