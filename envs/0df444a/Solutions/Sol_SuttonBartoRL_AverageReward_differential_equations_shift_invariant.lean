-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.differential_equations_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:00:18.285403+00:00
-- url     : https://prove2.me/submissions/414d93cb-a5a3-40ae-9e84-b53a120ac90f

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

namespace SuttonBartoRL.AverageReward.ShiftAux04dd

lemma pol_sum_add {S A : Type} [Fintype A] (π : SuttonBartoRL.FiniteMDP.Policy S A)
    (s : S) (f : A → ℝ) (c : ℝ) :
    ∑ a, π.prob s a * (f a + c) = ∑ a, π.prob s a * f a + c := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, π.sum_one, one_mul]

lemma p_sum_add {S A : Type} [Fintype S] [Fintype A] (M : SuttonBartoRL.AverageReward.MDP S A)
    (s : S) (a : A) (f : S → ℝ → ℝ) (c : ℝ) :
    ∑ s', ∑ r ∈ M.R, M.p s a s' r * (f s' r + c)
      = ∑ s', ∑ r ∈ M.R, M.p s a s' r * f s' r + c := by
  have h1 : ∀ s', ∑ r ∈ M.R, M.p s a s' r * (f s' r + c)
      = ∑ r ∈ M.R, M.p s a s' r * f s' r + (∑ r ∈ M.R, M.p s a s' r) * c := by
    intro s'
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [Finset.sum_congr rfl (fun s' _ => h1 s'), Finset.sum_add_distrib, ← Finset.sum_mul,
    M.p_sum, one_mul]

lemma sup'_add_c {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (c : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => f a + c)
      = Finset.univ.sup' Finset.univ_nonempty f + c := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun a _ => by
      have := Finset.le_sup' f (Finset.mem_univ a); linarith)
  · have : Finset.univ.sup' Finset.univ_nonempty f
        ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => f a + c) - c := by
      exact Finset.sup'_le _ _ (fun a _ => by
        have := Finset.le_sup' (fun a => f a + c) (Finset.mem_univ a); linarith)
    linarith

end SuttonBartoRL.AverageReward.ShiftAux04dd

open SuttonBartoRL.AverageReward.ShiftAux04dd in
open SuttonBartoRL.AverageReward in
theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A] (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (ρ c : ℝ) :
    (∀ v : S → ℝ, IsDiffBellmanV M π ρ v ↔ IsDiffBellmanV M π ρ (fun s => v s + c)) ∧
    (∀ q : S → A → ℝ, IsDiffBellmanQ M π ρ q ↔ IsDiffBellmanQ M π ρ (fun s a => q s a + c)) ∧
    (∀ v : S → ℝ, IsDiffBellmanOptV M ρ v ↔ IsDiffBellmanOptV M ρ (fun s => v s + c)) ∧
    (∀ q : S → A → ℝ, IsDiffBellmanOptQ M ρ q ↔ IsDiffBellmanOptQ M ρ (fun s a => q s a + c)) ∧
    (∀ (R Rbar : ℝ) (vhat : S → ℝ) (s s' : S),
      diffTDErrorV R Rbar (fun x => vhat x + c) s s' = diffTDErrorV R Rbar vhat s s') ∧
    (∀ (R Rbar : ℝ) (qhat : S → A → ℝ) (s : S) (a : A) (s' : S) (a' : A),
      diffTDErrorQ R Rbar (fun x b => qhat x b + c) s a s' a' = diffTDErrorQ R Rbar qhat s a s' a') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have key : ∀ s, ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + (v s' + c))
        = ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + v s') + c := by
      intro s
      have : ∀ a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + (v s' + c))
          = ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + v s') + c := by
        intro a
        simp only [← add_assoc]
        exact p_sum_add M s a (fun s' r => r - ρ + v s') c
      simp only [this]
      exact pol_sum_add π s _ c
    unfold IsDiffBellmanV
    simp only [key]
    constructor
    · intro h s; rw [← h s]
    · intro h s; have := h s; linarith
  · intro q
    have key : ∀ s a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + ∑ a', π.prob s' a' * (q s' a' + c))
        = ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + ∑ a', π.prob s' a' * q s' a') + c := by
      intro s a
      simp only [pol_sum_add π _ (fun a' => q _ a') c, ← add_assoc]
      exact p_sum_add M s a (fun s' r => r - ρ + ∑ a', π.prob s' a' * q s' a') c
    unfold IsDiffBellmanQ
    simp only [key]
    constructor
    · intro h s a; rw [← h s a]
    · intro h s a; have := h s a; linarith
  · intro v
    have key : ∀ s, Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + (v s' + c)))
        = Finset.univ.sup' Finset.univ_nonempty
          (fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + v s')) + c := by
      intro s
      have : ∀ a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + (v s' + c))
          = ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r - ρ + v s') + c := by
        intro a
        simp only [← add_assoc]
        exact p_sum_add M s a (fun s' r => r - ρ + v s') c
      simp only [this]
      exact sup'_add_c _ c
    unfold IsDiffBellmanOptV
    simp only [key]
    constructor
    · intro h s; rw [← h s]
    · intro h s; have := h s; linarith
  · intro q
    have key : ∀ s a, ∑ s', ∑ r ∈ M.R, M.p s a s' r *
        (r - ρ + Finset.univ.sup' Finset.univ_nonempty (fun a' => q s' a' + c))
        = ∑ s', ∑ r ∈ M.R, M.p s a s' r *
          (r - ρ + Finset.univ.sup' Finset.univ_nonempty (fun a' => q s' a')) + c := by
      intro s a
      simp only [sup'_add_c (fun a' => q _ a') c, ← add_assoc]
      exact p_sum_add M s a
        (fun s' r => r - ρ + Finset.univ.sup' Finset.univ_nonempty (fun a' => q s' a')) c
    unfold IsDiffBellmanOptQ
    simp only [key]
    constructor
    · intro h s a; rw [← h s a]
    · intro h s a; have := h s a; linarith
  · intro R Rbar vhat s s'
    simp only [diffTDErrorV]; ring
  · intro R Rbar qhat s a s' a'
    simp only [diffTDErrorQ]; ring
