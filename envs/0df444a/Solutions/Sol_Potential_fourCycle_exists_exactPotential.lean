-- Prove2me | solution 1 for Potential.fourCycle_exists_exactPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:01:43.13422+00:00
-- url     : https://prove2.me/submissions/bbb7cfe7-28e5-4cb2-9854-38843253c260

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_maskedProfile_update_mem
public import Theorems.Thm_Potential_maskedProfile_update_not_mem
public import Theorems.Thm_Potential_maskedProfile_insert

set_option autoImplicit true
@[expose] public section
public section
open Potential
namespace Potential
theorem _root_.solution {I : Type*} {A : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Nonempty (A i)]
    (u : Payoff A) (h : FourCycle u) : ∃ P : Profile A → ℝ, ExactPotential u P := by
  classical
  let base : Profile A := fun i => Classical.choice (inferInstance : Nonempty (A i))
  have aux : ∀ S : Finset I, ∃ P : Profile A → ℝ,
      (∀ s j, j ∈ S → ∀ a : A j,
        P (Function.update s j a) - P s =
          u j (maskedProfile base S (Function.update s j a)) -
            u j (maskedProfile base S s)) ∧
      (∀ s j, j ∉ S → ∀ a : A j, P (Function.update s j a) = P s) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro s j hj
        simp at hj
      · intro s j hj a
        rfl
    | @insert i S hi ih =>
      obtain ⟨P, hP, houtside⟩ := ih
      let Q : Profile A → ℝ := fun s => P s +
        u i (maskedProfile base (insert i S) s) - u i (maskedProfile base S s)
      refine ⟨Q, ?_, ?_⟩
      · intro s j hj a
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          dsimp only [Q]
          rw [houtside s i hi a, maskedProfile_update_not_mem base s S i a hi]
          ring
        · have hij : i ≠ j := by
            intro he
            subst j
            exact hi hj
          have hcycle := h (maskedProfile base S s) i j hij (s i) a
          have h1 := maskedProfile_insert base s S i
          have h2 := maskedProfile_update_mem base s S j a hj
          have h3 := maskedProfile_update_mem base s (insert i S) j a
            (Finset.mem_insert_of_mem hj)
          rw [← h1, ← h2, ← h3] at hcycle
          have hdiff := hP s j hj a
          dsimp only [Q]
          linarith
      · intro s j hj a
        have hjs : j ∉ S := fun hm => hj (Finset.mem_insert_of_mem hm)
        dsimp only [Q]
        rw [houtside s j hjs a,
          maskedProfile_update_not_mem base s (insert i S) j a hj,
          maskedProfile_update_not_mem base s S j a hjs]
  obtain ⟨P, hP, _⟩ := aux Finset.univ
  refine ⟨P, ?_⟩
  intro s i a
  have hm : ∀ t : Profile A, maskedProfile base Finset.univ t = t := by
    intro t
    funext j
    simp [maskedProfile]
  simpa only [hm] using hP s i (Finset.mem_univ i) a
end Potential
