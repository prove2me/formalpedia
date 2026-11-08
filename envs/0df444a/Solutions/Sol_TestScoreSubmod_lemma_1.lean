-- Prove2me | solution 1 for TestScoreSubmod.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:48:45.134918+00:00
-- url     : https://prove2.me/submissions/6b01aab2-2f91-4b07-b1b0-1eb032ebbcf8

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_utility
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

open scoped NNReal
open MeasureTheory

namespace Aux_TSSl1

lemma nn_sup0 (a : ℝ≥0) : a ⊔ 0 = a := sup_of_le_left (zero_le : (0:ℝ≥0) ≤ a)
lemma nn_0sup (a : ℝ≥0) : 0 ⊔ a = a := sup_of_le_right (zero_le : (0:ℝ≥0) ≤ a)
lemma nn_inf0 (a : ℝ≥0) : a ⊓ 0 = 0 := inf_of_le_right (zero_le : (0:ℝ≥0) ≤ a)
lemma nn_0inf (a : ℝ≥0) : 0 ⊓ a = 0 := inf_of_le_left (zero_le : (0:ℝ≥0) ≤ a)

end Aux_TSSl1

open TestScoreSubmod in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ≥0) → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (P : ι → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)]
    (hint : ∀ S : Finset ι, Integrable (fun x => g (mask S x)) (Measure.pi P)) :
    (∀ S, 0 ≤ utility g P S) ∧ Monotone (utility g P) ∧
      NonmonotoneSubmod.Shared.Submodular (utility g P) := by
  have hsup : ∀ (S T : Finset ι) (x : ι → ℝ≥0), mask (S ∪ T) x = mask S x ⊔ mask T x := by
    intro S T x
    funext i
    simp only [mask, Pi.sup_apply, Finset.mem_union]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hS, hT, Aux_TSSl1.nn_sup0, Aux_TSSl1.nn_0sup]
  have hinf : ∀ (S T : Finset ι) (x : ι → ℝ≥0), mask (S ∩ T) x = mask S x ⊓ mask T x := by
    intro S T x
    funext i
    simp only [mask, Pi.inf_apply, Finset.mem_inter]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hS, hT, Aux_TSSl1.nn_inf0, Aux_TSSl1.nn_0inf]
  refine ⟨fun S => integral_nonneg fun x => hg0 _, ?_, ?_⟩
  · intro S T hST
    unfold utility
    apply integral_mono (hint S) (hint T)
    intro x
    apply hmono
    intro i
    simp only [mask]
    by_cases h1 : i ∈ S
    · rw [if_pos h1, if_pos (hST h1)]
    · rw [if_neg h1]; exact zero_le
  · intro S T
    unfold utility
    rw [← integral_add (hint _) (hint _), ← integral_add (hint _) (hint _)]
    apply integral_mono ((hint _).add (hint _)) ((hint _).add (hint _))
    intro x
    simp only [Pi.add_apply]
    rw [hsup, hinf]
    exact hsub _ _
