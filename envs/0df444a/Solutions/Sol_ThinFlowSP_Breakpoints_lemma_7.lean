-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:33:09.422014+00:00
-- url     : https://prove2.me/submissions/a6853560-7043-4185-a9b6-f59e728a6053

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace Aux_TF_lemma7
open ThinFlowSP.Breakpoints

theorem step_ge (G : Net) (Astar : Finset G.A) (l p : G.V → ℝ) (w : G.V) :
    l w ≤ normStep G Astar l p w := by
  unfold normStep
  by_cases h : w ≠ G.s ∧ ∀ a, G.head a = w → a ∉ Astar
  · rw [if_pos h]; exact le_max_left _ _
  · rw [if_neg h]

theorem coord_le {V : Type} [Fintype V] (f : V → ℝ) (w : V) : |f w| ≤ ‖f‖ := by
  have := norm_le_pi_norm f w
  rwa [Real.norm_eq_abs] at this

theorem inf_lip (G : Net) (w : G.V) (p p' : G.V → ℝ) :
    |(⨅ a : {a : G.A // G.head a = w}, p' (G.tail a.1)) -
      ⨅ a : {a : G.A // G.head a = w}, p (G.tail a.1)| ≤ ‖p' - p‖ := by
  rcases isEmpty_or_nonempty {a : G.A // G.head a = w} with he | hne
  · simp only [Real.iInf_of_isEmpty, sub_self, abs_zero]
    exact norm_nonneg _
  · have hb : ∀ q : G.V → ℝ, BddBelow (Set.range fun a : {a : G.A // G.head a = w} => q (G.tail a.1)) :=
      fun q => (Set.finite_range _).bddBelow
    have key : ∀ q q' : G.V → ℝ, (⨅ a : {a : G.A // G.head a = w}, q' (G.tail a.1)) ≤
        (⨅ a : {a : G.A // G.head a = w}, q (G.tail a.1)) + ‖q' - q‖ := by
      intro q q'
      have : (⨅ a : {a : G.A // G.head a = w}, q' (G.tail a.1)) - ‖q' - q‖ ≤
          ⨅ a : {a : G.A // G.head a = w}, q (G.tail a.1) := by
        apply le_ciInf
        intro a
        have h1 := ciInf_le (hb q') a
        have h2 := coord_le (q' - q) (G.tail a.1)
        rw [Pi.sub_apply] at h2
        have h3 := le_abs_self (q' (G.tail a.1) - q (G.tail a.1))
        linarith
      linarith
    have k1 := key p p'
    have k2 := key p' p
    rw [norm_sub_rev] at k2
    rw [abs_sub_le_iff]
    constructor <;> linarith

theorem step_lip (G : Net) (Astar : Finset G.A) (l l' p p' : G.V → ℝ) :
    ‖normStep G Astar l' p' - normStep G Astar l p‖ ≤ max ‖l' - l‖ ‖p' - p‖ := by
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr
  intro w
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have h2 := coord_le (l' - l) w
  rw [Pi.sub_apply] at h2
  unfold normStep
  by_cases h : w ≠ G.s ∧ ∀ a, G.head a = w → a ∉ Astar
  · rw [if_pos h, if_pos h]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le_max h2 (inf_lip G w p p'))
  · rw [if_neg h, if_neg h]
    exact h2.trans (le_max_left _ _)

end Aux_TF_lemma7

open ThinFlowSP.Breakpoints Aux_TF_lemma7 in
theorem solution (G : Net) (Astar : Finset G.A) (hG : IsShortestPathGraph G) :
    (∀ l : G.V → ℝ, (∀ v, 0 ≤ l v) → ∀ v, l v ≤ ThinFlowSP.Breakpoints.normalize G Astar l v) ∧
    (∀ l l' : G.V → ℝ, (∀ v, 0 ≤ l v) → (∀ v, 0 ≤ l' v) →
      ‖ThinFlowSP.Breakpoints.normalize G Astar l' - ThinFlowSP.Breakpoints.normalize G Astar l‖ ≤ ‖l' - l‖) := by
  constructor
  · intro l _ v
    unfold ThinFlowSP.Breakpoints.normalize
    cases h : Fintype.card G.V with
    | zero => simp
    | succ n =>
      rw [Function.iterate_succ_apply']
      exact step_ge G Astar l _ v
  · intro l l' _ _
    unfold ThinFlowSP.Breakpoints.normalize
    have it : ∀ n : ℕ, ‖(normStep G Astar l')^[n] l' - (normStep G Astar l)^[n] l‖ ≤ ‖l' - l‖ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (step_lip G Astar l l' _ _).trans (max_le le_rfl ih)
    exact it _
