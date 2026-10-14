-- Prove2me | solution 1 for TPG.gate_eq_meanReward
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:21:29.953988+00:00
-- url     : https://prove2.me/submissions/cb3fcf9c-8a01-4f32-8a24-ee3466c4ee86

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_integral_Y_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (M : ℝ) (hM : E.RewardBound M) :
    E.gate T
      = (1 / (T : ℝ)) * ∑ t : Fin T,
          (E.meanReward (fun _ => 1) (t : ℕ) - E.meanReward (fun _ => 0) (t : ℕ)) := by
  have h1 : ∀ s : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ)) s ∧ (fun _ : ℕ => (1 : ℝ)) s ≤ 1 :=
    fun _ => ⟨zero_le_one, le_refl _⟩
  have h0 : ∀ s : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => (0 : ℝ)) s ∧ (fun _ : ℕ => (0 : ℝ)) s ≤ 1 :=
    fun _ => ⟨le_refl _, zero_le_one⟩
  unfold Env.gate Env.expLaw Env.meanReward
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_Y_trajLaw E T (fun _ => 1) h1 M hM t, integral_Y_trajLaw E T (fun _ => 0) h0 M hM t]
