-- Prove2me | solution 1 for ThompsonTutorial.Regret.ts_posterior_matching
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:35:07.675509+00:00
-- url     : https://prove2.me/submissions/7c2be052-abe4-419b-9300-7e369c1f3701

import Mathlib
import Definitions.Def_ThompsonTutorial_Regret_meanReward
import Definitions.Def_ThompsonTutorial_Regret_IsBayesModel
import Definitions.Def_ThompsonTutorial_Regret_history
import Definitions.Def_ThompsonTutorial_Regret_IsThompsonRun

open MeasureTheory ProbabilityTheory

open ThompsonTutorial.Regret in
theorem solution {Ω Θ X Y W : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (P : Measure Ω) [IsProbabilityMeasure P] (θ : Ω → Θ) (w : ℕ → Ω → W)
    (g : X → Θ → W → Y) (r : Y → ℝ) (f : Θ → X) (θhat : ℕ → Ω → Θ) (xs : ℕ → Ω → X)
    (hM : IsBayesModel P θ w g r) (hTS : IsThompsonRun P θ w g r f θhat xs)
    (t : ℕ) (ht : 1 ≤ t) (B : Set X) (hB : MeasurableSet B) :
    P[(xs t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | history g θ w xs t]
      =ᵐ[P] P[((fun ω => f (θ ω)) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | history g θ w xs t] := by
  have hx := ((hTS.2.2.1 t ht).2)
  have hpre : xs t ⁻¹' B = θhat t ⁻¹' (f ⁻¹' B) := by
    rw [hx]; rfl
  have hpre2 : ((fun ω => f (θ ω)) ⁻¹' B) = θ ⁻¹' (f ⁻¹' B) := rfl
  rw [hpre, hpre2]
  exact hTS.2.2.2.1 t ht (f ⁻¹' B) (hTS.1 hB)
