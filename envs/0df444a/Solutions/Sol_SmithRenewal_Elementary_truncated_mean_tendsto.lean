-- Prove2me | solution 1 for SmithRenewal.Elementary.truncated_mean_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:38:39.886541+00:00
-- url     : https://prove2.me/submissions/f9175c5a-55e7-4daf-b0a6-1209963e46ad

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SmithRenewal.Elementary

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X) :
    Tendsto (fun Δ : ℝ => mu1 (trunc Δ X) P) atTop (𝓝 (mu1 X P)) := by
  have hmono : Monotone (fun Δ : ℝ => mu1 (trunc Δ X) P) := by
    intro a b hab
    unfold mu1 trunc
    exact lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (min_le_min_left _ hab))
  have hsup : (⨆ Δ : ℝ, mu1 (trunc Δ X) P) = mu1 X P := by
    apply le_antisymm
    · refine iSup_le (fun Δ => ?_)
      unfold mu1 trunc
      exact lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · have hmeas : ∀ n : ℕ, Measurable (fun ω => ENNReal.ofReal (min (X 0 ω) (n : ℝ))) :=
        fun n => ((hX.measurable 0).min measurable_const).ennreal_ofReal
      have hm2 : Monotone (fun (n : ℕ) ω => ENNReal.ofReal (min (X 0 ω) (n : ℝ))) := by
        intro a b hab ω
        exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab))
      calc mu1 X P = ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal (min (X 0 ω) (n : ℝ)) ∂P := by
            unfold mu1
            apply lintegral_congr
            intro ω
            apply le_antisymm
            · obtain ⟨n, hn⟩ := exists_nat_ge (X 0 ω)
              exact le_iSup_of_le n (by rw [min_eq_left hn])
            · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))
        _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min (X 0 ω) (n : ℝ)) ∂P := lintegral_iSup hmeas hm2
        _ ≤ ⨆ Δ : ℝ, mu1 (trunc Δ X) P := by
            refine iSup_le (fun n => ?_)
            exact le_iSup_of_le (n : ℝ) le_rfl
  rw [← hsup]
  exact tendsto_atTop_iSup hmono
