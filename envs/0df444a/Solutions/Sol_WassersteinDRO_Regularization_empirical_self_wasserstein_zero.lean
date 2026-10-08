-- Prove2me | solution 1 for WassersteinDRO.Regularization.empirical_self_wasserstein_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:29:59.090529+00:00
-- url     : https://prove2.me/submissions/3752e6ab-4dc0-4a20-8c8e-fa21a489042d

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance

open MeasureTheory

open WassersteinDRO.Regularization in
theorem solution {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) :
    wassersteinDistance 1 (empiricalDistribution ξhat) (empiricalDistribution ξhat) = 0 := by
  unfold wassersteinDistance
  set Q := empiricalDistribution ξhat
  have hd : Measurable (fun x : E => (x, x)) := measurable_id.prodMk measurable_id
  have hle : (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q),
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π) ≤ 0 := by
    refine iInf₂_le_of_le (Q.map (fun x : E => (x, x))) ⟨?_, ?_⟩ ?_
    · rw [Measure.map_map measurable_fst hd]
      exact Measure.map_id
    · rw [Measure.map_map measurable_snd hd]
      exact Measure.map_id
    · refine (lintegral_map_le _ _).trans ?_
      simp
  rw [nonpos_iff_eq_zero.mp hle]
  norm_num
