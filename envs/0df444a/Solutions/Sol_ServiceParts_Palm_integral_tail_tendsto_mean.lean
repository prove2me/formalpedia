-- Prove2me | solution 1 for ServiceParts.Palm.integral_tail_tendsto_mean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:39:53.845714+00:00
-- url     : https://prove2.me/submissions/63c2355b-5b64-4b47-9d75-eb8032d4fb27

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology ServiceParts.Palm in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    Tendsto (fun t : ℝ => ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) atTop
      (𝓝 S.meanResupply) := by
  set L := S.resupply 0 with hL
  have hLm : Measurable L := S.resupply_measurable 0
  have hLi : Integrable L P := S.resupply_integrable
  have hnn : 0 ≤ᵐ[P] L := Filter.Eventually.of_forall (fun ω => S.resupply_nonneg 0 ω)
  have hfun : (fun u : ℝ => 1 - S.resupplyCdf u) = fun u => P.real {a | u < L a} := by
    funext u
    have hs : MeasurableSet {a | L a ≤ u} := measurableSet_le hLm measurable_const
    have hc : {a | L a ≤ u}ᶜ = {a | u < L a} := by
      ext a; simp [not_le]
    have h1 := prob_compl_eq_one_sub (μ := P) hs
    rw [hc] at h1
    simp only [ServiceParts.Palm.ResupplySystem.resupplyCdf, Measure.real]
    rw [h1, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hanti : Antitone (fun t : ℝ => P.real {a | t < L a}) := by
    intro s t hst
    exact measureReal_mono (fun a (h : t < L a) => lt_of_le_of_lt hst h)
  have hmeas : Measurable (fun t : ℝ => P.real {a | t < L a}) := hanti.measurable
  have key := lintegral_eq_lintegral_meas_lt P hnn hLm.aemeasurable
  have hfin : ∫⁻ ω, ENNReal.ofReal (L ω) ∂P < ⊤ := hLi.lintegral_lt_top
  have hint : IntegrableOn (fun t : ℝ => P.real {a | t < L a}) (Set.Ioi 0) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun t => measureReal_nonneg))]
    calc ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (P.real {a | t < L a})
        ≤ ∫⁻ t in Set.Ioi 0, P {a | t < L a} := by
          apply lintegral_mono
          intro t
          exact ENNReal.ofReal_toReal_le
      _ < ⊤ := by rw [← key]; exact hfin
  have hmean : S.meanResupply = ∫ t in Set.Ioi 0, P.real {a | t < L a} :=
    hLi.integral_eq_integral_meas_lt hnn
  rw [hfun, hmean]
  exact intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
