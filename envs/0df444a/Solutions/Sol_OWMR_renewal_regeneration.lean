-- Prove2me | solution 1 for OWMR.renewal_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T03:06:48.805094+00:00
-- url     : https://prove2.me/submissions/c25abd04-f81c-449e-be82-713738ddda9e

import Definitions.Def_owmr_renewal
import Mathlib.MeasureTheory.Measure.Prod

/-!
Regeneration at the first passage over a level `c`, in the form used by Lemmas 2 and 5:

  `∫_{[c,∞)} f dU ≤ sup_{y ≥ c} ∫ f(y + x) U(dx)`   for every measurable `f ≥ 0`.

Probabilistically, the partial sums at or above `c` start at the first-passage position
`y = D^{(τ_c)} ≥ c` and continue as `y` plus a fresh partial-sum process; the first-passage law has
total mass at most `1`. The proof needs no stopping times: it is an induction over the horizon `N`
of the partial sums `∑_{n<N} ℙ(D^{(n)} ∈ ·)`, using only the one-step split
`D^{(n+1)} = D_1 + D'^{(n)}` with `D_1 ∼ ρ` independent of `D'^{(n)} ∼ D^{(n)}`
(`measurePreserving_piFinSuccAbove`). Zero demands are allowed, and no almost-sure finiteness of
the first passage is needed.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

private lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

/-- `D^{(0)} = 0`. -/
private lemma lintegral_law_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) = f 0 := by
  rw [lintegral_map hf (measurable_psum 0)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, lintegral_const, measure_univ, mul_one]

/-- One-step split: `D^{(n+1)} = D_1 + D'^{(n)}` with `D_1 ∼ ρ` independent of `D'^{(n)}`. -/
private lemma lintegral_law_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (n : ℕ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂((Measure.pi fun _ : Fin (n + 1) => ρ).map fun z => ∑ j, (z j : ℝ))
      = ∫⁻ y, ∫⁻ x, f ((y : ℝ) + x)
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ := by
  rw [lintegral_map hf (measurable_psum _)]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ρ) 0
  have hF : Measurable fun p : ℝ≥0 × (Fin n → ℝ≥0) => f ((p.1 : ℝ) + ∑ j, (p.2 j : ℝ)) :=
    hf.comp (measurable_fst.coe_nnreal_real.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_snd).coe_nnreal_real))
  have key : ∫⁻ z, f (∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (n + 1) => ρ)
      = ∫⁻ z, (fun p : ℝ≥0 × (Fin n → ℝ≥0) => f ((p.1 : ℝ) + ∑ j, (p.2 j : ℝ)))
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ≥0) 0 z)
          ∂(Measure.pi fun _ : Fin (n + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map (f := fun x => f ((y : ℝ) + x)) (hf.comp (measurable_const_add _))
    (measurable_psum n)]

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (c : ℝ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in Set.Ici c, f x ∂(renewalMeasure ρ)
      ≤ ⨆ y ∈ Set.Ici c, ∫⁻ x, f (y + x) ∂(renewalMeasure ρ) := by
  have hU : ∀ g : ℝ → ℝ≥0∞, ∫⁻ x, g x ∂(renewalMeasure ρ)
      = ∑' n : ℕ, ∫⁻ x, g x ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) :=
    fun g => lintegral_sum_measure g _
  -- induction over the horizon, for all levels and all test functions at once
  have hind : ∀ N : ℕ, ∀ (c : ℝ) (f : ℝ → ℝ≥0∞), Measurable f →
      ∑ n ∈ Finset.range N, ∫⁻ x, (Set.Ici c).indicator f x
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ))
        ≤ ⨆ y ∈ Set.Ici c, ∫⁻ x, f (y + x) ∂(renewalMeasure ρ) := by
    intro N
    induction N with
    | zero => intro c f hf; simp
    | succ N ih =>
      intro c f hf
      by_cases hc : c ≤ 0
      · -- the start `y = 0` is itself admissible
        refine le_trans ?_ (le_iSup₂_of_le (0 : ℝ) (Set.mem_Ici.2 hc) le_rfl)
        simp only [zero_add]
        rw [hU f]
        refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range (N + 1)))
        exact Finset.sum_le_sum fun n _ => lintegral_mono (Set.indicator_le_self _ _)
      · have hc' : 0 < c := lt_of_not_ge hc
        have hFm : Measurable ((Set.Ici c).indicator f) := hf.indicator measurableSet_Ici
        rw [Finset.sum_range_succ', lintegral_law_zero ρ hFm,
          Set.indicator_of_notMem (by simp only [Set.mem_Ici]; linarith), add_zero,
          Finset.sum_congr rfl fun n _ => lintegral_law_succ ρ n hFm]
        have hmeas : ∀ n ∈ Finset.range N, Measurable fun y : ℝ≥0 =>
            ∫⁻ x, (Set.Ici c).indicator f ((y : ℝ) + x)
              ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) := fun n _ =>
          Measurable.lintegral_prod_right' (f := fun p : ℝ≥0 × ℝ => (Set.Ici c).indicator f
            ((p.1 : ℝ) + p.2)) (hFm.comp (measurable_fst.coe_nnreal_real.add measurable_snd))
        rw [← lintegral_finsetSum _ hmeas]
        calc ∫⁻ y, ∑ n ∈ Finset.range N, ∫⁻ x, (Set.Ici c).indicator f ((y : ℝ) + x)
              ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ
            ≤ ∫⁻ _y, ⨆ y' ∈ Set.Ici c, ∫⁻ x, f (y' + x) ∂(renewalMeasure ρ) ∂ρ := by
              refine lintegral_mono fun y => ?_
              by_cases hy : c ≤ (y : ℝ)
              · -- the first demand already reaches the level `c`
                refine le_trans ?_ (le_iSup₂_of_le (y : ℝ) (Set.mem_Ici.2 hy) le_rfl)
                rw [hU (fun x => f ((y : ℝ) + x))]
                refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range N))
                exact Finset.sum_le_sum fun n _ => lintegral_mono fun x =>
                  Set.indicator_le_self _ _ _
              · -- otherwise restart from `y` with the lower level `c - y`
                replace hy : (y : ℝ) < c := lt_of_not_ge hy
                have e : ∀ x : ℝ, (Set.Ici c).indicator f ((y : ℝ) + x)
                    = (Set.Ici (c - y)).indicator (fun x => f ((y : ℝ) + x)) x := by
                  intro x
                  by_cases hx : c - y ≤ x
                  · rw [Set.indicator_of_mem (Set.mem_Ici.2 (by linarith)),
                      Set.indicator_of_mem (Set.mem_Ici.2 hx)]
                  · rw [Set.indicator_of_notMem (by simp; linarith),
                      Set.indicator_of_notMem (by simpa using hx)]
                simp_rw [e]
                refine le_trans (ih (c - y) (fun x => f ((y : ℝ) + x))
                  (hf.comp (measurable_const.add measurable_id))) ?_
                refine iSup₂_le fun y'' hy'' => ?_
                refine le_trans (le_of_eq ?_) (le_iSup₂_of_le ((y : ℝ) + y'')
                  (Set.mem_Ici.2 (by simp only [Set.mem_Ici] at hy''; linarith)) le_rfl)
                simp_rw [add_assoc]
          _ = ⨆ y' ∈ Set.Ici c, ∫⁻ x, f (y' + x) ∂(renewalMeasure ρ) := by
              rw [lintegral_const, measure_univ, mul_one]
  rw [← lintegral_indicator measurableSet_Ici, hU, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => hind N c f hf
