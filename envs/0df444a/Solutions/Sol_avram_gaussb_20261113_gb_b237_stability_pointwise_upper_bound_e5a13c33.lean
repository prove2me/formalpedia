-- Prove2me | solution 1 for avram_gaussb_20261113_gb_b237_stability_pointwise_upper_bound_e5a13c33
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:53:10.739864+00:00
-- url     : https://prove2.me/submissions/fa972ed5-7610-406a-b5b7-1d5a4feb5ef5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

noncomputable section
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hff : ∀ m p s, Integrable
      (fun ω => (f m s ω - f p s ω)^2) ν)
    (hfg : ∀ m s, Integrable
      (fun ω => (f m s ω - g m s ω)^2) ν)
    (hgg : ∀ m p s, Integrable
      (fun ω => (g m s ω - g p s ω)^2) ν)
    (hffOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (f m s ω - f p s ω)^2 ∂ν) μ)
    (hfgOuter : ∀ m, Integrable
      (fun s => ∫ ω, (f m s ω - g m s ω)^2 ∂ν) μ)
    (hggOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (g m s ω - g p s ω)^2 ∂ν) μ)
    (hClose : Tendsto (fun m =>
      ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hCauchy : Tendsto (fun mp : ℕ × ℕ =>
      ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) 
    : (let V : ℕ → ℝ := (fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ); let W : ℕ × ℕ → ℝ := (fun mp => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ); (∀ (m p : ℕ), (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤
      3 * (V m + W (m, p) + V p))) := by

  dsimp only
  let V : ℕ → ℝ := fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ
  let W : ℕ × ℕ → ℝ := fun mp => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ
  have hBound (m p : ℕ) : (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤ 3 * (V m + W (m, p) + V p) := by
    have hInner (s : α) : (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ≤ 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) := by
      have hPt (ω : β) : (f m s ω - f p s ω)^2 ≤ 3 * ((f m s ω - g m s ω)^2 + (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2) := by
        nlinarith [ sq_nonneg ((f m s ω - g m s ω) - (g m s ω - g p s ω)), sq_nonneg ((f m s ω - g m s ω) + (f p s ω - g p s ω)), sq_nonneg ((g m s ω - g p s ω) + (f p s ω - g p s ω))]
      have hInt : Integrable (fun ω => 3 * ((f m s ω - g m s ω)^2 + (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2)) ν := (((hfg m s).add (hgg m p s)).add (hfg p s)).const_mul 3
      calc
        _ ≤ ∫ ω, 3 * ((f m s ω - g m s ω)^2 + (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2) ∂ν :=
          integral_mono (hff m p s) hInt hPt
        _ = 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) := by
          simpa only [Pi.add_apply, integral_const_mul] using
            congrArg (fun z : ℝ => 3 * z)
              ((integral_add ((hfg m s).add (hgg m p s)) (hfg p s)).trans
                (congrArg (fun z : ℝ => z + (∫ w, (f p s w - g p s w)^2 ∂ν))
                  (integral_add (hfg m s) (hgg m p s))))
    have hIntOuter : Integrable (fun s => 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν))) μ := (((hfgOuter m).add (hggOuter m p)).add (hfgOuter p)).const_mul 3
    calc
      _ ≤ ∫ s, 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) ∂μ :=
        integral_mono (hffOuter m p) hIntOuter hInner
      _ = 3 * (V m + W (m, p) + V p) := by
        dsimp [V, W]
        simpa only [Pi.add_apply, integral_const_mul] using
          congrArg (fun z : ℝ => 3 * z)
            ((integral_add ((hfgOuter m).add (hggOuter m p)) (hfgOuter p)).trans
              (congrArg (fun z : ℝ => z + (∫ s, (∫ w, (f p s w - g p s w)^2 ∂ν) ∂μ))
                (integral_add (hfgOuter m) (hggOuter m p))))
  exact hBound
