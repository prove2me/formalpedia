-- Prove2me | solution 1 for PandoraBO.Private20261023.uniform_seed_mixture_integral
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:50:44.235572+00:00
-- url     : https://prove2.me/submissions/da041954-2b40-444f-af27-c0d3bc3b1842

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

/-!
The independent analytic identity behind randomizing policies with one uniform
seed. The hypotheses are exactly the integrability needed by Fubini; policy
integrability is discharged separately by the finite-rollout foundation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace PandoraBO.Private20261023.Mixing

theorem seed_integral_eq_interval (f : ℝ → ℝ) :
    (∫ u, f u ∂seedLaw) = ∫ u in (0 : ℝ)..1, f u := by
  rw [seedLaw, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]

theorem seed_integral_mixture (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (f g : ℝ → ℝ)
    (hmix : Integrable
      (fun u => if u ≤ a then f (u / a) else g ((u - a) / (1 - a))) seedLaw) :
    (∫ u, (if u ≤ a then f (u / a) else g ((u - a) / (1 - a))) ∂seedLaw) =
      a * (∫ u, f u ∂seedLaw) + (1 - a) * (∫ u, g u ∂seedLaw) := by
  let F : ℝ → ℝ := fun u => if u ≤ a then f (u / a) else g ((u - a) / (1 - a))
  have hF : IntervalIntegrable F volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).mpr hmix
  have haI : a ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), mem_Icc] using
      (show 0 ≤ a ∧ a ≤ 1 from ⟨ha0.le, ha1.le⟩)
  have hparts := (IntervalIntegrable.trans_iff haI).mp hF
  have hleft : (∫ u in (0 : ℝ)..a, F u) = a * (∫ u in (0 : ℝ)..1, f u) := by
    calc
      (∫ u in (0 : ℝ)..a, F u) = ∫ u in (0 : ℝ)..a, f (u / a) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha0.le
        intro u hu
        exact if_pos hu.2.le
      _ = a * (∫ u in (0 : ℝ)..1, f u) := by
        rw [intervalIntegral.integral_comp_div f ha0.ne']
        simp only [zero_div, div_self ha0.ne', smul_eq_mul]
  have hden : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha1)
  have hright : (∫ u in a..1, F u) =
      (1 - a) * (∫ u in (0 : ℝ)..1, g u) := by
    calc
      (∫ u in a..1, F u) = ∫ u in a..1, g ((u - a) / (1 - a)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha1.le
        intro u hu
        exact if_neg (not_le.mpr hu.1)
      _ = ∫ u in a - a..1 - a, g (u / (1 - a)) :=
        intervalIntegral.integral_comp_sub_right (fun v => g (v / (1 - a))) a
      _ = (1 - a) * (∫ u in (0 : ℝ)..1, g u) := by
        rw [sub_self, intervalIntegral.integral_comp_div g hden]
        simp only [zero_div, div_self hden, smul_eq_mul]
  rw [seed_integral_eq_interval, seed_integral_eq_interval, seed_integral_eq_interval]
  exact (intervalIntegral.integral_add_adjacent_intervals hparts.1 hparts.2).symm.trans
    (congrArg₂ (· + ·) hleft hright)

theorem product_integral_mixture {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (f g F : X × ℝ → ℝ)
    (hformula : ∀ x u, F (x, u) =
      if u ≤ a then f (x, u / a) else g (x, (u - a) / (1 - a)))
    (hf : Integrable f (μ.prod seedLaw)) (hg : Integrable g (μ.prod seedLaw))
    (hF : Integrable F (μ.prod seedLaw)) :
    (∫ ω, F ω ∂μ.prod seedLaw) =
      a * (∫ ω, f ω ∂μ.prod seedLaw) + (1 - a) * (∫ ω, g ω ∂μ.prod seedLaw) := by
  letI : IsProbabilityMeasure seedLaw := by
    constructor
    simp [seedLaw, Real.volume_Icc]
  rw [integral_prod F hF, integral_prod f hf, integral_prod g hg]
  calc
    (∫ x, ∫ u, F (x, u) ∂seedLaw ∂μ) =
        ∫ x, a * (∫ u, f (x, u) ∂seedLaw) +
          (1 - a) * (∫ u, g (x, u) ∂seedLaw) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hF.prod_right_ae] with x hx
      have hmix : Integrable
          (fun u => if u ≤ a then f (x, u / a) else g (x, (u - a) / (1 - a))) seedLaw :=
        hx.congr (ae_of_all _ (fun u => hformula x u))
      rw [integral_congr_ae (ae_of_all _ (fun u => hformula x u))]
      exact seed_integral_mixture a ha0 ha1 (fun u => f (x, u)) (fun u => g (x, u)) hmix
    _ = a * (∫ x, ∫ u, f (x, u) ∂seedLaw ∂μ) +
        (1 - a) * (∫ x, ∫ u, g (x, u) ∂seedLaw ∂μ) := by
      rw [integral_add (hf.integral_prod_left.const_mul a)
        (hg.integral_prod_left.const_mul (1 - a)), integral_const_mul, integral_const_mul]

end PandoraBO.Private20261023.Mixing

theorem solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (f g F : X × ℝ → ℝ)
    (hformula : ∀ x u, F (x, u) =
      if u ≤ a then f (x, u / a) else g (x, (u - a) / (1 - a)))
    (hf : Integrable f (μ.prod PandoraBO.seedLaw))
    (hg : Integrable g (μ.prod PandoraBO.seedLaw))
    (hF : Integrable F (μ.prod PandoraBO.seedLaw)) :
    (∫ ω, F ω ∂μ.prod PandoraBO.seedLaw) =
      a * (∫ ω, f ω ∂μ.prod PandoraBO.seedLaw) +
        (1 - a) * (∫ ω, g ω ∂μ.prod PandoraBO.seedLaw) := by
  exact PandoraBO.Private20261023.Mixing.product_integral_mixture
    μ a ha0 ha1 f g F hformula hf hg hF
