-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.finiteEntropy_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-03T23:53:03.099212+00:00
-- url     : https://prove2.me/submissions/ef17a1b9-1e9e-44fa-902d-008cfc8e019d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

open scoped Matrix ComplexOrder

open scoped Matrix.Norms.L2Operator in
/-- Continuity of `X ↦ cfc (x log x) X` along self-adjoint matrices. -/
theorem fet_cfc {ι n : Type} [Fintype n] [DecidableEq n] {l : Filter ι}
    {X : ι → Matrix n n ℂ} {Y : Matrix n n ℂ} (hX : ∀ᶠ k in l, IsSelfAdjoint (X k))
    (h : Tendsto X l (nhds Y)) :
    Tendsto (fun k => cfc (fun x : ℝ => x * Real.log x) (X k)) l
      (nhds (cfc (fun x : ℝ => x * Real.log x) Y)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hY : IsSelfAdjoint Y := by
    have h1 : Tendsto (fun k => star (X k)) l (nhds (star Y)) :=
      (continuous_star.tendsto Y).comp h
    have h2 : Tendsto (fun k => star (X k)) l (nhds Y) :=
      h.congr' (hX.mono fun k hk => hk.symm)
    exact tendsto_nhds_unique h1 h2
  set R : ℝ := (‖Y‖ + 1) * ‖(1 : Matrix n n ℂ)‖ with hR
  have hn : Tendsto (fun k => ‖X k‖) l (nhds ‖Y‖) := h.norm
  have hlt : ∀ᶠ k in l, ‖X k‖ < ‖Y‖ + 1 := hn.eventually (gt_mem_nhds (by linarith))
  refine h.cfc (s := Metric.closedBall (0 : ℝ) R) (isCompact_closedBall 0 R) _ ?_ hX ?_ hY
    Real.continuous_mul_log.continuousOn
  · filter_upwards [hlt] with k hk
    refine (spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) (X k)).trans
      (Metric.closedBall_subset_closedBall ?_)
    exact mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
  · refine (spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) Y).trans
      (Metric.closedBall_subset_closedBall ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem fet_main {ι n : Type} [Fintype n] [DecidableEq n] {l : Filter ι}
    {X : ι → Matrix n n ℂ} {Y : Matrix n n ℂ} (hX : ∀ᶠ k in l, (X k).PosSemidef)
    (h : Tendsto X l (nhds Y)) :
    Tendsto (fun k => finiteEntropy (X k)) l (nhds (finiteEntropy Y)) := by
  have hc := fet_cfc (hX.mono fun k hk => hk.isHermitian.isSelfAdjoint) h
  have htr : Continuous fun M : Matrix n n ℂ => M.trace.re :=
    Complex.continuous_re.comp (continuous_id.matrix_trace)
  have ht := (htr.tendsto Y).comp h
  have hct := (htr.tendsto _).comp hc
  have hreal : Tendsto (fun k => -(cfc (fun x : ℝ => x * Real.log x) (X k)).trace.re +
      (X k).trace.re * Real.log (X k).trace.re) l
      (nhds (-(cfc (fun x : ℝ => x * Real.log x) Y).trace.re +
        Y.trace.re * Real.log Y.trace.re)) :=
    hct.neg.add ((Real.continuous_mul_log.tendsto _).comp ht)
  exact (ENNReal.continuous_ofReal.tendsto _).comp hreal

end QAlgorithms.Papers.Independent.Claimed50.P18

end

open QAlgorithms.Papers.Independent.Claimed50.P18 in
open QAlgorithms.Papers.Independent.Frontier18.P01 in
open scoped Matrix ComplexOrder in
theorem solution {ι n : Type} [Fintype n] [DecidableEq n] {l : Filter ι}
    {X : ι → Matrix n n ℂ} {Y : Matrix n n ℂ} (hX : ∀ᶠ k in l, (X k).PosSemidef)
    (h : Filter.Tendsto X l (nhds Y)) :
    Filter.Tendsto (fun k => finiteEntropy (X k)) l (nhds (finiteEntropy Y)) :=
  fet_main hX h
