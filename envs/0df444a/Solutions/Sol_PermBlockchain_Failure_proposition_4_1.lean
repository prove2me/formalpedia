-- Prove2me | solution 1 for PermBlockchain.Failure.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:37.660278+00:00
-- url     : https://prove2.me/submissions/c51a2ba5-2658-404a-9031-3d3654b0cf69

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace GTAux
open PermBlockchain.Failure Set

theorem tangent {f f' : ℝ → ℝ} (hc : ConvexOn ℝ (Ici (0:ℝ)) f)
    (hd : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f (f' x) (Ici 0) x) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f x + f' x * (y - x) ≤ f y := by
  have hx' : x ∈ Ici (0:ℝ) := hx
  have hy' : y ∈ Ici (0:ℝ) := hy
  rcases lt_trichotomy x y with h | h | h
  · have := hc.le_slope_of_hasDerivWithinAt hx' hy' h (hd x hx)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivWithinAt hy' hx' h (hd x hx)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

variable {m : ℕ} {M : Model m}

theorem exists_c (hM : M.Standing) {Δ : ℝ} (hA : M.Assumption1 Δ) :
    ∃ c : ℝ, 0 < c ∧ M.cl' c = M.γ := by
  set b := M.G ((M.L + Δ + M.L + M.h + M.l) / 2 - M.γ) with hb
  have hb0 : 0 ≤ b := ProbabilityTheory.cdf_nonneg _ _
  have hdar := exists_hasDerivWithinAt_eq_of_ge_of_le (f := M.cl) (f' := M.cl') hb0
    (fun x hx => (hM.hasDerivWithinAt_cl x hx.1).mono (fun y hy => hy.1)) hA.1.le hA.2.le
  obtain ⟨c, hc, hcg⟩ := hdar
  refine ⟨c, ?_, hcg⟩
  rcases hc.1.eq_or_lt with h | h
  · subst h; exact absurd hcg (ne_of_lt hA.1)
  · exact h

theorem cinv_nonneg (M : Model m) (x : ℝ) : 0 ≤ M.cinv x :=
  Real.sSup_nonneg (fun _ hs => hs.1)

theorem cinv_le (hM : M.Standing) {c x : ℝ} (hc : 0 ≤ c) (hcg : M.cl' c = M.γ)
    (hx : x ≤ M.γ) : M.cinv x ≤ c := by
  refine Real.sSup_le (fun t ht => ?_) hc
  by_contra hlt
  rw [not_le] at hlt
  have := hM.cl'_strictMonoOn hc ht.1 hlt
  linarith [ht.2]

theorem cinv_eq (hM : M.Standing) {c : ℝ} (hc : 0 ≤ c) (hcg : M.cl' c = M.γ) :
    M.cinv M.γ = c := by
  refine le_antisymm (cinv_le hM hc hcg le_rfl) ?_
  refine le_csSup ⟨c, fun t ht => ?_⟩ ⟨hc, hcg.le⟩
  by_contra hlt
  rw [not_le] at hlt
  have := hM.cl'_strictMonoOn hc ht.1 hlt
  linarith [ht.2]

theorem profit_le (hM : M.Standing) {c : ℝ} (hc : 0 ≤ c) (hcg : M.cl' c = M.γ) {s : ℝ}
    (hs : 0 ≤ s) : M.γ * s - M.cl s ≤ M.γ * c - M.cl c := by
  have := tangent hM.cl_convexOn hM.hasDerivWithinAt_cl hc hs
  rw [hcg] at this
  linarith

theorem profit_pos (hM : M.Standing) {c : ℝ} (hc : 0 < c) (hcg : M.cl' c = M.γ) :
    0 < M.γ * c - M.cl c := by
  have h1 := tangent hM.cl_convexOn hM.hasDerivWithinAt_cl (x := c / 2) (y := 0)
    (by linarith) le_rfl
  have h2 := tangent hM.cl_convexOn hM.hasDerivWithinAt_cl (x := c) (y := c / 2)
    hc.le (by linarith)
  have h3 : M.cl' (c / 2) < M.γ := by
    rw [← hcg]; exact hM.cl'_strictMonoOn (show (0:ℝ) ≤ c / 2 by linarith) hc.le (by linarith)
  rw [hM.cl_zero] at h1
  rw [hcg] at h2
  nlinarith

theorem WV_eq (X : Scenario) (Δ : ℝ) :
    M.WV X Δ = M.Ψl X Δ * M.sl X Δ - M.cl (M.sl X Δ) := by
  unfold Model.WV Model.Ψh; ring

end GTAux

namespace GTAux2
open PermBlockchain.Failure Set MeasureTheory

variable {m : ℕ} {M : Model m}

theorem G_nonpos (hM : M.Standing) {x : ℝ} (hx : x ≤ 0) : M.G x = 0 := by
  have := hM.isProbabilityMeasure
  have := hM.noAtoms
  unfold Model.G
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  have : M.μ (Iic x) = 0 := by
    refine measure_mono_null (t := Iio 0 ∪ {0}) (fun y hy => ?_)
      (measure_union_null hM.μ_Iio_zero (measure_singleton 0))
    rcases lt_or_eq_of_le (le_trans hy hx) with h | h
    · exact Or.inl h
    · exact Or.inr h
  simp [this]

theorem uN_pos (hM : M.Standing) {Δ : ℝ} (hA : M.Assumption1 Δ) : 0 < M.u .N Δ := by
  by_contra h
  rw [not_lt] at h
  have h0 := G_nonpos hM h
  have h1 := hA.2
  have h2 := hA.1
  have : M.G ((M.L + Δ + M.L + M.h + M.l) / 2 - M.γ) = 0 := h0
  rw [this] at h1
  linarith

theorem integrable_max (hM : M.Standing) (u : ℝ) : Integrable (fun φ => max u φ) M.μ := by
  have := hM.isProbabilityMeasure
  exact (integrable_const u).sup hM.integrable_id

theorem integral_max_lt (hM : M.Standing) {u1 u2 : ℝ} (h0 : 0 ≤ u1) (h : u1 < u2) :
    ∫ φ, max u1 φ ∂M.μ < ∫ φ, max u2 φ ∂M.μ := by
  have hi : Integrable (fun φ => max u2 φ - max u1 φ) M.μ :=
    (integrable_max hM u2).sub (integrable_max hM u1)
  have hnn : (0 : ℝ → ℝ) ≤ fun φ => max u2 φ - max u1 φ :=
    fun φ => sub_nonneg.2 (max_le_max h.le le_rfl)
  have := (integral_pos_iff_support_of_nonneg hnn hi).2 (by
    have hpos := hM.μ_Ioo_pos u1 u2 h0 h
    refine lt_of_lt_of_le hpos (measure_mono fun x hx => ?_)
    simp only [Function.mem_support]
    rw [max_eq_right hx.1.le, max_eq_left hx.2.le]
    linarith [hx.2])
  rw [integral_sub (integrable_max hM u2) (integrable_max hM u1)] at this
  linarith

theorem G_gt (hM : M.Standing) {Δ c : ℝ} (hA : M.Assumption1 Δ) (hcg : M.cl' c = M.γ)
    (hc : 0 ≤ c) : c < M.G (M.u .N Δ) := by
  by_contra h
  rw [not_lt] at h
  have hG0 : 0 ≤ M.G (M.u .N Δ) := ProbabilityTheory.cdf_nonneg _ _
  have := hM.cl'_strictMonoOn.monotoneOn hG0 hc h
  have h2 := hA.2
  change M.γ < M.cl' (M.G (M.u .N Δ)) at h2
  linarith

theorem WC_diff (hM : M.Standing) {u1 u2 : ℝ} (h : u1 ≤ u2) :
    (u2 - u1) * M.G u1 ≤ (∫ φ, max u2 φ ∂M.μ) - ∫ φ, max u1 φ ∂M.μ := by
  have := hM.isProbabilityMeasure
  rw [← integral_sub (integrable_max hM u2) (integrable_max hM u1)]
  have h1 : ∫ φ, (Iic u1).indicator (fun _ => u2 - u1) φ ∂M.μ = (u2 - u1) * M.G u1 := by
    rw [integral_indicator_const _ measurableSet_Iic]
    unfold Model.G
    rw [ProbabilityTheory.cdf_eq_real, smul_eq_mul, mul_comm]
  rw [← h1]
  refine integral_mono ?_ ((integrable_max hM u2).sub (integrable_max hM u1)) (fun φ => ?_)
  · exact (integrable_const _).indicator measurableSet_Iic
  · by_cases hφ : φ ≤ u1
    · simp only [indicator_of_mem (mem_Iic.2 hφ)]
      rw [max_eq_left (hφ.trans h), max_eq_left hφ]
    · simp only [indicator_of_notMem (show φ ∉ Iic u1 from hφ)]
      exact sub_nonneg.2 (max_le_max h le_rfl)

theorem WM_N (M : Model m) : M.WM .N = 0 := by
  simp [Model.WM, Model.payoff, Model.grossProfit, Scenario.profile]

theorem WM_F (M : Model m) : M.WM .F = - ∑ i, M.χ i := by
  simp [Model.WM, Model.payoff, Model.grossProfit, Scenario.profile]

theorem WM_P (M : Model m) :
    M.WM .P = - ∑ i ∈ Finset.univ.filter (fun i : Mfr m => i.IsHigh), M.χ i := by
  have h1 : ∀ i : Mfr m, M.payoff Scenario.P.profile i = if i.IsHigh then -M.χ i else 0 := by
    intro i
    by_cases hi : i.IsHigh
    · have : (Scenario.P.profile : Mfr m → Bool) i = true := hi
      simp [Model.payoff, Model.grossProfit, this, hi]
    · have : (Scenario.P.profile : Mfr m → Bool) i = false := by
        simpa [Mfr.IsHigh, Scenario.profile] using hi
      simp [Model.payoff, Model.grossProfit, this, hi]
  simp only [Model.WM, h1, ← Finset.sum_filter, Finset.sum_neg_distrib]

end GTAux2

open PermBlockchain.Failure MeasureTheory in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) (Δ : ℝ) (hΔ : 0 < Δ)
    (hA : M.Assumption1 Δ) :
    M.WC .P Δ ≤ M.WC .F Δ ∧ M.WC .N Δ < M.WC .P Δ := by
  have hu : M.u .P Δ = M.u .F Δ := rfl
  have hl := hM.l_lt_h
  have hL := hM.L_nonneg
  have hpos := GTAux2.uN_pos hM hA
  refine ⟨le_of_eq (by simp only [Model.WC, hu]), ?_⟩
  unfold Model.WC
  apply GTAux2.integral_max_lt hM hpos.le
  simp only [Model.u]
  linarith
