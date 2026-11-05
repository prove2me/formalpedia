-- Prove2me | solution 1 for PermBlockchain.Failure.proposition_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:38.529048+00:00
-- url     : https://prove2.me/submissions/358aec6b-f58e-4218-be36-99fc78532975

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


namespace GTAux3
open PermBlockchain.Failure

variable {m : ℕ} {M : Model m}

theorem WV_lower (hM : M.Standing) {c : ℝ} (hc : 0 < c) (hcg : M.cl' c = M.γ) (X : Scenario)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) : -M.cl c ≤ M.WV X Δ := by
  have hγ := hM.γ_pos
  have hhl := hM.l_lt_h
  have hs : 0 ≤ M.sl X Δ := by
    cases X <;> simp only [Model.sl] <;> exact GTAux.cinv_nonneg M _
  have hsc : M.sl X Δ ≤ c := by
    cases X <;> simp only [Model.sl]
    · exact GTAux.cinv_le hM hc.le hcg (by linarith)
    · exact GTAux.cinv_le hM hc.le hcg (by linarith)
    · exact GTAux.cinv_le hM hc.le hcg le_rfl
  have hp : 0 ≤ M.Ψl X Δ := by
    cases X <;> simp only [Model.Ψl]
    · exact le_max_right _ _
    · exact le_max_right _ _
    · exact hγ.le
  have := hM.cl_strictMonoOn.monotoneOn hs hc.le hsc
  rw [GTAux.WV_eq]
  nlinarith [mul_nonneg hp hs]

theorem big (hM : M.Standing) {c : ℝ} (hc : 0 < c) (hcg : M.cl' c = M.γ) {X : Scenario}
    (hX : X ≠ .N) {Δ : ℝ} (hΔ : 0 ≤ Δ) (hA : M.Assumption1 Δ)
    (hbig : 0 < M.WM X - M.γ * c + (Δ + M.h - M.l) / 2 * c) : M.W .N Δ < M.W X Δ := by
  have hl := hM.l_lt_h
  have hu : M.u X Δ = M.L + Δ + M.h - M.γ := by
    cases X
    · rfl
    · rfl
    · exact absurd rfl hX
  have hd : M.u X Δ - M.u .N Δ = (Δ + M.h - M.l) / 2 := by
    rw [hu]; simp only [Model.u]; ring
  have hWC := GTAux2.WC_diff hM (u1 := M.u .N Δ) (u2 := M.u X Δ) (by linarith)
  have hG := GTAux2.G_gt hM hA hcg hc.le
  have hWVN : M.WV .N Δ = M.γ * c - M.cl c := by
    rw [GTAux.WV_eq]; simp only [Model.Ψl, Model.sl, GTAux.cinv_eq hM hc.le hcg]
  have hWV := WV_lower hM hc hcg X hΔ
  have hdnn : 0 ≤ M.u X Δ - M.u .N Δ := by rw [hd]; linarith
  have hmul := mul_le_mul_of_nonneg_left hG.le hdnn
  rw [hd] at hWC hmul
  have hN := GTAux2.WM_N M
  unfold Model.W
  unfold Model.WC at *
  rw [hN, hWVN]
  nlinarith

end GTAux3

open PermBlockchain.Failure in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) :
    (∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ → M.W .N Δ < M.W .F Δ) ∧
    (∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ → M.W .N Δ < M.W .P Δ) ∧
    (∀ Δ : ℝ, 0 < Δ → M.Assumption1 Δ → ∃ χ₀ : ℝ, ∀ χ' : Mfr m → ℝ, (∀ i, 0 < χ' i) →
      χ₀ < ∑ i, χ' i → (M.withχ χ').W .F Δ < (M.withχ χ').W .N Δ) ∧
    (∀ Δ : ℝ, 0 < Δ → M.Assumption1 Δ → ∃ χ₀ : ℝ, ∀ χ' : Mfr m → ℝ, (∀ i, 0 < χ' i) →
      χ₀ < ∑ i ∈ Finset.univ.filter (fun i : Mfr m => i.IsHigh), χ' i →
      (M.withχ χ').W .P Δ < (M.withχ χ').W .N Δ) := by
  have hl := hM.l_lt_h
  have gen : ∀ X : Scenario, X ≠ .N → ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ →
      M.W .N Δ < M.W X Δ := by
    intro X hX
    by_cases hex : ∃ Δ', M.Assumption1 Δ'
    · obtain ⟨Δ', hΔ'⟩ := hex
      obtain ⟨c, hc, hcg⟩ := GTAux.exists_c hM hΔ'
      refine ⟨max 0 (2 * |M.WM X - M.γ * c| / c), fun Δ hΔ hA => ?_⟩
      have h0 : 0 < Δ := lt_of_le_of_lt (le_max_left _ _) hΔ
      have h1 : 2 * |M.WM X - M.γ * c| / c < Δ := lt_of_le_of_lt (le_max_right _ _) hΔ
      refine GTAux3.big hM hc hcg hX h0.le hA ?_
      have h2 : 2 * |M.WM X - M.γ * c| < Δ * c := by rwa [div_lt_iff₀ hc] at h1
      have h3 := neg_abs_le (M.WM X - M.γ * c)
      have h4 := mul_pos (sub_pos.2 hl) hc
      nlinarith
    · exact ⟨0, fun Δ _ hA => absurd ⟨Δ, hA⟩ hex⟩
  refine ⟨gen .F (by decide), gen .P (by decide), ?_, ?_⟩
  · intro Δ _ _
    refine ⟨M.WV .F Δ + M.WC .F Δ - M.WV .N Δ - M.WC .N Δ, fun χ' _ hlt => ?_⟩
    have e1 : (M.withχ χ').W .F Δ = M.WV .F Δ + (-∑ i, χ' i) + M.WC .F Δ := by
      show (M.withχ χ').WV .F Δ + (M.withχ χ').WM .F + (M.withχ χ').WC .F Δ = _
      rw [GTAux2.WM_F]; rfl
    have e2 : (M.withχ χ').W .N Δ = M.WV .N Δ + 0 + M.WC .N Δ := by
      show (M.withχ χ').WV .N Δ + (M.withχ χ').WM .N + (M.withχ χ').WC .N Δ = _
      rw [GTAux2.WM_N]; rfl
    rw [e1, e2]; linarith
  · intro Δ _ _
    refine ⟨M.WV .P Δ + M.WC .P Δ - M.WV .N Δ - M.WC .N Δ, fun χ' _ hlt => ?_⟩
    have e1 : (M.withχ χ').W .P Δ = M.WV .P Δ +
        (-∑ i ∈ Finset.univ.filter (fun i : Mfr m => i.IsHigh), χ' i) + M.WC .P Δ := by
      show (M.withχ χ').WV .P Δ + (M.withχ χ').WM .P + (M.withχ χ').WC .P Δ = _
      rw [GTAux2.WM_P]; rfl
    have e2 : (M.withχ χ').W .N Δ = M.WV .N Δ + 0 + M.WC .N Δ := by
      show (M.withχ χ').WV .N Δ + (M.withχ χ').WM .N + (M.withχ χ').WC .N Δ = _
      rw [GTAux2.WM_N]; rfl
    rw [e1, e2]; linarith
