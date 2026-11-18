-- Prove2me | solution 1 for OWMR.canonical_savings
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:48:08.62763+00:00
-- url     : https://prove2.me/submissions/8f99e12a-7ac1-4075-9fe3-abccd1484cbc

import Theorems.Thm_OWMR_F_properties
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_canonical_width_bound
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Lemma 3 (Canonical Savings and Width). For a canonical optimum `(ŝ, Ŝ)` at planning setup cost
`k > 0`, the savings `g(x) = G - F(Ŝ - x)`, with `G = J(k)`, are continuous and concave (as `F`
is convex and Lipschitz), lie in `[0, G]` on `[0, ŵ]` by the canonical conditions, vanish at `ŵ`,
satisfy `g(x) ≤ p (ŵ - x)` by the slope bound of `F`, and integrate to `k` against the renewal
measure on `[0, ŵ)`, by the renewal-reward identity `G = (k + ∫ F(Ŝ - x) U(dx)) / M(ŵ)`, which
also gives `G > 0`. The width bound `β ŵ ≤ G` for `H ≥ h` is the canonical width bound.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

namespace CSav

lemma marg_pos {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂(N.marginal i) := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_pos i

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma intOn_Ico (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (F : ℝ → ℝ) (hF : Continuous F) (w : ℝ) :
    IntegrableOn F (Set.Ico 0 w) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := w)).exists_bound_of_continuousOn
    hF.continuousOn
  exact Measure.integrableOn_of_bounded (renewalMeasure_Ico_lt_top ρ hρ w).ne
    hF.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ico fun x hx =>
      hC x (Set.Ico_subset_Icc_self hx))

lemma bdd_Icc (f : ℝ → ℝ) (hfc : Continuous f) (s S : ℝ) : ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := S)).exists_bound_of_continuousOn
    hfc.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

lemma F_cont {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) : Continuous (N.F i) := by
  obtain ⟨-, -, hlip, -⟩ := F_properties N hN i
  have hK : 0 ≤ N.H i + N.p := by linarith [hN.H_pos i, hN.p_pos]
  exact (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (N.H i + N.p)) fun a b => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]; exact hlip a b).continuous

end CSav

open CSav in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (k sh Sh : ℝ) (hk : 0 < k) (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh) :
    ∃ (G : ℝ) (g : ℝ → ℝ), N.J i k = ENNReal.ofReal G ∧ (∀ x, g x = G - N.F i (Sh - x)) ∧
      Continuous g ∧ ConcaveOn ℝ Set.univ g ∧
      (∀ x ∈ Set.Icc 0 (Sh - sh), 0 ≤ g x ∧ g x ≤ G) ∧ g (Sh - sh) = 0 ∧
      IntegrableOn g (Set.Ico 0 (Sh - sh)) (renewalMeasure (N.marginal i)) ∧
      ∫ x in Set.Ico 0 (Sh - sh), g x ∂(renewalMeasure (N.marginal i)) = k ∧
      (∀ x ∈ Set.Icc 0 (Sh - sh), g x ≤ N.p * ((Sh - sh) - x)) ∧
      0 < G ∧
      (N.h ≤ N.H i → N.h * N.p / (N.h + N.p) * (Sh - sh) ≤ G) := by
  obtain ⟨hF0, hFconv, -, hFslope⟩ := F_properties N hN i
  have hFc := F_cont N hN i
  have hρ := marg_pos N hN i
  set U := renewalMeasure (N.marginal i) with hU
  have hsS : sh < Sh := hcan.1
  set G := N.F i sh with hG
  have hG0 : 0 ≤ G := hF0 sh
  have hJ : N.J i k = ENNReal.ofReal G := hcan.2.2.1.symm
  -- `F ≤ G` on `[ŝ, Ŝ]` (canonical conditions)
  have hFle : ∀ y ∈ Set.Icc sh Sh, N.F i y ≤ G := fun y hy => by
    have h1 := hcan.2.2.2.2 y hy
    rw [← hcan.2.2.1] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hG0).1 h1
  -- the renewal-reward identity for the canonical policy
  have hUfin : U (Set.Ico 0 (Sh - sh)) ≠ ∞ := (renewalMeasure_Ico_lt_top _ hρ _).ne
  set M := (U (Set.Ico 0 (Sh - sh))).toReal with hM
  have hM1 : 1 ≤ M := by
    have := ENNReal.toReal_mono hUfin (one_le_renewal (N.marginal i) (Sh - sh) (by linarith))
    simpa [hM] using this
  have hM0 : 0 < M := by linarith
  have hFw : Continuous fun x => N.F i (Sh - x) := hFc.comp (continuous_const.sub continuous_id)
  set I := ∫ x in Set.Ico 0 (Sh - sh), N.F i (Sh - x) ∂U with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _
  have hRR := ss_renewal_reward (N.marginal i) hρ (N.F i) hFc.measurable hF0 k sh Sh hk.le hsS
    (bdd_Icc _ hFc sh Sh)
  have hGeq : G = (k + I) / M := by
    have h1 : ENNReal.ofReal G = ENNReal.ofReal ((k + I) / M) := by
      rw [← hRR, hcan.2.1, ← hcan.2.2.1]
    exact (ENNReal.ofReal_eq_ofReal_iff hG0 (div_nonneg (by linarith) hM0.le)).1 h1
  have hGM : G * M = k + I := by rw [hGeq]; field_simp
  refine ⟨G, fun x => G - N.F i (Sh - x), hJ, fun x => rfl, continuous_const.sub hFw, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- concavity
    refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
    have h1 := hFconv.2 (Set.mem_univ (Sh - a)) (Set.mem_univ (Sh - b)) hμ hν hμν
    simp only [smul_eq_mul] at h1 ⊢
    have e : μ * (Sh - a) + ν * (Sh - b) = Sh - (μ * a + ν * b) := by
      have : ν = 1 - μ := by linarith
      subst this; ring
    rw [e] at h1
    have : μ * G + ν * G = G := by rw [← add_mul, hμν, one_mul]
    nlinarith
  · -- `0 ≤ g ≤ G` on `[0, ŵ]`
    intro x hx
    refine ⟨?_, ?_⟩
    · have := hFle (Sh - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      linarith
    · linarith [hF0 (Sh - x)]
  · -- `g(ŵ) = 0`
    show G - N.F i (Sh - (Sh - sh)) = 0
    rw [sub_sub_cancel, hG, sub_self]
  · -- integrability on `[0, ŵ)`
    exact intOn_Ico (N.marginal i) hρ _ (continuous_const.sub hFw) _
  · -- `∫_{[0, ŵ)} g dU = k`
    show ∫ x in Set.Ico 0 (Sh - sh), (G - N.F i (Sh - x)) ∂U = k
    have hci : IntegrableOn (fun _ : ℝ => G) (Set.Ico 0 (Sh - sh)) U := integrableOn_const (C := G) hUfin
    rw [integral_sub hci (intOn_Ico (N.marginal i) hρ _ hFw _),
      setIntegral_const, smul_eq_mul, measureReal_def, ← hM, ← hI]
    linarith
  · -- `g(x) ≤ p (ŵ - x)`
    intro x hx
    have := hFslope sh (Sh - x) (by linarith [hx.2])
    show G - N.F i (Sh - x) ≤ N.p * (Sh - sh - x)
    have e : Sh - x - sh = Sh - sh - x := by ring
    rw [e] at this
    linarith
  · -- `G > 0`
    rw [hGeq]; exact div_pos (by linarith) hM0
  · -- the width bound
    intro hhH
    have hW := canonical_width_bound N hN i k sh Sh hcan
    have hh := hN.h_pos
    have hp := hN.p_pos
    have hH := hN.H_pos i
    set c := N.h * (N.H i + N.p) / (N.H i * (N.h + N.p)) with hc
    have hc0 : 0 ≤ c := by positivity
    have hc1 : c ≤ 1 := by
      rw [hc, div_le_one (by positivity)]
      nlinarith
    rw [hJ, ← ENNReal.ofReal_mul hc0] at hW
    have h1 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc0 hG0)).1 hW
    nlinarith
