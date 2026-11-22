-- Prove2me | solution 1 for TruncNewton.Global.wolfe_step_exists
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:19:52.32162+00:00
-- url     : https://prove2.me/submissions/0fdb5142-35cd-4f17-90d0-bfbb08655c0b

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

set_option autoImplicit false

open TruncNewton.Global Filter Topology Set

set_option linter.unusedVariables false in
theorem solution {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (hL : ∀ x0 : E n, Bornology.IsBounded {x | f x ≤ f x0})
    (α β : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2) (hαβ : α < β) (hβ1 : β < 1) :
    ∀ x p : E n, inner ℝ (gradient f x) p < 0 →
      ∃ t : ℝ, 0 < t ∧ cond19 f α x p t ∧ cond110 f β x p t := by
  intro x p hD
  set D := inner ℝ (gradient f x) p with hDdef
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- The restriction `φ(t) = f(x + t p)` and its derivative.
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x + s • p))
      (inner ℝ (gradient f (x + t • p)) p) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • p) p t := by
      simpa using ((hasDerivAt_id t).smul_const p).const_add x
    have h := (hdiff (x + t • p)).hasFDerivAt.comp_hasDerivAt t hline
    have heq : fderiv ℝ f (x + t • p) p = inner ℝ (gradient f (x + t • p)) p := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    exact h.congr_deriv heq
  have hφc : Continuous fun s : ℝ => f (x + s • p) :=
    continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt
  set ψ : ℝ → ℝ := fun s => f (x + s • p) - f x - α * s * D with hψdef
  have hψc : Continuous ψ := by
    simp only [hψdef]
    fun_prop
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  -- `ψ < 0` on some interval `(0, u)`, since `ψ'(0) = (1 - α) D < 0`.
  have hψd : HasDerivAt ψ ((1 - α) * D) 0 := by
    have h1 := (hφ 0).sub_const (f x)
    have h2 : HasDerivAt (fun s : ℝ => α * s * D) (α * D) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul α).mul_const D
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    rw [zero_smul, add_zero, ← hDdef]
    ring
  have hneg : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ s < 0 := by
    have hslope := (hasDerivAt_iff_tendsto_slope.mp hψd).mono_left
      (nhdsWithin_mono _ fun s (hs : s ∈ Ioi (0 : ℝ)) => ne_of_gt hs)
    have hlt : (1 - α) * D < 0 := mul_neg_of_pos_of_neg (by linarith) hD
    filter_upwards [hslope.eventually (eventually_lt_nhds hlt), self_mem_nhdsWithin] with s hs hs0
    rw [slope_def_field, hψ0, sub_zero, sub_zero] at hs
    exact (div_neg_iff.mp hs).elim (fun h => absurd h.2 (not_lt.mpr (le_of_lt hs0))) And.left
  obtain ⟨u, hu, hu_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hneg
  have hu : 0 < u := hu
  -- `ψ > 0` far out along the ray: the level set `{f ≤ f x}` is bounded.
  have hp : p ≠ 0 := by
    rintro rfl
    rw [hDdef, inner_zero_right] at hD
    exact lt_irrefl 0 hD
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  obtain ⟨R, hR⟩ := (hL x).subset_closedBall 0
  have hfar : ∀ t : ℝ, (‖x‖ + R + 1) / ‖p‖ ≤ t → 0 < ψ t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by
      have : 0 ≤ R := by
        have hxR := hR (by simp : x ∈ {y | f y ≤ f x})
        rw [Metric.mem_closedBall, dist_zero_right] at hxR
        linarith [norm_nonneg x]
      positivity) ht
    have hnorm : R < ‖x + t • p‖ := by
      have h1 : ‖x‖ + R + 1 ≤ t * ‖p‖ := by rwa [div_le_iff₀ hpn] at ht
      have h2 : ‖t • p‖ - ‖x‖ ≤ ‖x + t • p‖ := by
        have := norm_sub_norm_le (t • p) (-x)
        simpa [sub_neg_eq_add, add_comm] using this
      rw [norm_smul, Real.norm_of_nonneg ht0.le] at h2
      linarith
    have hnot : ¬ f (x + t • p) ≤ f x := by
      intro hle
      have := hR hle
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    push Not at hnot
    simp only [hψdef]
    have : α * t * D < 0 := by
      have := mul_pos hα ht0
      nlinarith
    linarith
  -- The first point `t*` in `[u/2, T]` with `ψ ≥ 0`.
  set T : ℝ := max ((‖x‖ + R + 1) / ‖p‖) u with hTdef
  have hTu : u ≤ T := le_max_right _ _
  set S : Set ℝ := Icc (u / 2) T ∩ {s | 0 ≤ ψ s} with hSdef
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hψc)
  have hTS : T ∈ S := ⟨⟨by linarith, le_rfl⟩, (hfar T (le_max_left _ _)).le⟩
  have hSb : BddBelow S := ⟨u / 2, fun s hs => hs.1.1⟩
  set ts := sInf S with htsdef
  have htsS : ts ∈ S := hSc.csInf_mem ⟨T, hTS⟩ hSb
  have hts_pos : 0 < ts := lt_of_lt_of_le (by linarith) htsS.1.1
  have hψts : 0 ≤ ψ ts := htsS.2
  -- `ψ < 0` on `(0, ts)`.
  have hbelow : ∀ s, 0 < s → s < ts → ψ s < 0 := by
    intro s hs0 hsts
    by_cases hsu : s < u
    · exact hu_sub ⟨hs0, hsu⟩
    · push Not at hsu
      by_contra hcon
      push Not at hcon
      have hsS : s ∈ S := ⟨⟨by linarith, by linarith [htsS.1.2]⟩, hcon⟩
      have := csInf_le hSb hsS
      linarith
  -- Mean value theorem for `φ` on `[0, ts]`.
  obtain ⟨s, hs, hsd⟩ := exists_hasDerivAt_eq_slope (fun r : ℝ => f (x + r • p))
    (fun r => inner ℝ (gradient f (x + r • p)) p) hts_pos hφc.continuousOn
    (fun r _ => hφ r)
  refine ⟨s, hs.1, ?_, ?_⟩
  · -- Armijo: `ψ s < 0`.
    have := hbelow s hs.1 hs.2
    simp only [hψdef] at this
    unfold cond19
    rw [← hDdef]
    linarith
  · -- Curvature: `φ'(s) = (φ(ts) - φ(0))/ts ≥ α D ≥ β D`.
    unfold cond110
    rw [← hDdef, hsd]
    simp only [zero_smul, add_zero, sub_zero]
    have hψts' : α * ts * D ≤ f (x + ts • p) - f x := by
      simp only [hψdef] at hψts
      linarith
    rw [le_div_iff₀ hts_pos]
    have hDts : D * ts < 0 := mul_neg_of_neg_of_pos hD hts_pos
    have hβα : β * (D * ts) ≤ α * (D * ts) := mul_le_mul_of_nonpos_right hαβ.le hDts.le
    linarith
