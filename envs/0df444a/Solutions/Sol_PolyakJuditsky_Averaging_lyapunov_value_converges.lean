-- Prove2me | solution 1 for PolyakJuditsky.Averaging.lyapunov_value_converges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:50:50.454723+00:00
-- url     : https://prove2.me/submissions/82b78fc6-3776-471a-a817-f04df1f4b024

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

theorem aux_lvc_inner_grad {N : ℕ} (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (y v : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (gradient V y) v = fderiv ℝ V y v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

/-- Descent inequality for a function with Lipschitz gradient (with constant `L`, not `L/2`). -/
theorem aux_lvc_descent {N : ℕ} (V : EuclideanSpace ℝ (Fin N) → ℝ) (hV : Differentiable ℝ V)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ x y, ‖gradient V x - gradient V y‖ ≤ L * ‖x - y‖)
    (a h : EuclideanSpace ℝ (Fin N)) :
    V (a + h) ≤ V a + inner ℝ (gradient V a) h + L * ‖h‖ ^ 2 := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => V (a + s • h))
      (inner ℝ (gradient V (a + s • h)) h) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => a + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add a
    have h2 := (hV (a + s • h)).hasFDerivAt.comp_hasDerivAt s h1
    rw [aux_lvc_inner_grad]
    exact h2
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => V (a + s • h))
    (fun s => inner ℝ (gradient V (a + s • h)) h) zero_lt_one
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt) (fun s _ => hderiv s)
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hc'
  have key : inner ℝ (gradient V (a + c • h)) h - inner ℝ (gradient V a) h ≤ L * ‖h‖ ^ 2 := by
    rw [← inner_sub_left]
    calc inner ℝ (gradient V (a + c • h) - gradient V a) h
        ≤ ‖gradient V (a + c • h) - gradient V a‖ * ‖h‖ := real_inner_le_norm _ _
      _ ≤ (L * ‖(a + c • h) - a‖) * ‖h‖ := by gcongr; exact hL _ _
      _ = L * c * ‖h‖ ^ 2 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.1.le]; ring
      _ ≤ L * ‖h‖ ^ 2 := by
        have h1 := hc.2.le
        have h2 : 0 ≤ L * ‖h‖ ^ 2 := by positivity
        nlinarith
  linarith

end PolyakJuditsky.Averaging

open PolyakJuditsky.Averaging

set_option maxHeartbeats 4000000 in
theorem solution {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (G S : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (hR : Continuous R) (h31 : LyapunovAssumption R xstar V)
    (h32 : LinearizationAssumption R xstar G lam)
    (h33 : NoiseAssumption P ℱ x₀ γ R ξ ξ0 xstar S) (h34 : StepAssumption γ lam) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, Tendsto (fun t => V (saIterate x₀ γ R ξ t ω - xstar)) atTop (𝓝 c) := by
  classical
  obtain ⟨hVd, lam₁, α, ε, L, hlam₁, hα, hε, hL, hVlow, hLip, hV0, hpos, hloc⟩ := h31
  obtain ⟨K₂, hK₂⟩ := h33.growth
  set K : ℝ := max K₂ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  obtain ⟨x, hx⟩ : ∃ x : ℕ → Ω → EuclideanSpace ℝ (Fin N), x = saIterate x₀ γ R ξ := ⟨_, rfl⟩
  have hxsucc : ∀ t, x (t + 1) = fun ω => x t ω - γ (t + 1) • (R (x t ω) + ξ (t + 1) ω) := by
    intro t; subst hx; rfl
  have hx0 : x 0 = fun _ => x₀ := by subst hx; rfl
  have hK₂' : ∀ t, ∀ᵐ ω ∂P, P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω + ‖R (x t ω)‖ ^ 2
      ≤ K₂ * (1 + ‖x t ω‖ ^ 2) := by subst hx; exact hK₂
  suffices hmain : ∀ᵐ ω ∂P, ∃ c : ℝ, Tendsto (fun t => V (x t ω - xstar)) atTop (𝓝 c) by
    subst hx; exact hmain
  clear hK₂
  -- measurability
  have hξm : ∀ t, Measurable[ℱ t] (ξ t) := h33.adapted
  have hxm : ∀ t, Measurable[ℱ t] (x t) := by
    intro t
    induction t with
    | zero => rw [hx0]; exact measurable_const
    | succ t ih =>
      have ih' : Measurable[ℱ (t + 1)] (x t) := ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl
      rw [hxsucc]
      have h1 : Measurable[ℱ (t + 1)] (fun ω => R (x t ω) + ξ (t + 1) ω) :=
        (hR.measurable.comp ih').add (hξm (t + 1))
      have h2 : Measurable[ℱ (t + 1)] (fun ω => γ (t + 1) • (R (x t ω) + ξ (t + 1) ω)) :=
        h1.const_smul (γ (t + 1))
      exact ih'.sub h2
  -- growth consequences
  have hcnn : ∀ t, ∀ᵐ ω ∂P, 0 ≤ P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω := fun t =>
    condExp_nonneg (ae_of_all _ fun ω => by positivity)
  have hgrow : ∀ t, ∀ᵐ ω ∂P, P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω + ‖R (x t ω)‖ ^ 2
      ≤ K * (1 + ‖x t ω‖ ^ 2) := by
    intro t
    filter_upwards [hK₂' t] with ω hω
    have : K₂ * (1 + ‖x t ω‖ ^ 2) ≤ K * (1 + ‖x t ω‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  have hRb : ∀ t, ∀ᵐ ω ∂P, ‖R (x t ω)‖ ^ 2 ≤ K * (1 + ‖x t ω‖ ^ 2) := by
    intro t; filter_upwards [hgrow t, hcnn t] with ω h1 h2; linarith
  -- square integrability
  have hξL2 : ∀ t, MemLp (ξ t) 2 P := h33.memLp
  have hRL2 : ∀ t, MemLp (x t) 2 P → MemLp (fun ω => R (x t ω)) 2 P := by
    intro t ih
    refine MemLp.of_le (g := fun ω => (K + 1) * (1 + ‖x t ω‖)) ?_ ?_ ?_
    · have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
      have h2 : MemLp (fun ω => ‖x t ω‖) 2 P := ih.norm
      have h3 : MemLp (fun ω => (1 : ℝ) + ‖x t ω‖) 2 P := h1.add h2
      exact h3.const_mul (K + 1)
    · exact hR.comp_aestronglyMeasurable ih.1
    · filter_upwards [hRb t] with ω hω
      have hn := norm_nonneg (x t ω)
      have hr := norm_nonneg (R (x t ω))
      rw [Real.norm_of_nonneg (by positivity)]
      have h2 : ‖R (x t ω)‖ ^ 2 ≤ ((K + 1) * (1 + ‖x t ω‖)) ^ 2 := by
        calc ‖R (x t ω)‖ ^ 2 ≤ K * (1 + ‖x t ω‖ ^ 2) := hω
          _ ≤ (K + 1) ^ 2 * (1 + ‖x t ω‖) ^ 2 := by
            apply mul_le_mul <;> nlinarith
          _ = ((K + 1) * (1 + ‖x t ω‖)) ^ 2 := by ring
      exact (pow_le_pow_iff_left₀ hr (by positivity) two_ne_zero).1 h2
  have hxL2 : ∀ t, MemLp (x t) 2 P := by
    intro t
    induction t with
    | zero => rw [hx0]; exact memLp_const x₀
    | succ t ih =>
      rw [hxsucc]
      have h1 : MemLp (fun ω => R (x t ω) + ξ (t + 1) ω) 2 P := (hRL2 t ih).add (hξL2 (t + 1))
      have h2 : MemLp (fun ω => γ (t + 1) • (R (x t ω) + ξ (t + 1) ω)) 2 P :=
        h1.const_smul (γ (t + 1))
      exact ih.sub h2
  have hxsq : ∀ t, Integrable (fun ω => ‖x t ω‖ ^ 2) P := fun t =>
    (memLp_two_iff_integrable_sq_norm (hxL2 t).1).1 (hxL2 t)
  have hξsq : ∀ t, Integrable (fun ω => ‖ξ t ω‖ ^ 2) P := fun t =>
    (memLp_two_iff_integrable_sq_norm (hξL2 t).1).1 (hξL2 t)
  have hRsq : ∀ t, Integrable (fun ω => ‖R (x t ω)‖ ^ 2) P := fun t =>
    (memLp_two_iff_integrable_sq_norm (hRL2 t (hxL2 t)).1).1 (hRL2 t (hxL2 t))
  have hpoly : ∀ t (A B : ℝ), Integrable (fun ω => A + B * ‖x t ω‖ ^ 2) P := fun t A B =>
    (integrable_const A).add ((hxsq t).const_mul B)
  -- bounds on V and its gradient
  set c₁ : ℝ := ‖gradient V 0‖ with hc₁
  have hc₁0 : 0 ≤ c₁ := norm_nonneg _
  have hVnn : ∀ y, 0 ≤ V y := fun y => le_trans (by positivity) (hVlow y)
  have hVup : ∀ y, V y ≤ (c₁ + L) * (1 + ‖y‖ ^ 2) := by
    intro y
    have h := aux_lvc_descent V hVd L hL.le hLip 0 y
    rw [zero_add, hV0] at h
    have h2 : inner ℝ (gradient V 0) y ≤ c₁ * ‖y‖ := real_inner_le_norm _ _
    have hy := norm_nonneg y
    have h3 : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
    nlinarith
  have hgb : ∀ y, ‖gradient V y‖ ≤ c₁ + L * ‖y‖ := by
    intro y
    have h1 := hLip y 0
    have h2 := norm_sub_norm_le (gradient V y) (gradient V 0)
    rw [sub_zero] at h1
    linarith
  -- the Lyapunov process
  set Vt : ℕ → Ω → ℝ := fun t ω => V (x t ω - xstar) with hVtdef
  have hVtmeas : ∀ t, Measurable[ℱ t] (Vt t) := fun t =>
    hVd.continuous.measurable.comp ((hxm t).sub measurable_const)
  have hVti : ∀ t, Integrable (Vt t) P := by
    intro t
    refine (hpoly t ((c₁ + L) * (1 + 2 * ‖xstar‖ ^ 2)) (2 * (c₁ + L))).mono'
      ((hVtmeas t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hVnn _)]
    have h1 := hVup (x t ω - xstar)
    have h2 : ‖x t ω - xstar‖ ≤ ‖x t ω‖ + ‖xstar‖ := norm_sub_le _ _
    have h3 := norm_nonneg (x t ω - xstar)
    have h4 : ‖x t ω - xstar‖ ^ 2 ≤ 2 * ‖x t ω‖ ^ 2 + 2 * ‖xstar‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x t ω‖ - ‖xstar‖)]
    have h5 : 0 ≤ c₁ + L := by linarith
    calc Vt t ω ≤ (c₁ + L) * (1 + ‖x t ω - xstar‖ ^ 2) := h1
      _ ≤ (c₁ + L) * (1 + (2 * ‖x t ω‖ ^ 2 + 2 * ‖xstar‖ ^ 2)) := by gcongr
      _ = _ := by ring
  -- gradient measurability
  have hgcont : Continuous (gradient V) := by
    have : LipschitzWith ⟨L, hL.le⟩ (gradient V) :=
      LipschitzWith.of_dist_le_mul fun y z => by rw [dist_eq_norm, dist_eq_norm]; exact hLip y z
    exact this.continuous
  have hgm : ∀ t, Measurable[ℱ t] (fun ω => gradient V (x t ω - xstar)) := fun t =>
    hgcont.measurable.comp ((hxm t).sub measurable_const)
  -- key one-step conditional inequality
  have hkey : ∀ t, P[Vt (t + 1) | ℱ t] ≤ᵐ[P]
      fun ω => Vt t ω + 2 * L * γ (t + 1) ^ 2 * K * (1 + ‖x t ω‖ ^ 2) := by
    intro t
    have hc : 0 < γ (t + 1) := h34.1 (t + 1) (by omega)
    set c := γ (t + 1) with hcdef
    set k : ℝ := 2 * L * c ^ 2 with hkdef
    have hk0 : 0 ≤ k := by positivity
    set gt : Ω → EuclideanSpace ℝ (Fin N) := fun ω => (-c) • gradient V (x t ω - xstar)
      with hgtdef
    set F1 : Ω → ℝ := fun ω => Vt t ω + k * ‖R (x t ω)‖ ^ 2 with hF1def
    set F2 : Ω → ℝ := fun ω => innerSL ℝ (gt ω) (ξ (t + 1) ω) with hF2def
    set F3 : Ω → ℝ := fun ω => k * ‖ξ (t + 1) ω‖ ^ 2 with hF3def
    have hgtmeas : Measurable[ℱ t] gt := (hgm t).const_smul (-c)
    have hgtm : StronglyMeasurable[ℱ t] gt := hgtmeas.stronglyMeasurable
    have hF1c : Continuous (fun v : EuclideanSpace ℝ (Fin N) => V (v - xstar) + k * ‖R v‖ ^ 2) :=
      (hVd.continuous.comp (continuous_id.sub continuous_const)).add
        (continuous_const.mul (hR.norm.pow 2))
    have hF1m : StronglyMeasurable[ℱ t] F1 :=
      (hF1c.measurable.comp (hxm t)).stronglyMeasurable
    have hF1i : Integrable F1 P := (hVti t).add ((hRsq t).const_mul k)
    have hF3i : Integrable F3 P := (hξsq (t + 1)).const_mul k
    set D : ℝ := c₁ + L * ‖xstar‖ with hDdef
    have hF2i : Integrable F2 P := by
      refine ((hpoly t (2 * c ^ 2 * D ^ 2) (2 * c ^ 2 * L ^ 2)).add (hξsq (t + 1))).mono' ?_
        (ae_of_all _ fun ω => ?_)
      · have hm1 : Measurable gt := hgtmeas.mono (ℱ.le t) le_rfl
        have hm2 : Measurable (ξ (t + 1)) := (hξm (t + 1)).mono (ℱ.le (t + 1)) le_rfl
        exact (hm1.inner hm2).aestronglyMeasurable
      · simp only [hF2def, innerSL_apply_apply, Real.norm_eq_abs, Pi.add_apply]
        have h1 := abs_real_inner_le_norm (gt ω) (ξ (t + 1) ω)
        have h2 : ‖gt ω‖ ≤ c * (D + L * ‖x t ω‖) := by
          simp only [hgtdef]
          rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hc]
          apply mul_le_mul_of_nonneg_left _ hc.le
          have h3 := hgb (x t ω - xstar)
          have h4 : ‖x t ω - xstar‖ ≤ ‖x t ω‖ + ‖xstar‖ := norm_sub_le _ _
          have h5 : L * ‖x t ω - xstar‖ ≤ L * (‖x t ω‖ + ‖xstar‖) :=
            mul_le_mul_of_nonneg_left h4 hL.le
          simp only [hDdef]; linarith
        have hg0 := norm_nonneg (gt ω)
        have hz0 := norm_nonneg (ξ (t + 1) ω)
        have hx0' := norm_nonneg (x t ω)
        have hD0 : 0 ≤ D := by positivity
        have h6 : ‖gt ω‖ ^ 2 ≤ 2 * c ^ 2 * D ^ 2 + 2 * c ^ 2 * L ^ 2 * ‖x t ω‖ ^ 2 := by
          have h7 : ‖gt ω‖ ^ 2 ≤ (c * (D + L * ‖x t ω‖)) ^ 2 :=
            pow_le_pow_left₀ hg0 h2 2
          nlinarith [sq_nonneg (D - L * ‖x t ω‖)]
        nlinarith [sq_nonneg (‖gt ω‖ - ‖ξ (t + 1) ω‖)]
    have hpt : ∀ ω, Vt (t + 1) ω ≤ (F1 + F2 + F3) ω := by
      intro ω
      simp only [Pi.add_apply, hF1def, hF2def, hF3def, hgtdef, hVtdef, innerSL_apply_apply]
      have hxe : x (t + 1) ω - xstar
          = (x t ω - xstar) + (-c) • (R (x t ω) + ξ (t + 1) ω) := by
        rw [hxsucc]; simp only [neg_smul]; abel
      rw [hxe]
      have hd := aux_lvc_descent V hVd L hL.le hLip (x t ω - xstar)
        ((-c) • (R (x t ω) + ξ (t + 1) ω))
      have hin : inner ℝ (gradient V (x t ω - xstar)) ((-c) • (R (x t ω) + ξ (t + 1) ω))
          = -c * inner ℝ (gradient V (x t ω - xstar)) (R (x t ω))
            + inner ℝ ((-c) • gradient V (x t ω - xstar)) (ξ (t + 1) ω) := by
        rw [inner_smul_right, inner_add_right, real_inner_smul_left]; ring
      have hnr : ‖(-c) • (R (x t ω) + ξ (t + 1) ω)‖ ^ 2
          ≤ 2 * c ^ 2 * ‖R (x t ω)‖ ^ 2 + 2 * c ^ 2 * ‖ξ (t + 1) ω‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hc, mul_pow]
        have h1 := norm_add_le (R (x t ω)) (ξ (t + 1) ω)
        have h2 := norm_nonneg (R (x t ω) + ξ (t + 1) ω)
        have h3 : ‖R (x t ω) + ξ (t + 1) ω‖ ^ 2 ≤ 2 * ‖R (x t ω)‖ ^ 2 + 2 * ‖ξ (t + 1) ω‖ ^ 2 := by
          nlinarith [sq_nonneg (‖R (x t ω)‖ - ‖ξ (t + 1) ω‖), norm_nonneg (R (x t ω)),
            norm_nonneg (ξ (t + 1) ω)]
        have h4 : 0 ≤ c ^ 2 := by positivity
        calc c ^ 2 * ‖R (x t ω) + ξ (t + 1) ω‖ ^ 2
            ≤ c ^ 2 * (2 * ‖R (x t ω)‖ ^ 2 + 2 * ‖ξ (t + 1) ω‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h3 h4
          _ = _ := by ring
      have hRp : 0 ≤ inner ℝ (gradient V (x t ω - xstar)) (R (x t ω)) := by
        by_cases hxx : x t ω = xstar
        · have h1 := hloc (x t ω) (by rw [hxx, sub_self, norm_zero]; exact hε.le)
          have h2 := hVnn (x t ω - xstar)
          have h3 : 0 ≤ lam₁ * V (x t ω - xstar) := mul_nonneg hlam₁.le h2
          linarith
        · exact (hpos (x t ω) hxx).le
      have hcR : 0 ≤ c * inner ℝ (gradient V (x t ω - xstar)) (R (x t ω)) := mul_nonneg hc.le hRp
      have hLn : L * ‖(-c) • (R (x t ω) + ξ (t + 1) ω)‖ ^ 2
          ≤ L * (2 * c ^ 2 * ‖R (x t ω)‖ ^ 2 + 2 * c ^ 2 * ‖ξ (t + 1) ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnr hL.le
      simp only [hkdef]
      nlinarith
    have h1 := condExp_mono (m := ℱ t) (hVti (t + 1)) ((hF1i.add hF2i).add hF3i) (ae_of_all _ hpt)
    have h2 := condExp_add (hF1i.add hF2i) hF3i (ℱ t)
    have h3 := condExp_add hF1i hF2i (ℱ t)
    have h4 : P[F1 | ℱ t] = F1 := condExp_of_stronglyMeasurable (ℱ.le t) hF1m hF1i
    have h5 : P[F2 | ℱ t] =ᵐ[P] fun ω => innerSL ℝ (gt ω) (P[ξ (t + 1) | ℱ t] ω) :=
      condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hgtm hF2i
        ((hξL2 (t + 1)).integrable one_le_two)
    have h6 := h33.mds t
    have h7 : P[F3 | ℱ t] =ᵐ[P] fun ω => k * P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω :=
      condExp_smul (μ := P) k (fun ω' => ‖ξ (t + 1) ω'‖ ^ 2) (ℱ t)
    filter_upwards [h1, h2, h3, h5, h6, h7, hgrow t] with ω e1 e2 e3 e5 e6 e7 e8
    rw [h4] at e3
    simp only [Pi.add_apply] at e2 e3
    rw [e6] at e5
    simp only [Pi.zero_apply, map_zero] at e5
    have e9 : k * P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω + k * ‖R (x t ω)‖ ^ 2
        ≤ k * (K * (1 + ‖x t ω‖ ^ 2)) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left e8 hk0
    calc P[Vt (t + 1) | ℱ t] ω ≤ P[F1 + F2 + F3 | ℱ t] ω := e1
      _ = F1 ω + P[F2 | ℱ t] ω + P[F3 | ℱ t] ω := by rw [e2, e3]
      _ = Vt t ω + k * ‖R (x t ω)‖ ^ 2 + 0
          + k * P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω := by rw [e5, e7]
      _ ≤ Vt t ω + 2 * L * c ^ 2 * K * (1 + ‖x t ω‖ ^ 2) := by
        simp only [hkdef] at e9 ⊢; nlinarith
  -- recursive inequality in Robbins–Siegmund form
  set A : ℝ := 4 * L * K / α with hAdef
  set B : ℝ := 2 * L * K * (1 + 2 * ‖xstar‖ ^ 2) with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set a : ℕ → ℝ := fun s => A * γ (s + 1) ^ 2 with hadef
  set b : ℕ → ℝ := fun s => B * γ (s + 1) ^ 2 with hbdef
  have ha0 : ∀ s, 0 ≤ a s := fun s => by positivity
  have hb0 : ∀ s, 0 ≤ b s := fun s => by positivity
  have hγsq : Summable (fun t : ℕ => γ (t + 1) ^ 2) := h34.2.2.2.2
  have has : Summable a := hγsq.mul_left A
  have hbs : Summable b := hγsq.mul_left B
  have hkey2 : ∀ t, P[Vt (t + 1) | ℱ t] ≤ᵐ[P] fun ω => (1 + a t) * Vt t ω + b t := by
    intro t
    filter_upwards [hkey t] with ω hω
    refine hω.trans ?_
    have hΔ : ‖x t ω - xstar‖ ^ 2 ≤ Vt t ω / α := by
      rw [le_div_iff₀ hα]; have := hVlow (x t ω - xstar); simp only [hVtdef]; linarith
    have hxx : ‖x t ω‖ ^ 2 ≤ 2 * ‖x t ω - xstar‖ ^ 2 + 2 * ‖xstar‖ ^ 2 := by
      have h1 := norm_sub_norm_le (x t ω) xstar
      have h2 := norm_nonneg (x t ω)
      have h3 := norm_nonneg xstar
      have h4 : ‖x t ω‖ ≤ ‖x t ω - xstar‖ + ‖xstar‖ := by linarith
      have h5 : ‖x t ω‖ ^ 2 ≤ (‖x t ω - xstar‖ + ‖xstar‖) ^ 2 := pow_le_pow_left₀ h2 h4 2
      nlinarith [sq_nonneg (‖x t ω - xstar‖ - ‖xstar‖)]
    have hm : 0 ≤ 2 * L * γ (t + 1) ^ 2 * K := by positivity
    have h6 : 1 + ‖x t ω‖ ^ 2 ≤ (1 + 2 * ‖xstar‖ ^ 2) + 2 * (Vt t ω / α) := by linarith
    calc Vt t ω + 2 * L * γ (t + 1) ^ 2 * K * (1 + ‖x t ω‖ ^ 2)
        ≤ Vt t ω + 2 * L * γ (t + 1) ^ 2 * K * ((1 + 2 * ‖xstar‖ ^ 2) + 2 * (Vt t ω / α)) := by
          have := mul_le_mul_of_nonneg_left h6 hm
          linarith
      _ = (1 + a t) * Vt t ω + b t := by
          simp only [hadef, hbdef, hAdef, hBdef]; ring
  -- normalisation
  set Ssum : ℕ → ℝ := fun t => ∑ s ∈ Finset.range t, a s with hSdef
  set e : ℕ → ℝ := fun t => Real.exp (-Ssum t) with hedef
  have he0 : ∀ t, 0 < e t := fun t => Real.exp_pos _
  have hSnn : ∀ t, 0 ≤ Ssum t := fun t => Finset.sum_nonneg (fun s _ => ha0 s)
  have he1 : ∀ t, e t ≤ 1 := fun t => by
    simp only [hedef]; rw [Real.exp_le_one_iff]; linarith [hSnn t]
  have hee : ∀ t, e (t + 1) * (1 + a t) ≤ e t := by
    intro t
    have h1 : e (t + 1) = e t * Real.exp (-a t) := by
      simp only [hedef, hSdef, Finset.sum_range_succ, neg_add, Real.exp_add]
    rw [h1, mul_assoc]
    have h2 : Real.exp (-a t) * (1 + a t) ≤ 1 := by
      have h5 := Real.add_one_le_exp (a t)
      have h3 : Real.exp (-a t) * Real.exp (a t) = 1 := by rw [← Real.exp_add]; simp
      have h4 := Real.exp_pos (-a t)
      nlinarith
    calc e t * (Real.exp (-a t) * (1 + a t)) ≤ e t * 1 :=
          mul_le_mul_of_nonneg_left h2 (he0 t).le
      _ = e t := mul_one _
  set cc : ℕ → ℝ := fun s => b s * e (s + 1) with hccdef
  have hcc0 : ∀ s, 0 ≤ cc s := fun s => mul_nonneg (hb0 s) (he0 _).le
  have hccs : Summable cc := Summable.of_nonneg_of_le hcc0 (fun s => by
      simp only [hccdef]
      calc b s * e (s + 1) ≤ b s * 1 := mul_le_mul_of_nonneg_left (he1 _) (hb0 s)
        _ = b s := mul_one _) hbs
  set C : ℝ := ∑' s, cc s with hCdef
  set Z : ℕ → Ω → ℝ := fun t ω => e t * Vt t ω + (C - ∑ s ∈ Finset.range t, cc s) with hZdef
  have hZm : ∀ t, Measurable[ℱ t] (Z t) := by
    intro t
    have hc : Continuous (fun r : ℝ => e t * r + (C - ∑ s ∈ Finset.range t, cc s)) := by
      fun_prop
    exact hc.measurable.comp (hVtmeas t)
  have hZi : ∀ t, Integrable (Z t) P := fun t =>
    ((hVti t).const_mul (e t)).add (integrable_const _)
  have hZnn : ∀ t ω, 0 ≤ Z t ω := by
    intro t ω
    have h1 : ∑ s ∈ Finset.range t, cc s ≤ C := hccs.sum_le_tsum _ (fun s _ => hcc0 s)
    have h2 : 0 ≤ e t * Vt t ω := mul_nonneg (he0 t).le (hVnn _)
    simp only [hZdef]; linarith
  have hsup : Supermartingale Z ℱ P := by
    refine supermartingale_nat (fun t => (hZm t).stronglyMeasurable) hZi (fun t => ?_)
    have hZe : Z (t + 1) = (e (t + 1) • Vt (t + 1))
        + fun _ => (C - ∑ s ∈ Finset.range (t + 1), cc s) := by
      funext ω; simp only [hZdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hZe]
    have h1 := condExp_add (m := ℱ t) (Integrable.smul (e (t + 1)) (hVti (t + 1)))
      (integrable_const (C - ∑ s ∈ Finset.range (t + 1), cc s))
    have h2 := condExp_smul (μ := P) (e (t + 1)) (Vt (t + 1)) (ℱ t)
    have h3 := condExp_const (μ := P) (ℱ.le t) (C - ∑ s ∈ Finset.range (t + 1), cc s)
    filter_upwards [h1, h2, hkey2 t] with ω e1 e2 e3
    rw [e1, Pi.add_apply, e2, h3]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ, hZdef, hccdef]
    have h4 := hee t
    have h5 : e (t + 1) * P[Vt (t + 1)|ℱ t] ω ≤ e (t + 1) * ((1 + a t) * Vt t ω + b t) :=
      mul_le_mul_of_nonneg_left e3 (he0 _).le
    have h6 : e (t + 1) * (1 + a t) * Vt t ω ≤ e t * Vt t ω :=
      mul_le_mul_of_nonneg_right h4 (hVnn _)
    nlinarith
  -- L¹ bound and convergence
  have hsub : Submartingale (-Z) ℱ P := hsup.neg
  have hint_le : ∀ t, ∫ ω, Z t ω ∂P ≤ ∫ ω, Z 0 ω ∂P := by
    intro t
    have := hsup.setIntegral_le (Nat.zero_le t) MeasurableSet.univ
    simpa [setIntegral_univ] using this
  have hbdd : ∀ t, eLpNorm ((-Z) t) 1 P ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂P) := by
    intro t
    rw [Pi.neg_apply, eLpNorm_neg, eLpNorm_one_eq_lintegral_enorm]
    have h1 : (∫⁻ ω, ‖Z t ω‖ₑ ∂P) = ∫⁻ ω, ENNReal.ofReal (Z t ω) ∂P := by
      congr 1; funext ω; exact Real.enorm_eq_ofReal (hZnn t ω)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal (hZi t) (ae_of_all _ (hZnn t))]
    exact ENNReal.ofReal_le_ofReal (hint_le t)
  have hconv := hsub.exists_ae_tendsto_of_bdd hbdd
  filter_upwards [hconv] with ω hω
  obtain ⟨c, hc⟩ := hω
  refine ⟨Real.exp (∑' s, a s) * (-c - (C - C)), ?_⟩
  have hS : Tendsto Ssum atTop (𝓝 (∑' s, a s)) := has.hasSum.tendsto_sum_nat
  have hCC : Tendsto (fun t => ∑ s ∈ Finset.range t, cc s) atTop (𝓝 C) :=
    hccs.hasSum.tendsto_sum_nat
  have hZc : Tendsto (fun t => Z t ω) atTop (𝓝 (-c)) := by
    have := hc.neg; simpa using this
  have hlim : Tendsto (fun t => Real.exp (Ssum t) * (Z t ω - (C - ∑ s ∈ Finset.range t, cc s)))
      atTop (𝓝 (Real.exp (∑' s, a s) * (-c - (C - C)))) :=
    ((Real.continuous_exp.tendsto _).comp hS).mul (hZc.sub (tendsto_const_nhds.sub hCC))
  refine hlim.congr (fun t => ?_)
  simp only [hZdef, hedef, hVtdef]
  rw [add_sub_cancel_right, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

