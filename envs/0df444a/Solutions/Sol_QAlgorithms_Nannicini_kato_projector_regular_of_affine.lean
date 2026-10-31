-- Prove2me | solution 1 for QAlgorithms.Nannicini.kato_projector_regular_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T15:48:20.333894+00:00
-- url     : https://prove2.me/submissions/6eec06a9-1f54-4195-84c0-0a415d1a79b0

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Set ℝ) (H : ℝ → E →L[ℂ] E) (D : E →L[ℂ] E)
    (hH : ∀ s t, H t = H s + ((t - s : ℝ) : ℂ) • D)
    (lam : ℝ → ℝ) (hlam : ContinuousOn lam S) (γ : ℝ) (hγ : 0 < γ)
    (P R : ℝ → E →L[ℂ] E)
    (hGP : ∀ s ∈ S, (H s - (lam s : ℂ) • 1) * P s = 0)
    (hPG : ∀ s ∈ S, P s * (H s - (lam s : ℂ) • 1) = 0)
    (hGR : ∀ s ∈ S, (H s - (lam s : ℂ) • 1) * R s = 1 - P s)
    (hRG : ∀ s ∈ S, R s * (H s - (lam s : ℂ) • 1) = 1 - P s)
    (hRP : ∀ s ∈ S, R s * P s = 0) (hPR : ∀ s ∈ S, P s * R s = 0)
    (hPn : ∀ s ∈ S, ‖P s‖ ≤ 1) (hRn : ∀ s ∈ S, ‖R s‖ ≤ 1 / γ)
    (hx : ∀ s ∈ S, ∃ x : E, ‖x‖ = 1 ∧ P s x = x) :
    ∃ R' : ℝ → E →L[ℂ] E, ∀ s ∈ S,
      HasDerivWithinAt P (-(R s * D * P s) - P s * D * R s) S s ∧
      HasDerivWithinAt R (R' s) S s ∧ ‖R' s‖ ≤ 6 * ‖D‖ / γ ^ 2 := by
  choose! xf hxf using hx
  set G : ℝ → E →L[ℂ] E := fun u => H u - (lam u : ℂ) • 1 with hGdef
  set P' : ℝ → E →L[ℂ] E := fun u => -(R u * D * P u) - P u * D * R u with hP'def
  set μ : ℝ → ℝ := fun u => (inner ℂ (xf u) ((P u * D * P u) (xf u))).re with hμdef
  refine ⟨fun u => -(P' u * R u) - R u * P' u - R u * D * R u +
    ((μ u : ℝ) : ℂ) • (R u * R u), ?_⟩
  intro s hs
  clear_value P'
  have hnr : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hγ1 : 0 < 1 / γ := by positivity
  ------------------------------------------------------------------ algebra
  have hGt : ∀ t, G t = G s + ((t - s : ℝ) : ℂ) • D - ((lam t - lam s : ℝ) : ℂ) • 1 := by
    intro t; simp only [hGdef, hH s t]; push_cast; module
  have hA4 : ∀ t, P s * G t = ((t - s : ℝ) : ℂ) • (P s * D) - ((lam t - lam s : ℝ) : ℂ) • P s := by
    intro t
    rw [hGt t, mul_sub, mul_add, hPG s hs, mul_smul_comm, mul_smul_comm, mul_one, zero_add]
  have hX : ∀ t ∈ S, P t - P s = ((lam t - lam s : ℝ) : ℂ) • (R s * (P t - P s) - (P t - P s) * R t)
      - ((t - s : ℝ) : ℂ) • (R s * D * P t + P s * D * R t) := by
    intro t ht
    have hRX : R s * (P t - P s) = R s * P t := by rw [mul_sub, hRP s hs, sub_zero]
    have hXR : (P t - P s) * R t = -(P s * R t) := by rw [sub_mul, hPR t ht, zero_sub]
    have A1 : (1 - P s) * P t = R s * (G s * P t) := by rw [← mul_assoc, hRG s hs]
    have A2 : P s * (1 - P t) = (P s * G t) * R t := by rw [mul_assoc, hGR t ht]
    have A3 : G s * P t = ((lam t - lam s : ℝ) : ℂ) • P t - ((t - s : ℝ) : ℂ) • (D * P t) := by
      have e : G s = G t - ((t - s : ℝ) : ℂ) • D + ((lam t - lam s : ℝ) : ℂ) • 1 := by
        rw [hGt t]; abel
      rw [e, add_mul, sub_mul, hGP t ht, smul_mul_assoc, smul_mul_assoc, one_mul]; abel
    have hsplit : P t - P s = (1 - P s) * P t - P s * (1 - P t) := by noncomm_ring
    rw [hRX, hXR, hsplit, A1, A2, A3, hA4 t]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_sub, smul_add,
      mul_add, add_mul, smul_neg, neg_mul, mul_neg, sub_neg_eq_add]
    module
  have hL : ∀ t ∈ S, ((lam t - lam s : ℝ) : ℂ) • (P s * P t) =
      ((t - s : ℝ) : ℂ) • (P s * D * P t) := by
    intro t ht
    have h0 : P s * G t * P t = 0 := by rw [mul_assoc, hGP t ht, mul_zero]
    rw [hA4 t, sub_mul, smul_mul_assoc, smul_mul_assoc, sub_eq_zero] at h0
    exact h0.symm
  have hY : ∀ t ∈ S, R t - R s = -((P t - P s) * R t) - R s * (P t - P s)
      - ((t - s : ℝ) : ℂ) • (R s * D * R t) + ((lam t - lam s : ℝ) : ℂ) • (R s * R t) := by
    intro t ht
    have B1 : R s * G t * R t = R s - R s * P t := by rw [mul_assoc, hGR t ht, mul_sub, mul_one]
    have B2 : R s * G t = 1 - P s + ((t - s : ℝ) : ℂ) • (R s * D)
        - ((lam t - lam s : ℝ) : ℂ) • R s := by
      rw [hGt t, mul_sub, mul_add, hRG s hs, mul_smul_comm, mul_smul_comm, mul_one]
    rw [B2] at B1
    have hRX : R s * (P t - P s) = R s * P t := by rw [mul_sub, hRP s hs, sub_zero]
    have hXR : (P t - P s) * R t = -(P s * R t) := by rw [sub_mul, hPR t ht, zero_sub]
    rw [hRX, hXR]
    simp only [add_mul, sub_mul, one_mul, smul_mul_assoc, mul_assoc] at B1
    rw [← sub_eq_zero] at B1 ⊢
    convert B1 using 1
    simp only [mul_assoc]
    module
  ------------------------------------------------------------------ analysis
  set F := 𝓝[S \ {s}] s with hF
  have hSev : ∀ᶠ t in F, t ∈ S \ {s} := eventually_mem_nhdsWithin
  have hlamT : Tendsto lam F (𝓝 (lam s)) :=
    (hlam s hs).tendsto.mono_left (nhdsWithin_mono _ Set.sdiff_subset)
  have hδT : Tendsto (fun t => lam t - lam s) F (𝓝 0) := by
    simpa using hlamT.sub_const (lam s)
  have htT : Tendsto (fun t => t - s) F (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t) F (𝓝 s) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using this.sub_const s
  have hlamev : ∀ᶠ t in F, |lam t - lam s| < γ / 4 := by
    have := Metric.tendsto_nhds.1 hlamT (γ / 4) (by positivity)
    filter_upwards [this] with t ht
    rwa [Real.dist_eq] at ht
  have hPs := hPn s hs
  have hRs := hRn s hs
  -- local Lipschitz bound for `P`
  have hXb : ∀ᶠ t in F, ‖P t - P s‖ ≤ 4 * ‖D‖ / γ * |t - s| := by
    filter_upwards [hSev, hlamev] with t ht hlt
    have htS := ht.1
    have hPt := hPn t htS
    have hRt := hRn t htS
    set X := P t - P s with hXdef
    have nA : ‖R s * X - X * R t‖ ≤ ‖R s‖ * ‖X‖ + ‖X‖ * ‖R t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    have nB : ‖R s * D * P t + P s * D * R t‖ ≤ ‖R s‖ * ‖D‖ * ‖P t‖ + ‖P s‖ * ‖D‖ * ‖R t‖ :=
      (norm_add_le _ _).trans (add_le_add norm_mul₃_le norm_mul₃_le)
    have hb : ‖X‖ ≤ |lam t - lam s| * (‖R s‖ * ‖X‖ + ‖X‖ * ‖R t‖) +
        |t - s| * (‖R s‖ * ‖D‖ * ‖P t‖ + ‖P s‖ * ‖D‖ * ‖R t‖) := by
      calc ‖X‖ = ‖((lam t - lam s : ℝ) : ℂ) • (R s * X - X * R t)
            - ((t - s : ℝ) : ℂ) • (R s * D * P t + P s * D * R t)‖ := by
              have e := hX t htS
              rw [← hXdef] at e
              conv_lhs => rw [e]
        _ ≤ ‖((lam t - lam s : ℝ) : ℂ) • (R s * X - X * R t)‖
            + ‖((t - s : ℝ) : ℂ) • (R s * D * P t + P s * D * R t)‖ := norm_sub_le _ _
        _ = |lam t - lam s| * ‖R s * X - X * R t‖
            + |t - s| * ‖R s * D * P t + P s * D * R t‖ := by rw [norm_smul, norm_smul, hnr, hnr]
        _ ≤ _ := by gcongr
    have i1 : |lam t - lam s| * (‖R s‖ * ‖X‖ + ‖X‖ * ‖R t‖) ≤ ‖X‖ / 2 := by
      calc |lam t - lam s| * (‖R s‖ * ‖X‖ + ‖X‖ * ‖R t‖)
          = |lam t - lam s| * (‖R s‖ + ‖R t‖) * ‖X‖ := by ring
        _ ≤ (γ / 4) * (1 / γ + 1 / γ) * ‖X‖ := by gcongr
        _ = ‖X‖ / 2 := by field_simp; ring
    have i2 : ‖R s‖ * ‖D‖ * ‖P t‖ + ‖P s‖ * ‖D‖ * ‖R t‖ ≤ 1 / γ * ‖D‖ * 1 + 1 * ‖D‖ * (1 / γ) := by
      gcongr
    have i3 : |t - s| * (‖R s‖ * ‖D‖ * ‖P t‖ + ‖P s‖ * ‖D‖ * ‖R t‖) ≤
        |t - s| * (1 / γ * ‖D‖ * 1 + 1 * ‖D‖ * (1 / γ)) := by gcongr
    have e4 : 4 * ‖D‖ / γ * |t - s| = 2 * (|t - s| * (1 / γ * ‖D‖ * 1 + 1 * ‖D‖ * (1 / γ))) := by
      field_simp; ring
    rw [e4]; linarith
  have hPT : Tendsto P F (𝓝 (P s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hXb ?_
    simpa using (htT.abs).const_mul (4 * ‖D‖ / γ)
  have hRT : Tendsto R F (𝓝 (R s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ᶠ t in F, ‖R t - R s‖ ≤ ‖P t - P s‖ * (2 / γ) + |t - s| * (‖D‖ / γ ^ 2)
        + |lam t - lam s| * (1 / γ ^ 2) := by
      filter_upwards [hSev] with t ht
      have htS := ht.1
      have hRt := hRn t htS
      rw [hY t htS]
      have n1 := norm_add_le (-((P t - P s) * R t) - R s * (P t - P s)
        - ((t - s : ℝ) : ℂ) • (R s * D * R t)) (((lam t - lam s : ℝ) : ℂ) • (R s * R t))
      have n2 := norm_sub_le (-((P t - P s) * R t) - R s * (P t - P s))
        (((t - s : ℝ) : ℂ) • (R s * D * R t))
      have n3 := norm_sub_le (-((P t - P s) * R t)) (R s * (P t - P s))
      rw [norm_neg] at n3
      rw [norm_smul, hnr] at n1 n2
      have m1 : ‖(P t - P s) * R t‖ ≤ ‖P t - P s‖ * (1 / γ) :=
        (norm_mul_le _ _).trans (by gcongr)
      have m2 : ‖R s * (P t - P s)‖ ≤ (1 / γ) * ‖P t - P s‖ :=
        (norm_mul_le _ _).trans (by gcongr)
      have m3 : ‖R s * D * R t‖ ≤ (1 / γ) * ‖D‖ * (1 / γ) :=
        norm_mul₃_le.trans (by gcongr)
      have m4 : ‖R s * R t‖ ≤ (1 / γ) * (1 / γ) := (norm_mul_le _ _).trans (by gcongr)
      have m3' : |t - s| * ‖R s * D * R t‖ ≤ |t - s| * ((1 / γ) * ‖D‖ * (1 / γ)) := by gcongr
      have m4' : |lam t - lam s| * ‖R s * R t‖ ≤ |lam t - lam s| * ((1 / γ) * (1 / γ)) := by
        gcongr
      have e1 : |t - s| * ((1 / γ) * ‖D‖ * (1 / γ)) = |t - s| * (‖D‖ / γ ^ 2) := by ring
      have e2 : |lam t - lam s| * ((1 / γ) * (1 / γ)) = |lam t - lam s| * (1 / γ ^ 2) := by ring
      have e3 : ‖P t - P s‖ * (1 / γ) + (1 / γ) * ‖P t - P s‖ = ‖P t - P s‖ * (2 / γ) := by ring
      linarith
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
    have h1 : Tendsto (fun t => ‖P t - P s‖) F (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hPT)
    have h3 := ((h1.mul_const (2 / γ)).add ((htT.abs).mul_const (‖D‖ / γ ^ 2))).add
      ((hδT.abs).mul_const (1 / γ ^ 2))
    simp only [abs_zero, zero_mul, add_zero] at h3
    exact h3
  ------------------------------------------------------------------ slopes
  have hne : ∀ t ∈ S \ {s}, ((t - s : ℝ) : ℂ) ≠ 0 := by
    intro t ht
    exact_mod_cast sub_ne_zero.2 ht.2
  have hsl : ∀ (f : ℝ → E →L[ℂ] E) t, slope f s t = ((t - s : ℝ) : ℂ)⁻¹ • (f t - f s) := by
    intro f t
    rw [slope_def_module, ← Complex.ofReal_inv, Complex.coe_smul]
  -- slope of `P`
  have hZb : ∀ᶠ t in F, ‖slope P s t‖ ≤ 4 * ‖D‖ / γ := by
    filter_upwards [hSev, hXb] with t ht hb
    rw [hsl, norm_smul, norm_inv, hnr]
    have hpos : 0 < |t - s| := abs_pos.2 (sub_ne_zero.2 ht.2)
    rw [inv_mul_le_iff₀ hpos]
    linarith
  have hZid : ∀ᶠ t in F, slope P s t = ((lam t - lam s : ℝ) : ℂ) •
      (R s * slope P s t - slope P s t * R t) - (R s * D * P t + P s * D * R t) := by
    filter_upwards [hSev] with t ht
    have h := hne t ht
    rw [hsl]
    have e := hX t ht.1
    generalize P t - P s = X at e ⊢
    conv_lhs => rw [e]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_sub, smul_comm _ ((lam t - lam s : ℝ) : ℂ),
      smul_smul, smul_smul, inv_mul_cancel₀ h, one_smul]
  have hPslope : Tendsto (slope P s) F (𝓝 (P' s)) := by
    have hsmall : Tendsto (fun t => ((lam t - lam s : ℝ) : ℂ) •
        (R s * slope P s t - slope P s t * R t)) F (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by
          have h3 := (hδT.abs).mul_const ((2 / γ) * (4 * ‖D‖ / γ))
          simp only [abs_zero, zero_mul] at h3
          exact h3)
      filter_upwards [hSev, hZb] with t ht hz
      have hRt := hRn t ht.1
      rw [norm_smul, hnr]
      gcongr
      calc ‖R s * slope P s t - slope P s t * R t‖
          ≤ ‖R s‖ * ‖slope P s t‖ + ‖slope P s t‖ * ‖R t‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ (1 / γ) * (4 * ‖D‖ / γ) + (4 * ‖D‖ / γ) * (1 / γ) := by gcongr
        _ = 2 / γ * (4 * ‖D‖ / γ) := by ring
    have hB : Tendsto (fun t => R s * D * P t + P s * D * R t) F
        (𝓝 (R s * D * P s + P s * D * R s)) :=
      (tendsto_const_nhds.mul hPT).add (tendsto_const_nhds.mul hRT)
    have := hsmall.sub hB
    rw [zero_sub] at this
    refine (this.congr' (hZid.mono fun t ht => ht.symm)).trans ?_
    simp only [hP'def, neg_add']
    exact le_rfl
  -- slope of `λ`
  obtain ⟨hx1, hxP⟩ := hxf s hs
  set x := xf s with hxdef
  have hlamslope : Tendsto (slope lam s) F (𝓝 (μ s)) := by
    have hc : Tendsto (fun t => inner ℂ x ((P s * P t) x)) F (𝓝 1) := by
      have h1 : Tendsto (fun t => (P s * P t) x) F (𝓝 ((P s * P s) x)) :=
        ((ContinuousLinearMap.apply ℂ E x).continuous.tendsto _).comp
          (tendsto_const_nhds.mul hPT)
      have h2 : Tendsto (fun t => inner ℂ x ((P s * P t) x)) F
          (𝓝 (inner ℂ x ((P s * P s) x))) := (tendsto_const_nhds (x := x)).inner h1
      have e : inner ℂ x ((P s * P s) x) = 1 := by
        rw [ContinuousLinearMap.mul_apply, hxP, hxP, inner_self_eq_norm_sq_to_K, hx1]
        simp
      rwa [e] at h2
    have hd : Tendsto (fun t => inner ℂ x ((P s * D * P t) x)) F
        (𝓝 (inner ℂ x ((P s * D * P s) x))) := by
      have h0 : Tendsto (fun t => P s * D * P t) F (𝓝 (P s * D * P s)) :=
        tendsto_const_nhds.mul hPT
      have h1 : Tendsto (fun t => (P s * D * P t) x) F (𝓝 ((P s * D * P s) x)) :=
        ((ContinuousLinearMap.apply ℂ E x).continuous.tendsto _).comp h0
      exact (tendsto_const_nhds (x := x)).inner h1
    have hq : Tendsto (fun t => ((slope lam s t : ℝ) : ℂ)) F
        (𝓝 (inner ℂ x ((P s * D * P s) x))) := by
      have hdiv := hd.div hc one_ne_zero
      rw [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [hSev, hc.eventually_ne one_ne_zero] with t ht hct
      rw [Pi.div_apply, div_eq_iff hct]
      have e := congrArg (fun A : E →L[ℂ] E => inner ℂ x (A x)) (hL t ht.1)
      simp only [ContinuousLinearMap.smul_apply, inner_smul_right] at e
      have h' : (t : ℂ) - (s : ℂ) ≠ 0 := by rw [← Complex.ofReal_sub]; exact hne t ht
      rw [slope_def_field]
      push_cast at e ⊢
      field_simp
      first | linear_combination e | linear_combination -e
    have := (Complex.continuous_re.tendsto _).comp hq
    simpa [Function.comp_def, hμdef] using this
  ------------------------------------------------------------------ conclusion
  have hPderiv : HasDerivWithinAt P (P' s) S s :=
    (hasDerivWithinAt_iff_tendsto_slope).2 hPslope
  have hP's : P' s = -(R s * D * P s) - P s * D * R s := by rw [hP'def]
  refine ⟨hP's ▸ hPderiv, ?_, ?_⟩
  · rw [hasDerivWithinAt_iff_tendsto_slope]
    have hqC : Tendsto (fun t => ((slope lam s t : ℝ) : ℂ)) F (𝓝 ((μ s : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hlamslope
    have hlim := ((((hPslope.mul hRT).neg).sub ((tendsto_const_nhds (x := R s)).mul hPslope)).sub
      ((tendsto_const_nhds (x := R s * D)).mul hRT)).add
      (hqC.smul ((tendsto_const_nhds (x := R s)).mul hRT))
    refine hlim.congr' ?_
    filter_upwards [hSev] with t ht
    have h' : (t : ℂ) - (s : ℂ) ≠ 0 := by rw [← Complex.ofReal_sub]; exact hne t ht
    rw [hsl R t, hY t ht.1, hsl P t, slope_def_field]
    push_cast
    simp only [smul_add, smul_sub, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc]
    rw [inv_mul_cancel₀ h', one_smul, div_eq_inv_mul]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
  · -- the bound `‖R'‖ ≤ 6‖D‖/γ²`
    have hP'n : ‖P' s‖ ≤ 2 * ‖D‖ / γ := by
      have m : ‖R s * D * P s‖ ≤ 1 / γ * ‖D‖ * 1 := norm_mul₃_le.trans (by gcongr)
      have m' : ‖P s * D * R s‖ ≤ 1 * ‖D‖ * (1 / γ) := norm_mul₃_le.trans (by gcongr)
      have := norm_sub_le (-(R s * D * P s)) (P s * D * R s)
      rw [norm_neg] at this
      calc ‖P' s‖ ≤ _ := by rw [hP's]; exact this
        _ ≤ 1 / γ * ‖D‖ * 1 + 1 * ‖D‖ * (1 / γ) := add_le_add m m'
        _ = 2 * ‖D‖ / γ := by ring
    have hμn : |μ s| ≤ ‖D‖ := by
      calc |μ s| ≤ ‖inner ℂ x ((P s * D * P s) x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(P s * D * P s) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖P s * D * P s‖ * ‖x‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ((1 * ‖D‖ * 1) * 1) := by
          rw [hx1]
          have h3 : ‖P s * D * P s‖ ≤ 1 * ‖D‖ * 1 := norm_mul₃_le.trans
            (mul_le_mul (mul_le_mul hPs (le_refl ‖D‖) (norm_nonneg _) zero_le_one) hPs
              (norm_nonneg _) (by positivity))
          simp only [one_mul, mul_one] at h3 ⊢
          exact h3
        _ = ‖D‖ := by ring
    have n1 := norm_add_le (-(P' s * R s) - R s * P' s - R s * D * R s)
      (((μ s : ℝ) : ℂ) • (R s * R s))
    have n2 := norm_sub_le (-(P' s * R s) - R s * P' s) (R s * D * R s)
    have n3 := norm_sub_le (-(P' s * R s)) (R s * P' s)
    rw [norm_neg] at n3
    rw [norm_smul, hnr] at n1
    have m1 : ‖P' s * R s‖ ≤ 2 * ‖D‖ / γ * (1 / γ) :=
      (norm_mul_le _ _).trans (mul_le_mul hP'n hRs (norm_nonneg _) (div_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) hγ.le))
    have m2 : ‖R s * P' s‖ ≤ 1 / γ * (2 * ‖D‖ / γ) :=
      (norm_mul_le _ _).trans (mul_le_mul hRs hP'n (norm_nonneg _) hγ1.le)
    have m3 : ‖R s * D * R s‖ ≤ 1 / γ * ‖D‖ * (1 / γ) :=
      norm_mul₃_le.trans (mul_le_mul (mul_le_mul hRs le_rfl (norm_nonneg _) hγ1.le) hRs
        (norm_nonneg _) (mul_nonneg hγ1.le (norm_nonneg _)))
    have m4 : |μ s| * ‖R s * R s‖ ≤ ‖D‖ * (1 / γ * (1 / γ)) :=
      mul_le_mul hμn ((norm_mul_le _ _).trans (mul_le_mul hRs hRs (norm_nonneg _) hγ1.le))
        (norm_nonneg _) (norm_nonneg _)
    have e : 6 * ‖D‖ / γ ^ 2 = 2 * ‖D‖ / γ * (1 / γ) + 1 / γ * (2 * ‖D‖ / γ)
        + 1 / γ * ‖D‖ * (1 / γ) + ‖D‖ * (1 / γ * (1 / γ)) := by field_simp; ring
    rw [e]
    linarith
