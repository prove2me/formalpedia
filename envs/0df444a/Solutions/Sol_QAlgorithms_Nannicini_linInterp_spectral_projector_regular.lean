-- Prove2me | solution 1 for QAlgorithms.Nannicini.linInterp_spectral_projector_regular
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T15:26:34.360294+00:00
-- url     : https://prove2.me/submissions/a1f4cfa2-1e30-48f6-badb-aeeac36e604e

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false

open Filter Topology

namespace KatoAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's formulas at a point, for an abstract family `H t = H s + (t - s) D` with a resolvent
pair `(P, R)` satisfying the algebraic identities and uniform bounds. -/
theorem kato_at (H P R : ℝ → (E →L[ℂ] E)) (D : E →L[ℂ] E) (lam : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (S : Set ℝ) (s : ℝ) (hs : s ∈ S)
    (hH : ∀ t ∈ S, H t = H s + ((t - s : ℝ) : ℂ) • D)
    (hHP : ∀ t ∈ S, H t * P t = (lam t : ℂ) • P t)
    (hPH : ∀ t ∈ S, P t * H t = (lam t : ℂ) • P t)
    (hHR : ∀ t ∈ S, H t * R t - (lam t : ℂ) • R t = 1 - P t)
    (hRH : ∀ t ∈ S, R t * H t - (lam t : ℂ) • R t = 1 - P t)
    (hRP : ∀ t ∈ S, R t * P t = 0) (hPR : ∀ t ∈ S, P t * R t = 0)
    (hPn : ∀ t ∈ S, ‖P t‖ ≤ 1) (hRn : ∀ t ∈ S, ‖R t‖ ≤ γ⁻¹)
    (hPP : P s * P s = P s)
    (hlam : ContinuousWithinAt lam S s)
    (φ : (E →L[ℂ] E) →L[ℂ] ℂ) (hφP : φ (P s) = 1) :
    HasDerivWithinAt P (-(R s * D * P s + P s * D * R s)) S s ∧
    HasDerivWithinAt R (φ (P s * D * P s) • (R s * R s) - R s * D * R s
        - R s * (-(R s * D * P s + P s * D * R s))
        - (-(R s * D * P s + P s * D * R s)) * R s) S s := by
  set P0 := P s with hP0def
  set R0 := R s with hR0def
  set H0 := H s with hH0def
  set g := γ⁻¹ with hgdef
  have hg : 0 < g := inv_pos.mpr hγ
  have hgγ : γ * g = 1 := mul_inv_cancel₀ hγ.ne'
  have hP0n : ‖P0‖ ≤ 1 := hPn s hs
  have hR0n : ‖R0‖ ≤ g := hRn s hs
  -- algebraic identities
  have id1 : ∀ t ∈ S, P t - P0 = ((lam t : ℂ) - lam s) • (R0 * (P t - P0) - (P t - P0) * R t)
      - ((t - s : ℝ) : ℂ) • (R0 * D * P t + P0 * D * R t) := by
    intro t ht
    have e1 : (1 - P0) * P t = ((lam t : ℂ) - lam s) • (R0 * (P t - P0))
        - ((t - s : ℝ) : ℂ) • (R0 * D * P t) := by
      calc (1 - P0) * P t = (R0 * H0 - (lam s : ℂ) • R0) * P t := by rw [hRH s hs]
        _ = R0 * (H t * P t) - ((t - s : ℝ) : ℂ) • (R0 * D * P t)
            - (lam s : ℂ) • (R0 * P t) := by
          rw [hH t ht]
          simp only [mul_add, add_mul, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        _ = _ := by
          rw [hHP t ht, mul_smul_comm, mul_sub, hRP s hs, sub_zero]
          module
    have e2 : P0 * (1 - P t) = ((lam t : ℂ) - lam s) • ((P t - P0) * R t)
        + ((t - s : ℝ) : ℂ) • (P0 * D * R t) := by
      calc P0 * (1 - P t) = P0 * (H t * R t - (lam t : ℂ) • R t) := by rw [hHR t ht]
        _ = (P0 * H0) * R t + ((t - s : ℝ) : ℂ) • (P0 * D * R t)
            - (lam t : ℂ) • (P0 * R t) := by
          rw [hH t ht]
          simp only [mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = _ := by
          rw [hPH s hs, smul_mul_assoc, sub_mul, hPR t ht]
          module
    calc P t - P0 = (1 - P0) * P t - P0 * (1 - P t) := by noncomm_ring
      _ = _ := by rw [e1, e2]; module
  have idY : ∀ t ∈ S, R t - R0 = ((lam t : ℂ) - lam s) • (R0 * R t)
      - ((t - s : ℝ) : ℂ) • (R0 * D * R t) - R0 * (P t - P0) - (P t - P0) * R t := by
    intro t ht
    have e34 : R0 * (1 - P t) - (1 - P0) * R t = ((t - s : ℝ) : ℂ) • (R0 * D * R t)
        - ((lam t : ℂ) - lam s) • (R0 * R t) := by
      rw [← hHR t ht, ← hRH s hs, hH t ht]
      simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
      module
    have h1 := hRP s hs
    have h2 := hPR t ht
    calc R t - R0 = R t - R0 + R0 * P0 - P t * R t := by rw [h1, h2]; abel
      _ = -(R0 * (1 - P t) - (1 - P0) * R t) - R0 * (P t - P0) - (P t - P0) * R t := by
        noncomm_ring
      _ = _ := by rw [e34]; module
  have eL : ∀ t ∈ S, ((lam t : ℂ) - lam s) • (P0 * P t)
      = ((t - s : ℝ) : ℂ) • (P0 * D * P t) := by
    intro t ht
    have : (lam t : ℂ) • (P0 * P t) = (lam s : ℂ) • (P0 * P t)
        + ((t - s : ℝ) : ℂ) • (P0 * D * P t) := by
      calc (lam t : ℂ) • (P0 * P t) = P0 * (H t * P t) := by rw [hHP t ht, mul_smul_comm]
        _ = (P0 * H0) * P t + ((t - s : ℝ) : ℂ) • (P0 * D * P t) := by
          rw [hH t ht]
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = _ := by rw [hPH s hs, smul_mul_assoc]
    rw [sub_smul, this]; abel
  set L := 𝓝[S] s with hL
  have hδ : Tendsto (fun t => (lam t : ℂ) - lam s) L (𝓝 0) := by
    have h1 : Tendsto (fun t => (lam t : ℂ)) L (𝓝 (lam s : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hlam
    simpa using h1.sub_const (lam s : ℂ)
  have hδn : Tendsto (fun t => ‖(lam t : ℂ) - lam s‖) L (𝓝 0) := by
    simpa using hδ.norm
  have hh : Tendsto (fun t : ℝ => ‖((t - s : ℝ) : ℂ)‖) L (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ‖((t - s : ℝ) : ℂ)‖) (𝓝 s) (𝓝 ‖((s - s : ℝ) : ℂ)‖) :=
      (by fun_prop : Continuous fun t : ℝ => ‖((t - s : ℝ) : ℂ)‖).tendsto s
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in L, t ∈ S ∧ ‖(lam t : ℂ) - lam s‖ ≤ γ / 4 := by
    refine (eventually_mem_nhdsWithin).and ?_
    exact (hδn.eventually (gt_mem_nhds (by positivity : (0:ℝ) < γ / 4))).mono fun t ht => ht.le
  have hXb : ∀ᶠ t in L, ‖P t - P0‖ ≤ 4 * g * ‖D‖ * ‖((t - s : ℝ) : ℂ)‖ := by
    filter_upwards [hev] with t ⟨ht, hδt⟩
    have hRt := hRn t ht
    have hPt := hPn t ht
    have b1 : ‖R0 * (P t - P0) - (P t - P0) * R t‖ ≤ 2 * g * ‖P t - P0‖ := by
      calc _ ≤ ‖R0‖ * ‖P t - P0‖ + ‖P t - P0‖ * ‖R t‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ g * ‖P t - P0‖ + ‖P t - P0‖ * g := by gcongr
        _ = _ := by ring
    have b2 : ‖R0 * D * P t + P0 * D * R t‖ ≤ 2 * g * ‖D‖ := by
      calc _ ≤ ‖R0‖ * ‖D‖ * ‖P t‖ + ‖P0‖ * ‖D‖ * ‖R t‖ :=
            (norm_add_le _ _).trans (add_le_add norm_mul₃_le norm_mul₃_le)
        _ ≤ g * ‖D‖ * 1 + 1 * ‖D‖ * g := by gcongr
        _ = _ := by ring
    have key : ‖P t - P0‖ ≤ ‖(lam t : ℂ) - lam s‖ * (2 * g * ‖P t - P0‖)
        + ‖((t - s : ℝ) : ℂ)‖ * (2 * g * ‖D‖) := by
      calc ‖P t - P0‖ = ‖_‖ := congrArg norm (id1 t ht)
        _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_smul, norm_smul]; gcongr
    have h4 : ‖(lam t : ℂ) - lam s‖ * (2 * g * ‖P t - P0‖) ≤ γ / 4 * (2 * g * ‖P t - P0‖) := by
      gcongr
    have h3 : γ / 4 * (2 * g * ‖P t - P0‖) = ‖P t - P0‖ / 2 := by
      linear_combination (‖P t - P0‖ / 2) * hgγ
    nlinarith
  have hX : Tendsto (fun t => P t - P0) L (𝓝 0) := by
    refine squeeze_zero_norm' hXb ?_
    simpa using hh.const_mul (4 * g * ‖D‖)
  have hYb : ∀ᶠ t in L, ‖R t - R0‖ ≤ ‖(lam t : ℂ) - lam s‖ * (g * g)
      + ‖((t - s : ℝ) : ℂ)‖ * (g * ‖D‖ * g) + 2 * g * ‖P t - P0‖ := by
    filter_upwards [hev] with t ⟨ht, _⟩
    have hRt := hRn t ht
    have c1 : ‖R0 * R t‖ ≤ g * g := (norm_mul_le _ _).trans (by gcongr)
    have c2 : ‖R0 * D * R t‖ ≤ g * ‖D‖ * g := norm_mul₃_le.trans (by gcongr)
    have c3 : ‖R0 * (P t - P0)‖ ≤ g * ‖P t - P0‖ := (norm_mul_le _ _).trans (by gcongr)
    have c4 : ‖(P t - P0) * R t‖ ≤ ‖P t - P0‖ * g := (norm_mul_le _ _).trans (by gcongr)
    have d1 := mul_le_mul_of_nonneg_left c1 (norm_nonneg ((lam t : ℂ) - lam s))
    have d2 := mul_le_mul_of_nonneg_left c2 (norm_nonneg ((t - s : ℝ) : ℂ))
    have n4 : ∀ a b c d : E →L[ℂ] E, ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      intro a b c d
      have := norm_sub_le (a - b - c) d
      have := norm_sub_le (a - b) c
      have := norm_sub_le a b
      linarith
    rw [idY t ht]
    calc _ ≤ ‖((lam t : ℂ) - lam s) • (R0 * R t)‖ + ‖((t - s : ℝ) : ℂ) • (R0 * D * R t)‖
          + ‖R0 * (P t - P0)‖ + ‖(P t - P0) * R t‖ :=
          n4 _ _ _ _
      _ ≤ _ := by rw [norm_smul, norm_smul]; linarith
  have hY : Tendsto (fun t => R t - R0) L (𝓝 0) := by
    refine squeeze_zero_norm' hYb ?_
    simpa using ((hδn.mul_const (g * g)).add (hh.mul_const (g * ‖D‖ * g))).add
      (hX.norm.const_mul (2 * g))
  have hPt : Tendsto P L (𝓝 P0) := by simpa using hX.add_const P0
  have hRt : Tendsto R L (𝓝 R0) := by simpa using hY.add_const R0
  -- slopes
  have hle : 𝓝[S \ {s}] s ≤ L := nhdsWithin_mono _ Set.diff_subset
  set c : ℝ → ℂ := fun t => (((t - s)⁻¹ : ℝ) : ℂ) with hcdef
  have hch : ∀ t, t ≠ s → c t * ((t - s : ℝ) : ℂ) = 1 := by
    intro t hts
    simp only [hcdef]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hts), Complex.ofReal_one]
  have hsl : ∀ (F : ℝ → (E →L[ℂ] E)) t, slope F s t = c t • (F t - F s) := by
    intro F t
    rw [slope_def_module, RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
  have hev' : ∀ᶠ t in 𝓝[S \ {s}] s, ((t ∈ S ∧ ‖(lam t : ℂ) - lam s‖ ≤ γ / 4) ∧
      ‖P t - P0‖ ≤ 4 * g * ‖D‖ * ‖((t - s : ℝ) : ℂ)‖) ∧ t ∈ S \ {s} :=
    ((hev.and hXb).filter_mono hle).and eventually_mem_nhdsWithin
  set P' := -(R0 * D * P0 + P0 * D * R0) with hP'def
  have hG : Tendsto (fun t => c t • (P t - P0)) (𝓝[S \ {s}] s) (𝓝 P') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (g := fun t =>
      ‖(lam t : ℂ) - lam s‖ * (2 * g * (4 * g * ‖D‖)) + g * ‖D‖ * ‖P t - P0‖
        + ‖D‖ * ‖R t - R0‖) ?_ ?_
    · filter_upwards [hev'] with t ⟨⟨⟨ht, _⟩, hXt⟩, hts⟩
      have hts : t ≠ s := hts.2
      have hRt := hRn t ht
      have hcn : ‖c t‖ * ‖((t - s : ℝ) : ℂ)‖ = 1 := by
        rw [← norm_mul, hch t hts, norm_one]
      have hGn : ‖c t • (P t - P0)‖ ≤ 4 * g * ‖D‖ := by
        rw [norm_smul]
        calc ‖c t‖ * ‖P t - P0‖ ≤ ‖c t‖ * (4 * g * ‖D‖ * ‖((t - s : ℝ) : ℂ)‖) := by gcongr
          _ = 4 * g * ‖D‖ * (‖c t‖ * ‖((t - s : ℝ) : ℂ)‖) := by ring
          _ = _ := by rw [hcn, mul_one]
      have hGid : c t • (P t - P0) = ((lam t : ℂ) - lam s) • (R0 * (c t • (P t - P0))
          - (c t • (P t - P0)) * R t) - (R0 * D * P t + P0 * D * R t) := by
        calc c t • (P t - P0) = c t • (((lam t : ℂ) - lam s) • (R0 * (P t - P0)
              - (P t - P0) * R t)
            - ((t - s : ℝ) : ℂ) • (R0 * D * P t + P0 * D * R t)) := by rw [← id1 t ht]
          _ = ((lam t : ℂ) - lam s) • (R0 * (c t • (P t - P0)) - (c t • (P t - P0)) * R t)
              - (c t * ((t - s : ℝ) : ℂ)) • (R0 * D * P t + P0 * D * R t) := by
            simp only [mul_smul_comm, smul_mul_assoc]
            module
          _ = _ := by rw [hch t hts, one_smul]
      have hBP : (R0 * D * P t + P0 * D * R t) + P'
          = R0 * D * (P t - P0) + P0 * D * (R t - R0) := by
        rw [hP'def]; noncomm_ring
      have hdiff : c t • (P t - P0) - P' = ((lam t : ℂ) - lam s) • (R0 * (c t • (P t - P0))
          - (c t • (P t - P0)) * R t) - (R0 * D * (P t - P0) + P0 * D * (R t - R0)) := by
        rw [← hBP]; conv_lhs => rw [hGid]
        abel
      rw [hdiff]
      have e1 : ‖R0 * (c t • (P t - P0)) - (c t • (P t - P0)) * R t‖
          ≤ 2 * g * (4 * g * ‖D‖) := by
        calc _ ≤ ‖R0‖ * ‖c t • (P t - P0)‖ + ‖c t • (P t - P0)‖ * ‖R t‖ :=
              (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
          _ ≤ g * (4 * g * ‖D‖) + (4 * g * ‖D‖) * g := by gcongr
          _ = _ := by ring
      have e2 : ‖R0 * D * (P t - P0) + P0 * D * (R t - R0)‖ ≤ g * ‖D‖ * ‖P t - P0‖
          + ‖D‖ * ‖R t - R0‖ := by
        calc _ ≤ ‖R0‖ * ‖D‖ * ‖P t - P0‖ + ‖P0‖ * ‖D‖ * ‖R t - R0‖ :=
              (norm_add_le _ _).trans (add_le_add norm_mul₃_le norm_mul₃_le)
          _ ≤ g * ‖D‖ * ‖P t - P0‖ + 1 * ‖D‖ * ‖R t - R0‖ := by gcongr
          _ = _ := by ring
      have e3 := mul_le_mul_of_nonneg_left e1 (norm_nonneg ((lam t : ℂ) - lam s))
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_smul]; linarith
    · have := ((hδn.mul_const (2 * g * (4 * g * ‖D‖))).add (hX.norm.const_mul (g * ‖D‖))).add
        (hY.norm.const_mul ‖D‖)
      simpa using this.mono_left hle
  have hφ1 : Tendsto (fun t => φ (P0 * P t)) L (𝓝 1) := by
    have : Tendsto (fun t => φ (P0 * P t)) L (𝓝 (φ (P0 * P0))) :=
      ((φ.continuous.comp (continuous_mul_left P0)).tendsto P0).comp hPt
    rwa [hPP, hφP] at this
  have hφ2 : Tendsto (fun t => φ (P0 * D * P t)) L (𝓝 (φ (P0 * D * P0))) :=
    ((φ.continuous.comp (continuous_mul_left (P0 * D))).tendsto P0).comp hPt
  have hlam' : Tendsto (fun t => c t * ((lam t : ℂ) - lam s)) (𝓝[S \ {s}] s)
      (𝓝 (φ (P0 * D * P0))) := by
    have := (hφ2.div hφ1 one_ne_zero).mono_left hle
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hev', (hφ1.eventually_ne one_ne_zero).filter_mono hle]
      with t ⟨⟨⟨ht, _⟩, _⟩, hts⟩ hne
    have hts : t ≠ s := hts.2
    rw [Pi.div_apply, div_eq_iff hne]
    have h1 := congrArg φ (eL t ht)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    calc φ (P0 * D * P t) = (c t * ((t - s : ℝ) : ℂ)) * φ (P0 * D * P t) := by
          rw [hch t hts, one_mul]
      _ = c t * (((t - s : ℝ) : ℂ) * φ (P0 * D * P t)) := mul_assoc _ _ _
      _ = c t * (((lam t : ℂ) - lam s) * φ (P0 * P t)) := by rw [h1]
      _ = _ := by ring
  have hRt' := hRt.mono_left hle
  refine ⟨?_, ?_⟩
  · rw [hasDerivWithinAt_iff_tendsto_slope]
    exact hG.congr' (Eventually.of_forall fun t => (hsl P t).symm)
  · rw [hasDerivWithinAt_iff_tendsto_slope]
    have hK : Tendsto (fun t => (c t * ((lam t : ℂ) - lam s)) • (R0 * R t) - R0 * D * R t
        - R0 * (c t • (P t - P0)) - (c t • (P t - P0)) * R t) (𝓝[S \ {s}] s)
        (𝓝 (φ (P0 * D * P0) • (R0 * R0) - R0 * D * R0 - R0 * P' - P' * R0)) :=
      (((hlam'.smul ((tendsto_const_nhds (x := R0)).mul hRt')).sub
        ((tendsto_const_nhds (x := R0 * D)).mul hRt')).sub
        ((tendsto_const_nhds (x := R0)).mul hG)).sub (hG.mul hRt')
    refine hK.congr' ?_
    filter_upwards [hev'] with t ⟨⟨⟨ht, _⟩, _⟩, hts⟩
    have hts : t ≠ s := hts.2
    rw [hsl R t, ← hR0def, idY t ht]
    calc _ = (c t * ((lam t : ℂ) - lam s)) • (R0 * R t)
          - (c t * ((t - s : ℝ) : ℂ)) • (R0 * D * R t) - R0 * (c t • (P t - P0))
          - (c t • (P t - P0)) * R t := by rw [hch t hts, one_smul]
      _ = _ := by simp only [mul_smul_comm, smul_mul_assoc]; module

end KatoAux

namespace KatoAux

open QAlgorithms

theorem bound_R' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (P R D : E →L[ℂ] E)
    (l : ℂ) (g : ℝ) (hg : 0 ≤ g) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ g) (hl : ‖l‖ ≤ ‖D‖) :
    ‖l • (R * R) - R * D * R - R * (-(R * D * P + P * D * R))
      - (-(R * D * P + P * D * R)) * R‖ ≤ 6 * g ^ 2 * ‖D‖ := by
  set Q := -(R * D * P + P * D * R) with hQdef
  have hQ : ‖Q‖ ≤ 2 * g * ‖D‖ := by
    rw [hQdef, norm_neg]
    calc _ ≤ ‖R‖ * ‖D‖ * ‖P‖ + ‖P‖ * ‖D‖ * ‖R‖ :=
          (norm_add_le _ _).trans (add_le_add norm_mul₃_le norm_mul₃_le)
      _ ≤ g * ‖D‖ * 1 + 1 * ‖D‖ * g := by gcongr
      _ = _ := by ring
  have a1 : ‖l • (R * R)‖ ≤ 1 * (g ^ 2 * ‖D‖) := by
    rw [norm_smul]
    calc _ ≤ ‖D‖ * (g * g) :=
          mul_le_mul hl ((norm_mul_le _ _).trans (by gcongr)) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have a2 : ‖R * D * R‖ ≤ 1 * (g ^ 2 * ‖D‖) :=
    norm_mul₃_le.trans ((by gcongr : ‖R‖ * ‖D‖ * ‖R‖ ≤ g * ‖D‖ * g).trans (le_of_eq (by ring)))
  have a3 : ‖R * Q‖ ≤ 2 * (g ^ 2 * ‖D‖) :=
    (norm_mul_le _ _).trans ((by gcongr : ‖R‖ * ‖Q‖ ≤ g * (2 * g * ‖D‖)).trans
      (le_of_eq (by ring)))
  have a4 : ‖Q * R‖ ≤ 2 * (g ^ 2 * ‖D‖) :=
    (norm_mul_le _ _).trans ((by gcongr : ‖Q‖ * ‖R‖ ≤ (2 * g * ‖D‖) * g).trans
      (le_of_eq (by ring)))
  have n4 : ∀ a b c d : E →L[ℂ] E, ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have := norm_sub_le (a - b - c) d
    have := norm_sub_le (a - b) c
    have := norm_sub_le a b
    linarith
  have := n4 (l • (R * R)) (R * D * R) (R * Q) (Q * R)
  have e : 6 * g ^ 2 * ‖D‖ = 6 * (g ^ 2 * ‖D‖) := by ring
  rw [e]; linarith

/-- The pointwise spectral data of a gapped Hermitian matrix. -/
structure Good {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam γ : ℝ)
    (P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (u : EuclideanSpace ℂ ι) : Prop where
  hHP : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A * P = (lam : ℂ) • P
  hPH : P * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A = (lam : ℂ) • P
  hHR : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A * R - (lam : ℂ) • R = 1 - P
  hRH : R * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A - (lam : ℂ) • R = 1 - P
  hRP : R * P = 0
  hPR : P * R = 0
  hPP : P * P = P
  hPn : ‖P‖ ≤ 1
  hRn : ‖R‖ ≤ γ⁻¹
  hinner : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)
  hfix : ∀ x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A x = (lam : ℂ) • x → P x = x
  hun : ‖u‖ = 1
  hPu : P u = u

theorem pointwise {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam γ : ℝ)
    (hγ : 0 < γ) (hA : HasGapAround A lam γ) :
    ∃ (P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (u : EuclideanSpace ℂ ι),
      Good A lam γ P R u := by
  obtain ⟨hH, ⟨k0, hk0, huniq⟩, hgap⟩ := hA
  set b := hH.eigenvectorBasis with hbdef
  set e := hH.eigenvalues with hedef
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) with heqv
  have hbr : ∀ i, ascEigenvalues A (Fin.rev (eqv.symm i)) = e i := by
    intro i
    simp only [ascEigenvalues, dif_pos hH, Fin.rev_rev]
    rfl
  set i0 := eqv (Fin.rev k0) with hi0def
  have he0 : e i0 = lam := by
    rw [← hbr i0, hi0def, Equiv.symm_apply_apply, Fin.rev_rev, hk0]
  have hne : ∀ i, i ≠ i0 → e i ≠ lam := by
    intro i hi he
    apply hi
    have := huniq _ ((hbr i).trans he)
    rw [hi0def, ← this, Fin.rev_rev, Equiv.apply_symm_apply]
  have hgi : ∀ i, i ≠ i0 → γ ≤ |e i - lam| := by
    intro i hi
    have := hgap (Fin.rev (eqv.symm i))
    rw [hbr i] at this
    exact this (hne i hi)
  have hz : ∀ i, i ≠ i0 → (e i : ℂ) - lam ≠ 0 := by
    intro i hi h
    exact hne i hi (by exact_mod_cast sub_eq_zero.mp h)
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hb : ∀ i, Matrix.toEuclideanLin A (b i) = (e i : ℂ) • b i := by
    intro i
    rw [Matrix.toEuclideanLin_apply, hbdef, hH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hedef]
  have hAx : ∀ x i, b.repr (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A x) i = (e i : ℂ) * b.repr x i := by
    intro x i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
    have hact : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A x = Matrix.toEuclideanLin A x := rfl
    rw [hact, ← hsym (b i) x, hb i, inner_smul_left]
    simp
  let N : (ι → ℂ) → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := fun c =>
    (b.repr.symm.toContinuousLinearEquiv : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (Matrix.diagonal c) ∘L
      (b.repr.toContinuousLinearEquiv : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
  have hN : ∀ c x i, b.repr (N c x) i = c i * b.repr x i := by
    intro c x i
    show b.repr (b.repr.symm (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (Matrix.diagonal c) (b.repr x))) i = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    show (WithLp.toLp 2 (Matrix.mulVec (Matrix.diagonal c) (WithLp.ofLp (b.repr x)))) i = _
    simp [Matrix.mulVec_diagonal]
  have hNn : ∀ (c : ι → ℂ) (M : ℝ), 0 ≤ M → (∀ i, ‖c i‖ ≤ M) → ‖N c‖ ≤ M := by
    intro c M hM hc
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
    rw [← b.repr.norm_map (N c x), ← b.repr.norm_map x, EuclideanSpace.norm_eq,
      EuclideanSpace.norm_eq, ← Real.sqrt_sq hM, ← Real.sqrt_mul (sq_nonneg M)]
    apply Real.sqrt_le_sqrt
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hN, norm_mul, mul_pow]
    gcongr
    exact hc i
  have hext : ∀ F G : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι,
      (∀ x i, b.repr (F x) i = b.repr (G x) i) → F = G := fun F G h =>
    ContinuousLinearMap.ext fun x => b.repr.injective (by ext i; exact h x i)
  set p : ι → ℂ := fun i => if i = i0 then 1 else 0 with hpdef
  set r : ι → ℂ := fun i => if i = i0 then 0 else ((e i : ℂ) - lam)⁻¹ with hrdef
  have hr1 : ∀ i, i ≠ i0 → ((e i : ℂ) - lam) * r i = 1 := by
    intro i hi
    simp only [hrdef, if_neg hi]
    exact mul_inv_cancel₀ (hz i hi)
  refine ⟨N p, N r, b i0, ?_⟩
  constructor
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hi, he0]
    · simp [hpdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hi, he0]
    · simp [hpdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hrdef, hi]
    · have h1 := hr1 i hi
      simp only [hpdef, if_neg hi]
      linear_combination (b.repr x i) * h1
  · apply hext; intro x i
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hrdef, hi]
    · have h1 := hr1 i hi
      simp only [hpdef, if_neg hi]
      linear_combination (b.repr x i) * h1
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, map_zero,
      PiLp.zero_apply, hN]
    by_cases hi : i = i0 <;> simp [hpdef, hrdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, map_zero,
      PiLp.zero_apply, hN]
    by_cases hi : i = i0 <;> simp [hpdef, hrdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, hN]
    by_cases hi : i = i0 <;> simp [hpdef, hi]
  · refine hNn p 1 zero_le_one fun i => ?_
    by_cases hi : i = i0 <;> simp [hpdef, hi]
  · refine hNn r γ⁻¹ (inv_nonneg.mpr hγ.le) fun i => ?_
    by_cases hi : i = i0
    · simp [hrdef, hi, hγ.le]
    · simp only [hrdef, if_neg hi, norm_inv]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact inv_anti₀ hγ (hgi i hi)
  · intro x y
    rw [← b.repr.inner_map_map (N p x) y, ← b.repr.inner_map_map x (N p y)]
    simp only [PiLp.inner_apply, hN]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = i0 <;> simp [hpdef, hi]
  · intro x hx
    apply b.repr.injective
    ext i
    have h1 := congrArg (fun y => b.repr y i) hx
    simp only [hAx, map_smul, PiLp.smul_apply, smul_eq_mul] at h1
    rw [hN]
    by_cases hi : i = i0
    · simp [hpdef, hi]
    · have h2 : ((e i : ℂ) - lam) * b.repr x i = 0 := by rw [sub_mul, h1, sub_self]
      have h3 := (mul_eq_zero.mp h2).resolve_left (hz i hi)
      simp [hpdef, hi, h3]
  · exact b.orthonormal.1 i0
  · apply b.repr.injective
    ext i
    rw [hN, OrthonormalBasis.repr_self]
    by_cases hi : i = i0 <;> simp [hpdef, hi, EuclideanSpace.single_apply]

end KatoAux

open QAlgorithms KatoAux in
theorem solution.{u} : ∃ K0 : ℝ, ∀ {ι : Type u} [Fintype ι]
    [DecidableEq ι] (HI HF : Matrix ι ι ℂ), HI.IsHermitian → HF.IsHermitian →
    ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
    ∀ (γ : ℝ), 0 < γ →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
    ∃ P P' R R' : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι),
      ContinuousOn P' (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt P (P' s) (Set.Icc 0 1) s ∧
        HasDerivWithinAt R (R' s) (Set.Icc 0 1) s ∧
        (∀ x, P s (P s x) = P s x) ∧
        (∀ x y, inner ℂ (P s x) y = inner ℂ x (P s y)) ∧
        (∀ x, act (linInterp HI HF s) x = (lam s : ℂ) • x → P s x = x) ∧
        (∀ x, act (linInterp HI HF s) (P s x) = (lam s : ℂ) • P s x) ∧
        (∀ x, act (linInterp HI HF s) (R s x) - (lam s : ℂ) • R s x = x - P s x) ∧
        (∀ x, R s (P s x) = 0) ∧ (∀ x, P s (R s x) = 0) ∧
        (∀ x, P' s x = -R s (act (HF - HI) (P s x)) - P s (act (HF - HI) (R s x))) ∧
        ‖P s‖ ≤ 1 ∧ ‖R s‖ ≤ 1 / γ ∧ ‖R' s‖ ≤ K0 * specNorm (HF - HI) / γ ^ 2 := by
  refine ⟨6, ?_⟩
  intro ι _ _ HI HF _ _ lam hlam γ hγ hgap
  set S := Set.Icc (0 : ℝ) 1 with hS
  set D := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (HF - HI) with hD
  set H : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := fun t =>
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (linInterp HI HF t) with hHdef
  have hpt : ∀ t, ∃ (P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
      (v : EuclideanSpace ℂ ι), t ∈ S → Good (linInterp HI HF t) (lam t) γ P R v := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨P, R, v, h⟩ := pointwise (linInterp HI HF t) (lam t) γ hγ (hgap t ht)
      exact ⟨P, R, v, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h ht⟩
  choose P R v hG using hpt
  have hH : ∀ s t : ℝ, H t = H s + ((t - s : ℝ) : ℂ) • D := by
    intro s t
    have : linInterp HI HF t = linInterp HI HF s + ((t - s : ℝ) : ℂ) • (HF - HI) := by
      simp only [linInterp]; push_cast; module
    simp only [hHdef, hD]
    rw [this, map_add, map_smul]
  let φ : ℝ → ((EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →L[ℂ] ℂ) := fun t =>
    (innerSL ℂ (v t)).comp (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ ι) (v t))
  have hφ : ∀ t (X : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι),
      φ t X = inner ℂ (v t) (X (v t)) := fun t X => rfl
  have hK : ∀ s ∈ S, _ := fun s hs =>
    kato_at H P R D lam γ hγ S s hs (fun t _ => hH s t)
      (fun t ht => (hG t ht).hHP) (fun t ht => (hG t ht).hPH) (fun t ht => (hG t ht).hHR)
      (fun t ht => (hG t ht).hRH) (fun t ht => (hG t ht).hRP) (fun t ht => (hG t ht).hPR)
      (fun t ht => (hG t ht).hPn) (fun t ht => (hG t ht).hRn) (hG s hs).hPP (hlam s hs) (φ s)
      (by
        rw [hφ, (hG s hs).hPu, inner_self_eq_norm_sq_to_K, (hG s hs).hun]
        simp)
  refine ⟨P, fun t => -(R t * D * P t + P t * D * R t), R,
    fun t => φ t (P t * D * P t) • (R t * R t) - R t * D * R t
      - R t * (-(R t * D * P t + P t * D * R t)) - (-(R t * D * P t + P t * D * R t)) * R t,
    ?_, fun s hs => ?_⟩
  · intro s hs
    have cP := (hK s hs).1.continuousWithinAt
    have cR := (hK s hs).2.continuousWithinAt
    exact (((cR.mul continuousWithinAt_const).mul cP).add
      ((cP.mul continuousWithinAt_const).mul cR)).neg
  have G := hG s hs
  refine ⟨(hK s hs).1, (hK s hs).2, fun x => ?_, G.hinner, fun x hx => G.hfix x hx,
    fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, G.hPn,
    by rw [one_div]; exact G.hRn, ?_⟩
  · have := congrArg (fun F => F x) G.hPP
    simpa only [ContinuousLinearMap.mul_apply] using this
  · have := congrArg (fun F => F x) G.hHP
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at this
    exact this
  · have := congrArg (fun F => F x) G.hHR
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  · have := congrArg (fun F => F x) G.hRP
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this
  · have := congrArg (fun F => F x) G.hPR
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this
  · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply]
    rw [neg_add, ← sub_eq_add_neg]
    rfl
  · have hDn : specNorm (HF - HI) = ‖D‖ := rfl
    have hl : ‖φ s (P s * D * P s)‖ ≤ ‖D‖ := by
      rw [hφ]
      calc _ ≤ ‖v s‖ * ‖(P s * D * P s) (v s)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖P s * D * P s‖ * ‖v s‖) := by
          have := (P s * D * P s).le_opNorm (v s); rw [G.hun] at this ⊢; simpa using this
        _ ≤ 1 * ((‖P s‖ * ‖D‖ * ‖P s‖) * 1) := by rw [G.hun]; gcongr; exact norm_mul₃_le
        _ ≤ 1 * ((1 * ‖D‖ * 1) * 1) := by gcongr <;> exact G.hPn
        _ = ‖D‖ := by ring
    have := bound_R' (P s) (R s) D (φ s (P s * D * P s)) γ⁻¹ (inv_nonneg.mpr hγ.le) G.hPn G.hRn hl
    rw [hDn]
    calc _ ≤ 6 * γ⁻¹ ^ 2 * ‖D‖ := this
      _ = _ := by field_simp
