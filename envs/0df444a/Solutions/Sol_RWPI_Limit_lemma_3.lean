-- Prove2me | solution 1 for RWPI.Limit.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:16:28.804946+00:00
-- url     : https://prove2.me/submissions/c4e9dd97-7d12-40e9-a6e2-fe91961a65b7

import Mathlib
import Definitions.Def_RWPI_Limit_rowNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology RWPI.Limit
open scoped ENNReal

namespace SolRWPILimitLemma3

private lemma norm_le_toLp_norm {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Fin d → ℝ) :
    ‖x‖ ≤ ‖WithLp.toLp p x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp p x))).mpr fun j => ?_
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [PiLp.norm_eq_ciSup]
    exact le_ciSup (f := fun i : Fin d => ‖x i‖) (Finite.bddAbove_range _) j
  · have hp_one : 1 ≤ p := Fact.out
    have hp_zero : p ≠ 0 := (zero_lt_one.trans_le hp_one).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
    rw [PiLp.norm_eq_sum hp_pos]
    have hj : ‖x j‖ = (‖x j‖ ^ p.toReal) ^ (1 / p.toReal) := by
      rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp_pos.ne', Real.rpow_one]
    rw [hj]
    refine Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) ?_ (one_div_nonneg.mpr hp_pos.le)
    exact Finset.single_le_sum (f := fun i : Fin d => ‖x i‖ ^ p.toReal)
      (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)

private lemma isCompact_toLp_closedBall {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (R : ℝ) :
    IsCompact {x : Fin d → ℝ | ‖WithLp.toLp p x‖ ≤ R} := by
  have hclosed : IsClosed {x : Fin d → ℝ | ‖WithLp.toLp p x‖ ≤ R} :=
    isClosed_le (continuous_norm.comp (PiLp.continuous_toLp p _)) continuous_const
  refine (isCompact_closedBall (0 : Fin d → ℝ) R).of_isClosed_subset hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_toLp_norm p x).trans hx

private lemma continuous_rowNorm_rpow {m l r : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs) (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowNorm p h θs zw.1 zw.2 ^ β) := by
  have hfderiv : Continuous (fun w : Fin m → ℝ => fderiv ℝ (fun x => h x θs) w) :=
    hC1.continuous_fderiv one_ne_zero
  have hvec : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) =>
      fun k : Fin m => ∑ j : Fin r,
        zw.1 j * fderiv ℝ (fun x => h x θs) zw.2 (Pi.single k 1) j) := by
    refine continuous_pi fun k => continuous_finsetSum Finset.univ fun j _ => ?_
    have h1 : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => zw.1 j) :=
      (continuous_apply j).comp continuous_fst
    have h2 : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) =>
        fderiv ℝ (fun x => h x θs) zw.2 (Pi.single k 1) j) :=
      (continuous_apply j).comp
        (((ContinuousLinearMap.apply ℝ (Fin r → ℝ) (Pi.single k 1)).continuous.comp hfderiv).comp
          continuous_snd)
    exact h1.mul h2
  have hrow : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowNorm p h θs zw.1 zw.2) :=
    continuous_norm.comp ((PiLp.continuous_toLp p _).comp hvec)
  exact hrow.rpow_const (fun _ => Or.inr hβ)

private lemma tendsto_prob_gt_of_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (hZmeas : ∀ n, Measurable (Z n)) (c : ℝ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 c)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => μ {ω | η < |Z n ω - c|}) atTop (𝓝 0) := by
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => Set.indicator {ω' | η < |Z n ω' - c|} 1 ω
  have hSmeas : ∀ n, MeasurableSet {ω | η < |Z n ω - c|} := fun n =>
    measurableSet_lt measurable_const (((hZmeas n).sub measurable_const).norm)
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    measurable_one.indicator (hSmeas n)
  have hFbound : ∀ n, ∀ᵐ ω ∂μ, F n ω ≤ (fun _ : Ω => (1 : ℝ≥0∞)) ω := fun n =>
    Eventually.of_forall fun ω => by
      dsimp [F, Set.indicator]
      split_ifs <;> simp
  have h1int : ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ ≠ ∞ := by simp
  have hFlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have hev : ∀ᶠ n in atTop, |Z n ω - c| < η :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hω).eventually (gt_mem_nhds hη)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have hnot : ω ∉ {ω' | η < |Z n ω' - c|} := not_lt.mpr hn.le
    simp [F, hnot]
  have hlin := tendsto_lintegral_of_dominated_convergence (fun _ : Ω => (1 : ℝ≥0∞))
    hFmeas hFbound h1int hFlim
  simpa [F, lintegral_indicator_one, hSmeas] using hlin

end SolRWPILimitLemma3

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 < ρ) (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (b c₀ : ℝ) (hb : 0 < b) (hc₀ : 0 < c₀) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => μ {ω | ∃ ζ : Fin r → ℝ, ‖WithLp.toLp p ζ‖ ≤ b ∧
      ε < |(1 / (n : ℝ)) * ∑ i : Fin n,
              (if ‖WithLp.toLp p (W i ω)‖ ≤ c₀
                then rowNorm p h θs ζ (W i ω) ^ (ρ / (ρ - 1)) else 0)
            - ∫ ω', (if ‖WithLp.toLp p (W 0 ω')‖ ≤ c₀
                then rowNorm p h θs ζ (W 0 ω') ^ (ρ / (ρ - 1)) else 0) ∂μ|}) atTop (𝓝 0) := by
  have _ := hq
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  set β : ℝ := ρ / (ρ - 1)
  have hβ_pos : 0 < β := div_pos (zero_lt_one.trans hρ) (sub_pos.mpr hρ)
  set Kζ : Set (Fin r → ℝ) := {ζ | ‖WithLp.toLp p ζ‖ ≤ b}
  set BW : Set (Fin m → ℝ) := {w | ‖WithLp.toLp p w‖ ≤ c₀}
  have hKζ_comp : IsCompact Kζ := SolRWPILimitLemma3.isCompact_toLp_closedBall p b
  have hBW_comp : IsCompact BW := SolRWPILimitLemma3.isCompact_toLp_closedBall p c₀
  have hG_cont : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowNorm p h θs zw.1 zw.2 ^ β) :=
    SolRWPILimitLemma3.continuous_rowNorm_rpow p h θs hC1 β hβ_pos.le
  have hprod_comp : IsCompact (Kζ ×ˢ BW) := hKζ_comp.prod hBW_comp
  obtain ⟨M, hM_bound⟩ := hprod_comp.exists_bound_of_continuousOn hG_cont.continuousOn
  have hM_nonneg : 0 ≤ M := by
    have h0_mem : ((0 : Fin r → ℝ), (0 : Fin m → ℝ)) ∈ Kζ ×ˢ BW := by
      refine ⟨?_, ?_⟩
      · change ‖WithLp.toLp p (0 : Fin r → ℝ)‖ ≤ b; simp [hb.le]
      · change ‖WithLp.toLp p (0 : Fin m → ℝ)‖ ≤ c₀; simp [hc₀.le]
    exact (norm_nonneg _).trans (hM_bound (0, 0) h0_mem)
  set ψ : (Fin r → ℝ) → (Fin m → ℝ) → ℝ := fun ζ w =>
    if ‖WithLp.toLp p w‖ ≤ c₀ then rowNorm p h θs ζ w ^ β else 0
  have hψ_meas : ∀ ζ : Fin r → ℝ, Measurable (ψ ζ) := fun ζ => by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le (continuous_norm.comp (PiLp.continuous_toLp p _)).measurable
        measurable_const
    · exact (hG_cont.comp (continuous_const.prodMk continuous_id)).measurable
  have hψ_bound : ∀ ζ ∈ Kζ, ∀ w : Fin m → ℝ, ‖ψ ζ w‖ ≤ M := by
    intro ζ hζ w
    dsimp [ψ]
    split_ifs with hw
    · exact hM_bound (ζ, w) ⟨hζ, hw⟩
    · simpa using hM_nonneg
  have hψ_int : ∀ ζ ∈ Kζ, ∀ i : ℕ, Integrable (fun ω => ψ ζ (W i ω)) μ := by
    intro ζ hζ i
    exact Integrable.of_bound ((hψ_meas ζ).comp (hWmeas i)).aestronglyMeasurable M
      (Eventually.of_forall fun ω => hψ_bound ζ hζ (W i ω))
  have hG_ucont : UniformContinuousOn
      (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowNorm p h θs zw.1 zw.2 ^ β) (Kζ ×ˢ BW) :=
    hprod_comp.uniformContinuousOn_of_continuous hG_cont.continuousOn
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hG_ucont (ε / 3) hε3
  have hψ_lip : ∀ ζ ∈ Kζ, ∀ ξ ∈ Kζ, dist ζ ξ < δ → ∀ w : Fin m → ℝ,
      |ψ ζ w - ψ ξ w| ≤ ε / 3 := by
    intro ζ hζ ξ hξ hdist w
    dsimp [ψ]
    split_ifs with hw
    · have hp1 : (ζ, w) ∈ Kζ ×ˢ BW := ⟨hζ, hw⟩
      have hp2 : (ξ, w) ∈ Kζ ×ˢ BW := ⟨hξ, hw⟩
      have hd : dist (ζ, w) (ξ, w) < δ := by
        simpa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdist
      exact (hδ (ζ, w) hp1 (ξ, w) hp2 hd).le
    · simp [hε3.le]
  obtain ⟨F_set, hF_sub, hF_fin, hF_cov⟩ := hKζ_comp.elim_finite_subcover_image
    (fun ξ _ => Metric.isOpen_ball (x := ξ) (ε := δ))
    (fun ζ hζ => Set.mem_biUnion hζ (Metric.mem_ball_self hδ_pos))
  let F : Finset (Fin r → ℝ) := hF_fin.toFinset
  have hterm_tendsto : ∀ ξ ∈ F, Tendsto (fun n : ℕ => μ {ω | ε / 3 <
      |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω) - ∫ ω', ψ ξ (W 0 ω') ∂μ|}) atTop (𝓝 0) := by
    intro ξ hξF
    have hξK : ξ ∈ Kζ := hF_sub (hF_fin.mem_toFinset.mp hξF)
    set Y : ℕ → Ω → ℝ := fun i ω => ψ ξ (W i ω)
    have hY_indep : iIndepFun Y μ := hindep.comp (fun _ => ψ ξ) (fun _ => hψ_meas ξ)
    have hY_pair : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) Y) := fun i j hij => hY_indep.indepFun hij
    have hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i => (hident i).comp (hψ_meas ξ)
    have hY_int : Integrable (Y 0) μ := hψ_int ξ hξK 0
    have hslln := ProbabilityTheory.strong_law_ae_real Y hY_int hY_pair hY_ident
    have hae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ i : Fin n, Y i ω) atTop
        (𝓝 (∫ ω', Y 0 ω' ∂μ)) := by
      filter_upwards [hslln] with ω hω
      refine hω.congr fun n => ?_
      rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n, one_div_mul_eq_div]
    have hZmeas : ∀ n : ℕ, Measurable (fun ω => (1 / (n : ℝ)) * ∑ i : Fin n, Y i ω) := fun n =>
      measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ =>
        (hψ_meas ξ).comp (hWmeas i))
    exact SolRWPILimitLemma3.tendsto_prob_gt_of_tendsto_ae _ hZmeas _ hae hε3
  have hsum_tendsto : Tendsto (fun n : ℕ => ∑ ξ ∈ F, μ {ω | ε / 3 <
      |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω) - ∫ ω', ψ ξ (W 0 ω') ∂μ|}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum F fun ξ hξ => hterm_tendsto ξ hξ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_tendsto
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ici_mem_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsub : {ω | ∃ ζ : Fin r → ℝ, ‖WithLp.toLp p ζ‖ ≤ b ∧
      ε < |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ζ (W i ω) - ∫ ω', ψ ζ (W 0 ω') ∂μ|} ⊆
      ⋃ ξ ∈ F, {ω | ε / 3 <
        |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω) - ∫ ω', ψ ξ (W 0 ω') ∂μ|} := by
    rintro ω ⟨ζ, hζK, hε_lt⟩
    obtain ⟨ξ, hξF_set, hζξ⟩ := Set.mem_iUnion₂.mp (hF_cov hζK)
    have hξF : ξ ∈ F := hF_fin.mem_toFinset.mpr hξF_set
    have hξK : ξ ∈ Kζ := hF_sub hξF_set
    rw [Metric.mem_ball] at hζξ
    have hdiff_emp : |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ζ (W i ω) -
        (1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω)| ≤ ε / 3 := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hn_pos)]
      calc (1 / (n : ℝ)) * |∑ i : Fin n, (ψ ζ (W i ω) - ψ ξ (W i ω))|
          ≤ (1 / (n : ℝ)) * ∑ i : Fin n, |ψ ζ (W i ω) - ψ ξ (W i ω)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (one_div_pos.mpr hn_pos).le
        _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, (ε / 3) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _ => hψ_lip ζ hζK ξ hξK hζξ (W i ω))
              (one_div_pos.mpr hn_pos).le
        _ = ε / 3 := by
            simp [Finset.sum_const, nsmul_eq_mul, hn_pos.ne']
    have hdiff_exp : |∫ ω', ψ ζ (W 0 ω') ∂μ - ∫ ω', ψ ξ (W 0 ω') ∂μ| ≤ ε / 3 := by
      rw [← integral_sub (hψ_int ζ hζK 0) (hψ_int ξ hξK 0)]
      calc |∫ ω', (ψ ζ (W 0 ω') - ψ ξ (W 0 ω')) ∂μ|
          ≤ ∫ ω', |ψ ζ (W 0 ω') - ψ ξ (W 0 ω')| ∂μ := by
            simpa only [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (fun ω' => ψ ζ (W 0 ω') - ψ ξ (W 0 ω'))
        _ ≤ ∫ _ω', (ε / 3) ∂μ := by
            refine integral_mono ((hψ_int ζ hζK 0).sub (hψ_int ξ hξK 0)).abs
              (integrable_const _) fun ω' => hψ_lip ζ hζK ξ hξK hζξ (W 0 ω')
        _ = ε / 3 := by simp
    refine Set.mem_biUnion hξF ?_
    change ε / 3 < |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω) - ∫ ω', ψ ξ (W 0 ω') ∂μ|
    have htri : |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ζ (W i ω) - ∫ ω', ψ ζ (W 0 ω') ∂μ| ≤
        |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ζ (W i ω) - (1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω)| +
        |(1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω) - ∫ ω', ψ ξ (W 0 ω') ∂μ| +
        |∫ ω', ψ ξ (W 0 ω') ∂μ - ∫ ω', ψ ζ (W 0 ω') ∂μ| := by
      set A := (1 / (n : ℝ)) * ∑ i : Fin n, ψ ζ (W i ω)
      set B := (1 / (n : ℝ)) * ∑ i : Fin n, ψ ξ (W i ω)
      set C := ∫ ω', ψ ξ (W 0 ω') ∂μ
      set D := ∫ ω', ψ ζ (W 0 ω') ∂μ
      calc |A - D| = |(A - B) + (B - C) + (C - D)| := by ring_nf
        _ ≤ |A - B| + |B - C| + |C - D| :=
            (abs_add_le (A - B + (B - C)) (C - D)).trans
              (add_le_add (abs_add_le (A - B) (B - C)) le_rfl)
    rw [abs_sub_comm (∫ ω', ψ ξ (W 0 ω') ∂μ)] at htri
    linarith
  exact (measure_mono hsub).trans (measure_biUnion_finset_le F _)
