-- Prove2me | solution 1 for WassersteinDRO.Regularization.convex_loss_p1_borel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:59:41.208304+00:00
-- url     : https://prove2.me/submissions/d93b4e37-7ac7-42d0-9309-e15eab543f4a

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_worstCaseRisk
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace D58

open WassersteinDRO.Regularization

/-- Kantorovich-type bound for one coupling. -/
theorem kant_pi {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    (Q P : Measure E) (g : E → ℝ) (L : NNReal) (hg : LipschitzWith L g)
    (hQ : Integrable g Q) (hP : Integrable g P) (π : Measure (E × E))
    (h1 : π.map Prod.fst = Q) (h2 : π.map Prod.snd = P) :
    ENNReal.ofReal (∫ x, g x ∂Q - ∫ x, g x ∂P) ≤
      (L : ENNReal) * ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π := by
  have hgm : Measurable g := hg.continuous.measurable
  have i1 : Integrable (fun x : E × E => g x.1) π := by
    have : Integrable g (π.map Prod.fst) := h1 ▸ hQ
    exact (integrable_map_measure hgm.aestronglyMeasurable measurable_fst.aemeasurable).mp this
  have i2 : Integrable (fun x : E × E => g x.2) π := by
    have : Integrable g (π.map Prod.snd) := h2 ▸ hP
    exact (integrable_map_measure hgm.aestronglyMeasurable measurable_snd.aemeasurable).mp this
  have e1 : ∫ x, g x ∂Q = ∫ x, g x.1 ∂π := by
    rw [← h1, integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
  have e2 : ∫ x, g x ∂P = ∫ x, g x.2 ∂π := by
    rw [← h2, integral_map measurable_snd.aemeasurable hgm.aestronglyMeasurable]
  rw [e1, e2, ← integral_sub i1 i2]
  have hi : Integrable (fun x : E × E => g x.1 - g x.2) π := i1.sub i2
  calc ENNReal.ofReal (∫ x, (g x.1 - g x.2) ∂π)
      ≤ ENNReal.ofReal (∫ x, max (g x.1 - g x.2) 0 ∂π) :=
        ENNReal.ofReal_le_ofReal (integral_mono hi hi.pos_part (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (g x.1 - g x.2) 0) ∂π :=
        ofReal_integral_eq_lintegral_ofReal hi.pos_part (ae_of_all _ (fun x => le_max_right _ _))
    _ ≤ ∫⁻ x, (L : ENNReal) * ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π := by
        refine lintegral_mono (fun x => ?_)
        have hd : g x.1 - g x.2 ≤ L * ‖x.1 - x.2‖ := by
          have := hg.dist_le_mul x.1 x.2
          rw [Real.dist_eq, dist_eq_norm] at this
          exact (le_abs_self _).trans this
        rw [Real.rpow_one, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
        exact ENNReal.ofReal_le_ofReal (max_le hd (by positivity))
    _ = (L : ENNReal) * ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- Kantorovich-type bound against the Wasserstein distance. -/
theorem kant {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    (Q P : Measure E) (g : E → ℝ) (L : NNReal) (hg : LipschitzWith L g)
    (hQ : Integrable g Q) (hP : Integrable g P) (hW : wassersteinDistance 1 Q P ≠ ⊤) :
    ENNReal.ofReal (∫ x, g x ∂Q - ∫ x, g x ∂P) ≤ (L : ENNReal) * wassersteinDistance 1 Q P := by
  unfold wassersteinDistance at hW ⊢
  simp only [div_one, ENNReal.rpow_one] at hW ⊢
  by_cases hL : L = 0
  · subst hL
    obtain ⟨π, hπ⟩ := iInf_lt_iff.mp (lt_top_iff_ne_top.mpr hW)
    obtain ⟨hm, -⟩ := iInf_lt_iff.mp hπ
    have := kant_pi Q P g 0 hg hQ hP π hm.1 hm.2
    simpa using this
  · rw [ENNReal.mul_iInf_of_ne (by simpa using hL) ENNReal.coe_ne_top]
    refine le_iInf fun π => ?_
    rw [ENNReal.mul_iInf_of_ne (by simpa using hL) ENNReal.coe_ne_top]
    exact le_iInf fun hm => kant_pi Q P g L hg hQ hP π hm.1 hm.2

/-- If two finite measures have zero `W₁`-distance, they coincide (on a Borel normed space). -/
theorem eq_of_W_zero {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    (Q P : Measure E) [IsFiniteMeasure Q] [IsFiniteMeasure P]
    (hW : wassersteinDistance 1 Q P = 0) (huniv : Q Set.univ = P Set.univ) : Q = P := by
  have hint : ∀ (g : E → ℝ) (L : NNReal), LipschitzWith L g → Integrable g Q → Integrable g P →
      ∫ x, g x ∂Q = ∫ x, g x ∂P := by
    intro g L hg hQ hP
    have a1 := kant Q P g L hg hQ hP (by rw [hW]; exact ENNReal.zero_ne_top)
    have a2 := kant Q P (fun x => - g x) L hg.neg hQ.neg hP.neg (by rw [hW]; exact ENNReal.zero_ne_top)
    rw [hW, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at a1 a2
    rw [integral_neg, integral_neg] at a2
    linarith
  have hclosed : ∀ F : Set E, IsClosed F → Q F = P F := by
    intro F hF
    have δpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
    have hlim : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have tQ := tendsto_integral_thickenedIndicator_of_isClosed Q hF δpos hlim
    have tP := tendsto_integral_thickenedIndicator_of_isClosed P hF δpos hlim
    have heq : (fun n : ℕ => ∫ ω, (thickenedIndicator (δpos n) F ω : ℝ) ∂Q) =
        (fun n : ℕ => ∫ ω, (thickenedIndicator (δpos n) F ω : ℝ) ∂P) := by
      funext n
      refine hint _ (1 * (1 / ((n:ℝ) + 1)).toNNReal⁻¹) ?_
        (integrable_thickenedIndicator F (δpos n)) (integrable_thickenedIndicator F (δpos n))
      exact (LipschitzWith.subtype_val _).comp (lipschitzWith_thickenedIndicator (δpos n) F)
    rw [heq] at tQ
    have := tendsto_nhds_unique tQ tP
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
  refine ext_of_generate_finite {s : Set E | IsClosed s}
    ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    (fun s hs => hclosed s hs) huniv

/-- Slope lemma for convex functions: asymptotic slopes from any base point dominate chord
slopes. -/
theorem slope_ev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ) (a x y : E) (hxy : x ≠ y) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t in atTop, (ℓ x - ℓ y) / ‖x - y‖ - δ ≤
      (ℓ (a + t • (‖x - y‖⁻¹ • (x - y))) - ℓ a) / t := by
  set s := ‖x - y‖ with hs_def
  have hs : 0 < s := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  set d := s⁻¹ • (x - y) with hd_def
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y (y + (y - a))
  have hg : ∀ u : ℝ, g u = y + u • (y - a) := by
    intro u
    simp only [g, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left]
    abel
  have hcv : ConvexOn ℝ Set.univ (ℓ ∘ g) := by
    have := hconv.comp_affineMap g
    simpa using this
  have hcont : Continuous (ℓ ∘ g) :=
    continuousOn_univ.mp (hcv.continuousOn isOpen_univ)
  -- w t = g (s / (t - s))
  have hu : Tendsto (fun t : ℝ => s / (t - s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ (-s) tendsto_id)
  have hw : Tendsto (fun t : ℝ => ℓ (g (s / (t - s)))) atTop (𝓝 (ℓ y)) := by
    have := (hcont.tendsto 0).comp hu
    simpa [Function.comp_def, hg] using this
  have hst : Tendsto (fun t : ℝ => s / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hat : Tendsto (fun t : ℝ => ℓ a / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hF := (((tendsto_const_nhds (x := ℓ y)).sub
    (((tendsto_const_nhds (x := (1:ℝ))).sub hst).mul hw)).div_const s).sub hat
  have hF0 : (ℓ y - (1 - 0) * ℓ y) / s - 0 = 0 := by ring
  rw [hF0] at hF
  filter_upwards [hF.eventually (lt_mem_nhds (show (-δ) < 0 by linarith)),
    eventually_gt_atTop s] with t ht hts
  have ht0 : 0 < t := hs.trans hts
  have hts' : t - s ≠ 0 := by linarith
  set w := g (s / (t - s)) with hw_def
  set A := ℓ (a + t • d) with hA_def
  -- convexity: x = (1 - s/t) • w + (s/t) • (a + t • d)
  have hx : (1 - s / t) • w + (s / t) • (a + t • d) = x := by
    rw [hw_def, hg, hd_def]
    have hsne : s ≠ 0 := hs.ne'
    have htne : t ≠ 0 := ht0.ne'
    have e1 : (1 - s / t) * (s / (t - s)) = s / t := by field_simp
    have e2 : (s / t) * t * s⁻¹ = 1 := by field_simp
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, e1, e2, one_smul, smul_sub]
    have e3 : (1 - s / t) • y + (s / t) • y = y := by rw [← add_smul]; simp
    calc (1 - s / t) • y + ((s / t) • y - (s / t) • a) + ((s / t) • a + (x - y))
        = ((1 - s / t) • y + (s / t) • y) + (x - y) := by abel
      _ = x := by rw [e3]; abel
  have hconvx := hconv.2 (Set.mem_univ w) (Set.mem_univ (a + t • d))
    (show 0 ≤ 1 - s / t by rw [sub_nonneg, div_le_one ht0]; exact hts.le)
    (show 0 ≤ s / t by positivity) (by ring)
  rw [hx, smul_eq_mul, smul_eq_mul] at hconvx
  have hA : (ℓ x - (1 - s / t) * ℓ w) / s ≤ A / t := by
    rw [div_le_iff₀ hs]
    have : s / t * A = A / t * s := by ring
    linarith
  have hcomb : (ℓ x - (1 - s / t) * ℓ w) / s - (ℓ y - (1 - s / t) * ℓ w) / s =
      (ℓ x - ℓ y) / s := by ring
  have hsd : (A - ℓ a) / t = A / t - ℓ a / t := sub_div _ _ _
  linarith

end D58

open WassersteinDRO.Regularization MeasureTheory in
theorem solution {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution ξhat) ℓ =
      (nominalRisk (empiricalDistribution ξhat) ℓ : EReal) +
        ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by
  classical
  set P := empiricalDistribution ξhat with hPdef
  have hNne : (N : ENNReal) ≠ 0 := by exact_mod_cast hN.ne'
  have hNinv : (N : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hNne
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  let Qm : ℝ → E → Measure E := fun θ v => (N : ENNReal)⁻¹ • ∑ i, (ENNReal.ofReal (1 - θ) •
    Measure.dirac (ξhat i) + ENNReal.ofReal θ • Measure.dirac (ξhat i + v))
  have hQint : ∀ θ v (g : E → ℝ), Integrable g (Qm θ v) := by
    intro θ v g
    refine Integrable.smul_measure ?_ hNinv
    refine integrable_finsetSum_measure.mpr (fun i _ => ?_)
    refine Integrable.add_measure ?_ ?_
    · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hQval : ∀ θ v (g : E → ℝ), 0 ≤ θ → θ ≤ 1 → ∫ x, g x ∂(Qm θ v) =
      (N:ℝ)⁻¹ * ∑ i, ((1 - θ) * g (ξhat i) + θ * g (ξhat i + v)) := by
    intro θ v g h0 h1
    simp only [Qm]
    rw [integral_smul_measure, integral_finsetSum_measure]
    · congr 1
      · simp
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
          integral_dirac, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal h0,
          smul_eq_mul, smul_eq_mul]
        · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
        · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · intro i _
      refine Integrable.add_measure ?_ ?_
      · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
      · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hQ0 : Qm 0 0 = P := by
    simp [Qm, hPdef, empiricalDistribution]
  have hPint : ∀ g : E → ℝ, Integrable g P := fun g => hQ0 ▸ hQint 0 0 g
  have hQuniv : ∀ θ v, 0 ≤ θ → θ ≤ 1 → Qm θ v Set.univ = 1 := by
    intro θ v h0 h1
    have e : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) h0]; simp
    simp only [Qm, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.add_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, e,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.inv_mul_cancel hNne (ENNReal.natCast_ne_top N)
  have hPuniv : P Set.univ = 1 := by rw [← hQ0]; exact hQuniv 0 0 le_rfl zero_le_one
  have hmem : ∀ θ v, 0 ≤ θ → θ ≤ 1 → θ * ‖v‖ ≤ ε →
      Qm θ v ∈ ambiguitySet ε 1 Set.univ P := by
    intro θ v h0 h1 hθv
    refine ⟨hQuniv θ v h0 h1, by simp, ?_⟩
    unfold wassersteinDistance
    simp only [div_one, ENNReal.rpow_one]
    let π : Measure (E × E) := (N : ENNReal)⁻¹ • ∑ i, (ENNReal.ofReal (1 - θ) •
      Measure.dirac (ξhat i, ξhat i) + ENNReal.ofReal θ • Measure.dirac (ξhat i + v, ξhat i))
    refine (iInf₂_le_of_le π ⟨?_, ?_⟩ ?_)
    · simp only [π, Qm]
      rw [Measure.map_smul, Measure.map_finset_sum measurable_fst.aemeasurable]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
        Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst]
    · simp only [π, hPdef, empiricalDistribution]
      rw [Measure.map_smul, Measure.map_finset_sum measurable_snd.aemeasurable]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
        Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd, ← add_smul,
        ← ENNReal.ofReal_add (by linarith) h0]
      simp
    · simp only [π]
      rw [lintegral_smul_measure, lintegral_finsetSum_measure]
      simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, sub_self,
        norm_zero, add_sub_cancel_left, Real.rpow_one, ENNReal.ofReal_zero, mul_zero, zero_add,
        smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hNne (ENNReal.natCast_ne_top N), one_mul,
        ← ENNReal.ofReal_mul h0]
      exact ENNReal.ofReal_le_ofReal hθv
  have hnom : ∀ θ v, 0 ≤ θ → θ ≤ 1 → nominalRisk (Qm θ v) ℓ = nominalRisk P ℓ +
      θ * ((N:ℝ)⁻¹ * ∑ i, (ℓ (ξhat i + v) - ℓ (ξhat i))) := by
    intro θ v h0 h1
    unfold nominalRisk
    rw [hQval θ v ℓ h0 h1, ← hQ0, hQval 0 0 ℓ le_rfl zero_le_one]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hlow : ∀ θ v, 0 ≤ θ → θ ≤ 1 → θ * ‖v‖ ≤ ε →
      (nominalRisk (Qm θ v) ℓ : EReal) ≤ worstCaseRisk ε 1 Set.univ P ℓ := by
    intro θ v h0 h1 hθv
    unfold worstCaseRisk
    exact le_iSup_of_le (Qm θ v) (le_iSup_of_le (hmem θ v h0 h1 hθv)
      (le_iSup_of_le (hQint θ v ℓ) le_rfl))
  have hW0 : (nominalRisk P ℓ : EReal) ≤ worstCaseRisk ε 1 Set.univ P ℓ := by
    have := hlow 0 0 le_rfl zero_le_one (by simpa using hε)
    rwa [hnom 0 0 le_rfl zero_le_one, zero_mul, add_zero] at this
  haveI : IsProbabilityMeasure P := ⟨hPuniv⟩
  apply le_antisymm
  · -- upper bound
    unfold worstCaseRisk
    refine iSup_le fun Q => iSup_le fun hQ => iSup_le fun hi => ?_
    obtain ⟨hQ1, -, hQW⟩ := hQ
    haveI : IsFiniteMeasure Q := ⟨by rw [hQ1]; exact ENNReal.one_lt_top⟩
    by_cases hLip : lipschitzModulus ℓ = ⊤
    · rcases hε.eq_or_lt with h0 | hpos
      · subst h0
        have hW : wassersteinDistance 1 Q P = 0 := by simpa using hQW
        have hQP := D58.eq_of_W_zero Q P hW (by rw [hQ1, hPuniv])
        subst hQP
        simp
      · rw [hLip, ENNReal.mul_top (by simpa using hpos), EReal.coe_ennreal_top,
          EReal.coe_add_top]
        exact le_top
    · set L := (lipschitzModulus ℓ).toNNReal with hLdef
      have hL : (L : ENNReal) = lipschitzModulus ℓ := ENNReal.coe_toNNReal hLip
      have hlip : LipschitzWith L ℓ := by
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        by_cases hxy : x = y
        · subst hxy; simp
        have h1 : ENNReal.ofReal (|ℓ x - ℓ y| / ‖x - y‖) ≤ lipschitzModulus ℓ := by
          unfold lipschitzModulus
          exact le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
        rw [← hL, ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
          div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))] at h1
        rw [Real.dist_eq, dist_eq_norm]
        exact h1
      have hk := D58.kant Q P ℓ L hlip hi (hPint ℓ) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQW)
      have hk2 : ENNReal.ofReal (∫ x, ℓ x ∂Q - ∫ x, ℓ x ∂P) ≤ ENNReal.ofReal (L * ε) := by
        refine hk.trans ?_
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal]
        gcongr
      have hk3 : ∫ x, ℓ x ∂Q - ∫ x, ℓ x ∂P ≤ L * ε :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hk2
      rw [← hL, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hε, EReal.coe_ennreal_ofReal,
        max_eq_left (by positivity), ← EReal.coe_add, EReal.coe_le_coe_iff]
      unfold nominalRisk
      linarith
  · -- lower bound
    rcases hε.eq_or_lt with h0 | hpos
    · subst h0
      simpa using hW0
    have key : ∀ x y : E, x ≠ y → ℓ y ≤ ℓ x → ∀ δ : ℝ, 0 < δ →
        ((nominalRisk P ℓ + ε * ((ℓ x - ℓ y) / ‖x - y‖ - δ) : ℝ) : EReal) ≤
          worstCaseRisk ε 1 Set.univ P ℓ := by
      intro x y hxy hle δ hδ
      have hev := (eventually_all.2 fun i => D58.slope_ev ℓ hconv (ξhat i) x y hxy δ hδ).and
        ((eventually_ge_atTop ε).and (eventually_gt_atTop (0:ℝ)))
      obtain ⟨t, hti, hεt, ht0⟩ := hev.exists
      set v := t • (‖x - y‖⁻¹ • (x - y)) with hv_def
      have hs : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hv : ‖v‖ = t := by
        rw [hv_def, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne', mul_one,
          Real.norm_eq_abs, abs_of_pos ht0]
      have hθ0 : 0 ≤ ε / t := by positivity
      have hθ1 : ε / t ≤ 1 := (div_le_one ht0).mpr hεt
      have hθv : ε / t * ‖v‖ ≤ ε := by rw [hv, div_mul_cancel₀ _ ht0.ne']
      refine le_trans ?_ (hlow (ε / t) v hθ0 hθ1 hθv)
      rw [hnom (ε / t) v hθ0 hθ1, EReal.coe_le_coe_iff]
      have hsum : ∑ i : Fin N, ε * ((ℓ x - ℓ y) / ‖x - y‖ - δ) ≤
          ∑ i, ε * ((ℓ (ξhat i + v) - ℓ (ξhat i)) / t) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hti i) hε)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have hsum2 : ∑ i, ε * ((ℓ (ξhat i + v) - ℓ (ξhat i)) / t) =
          ε / t * ∑ i, (ℓ (ξhat i + v) - ℓ (ξhat i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [hsum2] at hsum
      have e : ε / t * ((N:ℝ)⁻¹ * ∑ i, (ℓ (ξhat i + v) - ℓ (ξhat i))) =
          (ε / t * ∑ i, (ℓ (ξhat i + v) - ℓ (ξhat i))) / N := by
        field_simp
      rw [e]
      have : ε * ((ℓ x - ℓ y) / ‖x - y‖ - δ) ≤ (ε / t * ∑ i, (ℓ (ξhat i + v) - ℓ (ξhat i))) / N := by
        rw [le_div_iff₀ hNR]
        linarith
      linarith
    set W := worstCaseRisk ε 1 Set.univ P ℓ with hWdef
    by_cases hWtop : W = ⊤
    · rw [hWtop]; exact le_top
    have hWbot : W ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hW0
    obtain ⟨r, hr⟩ : ∃ r : ℝ, W = r := ⟨W.toReal, (EReal.coe_toReal hWtop hWbot).symm⟩
    rw [hr] at hW0 key ⊢
    have hnr : nominalRisk P ℓ ≤ r := EReal.coe_le_coe_iff.mp hW0
    have gen : ∀ x y : E, x ≠ y → ℓ y ≤ ℓ x →
        ε * ((ℓ x - ℓ y) / ‖x - y‖) ≤ r - nominalRisk P ℓ := by
      intro x y hxy hle
      refine le_of_forall_pos_le_add fun η hη => ?_
      have := key x y hxy hle (η / ε) (by positivity)
      rw [EReal.coe_le_coe_iff, mul_sub, mul_div_cancel₀ _ hpos.ne'] at this
      linarith
    have hbound : ENNReal.ofReal ε * lipschitzModulus ℓ ≤
        ENNReal.ofReal (r - nominalRisk P ℓ) := by
      unfold lipschitzModulus
      simp only [ENNReal.mul_iSup]
      refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
      rw [← ENNReal.ofReal_mul hε]
      apply ENNReal.ofReal_le_ofReal
      rcases le_total (ℓ y) (ℓ x) with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]; exact gen x y hxy h
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h), norm_sub_rev]
        exact gen y x (Ne.symm hxy) h
    calc (nominalRisk P ℓ : EReal) + ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal)
        ≤ (nominalRisk P ℓ : EReal) + ((ENNReal.ofReal (r - nominalRisk P ℓ) : ENNReal) : EReal) :=
          add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hbound)
      _ = r := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (sub_nonneg.mpr hnr), ← EReal.coe_add]
          congr 1
          ring
