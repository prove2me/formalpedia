-- Prove2me | solution 1 for WassersteinDRO.Regularization.witness_family_liminf
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-07T09:25:44.610908+00:00
-- url     : https://prove2.me/submissions/a17e35a0-8d14-4af9-90a8-a98f18702aff

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_ambiguitySet
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance
import Theorems.Thm_WassersteinDRO_Regularization_steep_gap_exists
import Theorems.Thm_WassersteinDRO_Regularization_convex_ray_slope_mono

set_option autoImplicit false

open MeasureTheory
open WassersteinDRO.Regularization

theorem solution {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E]
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hm : Measurable ℓ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hP : Integrable ℓ (empiricalDistribution ξhat))
    (lam : ℝ) (hlam : 0 < lam) (hlt : ENNReal.ofReal lam < lipschitzModulus ℓ) :
    ∃ Q : ℝ → Measure E, ∃ T₀ : ℝ,
      (∀ t : ℝ, T₀ ≤ t → Q t ∈ ambiguitySet ε 1 Set.univ (empiricalDistribution ξhat)) ∧
      (∀ t : ℝ, T₀ ≤ t → Integrable ℓ (Q t)) ∧
      ∀ r : ℝ, r < nominalRisk (empiricalDistribution ξhat) ℓ + ε * lam →
        Filter.Eventually (fun t => r < nominalRisk (Q t) ℓ) Filter.atTop := by
  -- 0. Abbreviations
  set Phat : Measure E := empiricalDistribution ξhat with hPhat
  set Rnom : ℝ := nominalRisk Phat ℓ with hRnom
  have hP' : Integrable ℓ Phat := hP
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- Phat is a probability measure
  have hsum1 : (∑ i, Measure.dirac (ξhat i) : Measure E) Set.univ = (N : ENNReal) := by
    rw [Measure.finsetSum_apply]
    have h1 : ∀ i : Fin N, (Measure.dirac (ξhat i)) Set.univ = 1 := fun i => by simp
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  have hPhat1 : Phat Set.univ = 1 := by
    rw [hPhat]
    simp only [empiricalDistribution]
    rw [Measure.smul_apply, hsum1]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast ne_of_gt hN) (ENNReal.natCast_ne_top N)
  have hProb : IsProbabilityMeasure Phat := ⟨hPhat1⟩
  -- 1. Steep pair from leaf 3A; unit direction u; x = y + d • u
  obtain ⟨x, y, hxy, hgap⟩ := steep_gap_exists ℓ lam (le_of_lt hlam) hlt
  set d : ℝ := ‖x - y‖ with hd_def
  have hd : 0 < d := by
    rw [hd_def, norm_pos_iff, sub_ne_zero]
    exact hxy
  set u : E := d⁻¹ • (x - y) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), ← hd_def,
      inv_mul_cancel₀ (ne_of_gt hd)]
  have hxu : x = y + d • u := by
    rw [hu_def, ← mul_smul, mul_inv_cancel₀ (ne_of_gt hd), one_smul]
    abel
  -- 2. Mean-distance constants and the witness family
  set C : ℝ := (1 / (N : ℝ)) * Finset.sum Finset.univ (fun i => ‖ξhat i - y‖) with hC
  set D : ℝ := Rnom - ℓ y with hD
  set ct : ℝ → ℝ := fun t => (1 / (N : ℝ)) * Finset.sum Finset.univ (fun i => ‖ξhat i - (y + t • u)‖) with hct
  set mt : ℝ → ℝ := fun t => ε / ct t with hmt
  set Qt : ℝ → Measure E := fun t => (ENNReal.ofReal (1 - mt t)) • Phat
      + (ENNReal.ofReal (mt t)) • Measure.dirac (y + t • u) with hQt
  set T₀ : ℝ := max d (C + ε) with hT₀
  have hct_t : ∀ t : ℝ, ct t = (1 / (N : ℝ)) * Finset.sum Finset.univ (fun i => ‖ξhat i - (y + t • u)‖) :=
    fun t => rfl
  have hmt_t : ∀ t : ℝ, mt t = ε / ct t := fun t => rfl
  have hQt_t : ∀ t : ℝ, Qt t = (ENNReal.ofReal (1 - mt t)) • Phat
      + (ENNReal.ofReal (mt t)) • Measure.dirac (y + t • u) := fun t => rfl
  have hT₀_eq : T₀ = max d (C + ε) := rfl
  have e1 : ∀ t : ℝ, (1 / (N : ℝ)) * ((N : ℝ) * t) = t := by
    intro t
    rw [one_div, inv_mul_cancel_left₀ hNne]
  -- 3. Lower bound ct t ≥ t - C
  have hct_low : ∀ t : ℝ, 0 ≤ t → t - C ≤ ct t := by
    intro t ht0
    have hxty : ‖(y + t • u) - y‖ = t := by
      rw [show (y + t • u) - y = t • u from by abel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht0, hu, mul_one]
    have hterm : ∀ i : Fin N, t - ‖ξhat i - y‖ ≤ ‖ξhat i - (y + t • u)‖ := by
      intro i
      have h := norm_sub_norm_le ((y + t • u) - y) (ξhat i - y)
      rw [hxty] at h
      have heq : ((y + t • u) - y) - (ξhat i - y) = (y + t • u) - ξhat i := by abel
      have hrev : ‖(y + t • u) - ξhat i‖ = ‖ξhat i - (y + t • u)‖ := norm_sub_rev _ _
      rw [heq, hrev] at h
      exact h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [Finset.sum_sub_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hNpos))
    rw [mul_sub, e1] at hmul
    rw [hct_t t, hC]
    linarith
  -- 4. Upper bound ct t ≤ t + C
  have hct_high : ∀ t : ℝ, 0 ≤ t → ct t ≤ t + C := by
    intro t ht0
    have hxty : ‖y - (y + t • u)‖ = t := by
      rw [show y - (y + t • u) = -(t • u) from by abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht0, hu, mul_one]
    have hterm : ∀ i : Fin N, ‖ξhat i - (y + t • u)‖ ≤ ‖ξhat i - y‖ + t := by
      intro i
      have h := norm_add_le (ξhat i - y) (y - (y + t • u))
      have heq : (ξhat i - y) + (y - (y + t • u)) = ξhat i - (y + t • u) := by abel
      rw [heq, hxty] at h
      exact h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hNpos))
    rw [mul_add, e1] at hmul
    rw [hct_t t, hC]
    linarith
  -- 5. Per-t package for t ≥ T₀
  have pkg : ∀ t : ℝ, T₀ ≤ t → 0 ≤ t ∧ d ≤ t ∧ 0 < ct t ∧ 0 < mt t ∧ mt t ≤ 1 ∧
      ENNReal.ofReal (1 - mt t) + ENNReal.ofReal (mt t) = 1 ∧
      Integrable ℓ (Measure.dirac (y + t • u)) := by
    intro t ht
    have hdt : d ≤ t := le_trans (le_max_left d (C + ε)) (hT₀_eq ▸ ht)
    have ht0 : 0 ≤ t := le_trans (norm_nonneg _) hdt
    have hCt : C + ε ≤ t := le_trans (le_max_right d (C + ε)) (hT₀_eq ▸ ht)
    have hct_pos : 0 < ct t := lt_of_lt_of_le hε (by linarith [hct_low t ht0, hCt])
    have hmt0 : 0 < mt t := by rw [hmt_t t]; exact div_pos hε hct_pos
    have hmt1 : mt t ≤ 1 := by
      rw [hmt_t t, div_le_one hct_pos]
      linarith [hct_low t ht0, hCt]
    have hof : ENNReal.ofReal (1 - mt t) + ENNReal.ofReal (mt t) = 1 := by
      refine (ENNReal.ofReal_add ?_ ?_).symm.trans ?_
      · linarith
      · linarith
      · rw [sub_add_cancel, ENNReal.ofReal_one]
    have hdi : Integrable ℓ (Measure.dirac (y + t • u)) :=
      MeasureTheory.integrable_dirac (lt_top_iff_ne_top.mpr enorm_ne_top)
    exact ⟨ht0, hdt, hct_pos, hmt0, hmt1, hof, hdi⟩
  -- 6. Growth along the ray from leaf 3B
  have hgrow : ∀ t : ℝ, d ≤ t → lam * t < ℓ (y + t • u) - ℓ y := by
    intro t hdt'
    have htpos : 0 < t := lt_of_lt_of_le hd hdt'
    have h3B := convex_ray_slope_mono ℓ hconv y u hu d t hd hdt'
    rw [← hxu] at h3B
    have hlamd : lam < (ℓ x - ℓ y) / d := by
      rw [lt_div_iff₀ hd]
      exact hgap
    have hle : lam < (ℓ (y + t • u) - ℓ y) / t := lt_of_lt_of_le hlamd h3B
    rw [lt_div_iff₀ htpos] at hle
    exact hle
  -- 7. Risk formula for Qt
  have hrisk : ∀ t : ℝ, T₀ ≤ t → nominalRisk (Qt t) ℓ = (1 - mt t) * Rnom + (mt t) * ℓ (y + t • u) := by
    intro t ht
    obtain ⟨-, -, -, hmt0, hmt1, -, hdi⟩ := pkg t ht
    have h1 : Integrable ℓ ((ENNReal.ofReal (1 - mt t)) • Phat) :=
      hP'.smul_measure ENNReal.ofReal_ne_top
    have h2 : Integrable ℓ ((ENNReal.ofReal (mt t)) • Measure.dirac (y + t • u)) :=
      hdi.smul_measure ENNReal.ofReal_ne_top
    rw [hQt_t t]
    show (∫ x, ℓ x ∂((ENNReal.ofReal (1 - mt t)) • Phat
        + (ENNReal.ofReal (mt t)) • Measure.dirac (y + t • u)))
        = (1 - mt t) * Rnom + (mt t) * ℓ (y + t • u)
    rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (le_of_lt hmt0)]
    have hR : (∫ x, ℓ x ∂Phat) = Rnom := hRnom.symm
    rw [hR, smul_eq_mul, smul_eq_mul]
  -- auxiliary: t + C → atTop
  have hadd : Filter.Tendsto (fun t : ℝ => t + C) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - C)] with t ht
    linarith
  have hNinv : ((N : ENNReal))⁻¹ = ENNReal.ofReal ((N : ℝ))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  refine ⟨Qt, T₀, ?_, ?_, ?_⟩
  · -- Obligation 1: Qt t ∈ ambiguitySet
    intro t ht
    obtain ⟨ht0, hdt, hct_pos, hmt0, hmt1, hof, -⟩ := pkg t ht
    have hdi1 : (Measure.dirac (y + t • u)) Set.univ = 1 := by simp
    have hQt1 : Qt t Set.univ = 1 := by
      rw [hQt_t t, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul, hPhat1, hdi1, mul_one, mul_one, hof]
    have hQt0 : Qt t Set.univᶜ = 0 := by
      rw [hQt_t t, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul, Set.compl_univ, measure_empty, measure_empty, mul_zero, mul_zero, add_zero]
    have hdiag : Measurable (fun x : E => (x, x)) := measurable_id.prodMk measurable_id
    set π : Measure (E × E) :=
      (ENNReal.ofReal (1 - mt t)) • (Phat.map (fun x : E => (x, x)))
      + (ENNReal.ofReal (mt t)) • ((Measure.dirac (y + t • u)).prod Phat) with hπ
    have hcomp1 : (Prod.fst ∘ fun x : E => (x, x)) = id := by ext x; rfl
    have hcomp2 : (Prod.snd ∘ fun x : E => (x, x)) = id := by ext x; rfl
    have hπfst : π.map Prod.fst = Qt t := by
      rw [hπ, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
        Measure.map_map measurable_fst hdiag, hcomp1, Measure.map_id, Measure.map_fst_prod,
        hPhat1, one_smul, hQt_t t]
    have hπsnd : π.map Prod.snd = Phat := by
      rw [hπ, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
        Measure.map_map measurable_snd hdiag, hcomp2, Measure.map_id, Measure.map_snd_prod,
        hdi1, one_smul, ← add_smul, hof, one_smul]
    have hcost : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π = ENNReal.ofReal ε := by
      simp only [Real.rpow_one]
      rw [hπ, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
      have h1 : ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂(Phat.map (fun x : E => (x, x))) = 0 := by
        rw [hPhat]
        simp only [empiricalDistribution, Measure.map_smul]
        have hmap_sum : ((∑ i : Fin N, Measure.dirac (ξhat i)).map (fun x : E => (x, x)))
            = ∑ i : Fin N, (Measure.dirac (ξhat i)).map (fun x : E => (x, x)) := by
          induction' Finset.univ (α := Fin N) using Finset.induction with a s ha ih
          · simp
          · rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hdiag, ih]
        rw [hmap_sum]
        have hdirac_map : ∀ i : Fin N, (Measure.dirac (ξhat i)).map (fun x : E => (x, x))
            = Measure.dirac (ξhat i, ξhat i) := fun i => Measure.map_dirac' hdiag (ξhat i)
        simp only [hdirac_map, lintegral_smul_measure, lintegral_finsetSum_measure Finset.univ _ _,
          lintegral_dirac]
        simp
      have h2 : ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂((Measure.dirac (y + t • u)).prod Phat)
          = ENNReal.ofReal (ct t) := by
        have hg_meas : Measurable (fun z : E × E => ENNReal.ofReal ‖(y + t • u) - z.2‖) := by
          have h1 : Measurable (fun b : E => ENNReal.ofReal ‖(y + t • u) - b‖) := by
            apply ENNReal.measurable_ofReal.comp
            apply Measurable.norm
            have hcont : Continuous (fun b : E => (y + t • u) - b) := by fun_prop
            exact hcont.measurable
          exact h1.comp measurable_snd
        have h_fst : ∀ᵐ z : E × E ∂((Measure.dirac (y + t • u)).prod Phat), z.1 = (y + t • u) := by
          rw [ae_iff]
          have hset : {z : E × E | ¬(z.1 = (y + t • u))} = {(y + t • u)}ᶜ ×ˢ Set.univ := by
            ext ⟨a, b⟩
            simp
          rw [hset, Measure.prod_prod]
          have hs : MeasurableSet ({(y + t • u)}ᶜ : Set E) := (measurableSet_singleton _).compl
          have h1 : (Measure.dirac (y + t • u)) {(y + t • u)}ᶜ = 0 := by
            have hmem : (y + t • u) ∉ ({(y + t • u)}ᶜ : Set E) := by simp
            rw [Measure.dirac_apply' _ hs]
            simp [hmem]
          rw [h1, zero_mul]
        have h_ae_eq : ∀ᵐ z : E × E ∂((Measure.dirac (y + t • u)).prod Phat),
            ENNReal.ofReal ‖z.1 - z.2‖ = ENNReal.ofReal ‖(y + t • u) - z.2‖ := by
          filter_upwards [h_fst] with z hz
          rw [hz]
        rw [lintegral_congr_ae h_ae_eq, lintegral_prod _ hg_meas.aemeasurable]
        simp only [lintegral_dirac]
        rw [hPhat]
        simp only [empiricalDistribution]
        rw [lintegral_smul_measure, lintegral_finsetSum_measure Finset.univ _ _]
        simp only [lintegral_dirac]
        have h_norm : ∀ i : Fin N, ENNReal.ofReal ‖(y + t • u) - ξhat i‖
            = ENNReal.ofReal ‖ξhat i - (y + t • u)‖ := fun i => by rw [norm_sub_rev]
        simp only [h_norm]
        have hNnn : (0:ℝ) ≤ (↑N)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _), hNinv, smul_eq_mul,
          ← ENNReal.ofReal_mul hNnn]
        congr 1
        rw [hct_t t, inv_eq_one_div]
      rw [h1, h2, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, ← ENNReal.ofReal_mul hmt0.le]
      congr 1
      rw [hmt_t t]
      exact div_mul_cancel₀ ε (ne_of_gt hct_pos)
    have hW : wassersteinDistance 1 (Qt t) Phat ≤ ENNReal.ofReal ε := by
      unfold wassersteinDistance
      rw [div_one, ENNReal.rpow_one]
      have hle : (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Qt t ∧ π.map Prod.snd = Phat),
          ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π)
          ≤ ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π := by
        calc (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Qt t ∧ π.map Prod.snd = Phat),
              ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π)
            ≤ (⨅ _ : π.map Prod.fst = Qt t ∧ π.map Prod.snd = Phat,
              ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π) := iInf_le _ π
          _ ≤ ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1:ℝ)) ∂π := iInf_le _ ⟨hπfst, hπsnd⟩
      exact hle.trans hcost.le
    exact ⟨hQt1, hQt0, hW⟩
  · -- Obligation 2: integrability
    intro t ht
    obtain ⟨-, -, -, hmt0, hmt1, -, hdi⟩ := pkg t ht
    have h1 : Integrable ℓ ((ENNReal.ofReal (1 - mt t)) • Phat) :=
      hP'.smul_measure ENNReal.ofReal_ne_top
    have h2 : Integrable ℓ ((ENNReal.ofReal (mt t)) • Measure.dirac (y + t • u)) :=
      hdi.smul_measure ENNReal.ofReal_ne_top
    rw [hQt_t t]
    exact h1.add_measure h2
  · -- Obligation 3: risk eventually exceeds every level below Rnom + ε * lam
    intro r hr
    have hrr : r - Rnom < ε * lam := by linarith
    have hL : Filter.Tendsto (fun t : ℝ => ε * ((lam * t - D) / (t + C))) Filter.atTop
        (nhds (ε * lam)) := by
      have h1 : Filter.Tendsto (fun t : ℝ => (lam * C + D) / (t + C)) Filter.atTop (nhds 0) := by
        have hnum : Filter.Tendsto (fun _ : ℝ => lam * C + D) Filter.atTop (nhds (lam * C + D)) :=
          tendsto_const_nhds
        exact hnum.div_atTop hadd
      have h2 : Filter.Tendsto (fun t : ℝ => lam - (lam * C + D) / (t + C)) Filter.atTop
          (nhds lam) := by
        have hnum2 : Filter.Tendsto (fun _ : ℝ => lam) Filter.atTop (nhds lam) :=
          tendsto_const_nhds
        have h := hnum2.sub h1
        rwa [sub_zero] at h
      have h3 := h2.const_mul ε
      refine h3.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (-C)] with t ht
      have htc : t + C ≠ 0 := by linarith
      field_simp
      ring
    have hev1 : ∀ᶠ t in Filter.atTop, r - Rnom < ε * ((lam * t - D) / (t + C)) :=
      hL.eventually (Ioi_mem_nhds hrr)
    have hev2 : ∀ᶠ t in Filter.atTop, D < lam * t := by
      have htop : Filter.Tendsto (fun t : ℝ => lam * t) Filter.atTop Filter.atTop :=
        (Filter.Tendsto.atTop_mul_const hlam Filter.tendsto_id).congr (fun t => mul_comm t lam)
      exact htop.eventually (Filter.eventually_gt_atTop D)
    filter_upwards [hev1, hev2, Filter.eventually_ge_atTop T₀] with t h1 h2 h3
    obtain ⟨ht0, hdt, hct_pos, hmt0, hmt1, -, -⟩ := pkg t h3
    have hct_le := hct_high t ht0
    have hgrow_t := hgrow t hdt
    have hrisk_t := hrisk t h3
    have hmt_ge : ε / (t + C) ≤ mt t := by
      have hC : (0 : ℝ) < t + C := by linarith
      rw [hmt_t t, div_le_iff₀ hC, div_mul_eq_mul_div, le_div_iff₀ hct_pos]
      exact mul_le_mul_of_nonneg_left hct_le (le_of_lt hε)
    have hpos : (0 : ℝ) ≤ lam * t - D := by
      have hD : D = Rnom - ℓ y := rfl
      linarith
    have hLle : ε * ((lam * t - D) / (t + C)) ≤ (mt t) * (lam * t - D) := by
      have he : ε * ((lam * t - D) / (t + C)) = (ε / (t + C)) * (lam * t - D) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hmt_ge hpos
    have hexc : (mt t) * (lam * t - D) < nominalRisk (Qt t) ℓ - Rnom := by
      rw [hrisk_t]
      have hlt' : (mt t) * (lam * t - D) < (mt t) * (ℓ (y + t • u) - Rnom) := by
        apply mul_lt_mul_of_pos_left _ hmt0
        have hD : D = Rnom - ℓ y := rfl
        linarith
      have hring : (1 - mt t) * Rnom + (mt t) * ℓ (y + t • u) - Rnom
          = (mt t) * (ℓ (y + t • u) - Rnom) := by ring
      linarith
    linarith

theorem WassersteinDRO.Regularization.witness_family_liminf {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E]
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hm : Measurable ℓ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hP : Integrable ℓ (empiricalDistribution ξhat))
    (lam : ℝ) (hlam : 0 < lam) (hlt : ENNReal.ofReal lam < lipschitzModulus ℓ) :
    ∃ Q : ℝ → Measure E, ∃ T₀ : ℝ,
      (∀ t : ℝ, T₀ ≤ t → Q t ∈ ambiguitySet ε 1 Set.univ (empiricalDistribution ξhat)) ∧
      (∀ t : ℝ, T₀ ≤ t → Integrable ℓ (Q t)) ∧
      ∀ r : ℝ, r < nominalRisk (empiricalDistribution ξhat) ℓ + ε * lam →
        Filter.Eventually (fun t => r < nominalRisk (Q t) ℓ) Filter.atTop :=
  solution ε hε hN ξhat ℓ hm hconv hP lam hlam hlt
