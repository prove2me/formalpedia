-- Prove2me | solution 1 for RobustSPA.Affiliated.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:10:50.741296+00:00
-- url     : https://prove2.me/submissions/6b93b4b9-8ddd-4744-a88a-ca469a386617

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting
import Theorems.Thm_RobustSPA_Affiliated_lemma_1
import Theorems.Thm_RobustSPA_Affiliated_nature_step_aff
import Theorems.Thm_RobustSPA_Affiliated_pointwise_bound_aff
import Theorems.Thm_RobustSPA_Affiliated_regret_Fstar_eq
import Theorems.Thm_RobustSPA_Affiliated_Fiid_subset_Faff
import Theorems.Thm_RobustSPA_IID_SPA_isDSIC
import Theorems.Thm_RobustSPA_IID_step_2_seller
import Theorems.Thm_RobustSPA_IID_step_1_nature
import Theorems.Thm_RobustSPA_IID_proposition_A_3

open MeasureTheory RobustSPA.IID RobustSPA.Affiliated

namespace RAffProp2Red

/-- Regret of a DSIC mechanism is bounded above uniformly over laws supported on the cube. -/
lemma regret_bdd {n : ℕ} (hn : 0 < n) (m : Mechanism n) (hm : m.IsDSIC) :
    ∃ C : ℝ, ∀ μ ∈ Fall n, regret m μ ≤ C := by
  obtain ⟨B, hB⟩ := hm.p_bdd
  refine ⟨1 + n * |B|, fun μ hμ => ?_⟩
  haveI := hμ.1
  have hae : ∀ᵐ v ∂μ, v ∈ cube n := by
    rw [ae_iff]
    simpa [Set.compl_def] using hμ.2
  have hC : 0 ≤ 1 + n * |B| := by positivity
  by_cases hint : Integrable (fun v => top v - ∑ i, m.p i v) μ
  · unfold regret
    calc ∫ v, (top v - ∑ i, m.p i v) ∂μ ≤ ∫ _v, (1 + n * |B|) ∂μ := by
          apply integral_mono_ae hint (integrable_const _)
          filter_upwards [hae] with v hv
          have htop : top v ≤ 1 := by
            haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
            exact ciSup_le fun i => (hv i (Set.mem_univ _)).2
          have hs : -(∑ i, m.p i v) ≤ n * |B| := by
            rw [← Finset.sum_neg_distrib]
            calc ∑ i, -m.p i v ≤ ∑ _i : Fin n, |B| := Finset.sum_le_sum fun i _ => by
                  have h1 := hB v hv i
                  have h2 := le_abs_self B
                  have h3 := neg_le_abs (m.p i v)
                  linarith
              _ = n * |B| := by simp
          linarith
      _ = 1 + n * |B| := by simp
  · unfold regret
    rw [integral_undef hint]
    exact hC

/-- The isorevenue law lives on `[0,1]`. -/
lemma G_supp (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (G : ProbabilityMeasure ℝ)
    (hG : ∀ t, cdfOf G t = isoCDF r t) : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 := by
  have h0 : (G : Measure ℝ) (Set.Iic 0) = 0 := by
    have := hG 0
    simp only [cdfOf, isoCDF, if_pos hr0] at this
    rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have h1 : (G : Measure ℝ) (Set.Iic 1) = 1 := by
    have := hG 1
    simp only [cdfOf, isoCDF, if_neg (not_lt.mpr hr1.le), lt_irrefl, if_false] at this
    have hne : (G : Measure ℝ) (Set.Iic 1) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hne, this, ENNReal.ofReal_one]
  have h2 : (G : Measure ℝ) (Set.Ioi 1) = 0 := by
    rw [← Set.compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic]
    exact h1
  have hsub : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ Set.Iic 0 ∪ Set.Ioi 1 := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl (le_of_lt hx)
    · exact Or.inr hx
  apply le_antisymm _ bot_le
  calc (G : Measure ℝ) (Set.Icc 0 1)ᶜ ≤ (G : Measure ℝ) (Set.Iic 0 ∪ Set.Ioi 1) := measure_mono hsub
    _ ≤ (G : Measure ℝ) (Set.Iic 0) + (G : Measure ℝ) (Set.Ioi 1) := measure_union_le _ _
    _ = 0 := by rw [h0, h2, add_zero]

/-- For one buyer every law on the cube is (trivially) i.i.d. -/
lemma Fall_one_subset_Fiid (μ : Measure (Fin 1 → ℝ)) (hμ : μ ∈ Fall 1) : μ ∈ Fiid 1 := by
  haveI := hμ.1
  have hmeas : Measurable (fun v : Fin 1 → ℝ => v 0) := measurable_pi_apply 0
  let G : ProbabilityMeasure ℝ := ⟨μ.map (fun v => v 0), Measure.isProbabilityMeasure_map hmeas.aemeasurable⟩
  have hpre : ∀ s : Set ℝ, (fun v : Fin 1 → ℝ => v 0) ⁻¹' s = Set.univ.pi (fun _ : Fin 1 => s) := by
    intro s; ext v; simp [Fin.forall_fin_one]
  refine ⟨G, ?_, ?_⟩
  · show (μ.map (fun v => v 0)) (Set.Icc 0 1)ᶜ = 0
    rw [Measure.map_apply hmeas (measurableSet_Icc.compl), Set.preimage_compl, hpre]
    exact hμ.2
  · symm
    apply Measure.pi_eq
    intro s hs
    show μ (Set.univ.pi s) = ∏ i : Fin 1, (μ.map (fun v => v 0)) (s i)
    rw [Fin.prod_univ_one, Measure.map_apply hmeas (hs 0)]
    congr 1
    ext v; simp [Fin.forall_fin_one]

/-- Bounds `0 ≤ Φ*_n(v) ≤ (v - r)/(n r)` on `(r, 1]` from the series form of Proposition A-3. -/
lemma phi_bounds (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (v : ℝ) (hv : v ∈ Set.Ioc r 1) :
    0 ≤ PhiStar n r v ∧ PhiStar n r v ≤ (v - r) / (n * r) := by
  have hS := ((proposition_A_3 n hn).2 r hr hrEq).1 v hv
  have hr0 := hr.1
  have hv0 : 0 < v := lt_trans hr0 hv.1
  set x := (v - r) / v with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith [hv.1]) hv0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hv0]; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact hS.nonneg fun j => by positivity
  · have hgeo : HasSum (fun j : ℕ => (x / n) * x ^ j) ((x / n) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
    have hle := hasSum_le (fun j => ?_) hS hgeo
    · have h1x : 1 - x = r / v := by rw [hx]; field_simp; ring
      calc PhiStar n r v ≤ (x / n) * (1 - x)⁻¹ := hle
        _ = (v - r) / (n * r) := by rw [h1x, hx]; field_simp
    · have hjn : (n : ℝ) ≤ ((j + n : ℕ) : ℝ) := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      have hxj : 0 ≤ x ^ (j + 1) := pow_nonneg hx0 _
      calc 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1) ≤ 1 / (n : ℝ) * x ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hnR hjn) hxj
        _ = (x / n) * x ^ j := by rw [pow_succ]; ring

/-- The common bound on the integrands. -/
lemma integrand_bound (n : ℕ) (hn : 0 < n) (r p z w Φ : ℝ) (hr0 : 0 < r) (hp : p ∈ Set.Ioc r 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) (hΦ0 : 0 ≤ Φ)
    (hΦ1 : Φ ≤ (p - r) / (n * r)) :
    |(((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z + (n : ℝ) * w) * Φ|
      ≤ 3 / r := by
  have hd : 0 < p - r := by linarith [hp.1]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set q := Φ / (p - r) with hq
  have hq0 : 0 ≤ q := div_nonneg hΦ0 hd.le
  have hq1 : q * (n * r) ≤ 1 := by
    rw [hq, div_mul_eq_mul_div, div_le_one hd]
    rw [le_div_iff₀ (by positivity)] at hΦ1
    linarith
  have hΦ : Φ = q * (p - r) := by rw [hq]; field_simp
  have heq : (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z + (n : ℝ) * w) * Φ
      = q * (((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w) := by
    rw [hΦ]; field_simp
  rw [heq, abs_mul, abs_of_nonneg hq0]
  have hp1 := hp.2
  have hbr : |((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w| ≤ 3 * n := by
    rw [abs_le]
    have hr1 : r ≤ 1 := by linarith [hp.1]
    have e1 : 0 ≤ ((n : ℝ) - 1) * r := mul_nonneg (by linarith) hr0.le
    have e2 : ((n : ℝ) - 1) * r ≤ n := by nlinarith
    have e3 : 0 ≤ ((n : ℝ) - 1) * p * z := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hz.1
    have e4 : ((n : ℝ) - 1) * p * z ≤ n := by
      have : ((n : ℝ) - 1) * p ≤ n := by nlinarith
      nlinarith [hz.2, hz.1]
    have e5 : 0 ≤ n * (p - r) * w := mul_nonneg (mul_nonneg (by linarith) hd.le) hw.1
    have e6 : n * (p - r) * w ≤ n := by
      have : (n : ℝ) * (p - r) ≤ n := by nlinarith
      nlinarith [hw.2, hw.1]
    constructor <;> nlinarith
  have hr' : q ≤ 1 / (n * r) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc q * |((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w|
      ≤ (1 / (n * r)) * (3 * n) := mul_le_mul hr' hbr (abs_nonneg _) (by positivity)
    _ = 3 / r := by field_simp

lemma F1_mono {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] : Monotone (F1 μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro u hu
  exact le_trans hu hab

lemma F1k_mono {n : ℕ} (k : ℕ) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] :
    Monotone (F1k k μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro u hu i hi
  exact le_trans (hu i hi) hab

lemma toReal_mem_Icc {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by
    have := prob_le_one (μ := μ) (s := s)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩

/-- Integrability of the integrand `(c₁ - 1 - c₂ z(p) + n w(p)) Φ*(p)` on `[r, 1]`. -/
lemma integrand_ii (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (z w : ℝ → ℝ) (hzm : Measurable z) (hwm : Measurable w)
    (hz : ∀ p ∈ Set.Ioc r 1, z p ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ p ∈ Set.Ioc r 1, w p ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun p => (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z p +
        (n : ℝ) * w p) * PhiStar n r p) volume r 1 := by
  have hr1 : r ≤ 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn
    linarith [hr.2]
  have hPhi : PhiStar n r = fun t => cdfOf ρ t := funext fun t => (hρ t).symm
  have hPm : Measurable (PhiStar n r) := by
    rw [hPhi]
    apply Monotone.measurable
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (Set.Iic_subset_Iic.mpr hab)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr1]
  apply Measure.integrableOn_of_bounded (M := 3 / r) (by simp)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun p hp => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := phi_bounds n hn r hr hrEq p hp
    exact integrand_bound n hn r p (z p) (w p) _ hr.1 hp (hz p hp) (hw p hp) h0 h1

end RAffProp2Red

open RAffProp2Red in
theorem solution (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (G : ProbabilityMeasure ℝ) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    (∀ μ ∈ Faff n, regret (SPA (ρ : Measure ℝ)) μ ≤
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ))) ∧
    (∀ m : Mechanism n, m.IsDSIC →
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) ≤
          regret m (Measure.pi fun _ : Fin n => (G : Measure ℝ))) ∧
    minimaxRegret n (Faff n) = minimaxRegret n (Fiid n) := by
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  set Gn : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => (G : Measure ℝ) with hGn_def
  set S : Mechanism n := SPA (ρ : Measure ℝ) with hS_def
  have hS : S.IsDSIC := SPA_isDSIC n ρ
  have hGn_iid : Gn ∈ Fiid n := ⟨G, G_supp r hr0 hr1 G hG, rfl⟩
  have hGn_aff : Gn ∈ Faff n := Fiid_subset_Faff n hGn_iid
  -- Part 2: the seller's step
  have part2 : ∀ m : Mechanism n, m.IsDSIC → regret S Gn ≤ regret m Gn :=
    step_2_seller n hn r hr hrEq ρ G hρ hG
  -- Part 1: nature's step
  have part1 : ∀ μ ∈ Faff n, regret S μ ≤ regret S Gn := by
    intro μ hμ
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1: every law is i.i.d.
      obtain rfl : n = 1 := by omega
      exact step_1_nature 1 hn r hr hrEq ρ G hρ hG μ (Fall_one_subset_Fiid μ hμ.1.1)
    · haveI : IsProbabilityMeasure μ := hμ.1.1.1
      have hns := nature_step_aff n hn2 r hr hrEq ρ hρ μ hμ
      have hst := regret_Fstar_eq n hn r hr hrEq ρ hρ G hG
      rw [hst]
      refine hns.trans (add_le_add le_rfl ?_)
      have hr1' : r ≤ 1 := hr1.le
      have hzF : ∀ p ∈ Set.Ioc r 1, (1 - r / p) ^ n ∈ Set.Icc (0 : ℝ) 1 ∧
          (1 - r / p) ^ (n - 1) ∈ Set.Icc (0 : ℝ) 1 := by
        intro p hp
        have hp0 : 0 < p := lt_trans hr0 hp.1
        have ha : 0 ≤ 1 - r / p := by
          rw [sub_nonneg, div_le_one hp0]; exact hp.1.le
        have hb : 1 - r / p ≤ 1 := by
          have : 0 ≤ r / p := div_nonneg hr0.le hp0.le
          linarith
        exact ⟨⟨pow_nonneg ha _, pow_le_one₀ ha hb⟩, ⟨pow_nonneg ha _, pow_le_one₀ ha hb⟩⟩
      apply intervalIntegral.integral_mono_on_of_le_Ioo hr1'
      · exact integrand_ii n hn r hr hrEq ρ hρ (F1 μ) (F1k (n - 1) μ)
          (F1_mono μ).measurable (F1k_mono _ μ).measurable
          (fun p _ => toReal_mem_Icc μ _) (fun p _ => toReal_mem_Icc μ _)
      · exact integrand_ii n hn r hr hrEq ρ hρ (fun p => (1 - r / p) ^ n)
          (fun p => (1 - r / p) ^ (n - 1)) (by fun_prop) (by fun_prop)
          (fun p hp => (hzF p hp).1) (fun p hp => (hzF p hp).2)
      · intro p hp
        have hp' : p ∈ Set.Ioc r 1 := ⟨hp.1, hp.2.le⟩
        have hΦ0 := (phi_bounds n hn r hr hrEq p hp').1
        apply mul_le_mul_of_nonneg_right _ hΦ0
        have hz := toReal_mem_Icc μ {u | top u ≤ p}
        have hw := toReal_mem_Icc μ {u : Fin n → ℝ | ∀ i : Fin n, (i : ℕ) < n - 1 → u i ≤ p}
        have hL := lemma_1 n hn2 μ hμ p
        have hFk : F1k (n - 1) μ p ≤ F1 μ p ^ (((n : ℝ) - 1) / (n : ℝ)) := by
          have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
            have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
            linarith
          have hw0 : 0 ≤ F1k (n - 1) μ p := hw.1
          have hz0 : 0 ≤ F1 μ p := hz.1
          calc F1k (n - 1) μ p = (F1k (n - 1) μ p ^ (1 / ((n : ℝ) - 1))) ^ ((n : ℝ) - 1) := by
                rw [← Real.rpow_mul hw0, one_div_mul_cancel hn1.ne', Real.rpow_one]
            _ ≤ (F1 μ p ^ (1 / (n : ℝ))) ^ ((n : ℝ) - 1) :=
                Real.rpow_le_rpow (Real.rpow_nonneg hw0 _) hL hn1.le
            _ = F1 μ p ^ (((n : ℝ) - 1) / (n : ℝ)) := by
                rw [← Real.rpow_mul hz0]; congr 1; ring
        have hpb := pointwise_bound_aff n hn2 r hr0 p hp
        obtain ⟨hgr, hval⟩ := hpb
        have hle := hgr.2 ⟨F1 μ p, hz, rfl⟩
        simp only at hle hval
        rw [hval] at hle
        have hnn : (0 : ℝ) ≤ n := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hFk hnn]
  refine ⟨part1, part2, ?_⟩
  -- Part 3: both minimax values equal `regret S Gn`
  have key : ∀ 𝓕 : Set (Measure (Fin n → ℝ)), Gn ∈ 𝓕 → 𝓕 ⊆ Fall n →
      (∀ μ ∈ 𝓕, regret S μ ≤ regret S Gn) → minimaxRegret n 𝓕 = regret S Gn := by
    intro 𝓕 hG𝓕 h𝓕 hp1
    unfold minimaxRegret
    have hbdd : ∀ m : {m : Mechanism n // m.IsDSIC},
        BddAbove (Set.range fun μ : 𝓕 => regret m.1 (μ : Measure (Fin n → ℝ))) := by
      intro m
      obtain ⟨C, hC⟩ := regret_bdd hn m.1 m.2
      exact ⟨C, by rintro _ ⟨μ, rfl⟩; exact hC μ (h𝓕 μ.2)⟩
    have hsup_ge : ∀ m : {m : Mechanism n // m.IsDSIC},
        regret S Gn ≤ ⨆ μ : 𝓕, regret m.1 (μ : Measure (Fin n → ℝ)) := fun m =>
      (part2 m.1 m.2).trans (le_ciSup (f := fun μ : 𝓕 => regret m.1 (μ : Measure (Fin n → ℝ)))
        (hbdd m) ⟨Gn, hG𝓕⟩)
    apply le_antisymm
    · refine (ciInf_le ⟨regret S Gn, ?_⟩ ⟨S, hS⟩).trans ?_
      · rintro _ ⟨m, rfl⟩; exact hsup_ge m
      · haveI : Nonempty 𝓕 := ⟨⟨Gn, hG𝓕⟩⟩
        exact ciSup_le fun μ => hp1 μ μ.2
    · haveI : Nonempty {m : Mechanism n // m.IsDSIC} := ⟨⟨S, hS⟩⟩
      exact le_ciInf hsup_ge
  rw [key (Faff n) hGn_aff (fun μ hμ => hμ.1.1) part1,
    key (Fiid n) hGn_iid (fun μ hμ => (Fiid_subset_Faff n hμ).1.1)
      (fun μ hμ => part1 μ (Fiid_subset_Faff n hμ))]
