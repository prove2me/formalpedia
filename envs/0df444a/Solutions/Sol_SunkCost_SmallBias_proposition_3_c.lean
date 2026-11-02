-- Prove2me | solution 1 for SunkCost.SmallBias.proposition_3_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:51:24.458417+00:00
-- url     : https://prove2.me/submissions/f320258d-59e1-453b-84b3-7e92f132e1e1

import Theorems.Thm_SunkCost_SmallBias_optimal_price_eq_max
import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

open MeasureTheory

lemma scx_F_le_one {F : StieltjesFunction ℝ} (hF : ValuationCDF F) (x : ℝ) : F x ≤ 1 := by
  rcases le_total x 1 with h | h
  · calc F x ≤ F 1 := F.mono h
      _ = 1 := hF.2.2.1 1 le_rfl
  · exact (hF.2.2.1 x h).le

lemma scx_F_lt_one {F : StieltjesFunction ℝ} (hF : ValuationCDF F) {x : ℝ} (hx : x < 1) :
    F x < 1 := by
  rcases lt_or_ge x 0 with h | h
  · rw [hF.2.1 x h.le]; norm_num
  · have := hF.2.2.2 ⟨h, hx.le⟩ ⟨zero_le_one, le_rfl⟩ hx
    rwa [hF.2.2.1 1 le_rfl] at this

lemma scx_key {P : Params} (hS : P.Standing) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) :
    lam * ((1 - P.κ) * P.α) < 1 - P.β := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  have hpos : 0 < P.α * (1 - P.κ) := mul_pos hα (by linarith)
  unfold lam1 at hlam1
  rw [lt_div_iff₀ hpos] at hlam1
  linarith [hlam1]

lemma scx_pHatA_lt {P : Params} (hS : P.Standing) {lam : ℝ} (hlam : 0 ≤ lam) :
    pHatA P lam < (1 - P.κ) * P.α := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  unfold pHatA
  have hd : 0 < lam * P.α + P.β := by nlinarith
  rw [div_lt_iff₀ hd]
  nlinarith [mul_pos hα (sub_pos.2 hκβ),
    mul_nonneg (mul_nonneg hα.le (sub_pos.2 hκ1).le) (mul_nonneg hlam hα.le)]

lemma scx_pHatA_anti {P : Params} (hS : P.Standing) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    pHatA P y ≤ pHatA P x := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  unfold pHatA
  have hdx : 0 < x * P.α + P.β := by nlinarith
  have hdy : 0 < y * P.α + P.β := by nlinarith
  rw [div_le_div_iff₀ hdy hdx]
  have hn : 0 ≤ P.κ * (1 - P.β) * P.α := by
    have := mul_nonneg (mul_nonneg hκ.le (sub_nonneg.2 hβ1)) hα.le
    linarith
  nlinarith [mul_nonneg hn (mul_nonneg (sub_nonneg.2 hxy) hα.le)]

/-- Characterization of the buyer set for `0 ≤ λ < λ₁`, `p ≥ 0`. -/
lemma scx_mem_buyers {P : Params} (hS : P.Standing) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (v : ℝ) :
    v ∈ buyers P lam p ↔ v ∈ Set.Icc (0 : ℝ) 1 ∧ v1 P lam p ≤ v ∧ v3 P p < v := by
  have key := scx_key hS hlam hlam1
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  have hb : 0 < P.β := by linarith
  have e1 : v1 P lam p ≤ v ↔ P.κ - lam * p ≤ v * P.β := by
    unfold v1; rw [div_le_iff₀ hb]
  have e3 : v3 P p < v ↔ p < (v - P.κ) * P.α := by
    unfold v3
    rw [← div_lt_iff₀ hα]; constructor <;> intro h <;> linarith
  rw [e1, e3]
  unfold buyers
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, hu⟩
    refine ⟨hv, ?_⟩
    unfold utility UsesLow UsesHigh at hu
    split_ifs at hu with hL hH
    · exfalso
      have hv1 := hv.2
      have hplt : p < (1 - P.κ) * P.α := by nlinarith
      nlinarith [mul_nonneg hlam (sub_nonneg.2 hplt.le)]
    · constructor <;> nlinarith
    · exfalso; linarith
    · exfalso; linarith
  · rintro ⟨hv, h1, h3⟩
    refine ⟨hv, ?_⟩
    have hplt : p < (1 - P.κ) * P.α := by nlinarith [hv.2]
    have hL : UsesLow P lam p v := by unfold UsesLow; linarith
    have hH : ¬ UsesHigh P lam p v := by
      unfold UsesHigh
      have : lam * p ≤ lam * ((1 - P.κ) * P.α) := mul_le_mul_of_nonneg_left hplt.le hlam
      nlinarith [hv.2]
    unfold utility
    rw [if_pos hL, if_neg hH]
    nlinarith

lemma scx_v1_le_v3 {P : Params} (hS : P.Standing) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hpa : pHatA P lam ≤ p) : v1 P lam p ≤ v3 P p := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  have hb : 0 < P.β := by linarith
  have hd : 0 < lam * P.α + P.β := by nlinarith
  unfold pHatA at hpa
  rw [div_le_iff₀ hd] at hpa
  unfold v1 v3
  have : p / P.α + P.κ = (p + P.α * P.κ) / P.α := by field_simp
  rw [this, div_le_div_iff₀ hb hα]
  nlinarith [hpa]

lemma scx_v3_pos {P : Params} (hS : P.Standing) {p : ℝ} (hp : 0 ≤ p) : 0 < v3 P p := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  unfold v3
  have := div_nonneg hp hα.le
  linarith

lemma scx_buyers_eq {P : Params} (hS : P.Standing) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (hpa : pHatA P lam ≤ p) :
    buyers P lam p = Set.Ioc (v3 P p) 1 := by
  ext v
  rw [scx_mem_buyers hS hlam hlam1 hp]
  have h13 := scx_v1_le_v3 hS hlam hpa
  have h3 := scx_v3_pos hS hp
  constructor
  · rintro ⟨⟨_, h1⟩, _, hv3⟩
    exact ⟨hv3, h1⟩
  · rintro ⟨hv3, h1⟩
    exact ⟨⟨by linarith, h1⟩, by linarith, hv3⟩

lemma scx_measure_Ioc_real {F : StieltjesFunction ℝ} (hF : ValuationCDF F) (a : ℝ) :
    (F.measure (Set.Ioc a 1)).toReal = 1 - F a := by
  rw [StieltjesFunction.measure_Ioc, hF.2.2.1 1 le_rfl,
    ENNReal.toReal_ofReal (by linarith [scx_F_le_one hF a])]

lemma scx_demand_eq {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (hpa : pHatA P lam ≤ p) :
    demand P F lam p = 1 - F (v3 P p) := by
  unfold demand
  rw [scx_buyers_eq hS hlam hlam1 hp hpa, scx_measure_Ioc_real hF]

lemma scx_profit_eq {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (hpa : pHatA P lam ≤ p) :
    profit P F lam p = rProfit P F p := by
  unfold profit rProfit
  rw [scx_demand_eq hS hF hlam hlam1 hp hpa]

lemma scx_demand_le_v3 {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) :
    demand P F lam p ≤ 1 - F (v3 P p) := by
  unfold demand
  rw [← scx_measure_Ioc_real hF]
  apply ENNReal.toReal_mono
  · rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_ne_top
  · apply measure_mono
    intro v hv
    rw [scx_mem_buyers hS hlam hlam1 hp] at hv
    exact ⟨hv.2.2, hv.1.2⟩

lemma scx_v1_pHatA {P : Params} (hS : P.Standing) {lam : ℝ} (hlam : 0 ≤ lam) :
    v1 P lam (pHatA P lam) = v3 P (pHatA P lam) := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  have hb : 0 < P.β := by linarith
  have hd : 0 < lam * P.α + P.β := by nlinarith
  unfold v1 v3 pHatA
  field_simp
  ring

lemma scx_demand_le_pa {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (hpa : p ≤ pHatA P lam) :
    demand P F lam p ≤ 1 - F (v3 P (pHatA P lam)) := by
  have hb : 0 < P.β := by linarith [hS.2.2.2.2.1, hS.2.2.1]
  have hle : v3 P (pHatA P lam) ≤ v1 P lam p := by
    rw [← scx_v1_pHatA hS hlam]
    unfold v1
    apply div_le_div_of_nonneg_right _ hb.le
    nlinarith [mul_le_mul_of_nonneg_left hpa hlam]
  have hmeas : (F.measure (Set.Icc (v3 P (pHatA P lam)) 1)).toReal
      = 1 - F (v3 P (pHatA P lam)) := by
    rw [StieltjesFunction.measure_Icc, hF.2.2.1 1 le_rfl,
      (hF.1.continuousWithinAt).leftLim_eq,
      ENNReal.toReal_ofReal (by linarith [scx_F_le_one hF (v3 P (pHatA P lam))])]
  unfold demand
  rw [← hmeas]
  apply ENNReal.toReal_mono
  · rw [StieltjesFunction.measure_Icc]; exact ENNReal.ofReal_ne_top
  · apply measure_mono
    intro v hv
    rw [scx_mem_buyers hS hlam hlam1 hp] at hv
    exact ⟨le_trans hle hv.2.1, hv.1.2⟩

lemma scx_demand_nonneg (P : Params) (F : StieltjesFunction ℝ) (lam p : ℝ) :
    0 ≤ demand P F lam p := ENNReal.toReal_nonneg

lemma scx_rProfit_pos {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {q : ℝ} (hcq : P.c < q) (hqA : q < (1 - P.κ) * P.α) :
    0 < rProfit P F q := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  unfold rProfit
  apply mul_pos (by linarith)
  have : v3 P q < 1 := by
    unfold v3
    have : q / P.α < 1 - P.κ := by rw [div_lt_iff₀ hα]; linarith
    linarith
  linarith [scx_F_lt_one hF this]

lemma scx_rProfit_zero {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {q : ℝ} (hqA : (1 - P.κ) * P.α ≤ q) :
    rProfit P F q = 0 := by
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  unfold rProfit
  have : 1 ≤ v3 P q := by
    unfold v3
    have : 1 - P.κ ≤ q / P.α := by rw [le_div_iff₀ hα]; linarith
    linarith
  rw [hF.2.2.1 _ this]; ring

lemma scx_rProfit_nonpos {P : Params} {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {q : ℝ} (hq : q ≤ P.c) :
    rProfit P F q ≤ 0 := by
  unfold rProfit
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [scx_F_le_one hF (v3 P q)])


lemma scx_cw_eq {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (hpa : pHatA P lam ≤ p) (hpA : p < (1 - P.κ) * P.α) :
    consumerWelfare P F lam p = ∫ v in Set.Ioc (v3 P p) 1, (P.α * (v - P.κ) - p) ∂F.measure := by
  have key := scx_key hS hlam hlam1
  unfold consumerWelfare
  rw [scx_buyers_eq hS hlam hlam1 hp hpa]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  have hmem : v ∈ buyers P lam p := by rw [scx_buyers_eq hS hlam hlam1 hp hpa]; exact hv
  rw [scx_mem_buyers hS hlam hlam1 hp] at hmem
  obtain ⟨⟨_, hv1⟩, h1, _⟩ := hmem
  obtain ⟨hα, hα1, hκ, hκ1, hκβ, hβ1, hc0⟩ := hS
  have hb : 0 < P.β := by linarith
  have hL : UsesLow P lam p v := by
    unfold v1 at h1; rw [div_le_iff₀ hb] at h1; unfold UsesLow; linarith
  have hH : ¬ UsesHigh P lam p v := by
    unfold UsesHigh
    have : lam * p ≤ lam * ((1 - P.κ) * P.α) := mul_le_mul_of_nonneg_left hpA.le hlam
    nlinarith
  unfold utility
  rw [if_pos hL, if_neg hH]
  ring

lemma scx_sw_eq {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {lam p : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < lam1 P) (hp : 0 ≤ p) (hpa : pHatA P lam ≤ p) (hpA : p < (1 - P.κ) * P.α) :
    socialWelfare P F lam p = ∫ v in Set.Ioc (v3 P p) 1, (P.α * (v - P.κ) - P.c) ∂F.measure := by
  unfold socialWelfare
  rw [scx_cw_eq hS hlam hlam1 hp hpa hpA]
  have hprof : profit P F lam p = ∫ _v in Set.Ioc (v3 P p) 1, (p - P.c) ∂F.measure := by
    rw [setIntegral_const, smul_eq_mul]
    unfold profit demand
    rw [scx_buyers_eq hS hlam hlam1 hp hpa, mul_comm]
    rfl
  rw [hprof, ← integral_add]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro v _
    ring
  · exact Continuous.integrableOn_Ioc (by fun_prop)
  · exact Continuous.integrableOn_Ioc (by fun_prop)

lemma scx_c_lt_pHatA {P : Params} (hS : P.Standing)
    (hc : ∀ l ∈ Set.Ioo 0 (lam1 P), P.c < pHatA P l) {x : ℝ} (hx : x ∈ Set.Ico 0 (lam1 P)) :
    P.c < pHatA P x := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h
    have hl1 : 0 < lam1 P := hx.2
    have := hc (lam1 P / 2) ⟨by linarith, by linarith⟩
    have := scx_pHatA_anti hS (le_refl 0) (by linarith : (0:ℝ) ≤ lam1 P / 2)
    linarith
  · exact hc x ⟨h, hx.2⟩

end SunkCost.SmallBias

open SunkCost.SmallBias MeasureTheory in
theorem solution (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (pr : ℝ)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hpr_lt : pr < P.κ * P.α * (1 - P.β) / P.β)
    (hc : ∀ l ∈ Set.Ioo 0 (lam1 P), P.c < pHatA P l)
    (l l' : ℝ) (hl : l ∈ Set.Ico 0 (lam1 P)) (hl' : l' ∈ Set.Ico 0 (lam1 P)) (hll' : l ≤ l')
    (p p' : ℝ) (hp : IsOptimalPrice P F l p) (hp' : IsOptimalPrice P F l' p') :
    profit P F l p ≤ profit P F l' p' ∧
    consumerWelfare P F l p ≤ consumerWelfare P F l' p' ∧
    socialWelfare P F l p ≤ socialWelfare P F l' p' := by
  have hcl := scx_c_lt_pHatA hS hc hl
  have hcl' := scx_c_lt_pHatA hS hc hl'
  have hpeq := (optimal_price_eq_max P hS F hF l hl.1 hl.2 pr hconc hpr hcl p).1 hp
  have hpeq' := (optimal_price_eq_max P hS F hF l' hl'.1 hl'.2 pr hconc hpr hcl' p').1 hp'
  have hanti := scx_pHatA_anti hS hl.1 hll'
  have hpaA := scx_pHatA_lt hS hl.1
  have hpaA' := scx_pHatA_lt hS hl'.1
  have hRpa : 0 < rProfit P F (pHatA P l) := scx_rProfit_pos hS hF hcl hpaA
  have hRpr : 0 < rProfit P F pr := lt_of_lt_of_le hRpa (hpr _)
  have hprc : P.c < pr := by
    by_contra h
    replace h := not_lt.mp h
    linarith [scx_rProfit_nonpos (P := P) hF h]
  have hprA : pr < (1 - P.κ) * P.α := by
    by_contra h
    replace h := not_lt.mp h
    linarith [scx_rProfit_zero hS hF h]
  have hc0 : 0 ≤ P.c := hS.2.2.2.2.2.2
  have hα : 0 < P.α := hS.1
  -- facts about p and p'
  have hp0 : 0 ≤ p := hp.1
  have hp'0 : 0 ≤ p' := hp'.1
  have hpa_p : pHatA P l ≤ p := hpeq ▸ le_max_left _ _
  have hpa_p' : pHatA P l' ≤ p' := hpeq' ▸ le_max_left _ _
  have hpr_p' : pr ≤ p' := hpeq' ▸ le_max_right _ _
  have hpA : p < (1 - P.κ) * P.α := hpeq ▸ max_lt hpaA hprA
  have hp'A : p' < (1 - P.κ) * P.α := hpeq' ▸ max_lt hpaA' hprA
  have hp'p : p' ≤ p := by
    rw [hpeq, hpeq']; exact max_le_max hanti le_rfl
  have hv3 : v3 P p' ≤ v3 P p := by
    unfold v3; have := div_le_div_of_nonneg_right hp'p hα.le; linarith
  have hsub : Set.Ioc (v3 P p) 1 ⊆ Set.Ioc (v3 P p') 1 := Set.Ioc_subset_Ioc_left hv3
  have hpos' : ∀ v ∈ Set.Ioc (v3 P p') 1, p' ≤ P.α * (v - P.κ) := by
    intro v hv
    have h := hv.1
    unfold v3 at h
    have : p' / P.α < v - P.κ := by linarith
    rw [div_lt_iff₀ hα] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- profit
    rw [scx_profit_eq hS hF hl.1 hl.2 hp0 hpa_p]
    rw [← scx_profit_eq hS hF hl'.1 hl'.2 hp0 (le_trans hanti hpa_p)]
    exact hp'.2 p hp0
  · -- consumer welfare
    rw [scx_cw_eq hS hl.1 hl.2 hp0 hpa_p hpA, scx_cw_eq hS hl'.1 hl'.2 hp'0 hpa_p' hp'A]
    calc ∫ v in Set.Ioc (v3 P p) 1, (P.α * (v - P.κ) - p) ∂F.measure
        ≤ ∫ v in Set.Ioc (v3 P p) 1, (P.α * (v - P.κ) - p') ∂F.measure := by
          apply setIntegral_mono_on (Continuous.integrableOn_Ioc (by fun_prop))
            (Continuous.integrableOn_Ioc (by fun_prop)) measurableSet_Ioc
          intro v _; linarith
      _ ≤ ∫ v in Set.Ioc (v3 P p') 1, (P.α * (v - P.κ) - p') ∂F.measure := by
          apply setIntegral_mono_set (Continuous.integrableOn_Ioc (by fun_prop))
          · apply ae_restrict_of_forall_mem measurableSet_Ioc
            intro v hv
            have := hpos' v hv
            simp only [Pi.zero_apply]
            linarith
          · exact hsub.eventuallyLE
  · -- social welfare
    rw [scx_sw_eq hS hF hl.1 hl.2 hp0 hpa_p hpA, scx_sw_eq hS hF hl'.1 hl'.2 hp'0 hpa_p' hp'A]
    apply setIntegral_mono_set (Continuous.integrableOn_Ioc (by fun_prop))
    · apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro v hv
      have := hpos' v hv
      simp only [Pi.zero_apply]
      linarith
    · exact hsub.eventuallyLE
