-- Prove2me | solution 1 for SunkCost.SmallBias.optimal_price_eq_max
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:49:08.755209+00:00
-- url     : https://prove2.me/submissions/7dd69edc-d305-451e-81e1-09e8727d67c8

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


/-- The optimal price is `max(p̂_a, p_r)`, with strictly smaller profit elsewhere. -/
lemma scx_opt_strict {P : Params} (hS : P.Standing) {F : StieltjesFunction ℝ}
    (hF : ValuationCDF F) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) {pr : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hc : P.c < pHatA P lam) :
    0 ≤ max (pHatA P lam) pr ∧
    profit P F lam (max (pHatA P lam) pr) = rProfit P F (max (pHatA P lam) pr) ∧
    ∀ q : ℝ, 0 ≤ q → q ≠ max (pHatA P lam) pr →
      profit P F lam q < profit P F lam (max (pHatA P lam) pr) := by
  have hc0 : 0 ≤ P.c := hS.2.2.2.2.2.2
  set A := (1 - P.κ) * P.α with hA
  set pa := pHatA P lam with hpa_def
  have hpaA : pa < A := scx_pHatA_lt hS hlam
  have hRpa : 0 < rProfit P F pa := scx_rProfit_pos hS hF hc hpaA
  have hRpr : 0 < rProfit P F pr := lt_of_lt_of_le hRpa (hpr pa)
  have hprc : P.c < pr := by
    by_contra h
    replace h := not_lt.mp h
    linarith [scx_rProfit_nonpos (P := P) hF h]
  have hprA : pr < A := by
    by_contra h
    replace h := not_lt.mp h
    linarith [scx_rProfit_zero hS hF h]
  have hpr_mem : pr ∈ Set.Icc 0 A := ⟨by linarith, hprA.le⟩
  -- uniqueness of the maximizer of rProfit
  have uniq : ∀ q : ℝ, 0 ≤ q → q ≠ pr → rProfit P F q < rProfit P F pr := by
    intro q hq hne
    rcases le_or_gt q A with hqA | hqA
    · have h := hconc.2 ⟨hq, hqA⟩ hpr_mem hne (by norm_num : (0:ℝ) < 1/2)
        (by norm_num : (0:ℝ) < 1/2) (by norm_num)
      have h2 := hpr ((1/2 : ℝ) • q + (1/2 : ℝ) • pr)
      simp only [smul_eq_mul] at h h2
      linarith
    · rw [scx_rProfit_zero hS hF hqA.le]; exact hRpr
  -- strict decrease to the right of pr
  have decr : ∀ a b : ℝ, pr ≤ a → a < b → a < A → rProfit P F b < rProfit P F a := by
    intro a b hpra hab haA
    rcases le_or_gt b A with hbA | hbA
    · rcases eq_or_lt_of_le hpra with h | h
      · subst h; exact uniq b (by linarith) (ne_of_gt hab)
      · set t := (b - a) / (b - pr) with ht
        have hbpr : 0 < b - pr := by linarith
        have ht0 : 0 < t := div_pos (by linarith) hbpr
        have ht1 : 0 < 1 - t := by
          rw [ht, sub_pos, div_lt_one hbpr]; linarith
        have hcomb : t * pr + (1 - t) * b = a := by
          rw [ht]; field_simp; ring
        have h := hconc.2 hpr_mem ⟨by linarith, hbA⟩ (ne_of_lt (by linarith)) ht0 ht1
          (by ring)
        simp only [smul_eq_mul] at h
        rw [hcomb] at h
        have := hpr b
        nlinarith [mul_nonneg ht0.le (sub_nonneg.2 this)]
    · rw [scx_rProfit_zero hS hF hbA.le]
      exact scx_rProfit_pos hS hF (by linarith) haA
  have hps0 : 0 ≤ max pa pr := le_trans (by linarith) (le_max_left pa pr)
  have hprof : profit P F lam (max pa pr) = rProfit P F (max pa pr) :=
    scx_profit_eq hS hF hlam hlam1 hps0 (le_max_left _ _)
  refine ⟨hps0, hprof, ?_⟩
  intro q hq hne
  rw [hprof]
  have hRps : 0 < rProfit P F (max pa pr) := by
    rcases le_total pr pa with h | h
    · rw [max_eq_left h]; exact hRpa
    · rw [max_eq_right h]; exact hRpr
  rcases lt_or_ge q P.c with hqc | hqc
  · unfold profit
    have := scx_demand_nonneg P F lam q
    nlinarith
  rcases lt_or_ge q pa with hqpa | hqpa
  · rcases le_total pr pa with h | h
    · rw [max_eq_left h]
      have hd := scx_demand_le_pa hS hF hlam hlam1 hq hqpa.le
      have hpos : 0 < 1 - F (v3 P pa) := by
        unfold rProfit at hRpa
        exact pos_of_mul_pos_right hRpa (by linarith)
      unfold profit rProfit
      calc (q - P.c) * demand P F lam q ≤ (q - P.c) * (1 - F (v3 P pa)) :=
            mul_le_mul_of_nonneg_left hd (by linarith)
        _ < (pa - P.c) * (1 - F (v3 P pa)) := mul_lt_mul_of_pos_right (by linarith) hpos
    · rw [max_eq_right h]
      have hd := scx_demand_le_v3 hS hF hlam hlam1 hq
      calc profit P F lam q ≤ rProfit P F q := by
            unfold profit rProfit; exact mul_le_mul_of_nonneg_left hd (by linarith)
        _ < rProfit P F pr := uniq q hq (by intro e; linarith)
  · rw [scx_profit_eq hS hF hlam hlam1 hq hqpa]
    rcases le_total pr pa with h | h
    · rw [max_eq_left h] at hne ⊢
      exact decr pa q h (lt_of_le_of_ne hqpa (Ne.symm hne)) hpaA
    · rw [max_eq_right h] at hne ⊢
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact uniq q hq hne
      · exact decr pr q le_rfl h' hprA

theorem scx_optimal_price_eq_max (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) (pr : ℝ)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hc : P.c < pHatA P lam) :
    ∀ p : ℝ, IsOptimalPrice P F lam p ↔ p = max (pHatA P lam) pr := by
  obtain ⟨h0, -, hlt⟩ := scx_opt_strict hS hF hlam hlam1 hconc hpr hc
  intro p
  constructor
  · rintro ⟨hp0, hpmax⟩
    by_contra hne
    have := hlt p hp0 hne
    have := hpmax _ h0
    linarith
  · rintro rfl
    refine ⟨h0, fun q hq => ?_⟩
    by_cases hq' : q = max (pHatA P lam) pr
    · rw [hq']
    · exact (hlt q hq hq').le

end SunkCost.SmallBias

open SunkCost.SmallBias in
theorem solution (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) (pr : ℝ)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hc : P.c < pHatA P lam) :
    ∀ p : ℝ, IsOptimalPrice P F lam p ↔ p = max (pHatA P lam) pr :=
  scx_optimal_price_eq_max P hS F hF lam hlam hlam1 pr hconc hpr hc
