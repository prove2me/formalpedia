-- Prove2me | solution 1 for WangWebsterFlexibility.Threshold.proposition_8
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:26:35.484467+00:00
-- url     : https://prove2.me/submissions/2f487b66-4d1f-4608-9786-7cdbc9439d87

import Definitions.Def_WangWebsterFlexibility_Threshold_Cutoff
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal
open WangWebsterFlexibility.Threshold

noncomputable def s225mbW (k : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)

noncomputable def s225mbMu : Measure ℝ≥0 :=
  Measure.sum (fun k : ℕ => s225mbW k • Measure.dirac ((4 : ℝ≥0) ^ k))

lemma s225mbMu_univ : s225mbMu Set.univ = 1 := by
  unfold s225mbMu
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, s225mbW, pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance s225mbMu_prob : IsProbabilityMeasure s225mbMu := ⟨s225mbMu_univ⟩

noncomputable def s225mbM : Model where
  demand₁ := ⟨s225mbMu, inferInstance⟩
  demand₂ := ⟨Measure.dirac 0, inferInstance⟩
  π₁ := 2
  π₂ := 1
  ρ := 1 / 2

lemma s225mb_tail (N : ℕ) :
    ((2 : ℝ)⁻¹) ^ (N + 1) ≤ s225mbMu.real (Set.Ici ((4 : ℝ≥0) ^ N)) := by
  have h1 : s225mbW N ≤ s225mbMu (Set.Ici ((4 : ℝ≥0) ^ N)) := by
    unfold s225mbMu
    rw [Measure.sum_apply _ measurableSet_Ici]
    refine le_trans ?_ (ENNReal.le_tsum N)
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_Ici.mpr le_rfl), smul_eq_mul,
      mul_one]
  have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
  unfold s225mbW at h2
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  exact h2

lemma s225mb_pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_left _ _

lemma s225mb_rDF0 (M : Model) (v : ℝ) (d : ℝ≥0 × ℝ≥0) (a₁ a₂ : ℝ) :
    revenueDF M v d a₁ a₂ 0 = M.π₁ * min (d.1 : ℝ) a₁ + M.π₂ * min (d.2 : ℝ) a₂ := by
  unfold revenueDF
  have e1 : min (pos ((d.1 : ℝ) - a₁)) 0 = 0 := min_eq_right (s225mb_pos_nonneg _)
  have e2 : pos (0 - pos ((d.1 : ℝ) - a₁)) = 0 := by
    unfold pos; exact max_eq_left (by linarith [le_max_left (0 : ℝ) ((d.1 : ℝ) - a₁)])
  rw [e1, e2, min_eq_right (s225mb_pos_nonneg _)]
  ring

lemma s225mb_rFF0 (M : Model) (v : ℝ) (d : ℝ≥0 × ℝ≥0) (q : ℝ) :
    revenueFF M v d q 0 = M.π₁ * min (d.1 : ℝ) q + M.π₂ * min (d.2 : ℝ) (pos (q - d.1)) := by
  unfold revenueFF
  have e1 : min (pos ((d.1 : ℝ) - q)) 0 = 0 := min_eq_right (s225mb_pos_nonneg _)
  have e2 : pos (0 - pos ((d.1 : ℝ) - q)) = 0 := by
    unfold pos; exact max_eq_left (by linarith [le_max_left (0 : ℝ) ((d.1 : ℝ) - q)])
  rw [e1, e2, min_eq_right (s225mb_pos_nonneg _)]
  ring

/-- Expectation lower bound for bounded continuous f dominating 2 min(d₁, q). -/
lemma s225mb_Ebound (q : ℝ≥0) (f : ℝ≥0 × ℝ≥0 → ℝ) (hf : Continuous f)
    (hlow : ∀ d : ℝ≥0 × ℝ≥0, 2 * min (d.1 : ℝ) q ≤ f d) (C : ℝ)
    (hup : ∀ d, f d ≤ C) :
    2 * (q : ℝ) * s225mbMu.real (Set.Ici q) ≤ s225mbM.expect f := by
  unfold Model.expect
  have hlaw : s225mbM.law = s225mbMu.prod (Measure.dirac 0) := rfl
  have : IsProbabilityMeasure s225mbM.law := by rw [hlaw]; infer_instance
  have hS : MeasurableSet (Set.Ici q ×ˢ (Set.univ : Set ℝ≥0)) :=
    measurableSet_Ici.prod MeasurableSet.univ
  have hint : Integrable f s225mbM.law := by
    refine Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun d => ?_)
    have h1 := hlow d
    have h2 : 0 ≤ 2 * min (d.1 : ℝ) q := by
      have := d.1.coe_nonneg; have := q.coe_nonneg
      exact mul_nonneg (by norm_num) (le_min (by assumption) (by assumption))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact hup d
  have hmono := integral_mono_of_nonneg (μ := s225mbM.law)
    (f := (Set.Ici q ×ˢ (Set.univ : Set ℝ≥0)).indicator (fun _ => 2 * (q : ℝ)))
    (Filter.Eventually.of_forall fun d => by
      simp only [Pi.zero_apply]
      exact Set.indicator_nonneg (fun _ _ => by positivity) d) hint
    (Filter.Eventually.of_forall fun d => by
      by_cases hd : d ∈ Set.Ici q ×ˢ (Set.univ : Set ℝ≥0)
      · rw [Set.indicator_of_mem hd]
        have : (q : ℝ) ≤ d.1 := by exact_mod_cast (Set.mem_prod.mp hd).1
        have := hlow d
        rw [min_eq_right ‹(q : ℝ) ≤ d.1›] at this
        exact this
      · rw [Set.indicator_of_notMem hd]
        have := hlow d
        have h2 : 0 ≤ 2 * min (d.1 : ℝ) q := by
          have := d.1.coe_nonneg; have := q.coe_nonneg
          exact mul_nonneg (by norm_num) (le_min (by assumption) (by assumption))
        linarith)
  rw [integral_indicator_const _ hS, smul_eq_mul] at hmono
  have hreal : s225mbM.law.real (Set.Ici q ×ˢ (Set.univ : Set ℝ≥0)) =
      s225mbMu.real (Set.Ici q) := by
    rw [hlaw, Measure.real, Measure.prod_prod, measure_univ, mul_one]; rfl
  rw [hreal] at hmono
  linarith

lemma s225mb_cont_min (q : ℝ) : Continuous (fun d : ℝ≥0 × ℝ≥0 => min (d.1 : ℝ) q) := by
  fun_prop

lemma s225mb_profits (γ : ℝ) (q : ℝ≥0) :
    (q : ℝ) * s225mbMu.real (Set.Ici q) ≤ profitFF s225mbM 0 γ 0 0 q ∧
    (q : ℝ) * s225mbMu.real (Set.Ici q) ≤ profitDF s225mbM 0 γ 0 0 q 0 := by
  have hz : s225mbM.expect (fun d => revenueDF s225mbM 0 d 0 0 ((0 : ℝ≥0) : ℝ)) = 0 := by
    have : (fun d => revenueDF s225mbM 0 d 0 0 ((0 : ℝ≥0) : ℝ)) = fun _ => 0 := by
      funext d
      rw [NNReal.coe_zero, s225mb_rDF0, min_eq_right d.1.coe_nonneg,
        min_eq_right d.2.coe_nonneg]
      ring
    rw [this]; unfold Model.expect; simp
  have hp1 : s225mbM.π₁ = 2 := rfl
  have hp2 : s225mbM.π₂ = 1 := rfl
  have hρ : s225mbM.ρ = 1 / 2 := rfl
  have hq0 := q.coe_nonneg
  have hDF : 2 * (q : ℝ) * s225mbMu.real (Set.Ici q) ≤
      s225mbM.expect (fun d => revenueDF s225mbM 0 d q ((0 : ℝ≥0) : ℝ) ((0 : ℝ≥0) : ℝ)) := by
    refine s225mb_Ebound q _ ?_ ?_ (2 * q) ?_
    · have : (fun d => revenueDF s225mbM 0 d q ((0 : ℝ≥0) : ℝ) ((0 : ℝ≥0) : ℝ)) =
          fun d : ℝ≥0 × ℝ≥0 => 2 * min (d.1 : ℝ) q + 1 * min (d.2 : ℝ) 0 := by
        funext d; rw [NNReal.coe_zero, s225mb_rDF0, hp1, hp2]
      rw [this]; fun_prop
    · intro d
      rw [NNReal.coe_zero, s225mb_rDF0, hp1, hp2, min_eq_right d.2.coe_nonneg]
      linarith
    · intro d
      rw [NNReal.coe_zero, s225mb_rDF0, hp1, hp2, min_eq_right d.2.coe_nonneg]
      have := min_le_right (d.1 : ℝ) q
      linarith
  have hFF : 2 * (q : ℝ) * s225mbMu.real (Set.Ici q) ≤
      s225mbM.expect (fun d => revenueFF s225mbM 0 d q ((0 : ℝ≥0) : ℝ)) := by
    refine s225mb_Ebound q _ ?_ ?_ (3 * q) ?_
    · have : (fun d => revenueFF s225mbM 0 d q ((0 : ℝ≥0) : ℝ)) =
          fun d : ℝ≥0 × ℝ≥0 => 2 * min (d.1 : ℝ) q + 1 * min (d.2 : ℝ) (max 0 (q - d.1)) := by
        funext d; rw [NNReal.coe_zero, s225mb_rFF0, hp1, hp2]; rfl
      rw [this]; fun_prop
    · intro d
      rw [NNReal.coe_zero, s225mb_rFF0, hp1, hp2]
      have : 0 ≤ min (d.2 : ℝ) (pos (q - d.1)) :=
        le_min d.2.coe_nonneg (s225mb_pos_nonneg _)
      linarith
    · intro d
      rw [NNReal.coe_zero, s225mb_rFF0, hp1, hp2]
      have h1 := min_le_right (d.1 : ℝ) q
      have h2 := min_le_right (d.2 : ℝ) (pos (q - d.1))
      have h3 : pos ((q : ℝ) - d.1) ≤ q := by
        unfold pos; have := d.1.coe_nonneg; exact max_le hq0 (by linarith)
      linarith
  constructor
  · unfold profitFF
    rw [hz, hρ]
    simp only [NNReal.coe_zero, mul_zero, zero_mul, sub_zero, add_zero] at hFF ⊢
    nlinarith [hFF]
  · unfold profitDF
    rw [hρ]
    simp only [NNReal.coe_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      at hz hDF ⊢
    rw [hz]
    nlinarith [hDF]

lemma s225mb_unbounded (R : ℝ) : ∃ q : ℝ≥0, R ≤ (q : ℝ) * s225mbMu.real (Set.Ici q) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R)
  refine ⟨(4 : ℝ≥0) ^ N, ?_⟩
  have ht := s225mb_tail N
  have hpos : (0 : ℝ) ≤ ((4 : ℝ≥0) ^ N : ℝ≥0) := NNReal.coe_nonneg _
  have h1 : ((4 : ℝ≥0) ^ N : ℝ) * ((2 : ℝ)⁻¹) ^ (N + 1) ≤
      ((4 : ℝ≥0) ^ N : ℝ) * s225mbMu.real (Set.Ici ((4 : ℝ≥0) ^ N)) :=
    mul_le_mul_of_nonneg_left ht hpos
  have h2 : ((4 : ℝ≥0) ^ N : ℝ) * ((2 : ℝ)⁻¹) ^ (N + 1) = (2 : ℝ) ^ N / 2 := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ, inv_pow]
    field_simp
    ring
  have h3 : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (Nat.lt_two_pow_self).le
  push_cast at h1 h2 ⊢
  linarith

lemma s225mb_top (X : EReal) (h : ∀ R : ℝ, (R : EReal) ≤ X) : X = ⊤ := by
  induction X using EReal.rec with
  | bot => exact absurd (h 0) (by simp)
  | coe x =>
    have := h (x + 1)
    rw [EReal.coe_le_coe_iff] at this; linarith
  | top => rfl

lemma s225mb_valueFF (γ : ℝ) : valueFF s225mbM 0 γ 0 = ⊤ := by
  apply s225mb_top
  intro R
  obtain ⟨q, hq⟩ := s225mb_unbounded R
  unfold valueFF
  refine le_trans ?_ (le_iSup₂ (f := fun (s : ℝ≥0) (q : ℝ≥0) =>
    (profitFF s225mbM 0 γ 0 s q : EReal)) 0 q)
  exact EReal.coe_le_coe_iff.mpr (hq.trans (s225mb_profits γ q).1)

lemma s225mb_valueDF (γ : ℝ) : valueDF s225mbM 0 γ 0 = ⊤ := by
  apply s225mb_top
  intro R
  obtain ⟨q, hq⟩ := s225mb_unbounded R
  unfold valueDF
  refine le_trans ?_ (le_iSup (fun s : ℝ≥0 => ⨆ (q₁ : ℝ≥0) (q₂ : ℝ≥0),
    (profitDF s225mbM 0 γ 0 s q₁ q₂ : EReal)) 0)
  refine le_trans ?_ (le_iSup₂ (f := fun (q₁ : ℝ≥0) (q₂ : ℝ≥0) =>
    (profitDF s225mbM 0 γ 0 0 q₁ q₂ : EReal)) q 0)
  exact EReal.coe_le_coe_iff.mpr (hq.trans (s225mb_profits γ q).2)

theorem solution : ¬ (∀ (M : Model)
    (hπ : M.π₂ < M.π₁)
    (hρ₀ : 0 < M.ρ) (hρ₁ : M.ρ < 1)
    (v : ℝ) (hv : 0 ≤ v) (hvπ : v < M.π₂),
    ∃ Γ : ℝ → ℝ,
      (∀ c ∈ Set.Icc 0 v, IsThreshold M c v (Γ c) ∧
        ∀ G : ℝ, IsThreshold M c v G → G = Γ c) ∧
      (∀ c ∈ Set.Ioo 0 v, ∃ a : ℝ, a ≤ 0 ∧ HasDerivAt Γ a c) ∧
      (∀ c : ℝ, c = 0 ∨ c = v →
        ∃ a : ℝ, a ≤ 0 ∧ HasDerivWithinAt Γ a (Set.Icc 0 v) c)) := by
  intro h
  obtain ⟨Γ, h1, -, -⟩ :=
    h s225mbM (by show (1 : ℝ) < 2; norm_num) (by show (0 : ℝ) < 1 / 2; norm_num)
      (by show (1 / 2 : ℝ) < 1; norm_num) 0 le_rfl (by show (0 : ℝ) < 1; norm_num)
  obtain ⟨⟨-, -, -, γ, -, -, hlt⟩, -⟩ := h1 0 ⟨le_rfl, le_rfl⟩
  rw [s225mb_valueDF, s225mb_valueFF] at hlt
  exact lt_irrefl _ hlt
