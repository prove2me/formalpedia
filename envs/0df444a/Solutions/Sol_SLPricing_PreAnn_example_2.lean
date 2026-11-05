-- Prove2me | solution 1 for SLPricing.PreAnn.example_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:41:31.461069+00:00
-- url     : https://prove2.me/submissions/05bb7db7-cfd5-42fd-abe6-c6f8c6ad3f45

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLEx2
open SLPricing.PreAnn

/-- Late mass when `[θ, 1]` bought early: `max (θ − max 0 (p − q)) 0`. -/
noncomputable def L (θ p q : ℝ) : ℝ := max (θ - max 0 (p - q)) 0

lemma late_eq (θ : ℝ) (hx : θ ∈ Icc (0 : ℝ) 1) (p q : ℝ) :
    lateMass (Icc θ 1) p q = L θ p q := by
  unfold lateMass L
  have hset : {x ∈ Icc (0 : ℝ) 1 \ Icc θ 1 | p ≤ x + q} = Ico (max 0 (p - q)) θ := by
    ext x
    simp only [mem_ofPred_eq, mem_diff, mem_Icc, mem_Ico, max_le_iff, not_and, not_le]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
      refine ⟨⟨h0, by linarith⟩, ?_⟩
      by_contra h
      push_neg at h
      exact absurd (h2 h) (not_lt.mpr h1)
    · rintro ⟨⟨h0, h3⟩, h4⟩
      exact ⟨⟨⟨h0, by linarith [hx.2]⟩, fun h => absurd h (not_le.mpr h4)⟩, by linarith⟩
  rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal']

lemma L_nonneg (θ p q : ℝ) : 0 ≤ L θ p q := le_max_right _ _

lemma L_le (θ p q : ℝ) (h : 0 ≤ θ) : L θ p q ≤ θ := by
  unfold L
  apply max_le _ h
  linarith [le_max_left 0 (p - q)]

lemma measurable_L (θ p : ℝ) : Measurable (fun q => L θ p q) := by
  unfold L; fun_prop

lemma integrable_L (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ p : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun q => L θ p q) μ := by
  refine Integrable.mono' (integrable_const θ) (measurable_L θ p).aestronglyMeasurable
    (ae_of_all _ ?_)
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (L_nonneg _ _ _)]
  exact L_le θ p q hθ

/-- Pointwise symmetrisation bound. -/
lemma L_symm (θ p R q : ℝ) (h1 : θ / 2 ≤ p) (h2 : p ≤ θ) (hR : p ≤ R) :
    2 * (θ - p) + (2 * p - θ) * ({q : ℝ | R < |q|}.indicator 1 q) ≤ L θ p q + L θ p (-q) := by
  unfold L
  by_cases hq : q ∈ {q : ℝ | R < |q|}
  · rw [indicator_of_mem hq]
    simp only [mem_ofPred_eq] at hq
    simp only [Pi.one_apply, mul_one]
    rw [abs_eq_max_neg] at hq
    simp only [max_def] at hq ⊢
    split_ifs at hq ⊢ <;> linarith
  · rw [indicator_of_notMem hq]
    simp only [mul_zero, add_zero]
    simp only [max_def]
    split_ifs <;> linarith

/-- The real inequality behind the no-SL bound at `δc = 0`. -/
lemma real_bound (θ p₂ c : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (θ - c) * (1 - θ) + (p₂ - c) * max (θ - max 0 p₂) 0 ≤ (1 - c) ^ 2 / 3 := by
  rcases le_total 0 p₂ with h | h
  · rw [max_eq_right h]
    rcases le_total (θ - p₂) 0 with h' | h'
    · rw [max_eq_right h']
      nlinarith [sq_nonneg (3 * (θ - c) - 2 * (1 - c)), sq_nonneg (2 * θ - 1 - c)]
    · rw [max_eq_left h']
      nlinarith [sq_nonneg (3 * (θ - c) - 2 * (1 - c)), sq_nonneg (θ + c - 2 * p₂)]
  · rw [max_eq_left h]
    have : (p₂ - c) * max (θ - 0) 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_max_right _ _)
    nlinarith [sq_nonneg (2 * θ - 1 - c)]

lemma prePost_noSL (P : Params) (m : ℝ) : prePost P.noSL m = Measure.dirac 0 := by
  simp [prePost, preVar, Params.noSL, gaussianReal_zero_var]

/-- Every pre-announced equilibrium profit without SL at `δc = 0` is at most `(1 − c)²/3`. -/
lemma noSL_bound (P : Params) (hP : P.Standing) (hδ : P.δc = 0) (p₁ p₂ : ℝ) (B : Set ℝ)
    (hB : IsPreEq P.noSL p₁ p₂ B) : preProfit P.noSL p₁ p₂ B ≤ (1 - P.c) ^ 2 / 3 := by
  obtain ⟨hBm, hBsub, hbuy, hdel⟩ := hB
  have hδ' : P.noSL.δc = 0 := hδ
  have hbuy' : ∀ x ∈ B, p₁ ≤ x := fun x hx => by linarith [(hbuy x hx).1]
  have hdel' : ∀ x ∈ Icc (0 : ℝ) 1 \ B, x ≤ p₁ := fun x hx => by
    have := hdel x hx
    unfold DelaysPre at this
    rw [hδ', zero_mul] at this
    linarith
  set θ := max 0 (min p₁ 1) with hθ
  have hθ0 : 0 ≤ θ := le_max_left _ _
  have hθ1 : θ ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hsub1 : B ⊆ Icc θ 1 := fun x hx =>
    ⟨max_le (hBsub hx).1 (le_trans (min_le_left _ _) (hbuy' x hx)), (hBsub hx).2⟩
  have hsub2 : Ioc θ 1 ⊆ B := by
    intro x hx
    by_contra hxB
    have hx0 : 0 ≤ x := le_trans hθ0 hx.1.le
    have := hdel' x ⟨⟨hx0, hx.2⟩, hxB⟩
    have h1 : min p₁ 1 < x := lt_of_le_of_lt (le_max_right _ _) hx.1
    rcases le_total p₁ 1 with h | h
    · rw [min_eq_left h] at h1; linarith
    · rw [min_eq_right h] at h1; linarith [hx.2]
  have hmass : mass B = 1 - θ := by
    unfold mass
    have : volume B = ENNReal.ofReal (1 - θ) := by
      apply le_antisymm
      · exact (measure_mono hsub1).trans_eq Real.volume_Icc
      · rw [← Real.volume_Ioc]; exact measure_mono hsub2
    rw [this, ENNReal.toReal_ofReal (by linarith)]
  have hlate : lateMass B p₂ 0 = max (θ - max 0 p₂) 0 := by
    unfold lateMass
    set S := {x ∈ Icc (0 : ℝ) 1 \ B | p₂ ≤ x + 0}
    have hS1 : S ⊆ Icc (max 0 p₂) θ := by
      rintro x ⟨⟨hx01, hxB⟩, hx⟩
      refine ⟨max_le hx01.1 (by linarith), ?_⟩
      by_contra h
      push_neg at h
      exact hxB (hsub2 ⟨h, hx01.2⟩)
    have hS2 : Ico (max 0 p₂) θ ⊆ S := by
      rintro x ⟨hx1, hx2⟩
      have h0 : 0 ≤ x := le_trans (le_max_left _ _) hx1
      refine ⟨⟨⟨h0, by linarith⟩, fun hxB => ?_⟩, by linarith [le_max_right 0 p₂]⟩
      linarith [(hsub1 hxB).1]
    have : volume S = ENNReal.ofReal (θ - max 0 p₂) := by
      apply le_antisymm
      · exact (measure_mono hS1).trans_eq Real.volume_Icc
      · rw [← Real.volume_Ico]; exact measure_mono hS2
    rw [this, ENNReal.toReal_ofReal']
  unfold preProfit
  rw [prePost_noSL, integral_dirac, hmass, hlate]
  have hc : P.noSL.c = P.c := rfl
  rw [hc]
  have hp1 : (p₁ - P.c) * (1 - θ) ≤ (θ - P.c) * (1 - θ) := by
    rcases le_total p₁ 1 with h | h
    · apply mul_le_mul_of_nonneg_right _ (by linarith)
      have : p₁ ≤ θ := by rw [hθ, min_eq_left h]; exact le_max_right _ _
      linarith
    · have : θ = 1 := by rw [hθ, min_eq_right h]; exact max_eq_right zero_le_one
      rw [this]; simp
  have := real_bound θ p₂ P.c hθ0 hθ1 hP.c_nonneg hP.c_lt_one
  linarith

end SLEx2

open SLPricing.PreAnn SLEx2

theorem solution (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (hδ : P.δc = 0) :
    preValue P.noSL < preValue P := by
  set w := 1 - P.c with hw
  have hw0 : 0 < w := by linarith [hP.c_lt_one]
  -- upper bound without SL
  have hup : preValue P.noSL ≤ ((w ^ 2 / 3 : ℝ) : EReal) := by
    apply iSup_le
    rintro ⟨⟨p₁, p₂, B⟩, hB⟩
    rw [EReal.coe_le_coe_iff]
    exact noSL_bound P hP hδ p₁ p₂ B hB
  -- the plan with SL
  set θ := (2 + P.c) / 3 with hθ
  have hθ0 : 0 < θ := by linarith [hP.c_nonneg]
  have hθ1 : θ < 1 := by linarith [hP.c_lt_one]
  have hθI : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ0.le, hθ1.le⟩
  set μ := prePost P (1 - θ) with hμ
  have hμ' : μ = gaussianReal 0 (preVar P (1 - θ)) := rfl
  haveI : IsProbabilityMeasure μ := by rw [hμ']; infer_instance
  set S := {q : ℝ | 1 < |q|} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  have hv : preVar P (1 - θ) ≠ 0 := by
    unfold preVar
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    have h1 : 0 < (1 - θ) * P.γ := mul_pos (by linarith) hγ
    have := pow_pos hP.σp_pos 2
    positivity
  set m0 := μ.real S with hm0
  have hm0pos : 0 < m0 := by
    have hvol : volume S ≠ 0 := by
      have : Ioi (1 : ℝ) ⊆ S := fun x hx => by
        simp only [hS, mem_ofPred_eq]; rw [abs_of_pos (by linarith [mem_Ioi.1 hx])]; exact hx
      intro h
      have := measure_mono_null this h
      rw [Real.volume_Ioi] at this
      exact ENNReal.top_ne_zero this
    have hac : volume ≪ μ := by rw [hμ']; exact gaussianReal_absolutelyContinuous' 0 hv
    have hμS : μ S ≠ 0 := fun h => hvol (hac h)
    rw [hm0, measureReal_def]
    exact ENNReal.toReal_pos hμS (measure_ne_top μ S)
  set t := min (w / 6) (w * m0 / 6) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by positivity)
  have ht1 : t ≤ w / 6 := min_le_left _ _
  have ht2 : t ≤ w * m0 / 6 := min_le_right _ _
  set p₂ := (1 + 2 * P.c) / 3 + t with hp₂
  -- equilibrium
  have hEq : IsPreEq P θ p₂ (Icc θ 1) := by
    refine ⟨measurableSet_Icc, fun x hx => ⟨le_trans hθ0.le hx.1, hx.2⟩, ?_, ?_⟩
    · intro x hx
      refine ⟨by linarith [hx.1], ?_⟩
      rw [hδ, zero_mul]; linarith [hx.1]
    · intro x hx
      unfold DelaysPre
      rw [hδ, zero_mul]
      have : x < θ := by
        by_contra h; push_neg at h; exact hx.2 ⟨h, hx.1.2⟩
      linarith
  have hmass : mass (Icc θ 1) = 1 - θ := by
    unfold mass; rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  -- symmetrisation of the integral
  have hI : 2 * (θ - p₂) + (2 * p₂ - θ) * m0 ≤ 2 * ∫ q, L θ p₂ q ∂μ := by
    have hneg : ∫ q, L θ p₂ (-q) ∂μ = ∫ q, L θ p₂ q ∂μ := by
      have hmap : μ.map (fun x => -x) = μ := by
        rw [hμ', gaussianReal_map_neg, neg_zero]
      conv_rhs => rw [← hmap]
      rw [integral_map measurable_neg.aemeasurable
        (measurable_L θ p₂).aestronglyMeasurable]
    have hiL := integrable_L μ θ p₂ hθ0.le
    have hiL' : Integrable (fun q => L θ p₂ (-q)) μ := by
      refine Integrable.mono' (integrable_const θ)
        ((measurable_L θ p₂).comp measurable_neg).aestronglyMeasurable (ae_of_all _ ?_)
      intro q
      rw [Real.norm_eq_abs, abs_of_nonneg (L_nonneg _ _ _)]
      exact L_le θ p₂ _ hθ0.le
    have hind : Integrable (fun q => 2 * (θ - p₂) + (2 * p₂ - θ) * S.indicator 1 q) μ :=
      (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hSm).const_mul _)
    have hmono := integral_mono hind (hiL.add hiL') (fun q =>
      L_symm θ p₂ 1 q (by rw [hp₂, hθ]; linarith [hP.c_nonneg])
        (by rw [hp₂, hθ]; linarith) (by rw [hp₂]; linarith))
    have hl : ∫ q, (2 * (θ - p₂) + (2 * p₂ - θ) * S.indicator 1 q) ∂μ
        = 2 * (θ - p₂) + (2 * p₂ - θ) * m0 := by
      have hi2 : Integrable (fun q => (2 * p₂ - θ) * S.indicator 1 q) μ :=
        ((integrable_const (1 : ℝ)).indicator hSm).const_mul _
      rw [integral_add (integrable_const _) hi2, integral_const,
        integral_const_mul (2 * p₂ - θ), integral_indicator_one hSm]
      simp [hm0]
    have hr : ∫ q, ((fun q => L θ p₂ q) + fun q => L θ p₂ (-q)) q ∂μ
        = 2 * ∫ q, L θ p₂ q ∂μ := by
      rw [integral_add' hiL hiL', hneg]; ring
    rw [hl, hr] at hmono
    exact hmono
  have hprof : preProfit P θ p₂ (Icc θ 1) =
      (θ - P.c) * (1 - θ) + (p₂ - P.c) * ∫ q, L θ p₂ q ∂μ := by
    unfold preProfit
    rw [hmass]
    simp only [late_eq θ hθI]
    rfl
  have hlow : w ^ 2 / 3 < preProfit P θ p₂ (Icc θ 1) := by
    rw [hprof]
    have hpc : 0 ≤ p₂ - P.c := by rw [hp₂]; linarith
    have h2 := mul_le_mul_of_nonneg_left hI hpc
    have e1 : θ - P.c = 2 * w / 3 := by rw [hθ, hw]; ring
    have e2 : 1 - θ = w / 3 := by rw [hθ, hw]; ring
    have e3 : p₂ - P.c = w / 3 + t := by rw [hp₂, hw]; ring
    have e4 : θ - p₂ = w / 3 - t := by rw [hp₂, hθ, hw]; ring
    have e5 : 2 * p₂ - θ = P.c + 2 * t := by rw [hp₂, hθ]; ring
    rw [e1, e2]
    rw [e3, e4, e5] at h2
    rw [e3]
    have hm1 : 0 ≤ P.c * m0 := mul_nonneg hP.c_nonneg hm0pos.le
    have key : t * t < w / 3 * (t * m0) := by
      have : t < w * m0 / 3 := by linarith
      calc t * t < (w * m0 / 3) * t := by nlinarith
        _ = w / 3 * (t * m0) := by ring
    nlinarith [mul_nonneg ht0.le hm1, mul_nonneg ht0.le (mul_nonneg ht0.le hm0pos.le)]
  have hge : ((preProfit P θ p₂ (Icc θ 1) : ℝ) : EReal) ≤ preValue P :=
    le_iSup (fun o : {o : ℝ × ℝ × Set ℝ // IsPreEq P o.1 o.2.1 o.2.2} =>
      ((preProfit P o.1.1 o.1.2.1 o.1.2.2 : ℝ) : EReal)) ⟨(θ, p₂, Icc θ 1), hEq⟩
  calc preValue P.noSL ≤ ((w ^ 2 / 3 : ℝ) : EReal) := hup
    _ < ((preProfit P θ p₂ (Icc θ 1) : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 hlow
    _ ≤ preValue P := hge
