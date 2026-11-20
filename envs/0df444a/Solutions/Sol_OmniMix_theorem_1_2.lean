-- Prove2me | solution 1 for OmniMix.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T04:04:41.172644+00:00
-- url     : https://prove2.me/submissions/dfe1f7a4-ddbd-43d6-9d52-ba1342207078

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_regret

universe u

namespace OmniMix_Theorem12_Proof

open OmniMix MeasureTheory
open scoped ENNReal unitInterval

/-! ### Section 1: Finite Forecast Distributions and Basic EReal Helpers -/

noncomputable def FinDist.dirac (q : unitInterval) : FinDist where
  wt := Finsupp.single q 1
  nonneg p := by
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  sum_one := by simp

lemma FinDist.expect_dirac (q : unitInterval) (g : unitInterval → EReal) :
    (FinDist.dirac q).expect g = g q := by
  unfold FinDist.expect FinDist.dirac
  rw [Finsupp.support_single_ne_zero q one_ne_zero]
  simp

lemma FinDist.mem_support_dirac {q p : unitInterval}
    (hp : p ∈ (FinDist.dirac q).wt.support) : p = q := by
  exact Finset.mem_singleton.mp (Finsupp.support_single_subset hp)

lemma FinDist.sum_dirac_mul (q : unitInterval) (f : unitInterval → ℝ) :
    (∑ p ∈ (FinDist.dirac q).wt.support, (FinDist.dirac q).wt p * f p) = f q := by
  change (Finsupp.single q (1 : ℝ)).sum (fun p w => w * f p) = f q
  simp

noncomputable def FinDist.pair (p₁ p₂ : unitInterval) (w₁ w₂ : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hsum : w₁ + w₂ = 1) : FinDist where
  wt := Finsupp.single p₁ w₁ + Finsupp.single p₂ w₂
  nonneg p := by
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    have h1 : 0 ≤ (if p₁ = p then w₁ else 0) := by split_ifs <;> linarith
    have h2 : 0 ≤ (if p₂ = p then w₂ else 0) := by split_ifs <;> linarith
    linarith
  sum_one := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp [hsum]

lemma FinDist.mem_support_pair {p₁ p₂ : unitInterval} {w₁ w₂ : ℝ}
    {hw₁ : 0 ≤ w₁} {hw₂ : 0 ≤ w₂} {hsum : w₁ + w₂ = 1} {p : unitInterval}
    (hp : p ∈ (FinDist.pair p₁ p₂ w₁ w₂ hw₁ hw₂ hsum).wt.support) :
    p = p₁ ∨ p = p₂ := by
  have hsub := Finsupp.support_add (g₁ := Finsupp.single p₁ w₁) (g₂ := Finsupp.single p₂ w₂) hp
  rcases Finset.mem_union.mp hsub with h1 | h2
  · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h1))
  · exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h2))

lemma FinDist.sum_pair_mul (p₁ p₂ : unitInterval) (w₁ w₂ : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hsum : w₁ + w₂ = 1) (f : unitInterval → ℝ) :
    (∑ p ∈ (FinDist.pair p₁ p₂ w₁ w₂ hw₁ hw₂ hsum).wt.support,
      (FinDist.pair p₁ p₂ w₁ w₂ hw₁ hw₂ hsum).wt p * f p) = w₁ * f p₁ + w₂ * f p₂ := by
  change (Finsupp.single p₁ w₁ + Finsupp.single p₂ w₂).sum (fun p w => w * f p) =
    w₁ * f p₁ + w₂ * f p₂
  rw [Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring)]
  simp

lemma EReal_sum_coe {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → ℝ) :
    (∑ i ∈ s, ((h i : ℝ) : EReal)) = ((∑ i ∈ s, h i : ℝ) : EReal) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma FinDist.expect_eq_coe_sum (D : FinDist) (g : unitInterval → EReal) (f : unitInterval → ℝ)
    (hf : ∀ p ∈ D.wt.support, g p = ((f p : ℝ) : EReal)) :
    D.expect g = ((∑ p ∈ D.wt.support, D.wt p * f p : ℝ) : EReal) := by
  unfold FinDist.expect
  have hcongr : ∑ p ∈ D.wt.support, ((D.wt p : ℝ) : EReal) * g p =
      ∑ p ∈ D.wt.support, ((D.wt p * f p : ℝ) : EReal) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hf p hp, ← EReal.coe_mul]
  rw [hcongr, EReal_sum_coe]

lemma FinDist.sum_wt (D : FinDist) : ∑ p ∈ D.wt.support, D.wt p = 1 :=
  D.sum_one

lemma exp_le_quad_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  have hexp_neg : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hmul : (1 - x) * Real.exp x ≤ 1 := by
    calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_right hexp_neg hexp_pos.le
      _ = Real.exp (-x + x) := (Real.exp_add (-x) x).symm
      _ = 1 := by simp
  have hdiv : Real.exp x ≤ 1 / (1 - x) := (le_div_iff₀ hpos).mpr (by linarith)
  have halg : 1 / (1 - x) ≤ 1 + x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  exact hdiv.trans halg

lemma exp_convex_finset {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) :
    Real.exp (∑ i ∈ s, w i * x i) ≤ ∑ i ∈ s, w i * Real.exp (x i) := by
  set μ := ∑ i ∈ s, w i * x i
  have hstep : ∀ i ∈ s, w i * (1 + (x i - μ)) ≤ w i * (Real.exp (x i) * Real.exp (-μ)) := by
    intro i hi
    refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
    have h := Real.add_one_le_exp (x i - μ)
    have heq : Real.exp (x i - μ) = Real.exp (x i) * Real.exp (-μ) := by
      rw [sub_eq_add_neg, Real.exp_add]
    linarith
  have hsum_le := Finset.sum_le_sum hstep
  have hlhs : ∑ i ∈ s, w i * (1 + (x i - μ)) = 1 := by
    have h1 : ∑ i ∈ s, w i * (1 + (x i - μ)) =
        (∑ i ∈ s, w i) * (1 - μ) + ∑ i ∈ s, w i * x i := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, hsum]
    dsimp [μ]
    ring
  have hrhs : ∑ i ∈ s, w i * (Real.exp (x i) * Real.exp (-μ)) =
      (∑ i ∈ s, w i * Real.exp (x i)) * Real.exp (-μ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hlhs, hrhs] at hsum_le
  have hexp_pos : 0 < Real.exp μ := Real.exp_pos μ
  have hmul := mul_le_mul_of_nonneg_right hsum_le hexp_pos.le
  calc Real.exp μ = 1 * Real.exp μ := (one_mul _).symm
    _ ≤ (∑ i ∈ s, w i * Real.exp (x i)) * Real.exp (-μ) * Real.exp μ := hmul
    _ = (∑ i ∈ s, w i * Real.exp (x i)) * (Real.exp (-μ) * Real.exp μ) := by ring
    _ = (∑ i ∈ s, w i * Real.exp (x i)) * Real.exp (-μ + μ) := by rw [← Real.exp_add]
    _ = ∑ i ∈ s, w i * Real.exp (x i) := by simp

/-! ### Section 2: Direct Proof of Eq. (28) from Properness and Mixability -/

noncomputable def Lval (ℓ : Loss) (p : unitInterval) (y : Bool) : ℝ :=
  (ℓ p y).toReal

lemma coe_Lval_eq {ℓ : Loss} {p : unitInterval} {y : Bool}
    (hb : ℓ p y ≠ ⊥) (ht : ℓ p y ≠ ⊤) :
    ((Lval ℓ p y : ℝ) : EReal) = ℓ p y :=
  EReal.coe_toReal ht hb

noncomputable def expDiff (ℓ : Loss) (β : ℝ) (p q : unitInterval) (y : Bool) : ℝ :=
  if ℓ q y = ⊤ then 0 else Real.exp (β * (Lval ℓ p y - Lval ℓ q y))

lemma expDiff_nonneg (ℓ : Loss) (β : ℝ) (p q : unitInterval) (y : Bool) :
    0 ≤ expDiff ℓ β p q y := by
  unfold expDiff
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma lintegral_dirac_unitInterval (p : unitInterval) (f : unitInterval → ℝ≥0∞) :
    ∫⁻ z, f z ∂(Measure.dirac p) = f p := by
  have hae : f =ᵐ[Measure.dirac p] (fun _ => f p) := by
    rw [Filter.EventuallyEq, ae_iff]
    have hsub : {z : unitInterval | ¬f z = f p} ⊆ ({p} : Set unitInterval)ᶜ := by
      intro z hz hzp
      rw [Set.mem_singleton_iff] at hzp
      exact hz (congrArg f hzp)
    have hmeas : MeasurableSet (({p} : Set unitInterval)ᶜ) :=
      (measurableSet_singleton p).compl
    have h0 : Measure.dirac p (({p} : Set unitInterval)ᶜ) = 0 := by
      rw [Measure.dirac_apply' p hmeas]
      simp
    exact measure_mono_null hsub h0
  rw [lintegral_congr_ae hae, lintegral_const, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]

lemma EReal_exp_neg_mul_loss {ℓ : Loss} {β : ℝ} (hβ : 0 < β)
    (hbot : ∀ p y, ℓ p y ≠ ⊥) (p q : unitInterval) (y : Bool) :
    EReal.exp (-((β : EReal) * ℓ q y)) =
      ENNReal.ofReal (Real.exp (-β * Lval ℓ p y) * expDiff ℓ β p q y) := by
  unfold expDiff
  by_cases hqt : ℓ q y = ⊤
  · simp only [hqt, ↓reduceIte, mul_zero, ENNReal.ofReal_zero]
    rw [EReal.coe_mul_top_of_pos hβ, EReal.neg_top, EReal.exp_bot]
  · simp only [hqt, ↓reduceIte]
    have hq_eq : ℓ q y = ((Lval ℓ q y : ℝ) : EReal) := (coe_Lval_eq (hbot q y) hqt).symm
    rw [hq_eq, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring

lemma mixable_two_point_ineq {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (q : unitInterval) :
    (1 - (p : ℝ)) * expDiff ℓ β p q false + (p : ℝ) * expDiff ℓ β p q true ≤ 1 := by
  have hp_top : ∀ y, ℓ p y ≠ ⊤ := htop p hp0 hp1
  set E0 := expDiff ℓ β p q false
  set E1 := expDiff ℓ β p q true
  have hE0 : 0 ≤ E0 := expDiff_nonneg ℓ β p q false
  have hE1 : 0 ≤ E1 := expDiff_nonneg ℓ β p q true
  set u0 := E0 - 1
  set u1 := E1 - 1
  suffices hmain : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (1 - (p : ℝ)) * u0 + (p : ℝ) * u1 ≤ 2 * ε * (u0 ^ 2 + u1 ^ 2) by
    by_contra hlt
    push_neg at hlt
    have hS : 0 < (1 - (p : ℝ)) * u0 + (p : ℝ) * u1 := by
      dsimp [u0, u1]; linarith
    set D := 4 * (u0 ^ 2 + u1 ^ 2 + 1)
    have hD : 0 < D := by dsimp [D]; positivity
    set ε := min (1 / 2) (((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) / D)
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hS hD)
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    have hε2 : ε ≤ ((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) / D := min_le_right _ _
    have hbnd := hmain ε hε0 hε1
    have hmul : 2 * ε * (u0 ^ 2 + u1 ^ 2) < (1 - (p : ℝ)) * u0 + (p : ℝ) * u1 := by
      have hle : 2 * ε * (u0 ^ 2 + u1 ^ 2) ≤
          2 * (((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) / D) * (u0 ^ 2 + u1 ^ 2) := by
        have hsq : 0 ≤ u0 ^ 2 + u1 ^ 2 := by positivity
        nlinarith
      have hstrict : 2 * (((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) / D) * (u0 ^ 2 + u1 ^ 2) <
          (1 - (p : ℝ)) * u0 + (p : ℝ) * u1 := by
        have hrew : 2 * (((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) / D) * (u0 ^ 2 + u1 ^ 2) =
            (2 * ((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) * (u0 ^ 2 + u1 ^ 2)) / D := by ring
        rw [hrew, div_lt_iff₀ hD]
        dsimp [D]
        nlinarith [sq_nonneg u0, sq_nonneg u1]
      exact lt_of_le_of_lt hle hstrict
    linarith
  intro ε hε0 hε1
  set μ : Measure unitInterval :=
    ENNReal.ofReal (1 - ε) • Measure.dirac p + ENNReal.ofReal ε • Measure.dirac q
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hε0.le]
    ring_nf
    exact ENNReal.ofReal_one
  obtain ⟨r, hr⟩ := hmix μ hprob
  have hr_step : ∀ y : Bool, ℓ r y ≠ ⊤ ∧
      Real.log (1 + ε * (expDiff ℓ β p q y - 1)) ≤ -β * (Lval ℓ r y - Lval ℓ p y) := by
    intro y
    have hy := hr y
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac_unitInterval, lintegral_dirac_unitInterval] at hy
    simp only [smul_eq_mul] at hy
    have hpp : EReal.exp (-((β : EReal) * ℓ p y)) =
        ENNReal.ofReal (Real.exp (-β * Lval ℓ p y)) := by
      have hp_eq := (coe_Lval_eq (hbot p y) (hp_top y)).symm
      rw [hp_eq, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
      congr 1; ring
    have hpq := EReal_exp_neg_mul_loss hβ hbot p q y
    rw [hpp, hpq] at hy
    have hE_nonneg := expDiff_nonneg ℓ β p q y
    have hexp_pos : 0 < Real.exp (-β * Lval ℓ p y) := Real.exp_pos _
    have hlhs_eq : ENNReal.ofReal (1 - ε) * ENNReal.ofReal (Real.exp (-β * Lval ℓ p y)) +
        ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-β * Lval ℓ p y) * expDiff ℓ β p q y) =
        ENNReal.ofReal (Real.exp (-β * Lval ℓ p y) * (1 + ε * (expDiff ℓ β p q y - 1))) := by
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hε0.le,
        ← ENNReal.ofReal_add (mul_nonneg (by linarith) hexp_pos.le)
          (mul_nonneg hε0.le (mul_nonneg hexp_pos.le hE_nonneg))]
      congr 1; ring
    rw [hlhs_eq] at hy
    have hfactor_pos : 0 < 1 + ε * (expDiff ℓ β p q y - 1) := by nlinarith
    have hlhs_pos : 0 < ENNReal.ofReal
        (Real.exp (-β * Lval ℓ p y) * (1 + ε * (expDiff ℓ β p q y - 1))) :=
      ENNReal.ofReal_pos.mpr (mul_pos hexp_pos hfactor_pos)
    have hr_top : ℓ r y ≠ ⊤ := by
      intro hrt
      rw [hrt, EReal.coe_mul_top_of_pos hβ, EReal.neg_top, EReal.exp_bot] at hy
      exact not_lt_of_ge hy hlhs_pos
    refine ⟨hr_top, ?_⟩
    have hr_eq : EReal.exp (-((β : EReal) * ℓ r y)) =
        ENNReal.ofReal (Real.exp (-β * Lval ℓ r y)) := by
      have hre := (coe_Lval_eq (hbot r y) hr_top).symm
      rw [hre, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
      congr 1; ring
    rw [hr_eq, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at hy
    have hdiv : 1 + ε * (expDiff ℓ β p q y - 1) ≤ Real.exp (-β * (Lval ℓ r y - Lval ℓ p y)) := by
      have hmul := mul_le_mul_of_nonneg_left hy (Real.exp_pos (β * Lval ℓ p y)).le
      have h1 : Real.exp (β * Lval ℓ p y) *
          (Real.exp (-β * Lval ℓ p y) * (1 + ε * (expDiff ℓ β p q y - 1))) =
          1 + ε * (expDiff ℓ β p q y - 1) := by
        calc Real.exp (β * Lval ℓ p y) *
              (Real.exp (-β * Lval ℓ p y) * (1 + ε * (expDiff ℓ β p q y - 1)))
            = (Real.exp (β * Lval ℓ p y) * Real.exp (-β * Lval ℓ p y)) *
                (1 + ε * (expDiff ℓ β p q y - 1)) := by ring
          _ = Real.exp (β * Lval ℓ p y + (-β * Lval ℓ p y)) *
                (1 + ε * (expDiff ℓ β p q y - 1)) := by rw [← Real.exp_add]
          _ = 1 + ε * (expDiff ℓ β p q y - 1) := by simp
      have h2 : Real.exp (β * Lval ℓ p y) * Real.exp (-β * Lval ℓ r y) =
          Real.exp (-β * (Lval ℓ r y - Lval ℓ p y)) := by
        rw [← Real.exp_add]; congr 1; ring
      linarith
    calc Real.log (1 + ε * (expDiff ℓ β p q y - 1))
        ≤ Real.log (Real.exp (-β * (Lval ℓ r y - Lval ℓ p y))) :=
          Real.log_le_log hfactor_pos hdiv
      _ = -β * (Lval ℓ r y - Lval ℓ p y) := Real.log_exp _
  obtain ⟨hr0_top, hlog0⟩ := hr_step false
  obtain ⟨hr1_top, hlog1⟩ := hr_step true
  have hbern := hprop p r
  unfold bern at hbern
  rw [← coe_Lval_eq (hbot p false) (hp_top false), ← coe_Lval_eq (hbot p true) (hp_top true),
    ← coe_Lval_eq (hbot r false) hr0_top, ← coe_Lval_eq (hbot r true) hr1_top] at hbern
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hbern
  have hprop_diff : 0 ≤ (1 - (p : ℝ)) * (Lval ℓ r false - Lval ℓ p false) +
      (p : ℝ) * (Lval ℓ r true - Lval ℓ p true) := by linarith
  have hlog_sum : (1 - (p : ℝ)) * Real.log (1 + ε * u0) + (p : ℝ) * Real.log (1 + ε * u1) ≤ 0 := by
    have hp_sub : 0 ≤ 1 - (p : ℝ) := by linarith
    have hp_nonneg : 0 ≤ (p : ℝ) := hp0.le
    have hcomb : (1 - (p : ℝ)) * Real.log (1 + ε * u0) + (p : ℝ) * Real.log (1 + ε * u1) ≤
        -β * ((1 - (p : ℝ)) * (Lval ℓ r false - Lval ℓ p false) +
          (p : ℝ) * (Lval ℓ r true - Lval ℓ p true)) := by
      dsimp [u0, u1, E0, E1]
      nlinarith
    nlinarith
  have hrat : ∀ u : ℝ, -1 ≤ u → ε * (u - 2 * ε * u ^ 2) ≤ Real.log (1 + ε * u) := by
    intro u hu
    have hden_ge : 1 / 2 ≤ 1 + ε * u := by nlinarith
    have hden_pos : 0 < 1 + ε * u := by linarith
    have hlog_lb : (ε * u) / (1 + ε * u) ≤ Real.log (1 + ε * u) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hden_pos)
      rw [Real.log_inv] at h
      have halg : 1 - (1 + ε * u)⁻¹ = (ε * u) / (1 + ε * u) := by
        field_simp
        ring
      linarith
    have hrat_lb : ε * (u - 2 * ε * u ^ 2) ≤ (ε * u) / (1 + ε * u) := by
      rw [le_div_iff₀ hden_pos]
      have h12 : 0 ≤ 1 + 2 * ε * u := by
        rcases le_or_gt 0 u with hu0 | hu_neg
        · positivity
        · nlinarith
      have hdiff_nonneg : 0 ≤ (ε * u) ^ 2 * (1 + 2 * ε * u) :=
        mul_nonneg (sq_nonneg _) h12
      have hid : ε * u - ε * (u - 2 * ε * u ^ 2) * (1 + ε * u) =
          (ε * u) ^ 2 * (1 + 2 * ε * u) := by ring
      linarith
    exact hrat_lb.trans hlog_lb
  have hr0 := hrat u0 (by dsimp [u0]; linarith)
  have hr1 := hrat u1 (by dsimp [u1]; linarith)
  have hp_sub : 0 ≤ 1 - (p : ℝ) := by linarith
  have hp_nonneg : 0 ≤ (p : ℝ) := hp0.le
  have hcomb : ε * (((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) -
      2 * ε * ((1 - (p : ℝ)) * u0 ^ 2 + (p : ℝ) * u1 ^ 2)) ≤ 0 := by
    calc ε * (((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) -
          2 * ε * ((1 - (p : ℝ)) * u0 ^ 2 + (p : ℝ) * u1 ^ 2))
        = (1 - (p : ℝ)) * (ε * (u0 - 2 * ε * u0 ^ 2)) +
            (p : ℝ) * (ε * (u1 - 2 * ε * u1 ^ 2)) := by ring
      _ ≤ (1 - (p : ℝ)) * Real.log (1 + ε * u0) + (p : ℝ) * Real.log (1 + ε * u1) := by nlinarith
      _ ≤ 0 := hlog_sum
  have hinner : ((1 - (p : ℝ)) * u0 + (p : ℝ) * u1) -
      2 * ε * ((1 - (p : ℝ)) * u0 ^ 2 + (p : ℝ) * u1 ^ 2) ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    linarith [mul_pos hε0 hpos]
  have hsq_le : (1 - (p : ℝ)) * u0 ^ 2 + (p : ℝ) * u1 ^ 2 ≤ u0 ^ 2 + u1 ^ 2 := by
    nlinarith [sq_nonneg u0, sq_nonneg u1]
  calc (1 - (p : ℝ)) * u0 + (p : ℝ) * u1
      ≤ 2 * ε * ((1 - (p : ℝ)) * u0 ^ 2 + (p : ℝ) * u1 ^ 2) := sub_nonpos.mp hinner
    _ ≤ 2 * ε * (u0 ^ 2 + u1 ^ 2) := mul_le_mul_of_nonneg_left hsq_le (by positivity)

/-! ### Section 3: Properness Monotonicity, Curvature Bound, and Clipping -/

noncomputable def mkUnit (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : unitInterval :=
  ⟨r, hr0, hr1⟩

noncomputable def deltaLoss (ℓ : Loss) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ℝ :=
  Lval ℓ (mkUnit r hr0 hr1) true - Lval ℓ (mkUnit r hr0 hr1) false

noncomputable def logit (r : ℝ) : ℝ :=
  Real.log (r / (1 - r))

lemma proper_real_ineq {ℓ : Loss} (hprop : IsProper ℓ) (hbot : ∀ p y, ℓ p y ≠ ⊥)
    {p q : unitInterval} (hp0 : ℓ p false ≠ ⊤) (hp1 : ℓ p true ≠ ⊤)
    (hq0 : ℓ q false ≠ ⊤) (hq1 : ℓ q true ≠ ⊤) :
    (1 - (p : ℝ)) * Lval ℓ p false + (p : ℝ) * Lval ℓ p true ≤
      (1 - (p : ℝ)) * Lval ℓ q false + (p : ℝ) * Lval ℓ q true := by
  have h := hprop p q
  unfold bern at h
  rw [← coe_Lval_eq (hbot p false) hp0, ← coe_Lval_eq (hbot p true) hp1,
    ← coe_Lval_eq (hbot q false) hq0, ← coe_Lval_eq (hbot q true) hq1] at h
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

lemma proper_step_bounds {ℓ : Loss} (hprop : IsProper ℓ) (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s) (hs1 : s < 1) :
    0 ≤ deltaLoss ℓ r hr0.le (hrs.trans hs1.le) - deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le ∧
      r * (deltaLoss ℓ r hr0.le (hrs.trans hs1.le) - deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le) ≤
        Lval ℓ (mkUnit s (hr0.trans_le hrs).le hs1.le) false -
          Lval ℓ (mkUnit r hr0.le (hrs.trans hs1.le)) false ∧
      Lval ℓ (mkUnit s (hr0.trans_le hrs).le hs1.le) false -
          Lval ℓ (mkUnit r hr0.le (hrs.trans hs1.le)) false ≤
        s * (deltaLoss ℓ r hr0.le (hrs.trans hs1.le) - deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le) ∧
      -(1 - r) * (deltaLoss ℓ r hr0.le (hrs.trans hs1.le) -
          deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le) ≤
        Lval ℓ (mkUnit s (hr0.trans_le hrs).le hs1.le) true -
          Lval ℓ (mkUnit r hr0.le (hrs.trans hs1.le)) true ∧
      Lval ℓ (mkUnit s (hr0.trans_le hrs).le hs1.le) true -
          Lval ℓ (mkUnit r hr0.le (hrs.trans hs1.le)) true ≤
        -(1 - s) * (deltaLoss ℓ r hr0.le (hrs.trans hs1.le) -
          deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le) := by
  set pr := mkUnit r hr0.le (hrs.trans hs1.le)
  set ps := mkUnit s (hr0.trans_le hrs).le hs1.le
  set w := deltaLoss ℓ r hr0.le (hrs.trans hs1.le) - deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le
  have hpr := htop pr hr0 (hrs.trans_lt hs1)
  have hps := htop ps (hr0.trans_le hrs) hs1
  have h1 := proper_real_ineq hprop hbot (hpr false) (hpr true) (hps false) (hps true)
  have h2 := proper_real_ineq hprop hbot (hps false) (hps true) (hpr false) (hpr true)
  have hpr_v : (pr : ℝ) = r := rfl
  have hps_v : (ps : ℝ) = s := rfl
  rw [hpr_v] at h1
  rw [hps_v] at h2
  have hw_def : w = (Lval ℓ pr true - Lval ℓ pr false) - (Lval ℓ ps true - Lval ℓ ps false) := rfl
  have hL0_lb : r * w ≤ Lval ℓ ps false - Lval ℓ pr false := by nlinarith
  have hL0_ub : Lval ℓ ps false - Lval ℓ pr false ≤ s * w := by nlinarith
  have hw_nonneg : 0 ≤ w := by
    rcases eq_or_lt_of_le hrs with rfl | hlt
    · have hp_eq : pr = ps := Subtype.ext rfl
      rw [hw_def, hp_eq]; ring_nf; exact le_rfl
    · nlinarith
  refine ⟨hw_nonneg, hL0_lb, hL0_ub, by nlinarith, by nlinarith⟩

lemma proper_boundary_left {ℓ : Loss} (hprop : IsProper ℓ) (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {q : unitInterval} (hq : (q : ℝ) ≤ δ)
    (hqt : ℓ q true ≠ ⊤) :
    Lval ℓ (mkUnit δ hδ0.le hδ1.le) true ≤ Lval ℓ q true := by
  set pδ := mkUnit δ hδ0.le hδ1.le
  have hpδ := htop pδ hδ0 hδ1
  have hqf : ℓ q false ≠ ⊤ := by
    intro htop_f
    have h := hprop q pδ
    unfold bern at h
    have hq_lt1 : (q : ℝ) < 1 := hq.trans_lt hδ1
    have h1mq : 0 < 1 - (q : ℝ) := by linarith
    rw [htop_f, EReal.coe_mul_top_of_pos h1mq, ← coe_Lval_eq (hbot q true) hqt,
      ← EReal.coe_mul, EReal.top_add_coe,
      ← coe_Lval_eq (hbot pδ false) (hpδ false), ← coe_Lval_eq (hbot pδ true) (hpδ true),
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  rcases eq_or_lt_of_le hq with hq_eq | hq_lt
  · have heq : q = pδ := Subtype.ext hq_eq
    subst heq; exact le_rfl
  · have h1 := proper_real_ineq hprop hbot hqf hqt (hpδ false) (hpδ true)
    have h2 := proper_real_ineq hprop hbot (hpδ false) (hpδ true) hqf hqt
    have hpδ_v : (pδ : ℝ) = δ := rfl
    rw [hpδ_v] at h2
    have hdiff : 0 ≤ (Lval ℓ q true - Lval ℓ q false) - (Lval ℓ pδ true - Lval ℓ pδ false) := by
      have : 0 ≤ (δ - (q : ℝ)) *
          ((Lval ℓ q true - Lval ℓ q false) - (Lval ℓ pδ true - Lval ℓ pδ false)) := by linarith
      exact nonneg_of_mul_nonneg_right this (by linarith)
    nlinarith

lemma proper_boundary_right {ℓ : Loss} (hprop : IsProper ℓ) (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {q : unitInterval} (hq : 1 - δ ≤ (q : ℝ))
    (hqf : ℓ q false ≠ ⊤) :
    Lval ℓ (mkUnit (1 - δ) (by linarith) (by linarith)) false ≤ Lval ℓ q false := by
  have hq0 : 0 ≤ (q : ℝ) := q.2.1
  have hq1 : (q : ℝ) ≤ 1 := q.2.2
  set pr := mkUnit (1 - δ) (by linarith) (by linarith)
  have hpr := htop pr (by change 0 < 1 - δ; linarith) (by change 1 - δ < 1; linarith)
  have hqt : ℓ q true ≠ ⊤ := by
    intro htop_t
    have h := hprop q pr
    unfold bern at h
    have hq_pos : 0 < (q : ℝ) := by linarith
    rw [htop_t, EReal.coe_mul_top_of_pos hq_pos, ← coe_Lval_eq (hbot q false) hqf,
      ← EReal.coe_mul, EReal.coe_add_top,
      ← coe_Lval_eq (hbot pr false) (hpr false), ← coe_Lval_eq (hbot pr true) (hpr true),
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  rcases eq_or_lt_of_le hq with hq_eq | hq_lt
  · have heq : q = pr := Subtype.ext hq_eq.symm
    subst heq; exact le_rfl
  · have h1 := proper_real_ineq hprop hbot hqf hqt (hpr false) (hpr true)
    have h2 := proper_real_ineq hprop hbot (hpr false) (hpr true) hqf hqt
    have hpr_v : (pr : ℝ) = 1 - δ := rfl
    rw [hpr_v] at h2
    have hdiff : 0 ≤ (Lval ℓ pr true - Lval ℓ pr false) - (Lval ℓ q true - Lval ℓ q false) := by
      have : 0 ≤ ((q : ℝ) - (1 - δ)) *
          ((Lval ℓ pr true - Lval ℓ pr false) - (Lval ℓ q true - Lval ℓ q false)) := by linarith
      exact nonneg_of_mul_nonneg_right this (by linarith)
    nlinarith

lemma kl_div_bound {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    β * ((1 - r) * (Lval ℓ (mkUnit s hs0.le hs1.le) false - Lval ℓ (mkUnit r hr0.le hr1.le) false) +
        r * (Lval ℓ (mkUnit s hs0.le hs1.le) true - Lval ℓ (mkUnit r hr0.le hr1.le) true)) ≤
      (1 - r) * Real.log ((1 - r) / (1 - s)) + r * Real.log (r / s) := by
  set pr := mkUnit r hr0.le hr1.le
  set ps := mkUnit s hs0.le hs1.le
  have hpr := htop pr hr0 hr1
  have hmix_ineq := mixable_two_point_ineq hβ hprop hbot htop hmix (p := ps) hs0 hs1 pr
  have hps_v : (ps : ℝ) = s := rfl
  rw [hps_v] at hmix_ineq
  have hE0 : expDiff ℓ β ps pr false = Real.exp (β * (Lval ℓ ps false - Lval ℓ pr false)) := by
    simp [expDiff, hpr false]
  have hE1 : expDiff ℓ β ps pr true = Real.exp (β * (Lval ℓ ps true - Lval ℓ pr true)) := by
    simp [expDiff, hpr true]
  rw [hE0, hE1] at hmix_ineq
  set U0 := ((1 - s) / (1 - r)) * Real.exp (β * (Lval ℓ ps false - Lval ℓ pr false))
  set U1 := (s / r) * Real.exp (β * (Lval ℓ ps true - Lval ℓ pr true))
  have h1mr : 0 < 1 - r := by linarith
  have h1ms : 0 < 1 - s := by linarith
  have hU0_pos : 0 < U0 := mul_pos (div_pos h1ms h1mr) (Real.exp_pos _)
  have hU1_pos : 0 < U1 := mul_pos (div_pos hs0 hr0) (Real.exp_pos _)
  have hlog0 := Real.log_le_sub_one_of_pos hU0_pos
  have hlog1 := Real.log_le_sub_one_of_pos hU1_pos
  have havg : (1 - r) * U0 + r * U1 =
      (1 - s) * Real.exp (β * (Lval ℓ ps false - Lval ℓ pr false)) +
        s * Real.exp (β * (Lval ℓ ps true - Lval ℓ pr true)) := by
    dsimp [U0, U1]
    field_simp [h1mr.ne', hr0.ne']
  have hsum_log : (1 - r) * Real.log U0 + r * Real.log U1 ≤ 0 := by nlinarith
  have hU0_log : Real.log U0 =
      -Real.log ((1 - r) / (1 - s)) + β * (Lval ℓ ps false - Lval ℓ pr false) := by
    dsimp [U0]
    rw [Real.log_mul (div_pos h1ms h1mr).ne' (Real.exp_pos _).ne', Real.log_exp,
      ← Real.log_inv, inv_div]
  have hU1_log : Real.log U1 = -Real.log (r / s) + β * (Lval ℓ ps true - Lval ℓ pr true) := by
    dsimp [U1]
    rw [Real.log_mul (div_pos hs0 hr0).ne' (Real.exp_pos _).ne', Real.log_exp,
      ← Real.log_inv, inv_div]
  rw [hU0_log, hU1_log] at hsum_log
  linarith

lemma curvature_bound {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s) (hs1 : s < 1) :
    0 ≤ deltaLoss ℓ r hr0.le (hrs.trans hs1.le) - deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le ∧
      deltaLoss ℓ r hr0.le (hrs.trans hs1.le) - deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le ≤
        (logit s - logit r) / β := by
  have hw_nonneg := (proper_step_bounds hprop hbot htop hr0 hrs hs1).1
  refine ⟨hw_nonneg, ?_⟩
  rcases eq_or_lt_of_le hrs with rfl | hlt
  · simp
  · have hkl1 := kl_div_bound hβ hprop hbot htop hmix hr0 (hlt.trans hs1) (hr0.trans hlt) hs1
    have hkl2 := kl_div_bound hβ hprop hbot htop hmix (hr0.trans hlt) hs1 hr0 (hlt.trans hs1)
    set pr := mkUnit r hr0.le (hrs.trans hs1.le)
    set ps := mkUnit s (hr0.trans_le hrs).le hs1.le
    have h1mr : 0 < 1 - r := by linarith
    have h1ms : 0 < 1 - s := by linarith
    have hlog_add1 : Real.log ((1 - r) / (1 - s)) + Real.log ((1 - s) / (1 - r)) = 0 := by
      rw [← Real.log_mul (div_pos h1mr h1ms).ne' (div_pos h1ms h1mr).ne',
        div_mul_div_cancel₀ h1ms.ne', div_self h1mr.ne', Real.log_one]
    have hlog_add2 : Real.log (r / s) + Real.log (s / r) = 0 := by
      rw [← Real.log_mul (div_pos hr0 (hr0.trans hlt)).ne' (div_pos (hr0.trans hlt) hr0).ne',
        div_mul_div_cancel₀ (hr0.trans hlt).ne', div_self hr0.ne', Real.log_one]
    have hrhs_eq : ((1 - r) * Real.log ((1 - r) / (1 - s)) + r * Real.log (r / s)) +
        ((1 - s) * Real.log ((1 - s) / (1 - r)) + s * Real.log (s / r)) =
        (s - r) * (logit s - logit r) := by
      unfold logit
      rw [Real.log_div (hr0.trans hlt).ne' h1ms.ne', Real.log_div hr0.ne' h1mr.ne',
        Real.log_div h1mr.ne' h1ms.ne', Real.log_div h1ms.ne' h1mr.ne',
        Real.log_div hr0.ne' (hr0.trans hlt).ne', Real.log_div (hr0.trans hlt).ne' hr0.ne']
      ring
    have hlhs_eq : β * ((1 - r) * (Lval ℓ ps false - Lval ℓ pr false) +
          r * (Lval ℓ ps true - Lval ℓ pr true)) +
        β * ((1 - s) * (Lval ℓ pr false - Lval ℓ ps false) +
          s * (Lval ℓ pr true - Lval ℓ ps true)) =
        β * (s - r) * (deltaLoss ℓ r hr0.le (hrs.trans hs1.le) -
          deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le) := by
      unfold deltaLoss
      ring
    have hadded : β * (s - r) * (deltaLoss ℓ r hr0.le (hrs.trans hs1.le) -
        deltaLoss ℓ s (hr0.trans_le hrs).le hs1.le) ≤ (s - r) * (logit s - logit r) := by
      linarith
    rw [le_div_iff₀ hβ]
    have hsr : 0 < s - r := by linarith
    nlinarith

lemma logit_diff_pos {r s : ℝ} (hr0 : 0 < r) (hrs : r < s) (hs1 : s < 1) :
    0 < logit s - logit r := by
  unfold logit
  have h1mr : 0 < 1 - r := by linarith
  have h1ms : 0 < 1 - s := by linarith
  have hs0 : 0 < s := hr0.trans hrs
  rw [← Real.log_div (div_pos hs0 h1ms).ne' (div_pos hr0 h1mr).ne']
  apply Real.log_pos
  have heq : (s / (1 - s)) / (r / (1 - r)) = (s * (1 - r)) / (r * (1 - s)) := by
    field_simp [h1ms.ne', h1mr.ne', hr0.ne']
  rw [heq, one_lt_div (mul_pos hr0 h1ms)]
  nlinarith

lemma logit_diff_le {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s) (hs1 : s < 1) :
    logit s - logit r ≤ (s - r) / (r * (1 - s)) := by
  unfold logit
  have h1mr : 0 < 1 - r := by linarith
  have h1ms : 0 < 1 - s := by linarith
  have hs0 : 0 < s := hr0.trans_le hrs
  rw [← Real.log_div (div_pos hs0 h1ms).ne' (div_pos hr0 h1mr).ne']
  have hquot_pos : 0 < (s / (1 - s)) / (r / (1 - r)) :=
    div_pos (div_pos hs0 h1ms) (div_pos hr0 h1mr)
  have h := Real.log_le_sub_one_of_pos hquot_pos
  have halg : (s / (1 - s)) / (r / (1 - r)) - 1 = (s - r) / (r * (1 - s)) := by
    field_simp [h1ms.ne', h1mr.ne', hr0.ne']
    ring
  linarith

noncomputable def halfPt : unitInterval := mkUnit (1 / 2) (by norm_num) (by norm_num)

lemma half_point_loss_bound {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) (q : unitInterval) (y : Bool) (hq_top : ℓ q y ≠ ⊤) :
    Lval ℓ halfPt y - Lval ℓ q y ≤ 1 / β := by
  have hmix_ineq := mixable_two_point_ineq hβ hprop hbot htop hmix
    (p := halfPt) (by norm_num [halfPt, mkUnit]) (by norm_num [halfPt, mkUnit]) q
  have hhalf_val : (halfPt : ℝ) = 1 / 2 := rfl
  rw [hhalf_val] at hmix_ineq
  have hEy_le : expDiff ℓ β halfPt q y ≤ 2 := by
    cases y
    · have h1 := expDiff_nonneg ℓ β halfPt q true
      linarith
    · have h0 := expDiff_nonneg ℓ β halfPt q false
      linarith
  have hEy_eq : expDiff ℓ β halfPt q y = Real.exp (β * (Lval ℓ halfPt y - Lval ℓ q y)) := by
    simp [expDiff, hq_top]
  rw [hEy_eq] at hEy_le
  have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hexp_le : Real.exp (β * (Lval ℓ halfPt y - Lval ℓ q y)) ≤ Real.exp 1 :=
    hEy_le.trans h2_le_exp1
  have hlin : β * (Lval ℓ halfPt y - Lval ℓ q y) ≤ 1 := Real.exp_le_exp.mp hexp_le
  rwa [le_div_iff₀ hβ, mul_comm]

noncomputable def clipVal (δ q : ℝ) : ℝ := max δ (min (1 - δ) q)

lemma clipVal_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (q : ℝ) :
    δ ≤ clipVal δ q ∧ clipVal δ q ≤ 1 - δ ∧ 0 ≤ clipVal δ q ∧ clipVal δ q ≤ 1 := by
  unfold clipVal
  have hlo : δ ≤ max δ (min (1 - δ) q) := le_max_left _ _
  have hhi : max δ (min (1 - δ) q) ≤ 1 - δ := max_le (by linarith) (min_le_left _ _)
  exact ⟨hlo, hhi, by linarith, by linarith⟩

lemma clip_loss_bound {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (q : unitInterval) (y : Bool) (hq_top : ℓ q y ≠ ⊤) :
    Lval ℓ (mkUnit (clipVal δ (q : ℝ)) (clipVal_bounds hδ0 hδ1 (q : ℝ)).2.2.1
      (clipVal_bounds hδ0 hδ1 (q : ℝ)).2.2.2) y - Lval ℓ q y ≤ 2 * δ / β := by
  have hδ_lt1 : δ < 1 := by linarith
  set qU := mkUnit (clipVal δ (q : ℝ)) (clipVal_bounds hδ0 hδ1 (q : ℝ)).2.2.1
    (clipVal_bounds hδ0 hδ1 (q : ℝ)).2.2.2
  by_cases hleft : (q : ℝ) < δ
  · have hqbar : clipVal δ (q : ℝ) = δ := by
      unfold clipVal
      rw [min_eq_right (by linarith), max_eq_left hleft.le]
    set pδ := mkUnit δ hδ0.le hδ_lt1.le
    have heq_unit : qU = pδ := Subtype.ext hqbar
    rw [heq_unit]
    cases y
    · have hmix_ineq := mixable_two_point_ineq hβ hprop hbot htop hmix
        (p := pδ) hδ0 hδ_lt1 q
      have hpδ_val : (pδ : ℝ) = δ := rfl
      rw [hpδ_val] at hmix_ineq
      have h1 := expDiff_nonneg ℓ β pδ q true
      have hE0_le : (1 - δ) * expDiff ℓ β pδ q false ≤ 1 := by nlinarith
      have hE0_eq : expDiff ℓ β pδ q false = Real.exp (β * (Lval ℓ pδ false - Lval ℓ q false)) := by
        simp [expDiff, hq_top]
      rw [hE0_eq] at hE0_le
      have hdiv : Real.exp (β * (Lval ℓ pδ false - Lval ℓ q false)) ≤ 1 / (1 - δ) :=
        (le_div_iff₀ (by linarith)).mpr (by linarith)
      have h1_le_exp : 1 / (1 - δ) ≤ Real.exp (2 * δ) := by
        have h1 : 1 / (1 - δ) ≤ 1 + 2 * δ := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        exact h1.trans (by linarith [Real.add_one_le_exp (2 * δ)])
      have hlin : β * (Lval ℓ pδ false - Lval ℓ q false) ≤ 2 * δ :=
        Real.exp_le_exp.mp (hdiv.trans h1_le_exp)
      rwa [le_div_iff₀ hβ, mul_comm]
    · have hle := proper_boundary_left hprop hbot htop hδ0 hδ_lt1 hleft.le hq_top
      have hpos : 0 ≤ 2 * δ / β := div_nonneg (by linarith) hβ.le
      linarith
  · push_neg at hleft
    by_cases hright : 1 - δ < (q : ℝ)
    · have hqbar : clipVal δ (q : ℝ) = 1 - δ := by
        unfold clipVal
        rw [min_eq_left hright.le, max_eq_right (by linarith)]
      set pr := mkUnit (1 - δ) (by linarith) (by linarith)
      have heq_unit : qU = pr := Subtype.ext hqbar
      rw [heq_unit]
      cases y
      · have hle := proper_boundary_right hprop hbot htop hδ0 hδ_lt1 hright.le hq_top
        have hpos : 0 ≤ 2 * δ / β := div_nonneg (by linarith) hβ.le
        linarith
      · have hmix_ineq := mixable_two_point_ineq hβ hprop hbot htop hmix
          (p := pr) (by change 0 < 1 - δ; linarith) (by change 1 - δ < 1; linarith) q
        have hpr_val : (pr : ℝ) = 1 - δ := rfl
        rw [hpr_val] at hmix_ineq
        have h0 := expDiff_nonneg ℓ β pr q false
        have hE1_le : (1 - δ) * expDiff ℓ β pr q true ≤ 1 := by nlinarith
        have hE1_eq : expDiff ℓ β pr q true = Real.exp (β * (Lval ℓ pr true - Lval ℓ q true)) := by
          simp [expDiff, hq_top]
        rw [hE1_eq] at hE1_le
        have hdiv : Real.exp (β * (Lval ℓ pr true - Lval ℓ q true)) ≤ 1 / (1 - δ) :=
          (le_div_iff₀ (by linarith)).mpr (by linarith)
        have h1_le_exp : 1 / (1 - δ) ≤ Real.exp (2 * δ) := by
          have h1 : 1 / (1 - δ) ≤ 1 + 2 * δ := by
            rw [div_le_iff₀ (by linarith)]
            nlinarith
          exact h1.trans (by linarith [Real.add_one_le_exp (2 * δ)])
        have hlin : β * (Lval ℓ pr true - Lval ℓ q true) ≤ 2 * δ :=
          Real.exp_le_exp.mp (hdiv.trans h1_le_exp)
        rwa [le_div_iff₀ hβ, mul_comm]
    · push_neg at hright
      have hqbar : clipVal δ (q : ℝ) = (q : ℝ) := by
        unfold clipVal
        rw [min_eq_right hright, max_eq_right hleft]
      have heq_unit : qU = q := Subtype.ext hqbar
      rw [heq_unit, sub_self]
      exact div_nonneg (by linarith) hβ.le

lemma snap_loss_bound {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {δ h r s : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hr_lo : δ ≤ r) (hr_hi : r ≤ 1 - δ) (hs_lo : δ ≤ s) (hs_hi : s ≤ 1 - δ)
    (hdist : |r - s| ≤ h) (y : Bool) :
    |Lval ℓ (mkUnit r (by linarith) (by linarith)) y -
      Lval ℓ (mkUnit s (by linarith) (by linarith)) y| ≤ h / (β * δ ^ 2) := by
  have hh_nonneg : 0 ≤ h := (abs_nonneg (r - s)).trans hdist
  have haux : ∀ (a b : ℝ) (ha : δ ≤ a) (hab : a ≤ b) (hb : b ≤ 1 - δ), b - a ≤ h →
      |Lval ℓ (mkUnit a (by linarith) (by linarith)) y -
        Lval ℓ (mkUnit b (by linarith) (by linarith)) y| ≤ h / (β * δ ^ 2) := by
    intro a b ha hab hb hba
    have ha0 : 0 < a := by linarith
    have hb1 : b < 1 := by linarith
    obtain ⟨hw0, h0_lb, h0_ub, h1_lb, h1_ub⟩ := proper_step_bounds hprop hbot htop ha0 hab hb1
    obtain ⟨_, hw_curv⟩ := curvature_bound hβ hprop hbot htop hmix ha0 hab hb1
    set w := deltaLoss ℓ a ha0.le (hab.trans hb1.le) - deltaLoss ℓ b (ha0.trans_le hab).le hb1.le
    have habs_le_w : |Lval ℓ (mkUnit a (by linarith) (by linarith)) y -
        Lval ℓ (mkUnit b (by linarith) (by linarith)) y| ≤ w := by
      cases y
      · rw [abs_le]; constructor <;> nlinarith
      · rw [abs_le]; constructor <;> nlinarith
    have hlogit : logit b - logit a ≤ h / δ ^ 2 := by
      have h1 := logit_diff_le ha0 hab hb1
      have hden_ge : δ ^ 2 ≤ a * (1 - b) := by nlinarith
      have hden_pos : 0 < a * (1 - b) := by nlinarith
      calc logit b - logit a ≤ (b - a) / (a * (1 - b)) := h1
        _ ≤ h / (a * (1 - b)) := div_le_div_of_nonneg_right hba hden_pos.le
        _ ≤ h / δ ^ 2 := div_le_div_of_nonneg_left hh_nonneg (sq_pos_of_pos hδ0) hden_ge
    have hw_le : w ≤ h / (β * δ ^ 2) := by
      calc w ≤ (logit b - logit a) / β := hw_curv
        _ ≤ (h / δ ^ 2) / β := div_le_div_of_nonneg_right hlogit hβ.le
        _ = h / (β * δ ^ 2) := by rw [div_div, mul_comm]
    exact habs_le_w.trans hw_le
  rcases le_total r s with hrs | hsr
  · exact haux r s hr_lo hrs hs_hi (by linarith [abs_le.mp hdist])
  · rw [abs_sub_comm]
    exact haux s r hs_lo hsr hr_hi (by linarith [abs_le.mp hdist])

/-! ### Section 4: Discrete Threshold Grid, V-Shaped Decomposition, and Discrete Lemma 3.6 -/

noncomputable def gridStep (δ : ℝ) (N : ℕ) : ℝ :=
  (1 - 2 * δ) / (N : ℝ)

noncomputable def gridPt (δ : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  δ + (i : ℝ) * gridStep δ N

noncomputable def midPt (δ : ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  gridPt δ N k + gridStep δ N / 2

def yVal (y : Bool) : ℝ := if y then 1 else 0

noncomputable def bVal (u p q : ℝ) : ℝ :=
  (if p < u ∧ u ≤ q then 1 else 0) - (if q < u ∧ u ≤ p then 1 else 0)

noncomputable def dVal (u p q : ℝ) : ℝ :=
  |u - p| * (bVal u p q) ^ 2

noncomputable def vLoss (u p : ℝ) (y : Bool) : ℝ :=
  if y then (if p < u then 1 - u else 0) else (if u ≤ p then u else 0)

lemma gridStep_pos {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N) :
    0 < gridStep δ N := by
  unfold gridStep
  exact div_pos (by linarith) (Nat.cast_pos.mpr hN)

lemma gridPt_zero (δ : ℝ) (N : ℕ) : gridPt δ N 0 = δ := by
  simp [gridPt]

lemma gridPt_last (δ : ℝ) {N : ℕ} (hN : 0 < N) : gridPt δ N N = 1 - δ := by
  unfold gridPt gridStep
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp [hN_ne]
  ring

lemma gridPt_succ_sub (δ : ℝ) (N : ℕ) (i : ℕ) :
    gridPt δ N (i + 1) - gridPt δ N i = gridStep δ N := by
  unfold gridPt
  push_cast
  ring

lemma gridPt_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N)
    {i : ℕ} (hi : i ≤ N) :
    δ ≤ gridPt δ N i ∧ gridPt δ N i ≤ 1 - δ ∧ 0 < gridPt δ N i ∧ gridPt δ N i < 1 ∧
      0 ≤ gridPt δ N i ∧ gridPt δ N i ≤ 1 := by
  have hh := gridStep_pos hδ1 hN
  have hlo : δ ≤ gridPt δ N i := by
    unfold gridPt
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh.le)
  have hhi : gridPt δ N i ≤ 1 - δ := by
    calc gridPt δ N i = δ + (i : ℝ) * gridStep δ N := rfl
      _ ≤ δ + (N : ℝ) * gridStep δ N := by
          linarith [mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hh.le]
      _ = gridPt δ N N := rfl
      _ = 1 - δ := gridPt_last δ hN
  exact ⟨hlo, hhi, by linarith, by linarith, by linarith, by linarith⟩

noncomputable def gridUnit (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (N : ℕ) (hN : 0 < N)
    (i : ℕ) (hi : i ≤ N) : unitInterval :=
  mkUnit (gridPt δ N i) (gridPt_bounds hδ0 hδ1 hN hi).2.2.2.2.1
    (gridPt_bounds hδ0 hδ1 hN hi).2.2.2.2.2

lemma gridPt_lt_midPt_iff {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N) (i k : ℕ) :
    gridPt δ N i < midPt δ N k ↔ i ≤ k := by
  have hh := gridStep_pos hδ1 hN
  unfold midPt gridPt
  constructor
  · intro hlt
    by_contra hnk
    push_neg at hnk
    have h1 : (k : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hnk
    nlinarith
  · intro hik
    have h1 : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
    nlinarith

lemma midPt_le_gridPt_iff {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N) (k j : ℕ) :
    midPt δ N k ≤ gridPt δ N j ↔ k < j := by
  rw [← not_lt, gridPt_lt_midPt_iff hδ1 hN j k, not_le]

lemma bVal_bounds (u p q : ℝ) : -1 ≤ bVal u p q ∧ bVal u p q ≤ 1 ∧ (bVal u p q) ^ 2 ≤ 1 := by
  unfold bVal
  by_cases h1 : p < u ∧ u ≤ q <;> by_cases h2 : q < u ∧ u ≤ p
  · exfalso; linarith [h1.1, h1.2, h2.1, h2.2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

lemma vLoss_diff_eq (u p q : ℝ) (y : Bool) :
    vLoss u p y - vLoss u q y = bVal u p q * (yVal y - p) - dVal u p q := by
  unfold vLoss dVal bVal yVal
  rcases lt_or_ge p u with hpu | hup <;> rcases lt_or_ge q u with hqu | huq <;> cases y
  · simp [hpu, hqu, not_le.mpr hpu, not_le.mpr hqu]
  · simp [hpu, hqu, not_le.mpr hpu, not_le.mpr hqu]
  · simp [hpu, huq, not_le.mpr hpu, not_lt.mpr huq, abs_of_pos (sub_pos.mpr hpu)]; ring
  · simp [hpu, huq, not_le.mpr hpu, not_lt.mpr huq, abs_of_pos (sub_pos.mpr hpu)]
  · simp [hup, hqu, not_lt.mpr hup, not_le.mpr hqu, abs_of_nonpos (sub_nonpos.mpr hup)]
  · simp [hup, hqu, not_lt.mpr hup, not_le.mpr hqu, abs_of_nonpos (sub_nonpos.mpr hup)]
  · simp [hup, huq, not_lt.mpr hup, not_lt.mpr huq]
  · simp [hup, huq, not_lt.mpr hup, not_lt.mpr huq]

noncomputable def snapIdx (δ : ℝ) (N : ℕ) (q : ℝ) : ℕ :=
  ((Finset.range N).filter (fun k => midPt δ N k ≤ q)).card

lemma filter_midPt_eq_range {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N) (q : ℝ) :
    ∀ M : ℕ, (Finset.range M).filter (fun k => midPt δ N k ≤ q) =
      Finset.range (((Finset.range M).filter (fun k => midPt δ N k ≤ q)).card) := by
  have hh := gridStep_pos hδ1 hN
  intro M
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hm
    · have hall : (Finset.range m).filter (fun k => midPt δ N k ≤ q) = Finset.range m := by
        rw [Finset.filter_eq_self]
        intro k hk
        have hkm : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (Finset.mem_range.mp hk).le
        unfold midPt gridPt at hm ⊢
        nlinarith
      rw [hall, ← Finset.range_add_one, Finset.card_range]
    · exact ih

lemma snapIdx_le (δ : ℝ) (N : ℕ) (q : ℝ) : snapIdx δ N q ≤ N := by
  unfold snapIdx
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma midPt_le_iff_lt_snapIdx {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N) (q : ℝ)
    {k : ℕ} (hk : k < N) :
    midPt δ N k ≤ q ↔ k < snapIdx δ N q := by
  have heq : (Finset.range N).filter (fun m => midPt δ N m ≤ q) =
      Finset.range (snapIdx δ N q) := filter_midPt_eq_range hδ1 hN q N
  have hmem : k ∈ (Finset.range N).filter (fun m => midPt δ N m ≤ q) ↔
      k ∈ Finset.range (snapIdx δ N q) := by rw [heq]
  simp only [Finset.mem_filter, Finset.mem_range] at hmem
  exact ⟨fun h => hmem.mp ⟨hk, h⟩, fun h => (hmem.mpr h).2⟩

lemma bVal_dVal_snap_eq {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N)
    (p q : ℝ) {k : ℕ} (hk : k < N) :
    bVal (midPt δ N k) p q = bVal (midPt δ N k) p (gridPt δ N (snapIdx δ N q)) ∧
      dVal (midPt δ N k) p q = dVal (midPt δ N k) p (gridPt δ N (snapIdx δ N q)) := by
  have hiff : midPt δ N k ≤ q ↔ midPt δ N k ≤ gridPt δ N (snapIdx δ N q) :=
    (midPt_le_iff_lt_snapIdx hδ1 hN q hk).trans (midPt_le_gridPt_iff hδ1 hN k (snapIdx δ N q)).symm
  have hlt_iff : q < midPt δ N k ↔ gridPt δ N (snapIdx δ N q) < midPt δ N k := by
    rw [← not_le, ← not_le, hiff]
  have hb : bVal (midPt δ N k) p q = bVal (midPt δ N k) p (gridPt δ N (snapIdx δ N q)) := by
    unfold bVal
    simp only [hiff, hlt_iff]
  exact ⟨hb, by unfold dVal; rw [hb]⟩

lemma clipVal_sub_gridPt_snapIdx_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N)
    (q : ℝ) :
    |clipVal δ q - gridPt δ N (snapIdx δ N q)| ≤ gridStep δ N := by
  have hh := gridStep_pos hδ1 hN
  set j := snapIdx δ N q
  have hjN : j ≤ N := snapIdx_le δ N q
  rcases eq_or_lt_of_le (Nat.zero_le j) with hj0 | hj_pos
  · rw [← hj0, gridPt_zero]
    have hq_lt : q < midPt δ N 0 := by
      rw [← not_le, midPt_le_iff_lt_snapIdx hδ1 hN q hN]
      change ¬(0 < j); omega
    have hmid0 : midPt δ N 0 = δ + gridStep δ N / 2 := by simp [midPt, gridPt]
    have hclip_lo := (clipVal_bounds hδ0 hδ1 q).1
    have hclip_hi : clipVal δ q ≤ δ + gridStep δ N / 2 := by
      unfold clipVal
      exact max_le (by linarith) ((min_le_right _ _).trans (by linarith))
    rw [abs_le]; constructor <;> linarith
  · rcases eq_or_lt_of_le hjN with hj_eq | hj_lt
    · rw [hj_eq, gridPt_last δ hN]
      have hkm : N - 1 < N := Nat.sub_lt hN Nat.one_pos
      have hq_ge : midPt δ N (N - 1) ≤ q := by
        rw [midPt_le_iff_lt_snapIdx hδ1 hN q hkm]
        change N - 1 < j; omega
      have hmid_last : midPt δ N (N - 1) = 1 - δ - gridStep δ N / 2 := by
        have h1 : gridPt δ N ((N - 1) + 1) - gridPt δ N (N - 1) = gridStep δ N :=
          gridPt_succ_sub δ N (N - 1)
        have h2 : (N - 1) + 1 = N := Nat.sub_add_cancel hN
        rw [h2, gridPt_last δ hN] at h1
        unfold midPt; linarith
      have hclip_hi := (clipVal_bounds hδ0 hδ1 q).2.1
      have hclip_lo : 1 - δ - gridStep δ N / 2 ≤ clipVal δ q := by
        unfold clipVal
        exact le_trans (le_min (by linarith) (by linarith)) (le_max_right _ _)
      rw [abs_le]; constructor <;> linarith
    · have hq_lo : midPt δ N (j - 1) ≤ q := by
        rw [midPt_le_iff_lt_snapIdx hδ1 hN q (by omega)]
        change j - 1 < j; omega
      have hq_hi : q < midPt δ N j := by
        rw [← not_le, midPt_le_iff_lt_snapIdx hδ1 hN q hj_lt]
        change ¬(j < j); omega
      have hmid_prev : midPt δ N (j - 1) = gridPt δ N j - gridStep δ N / 2 := by
        have h1 := gridPt_succ_sub δ N (j - 1)
        have h2 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
        rw [h2] at h1
        unfold midPt; linarith
      have hmid_curr : midPt δ N j = gridPt δ N j + gridStep δ N / 2 := rfl
      have h0_le_jm1 : midPt δ N 0 ≤ midPt δ N (j - 1) := by
        unfold midPt gridPt
        have : (0 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
      have hj_le_last : midPt δ N j ≤ midPt δ N (N - 1) := by
        unfold midPt gridPt
        have : (j : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
        nlinarith
      have hmid0_gt : δ < midPt δ N 0 := by
        unfold midPt; rw [gridPt_zero]; linarith
      have hmid_last_lt : midPt δ N (N - 1) < 1 - δ := by
        have h1 := gridPt_succ_sub δ N (N - 1)
        have h2 : (N - 1) + 1 = N := Nat.sub_add_cancel hN
        rw [h2, gridPt_last δ hN] at h1
        unfold midPt; linarith
      have hclip_eq : clipVal δ q = q := by
        unfold clipVal
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      rw [hclip_eq, abs_le]
      constructor <;> linarith

noncomputable def wStep (ℓ : Loss) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (N : ℕ) (hN : 0 < N) (k : ℕ) : ℝ :=
  if hk : k < N then
    deltaLoss ℓ (gridPt δ N k) (gridPt_bounds hδ0 hδ1 hN hk.le).2.2.2.2.1
      (gridPt_bounds hδ0 hδ1 hN hk.le).2.2.2.2.2 -
    deltaLoss ℓ (gridPt δ N (k + 1)) (gridPt_bounds hδ0 hδ1 hN hk).2.2.2.2.1
      (gridPt_bounds hδ0 hδ1 hN hk).2.2.2.2.2
  else 0

lemma wStep_bounds {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N)
    {k : ℕ} (hk : k < N) :
    0 ≤ wStep ℓ δ hδ0 hδ1 N hN k ∧
      wStep ℓ δ hδ0 hδ1 N hN k ≤ (logit (gridPt δ N (k + 1)) - logit (gridPt δ N k)) / β := by
  unfold wStep
  rw [dif_pos hk]
  have hh := gridStep_pos hδ1 hN
  have hle : gridPt δ N k ≤ gridPt δ N (k + 1) := by
    linarith [gridPt_succ_sub δ N k]
  exact curvature_bound hβ hprop hbot htop hmix
    (gridPt_bounds hδ0 hδ1 hN hk.le).2.2.1 hle (gridPt_bounds hδ0 hδ1 hN hk).2.2.2.1

lemma sum_logit_gridPt {δ : ℝ} (N : ℕ) :
    (∑ k ∈ Finset.range N, (logit (gridPt δ N (k + 1)) - logit (gridPt δ N k))) =
      logit (gridPt δ N N) - logit (gridPt δ N 0) :=
  Finset.sum_range_sub (fun k => logit (gridPt δ N k)) N

lemma logit_range_eq_M {T : ℕ} :
    let δ := 1 / (2 * (T : ℝ) + 2)
    logit (1 - δ) - logit δ = 2 * Real.log (2 * (T : ℝ) + 1) := by
  intro δ
  unfold logit
  have hT : 0 < 2 * (T : ℝ) + 1 := by positivity
  have hT2 : 0 < 2 * (T : ℝ) + 2 := by positivity
  have hδ_mul : δ * (2 * (T : ℝ) + 2) = 1 := one_div_mul_cancel hT2.ne'
  have h1mδ_pos : 0 < 1 - δ := by
    have : (1 - δ) * (2 * (T : ℝ) + 2) = 2 * (T : ℝ) + 1 := by linarith
    nlinarith
  have h1 : (1 - δ) / (1 - (1 - δ)) = 2 * (T : ℝ) + 1 := by
    have hδ_pos : 0 < δ := by dsimp [δ]; positivity
    rw [sub_sub_cancel, div_eq_iff hδ_pos.ne']
    linarith
  have h2 : δ / (1 - δ) = (2 * (T : ℝ) + 1)⁻¹ := by
    rw [inv_eq_one_div, div_eq_div_iff h1mδ_pos.ne' hT.ne']
    linarith
  rw [h1, h2, Real.log_inv]
  ring

lemma sum_wStep_le {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k) ≤ (logit (1 - δ) - logit δ) / β := by
  calc (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k)
      ≤ ∑ k ∈ Finset.range N, (logit (gridPt δ N (k + 1)) - logit (gridPt δ N k)) / β := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact (wStep_bounds hβ hprop hbot htop hmix hδ0 hδ1 hN (Finset.mem_range.mp hk)).2
    _ = (∑ k ∈ Finset.range N, (logit (gridPt δ N (k + 1)) - logit (gridPt δ N k))) / β :=
        (Finset.sum_div _ _ _).symm
    _ = (logit (1 - δ) - logit δ) / β := by
        rw [sum_logit_gridPt, gridPt_last δ hN, gridPt_zero]

lemma discrete_vLoss_approx {ℓ : Loss} {β : ℝ} (_hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N)
    {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) (y : Bool) :
    |Lval ℓ (gridUnit δ hδ0 hδ1 N hN i hi) y - Lval ℓ (gridUnit δ hδ0 hδ1 N hN j hj) y -
      ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
        (vLoss (midPt δ N k) (gridPt δ N i) y - vLoss (midPt δ N k) (gridPt δ N j) y)| ≤
      (gridStep δ N / 2) * ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k := by
  have hh := gridStep_pos hδ1 hN
  have hone_step : ∀ m : ℕ, (hm : m < N) →
      |Lval ℓ (gridUnit δ hδ0 hδ1 N hN (m + 1) hm) y -
          Lval ℓ (gridUnit δ hδ0 hδ1 N hN m hm.le) y -
        ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
          (vLoss (midPt δ N k) (gridPt δ N (m + 1)) y - vLoss (midPt δ N k) (gridPt δ N m) y)| ≤
        (gridStep δ N / 2) * wStep ℓ δ hδ0 hδ1 N hN m := by
    intro m hm
    have hsum_single : ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
        (vLoss (midPt δ N k) (gridPt δ N (m + 1)) y - vLoss (midPt δ N k) (gridPt δ N m) y) =
        wStep ℓ δ hδ0 hδ1 N hN m *
          (vLoss (midPt δ N m) (gridPt δ N (m + 1)) y - vLoss (midPt δ N m) (gridPt δ N m) y) := by
      rw [Finset.sum_eq_single m]
      · intro k hk hkm
        have hzero : vLoss (midPt δ N k) (gridPt δ N (m + 1)) y -
            vLoss (midPt δ N k) (gridPt δ N m) y = 0 := by
          rcases lt_or_gt_of_ne hkm with hlt | hgt
          · have h1 : midPt δ N k ≤ gridPt δ N m := (midPt_le_gridPt_iff hδ1 hN k m).mpr hlt
            have h2 : midPt δ N k ≤ gridPt δ N (m + 1) :=
              (midPt_le_gridPt_iff hδ1 hN k (m + 1)).mpr (by omega)
            unfold vLoss
            cases y <;> simp [h1, h2, not_lt.mpr h1, not_lt.mpr h2]
          · have h1 : gridPt δ N m < midPt δ N k :=
              (gridPt_lt_midPt_iff hδ1 hN m k).mpr (by omega)
            have h2 : gridPt δ N (m + 1) < midPt δ N k :=
              (gridPt_lt_midPt_iff hδ1 hN (m + 1) k).mpr hgt
            unfold vLoss
            cases y <;> simp [h1, h2, not_le.mpr h1, not_le.mpr h2]
        rw [hzero, mul_zero]
      · intro hm_not
        exact absurd (Finset.mem_range.mpr hm) hm_not
    rw [hsum_single]
    have hm1_gt : midPt δ N m ≤ gridPt δ N (m + 1) :=
      (midPt_le_gridPt_iff hδ1 hN m (m + 1)).mpr (Nat.lt_succ_self m)
    have hm_lt : gridPt δ N m < midPt δ N m :=
      (gridPt_lt_midPt_iff hδ1 hN m m).mpr le_rfl
    have hle_grid : gridPt δ N m ≤ gridPt δ N (m + 1) := by linarith [gridPt_succ_sub δ N m]
    obtain ⟨hw0, h0_lb, h0_ub, h1_lb, h1_ub⟩ := proper_step_bounds hprop hbot htop
      (gridPt_bounds hδ0 hδ1 hN hm.le).2.2.1 hle_grid (gridPt_bounds hδ0 hδ1 hN hm).2.2.2.1
    have hw_eq : wStep ℓ δ hδ0 hδ1 N hN m =
        deltaLoss ℓ (gridPt δ N m) (gridPt_bounds hδ0 hδ1 hN hm.le).2.2.2.2.1
          (gridPt_bounds hδ0 hδ1 hN hm.le).2.2.2.2.2 -
        deltaLoss ℓ (gridPt δ N (m + 1)) (gridPt_bounds hδ0 hδ1 hN hm).2.2.2.2.1
          (gridPt_bounds hδ0 hδ1 hN hm).2.2.2.2.2 := dif_pos hm
    have hstep_eq := gridPt_succ_sub δ N m
    have hmid_eq : midPt δ N m = gridPt δ N m + gridStep δ N / 2 := rfl
    cases y
    · have hv : vLoss (midPt δ N m) (gridPt δ N (m + 1)) false -
          vLoss (midPt δ N m) (gridPt δ N m) false = midPt δ N m := by
        unfold vLoss
        simp [hm1_gt, not_le.mpr hm_lt]
      rw [hv, hw_eq]
      unfold gridUnit
      rw [abs_le]
      constructor <;> nlinarith
    · have hv : vLoss (midPt δ N m) (gridPt δ N (m + 1)) true -
          vLoss (midPt δ N m) (gridPt δ N m) true = -(1 - midPt δ N m) := by
        unfold vLoss
        simp [hm_lt, not_lt.mpr hm1_gt]
      rw [hv, hw_eq]
      unfold gridUnit
      rw [abs_le]
      constructor <;> nlinarith
  have hordered : ∀ a b : ℕ, (ha : a ≤ b) → (hb : b ≤ N) →
      |Lval ℓ (gridUnit δ hδ0 hδ1 N hN b hb) y - Lval ℓ (gridUnit δ hδ0 hδ1 N hN a (ha.trans hb)) y -
        ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
          (vLoss (midPt δ N k) (gridPt δ N b) y - vLoss (midPt δ N k) (gridPt δ N a) y)| ≤
        (gridStep δ N / 2) * ∑ m ∈ Finset.Ico a b, wStep ℓ δ hδ0 hδ1 N hN m := by
    intro a b hab hb
    induction b with
    | zero =>
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
      subst ha0; simp
    | succ m ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · have ham : a ≤ m := Nat.lt_succ_iff.mp hlt
        have hmN : m < N := hb
        have hprev := ih ham hmN.le
        have hcurr := hone_step m hmN
        have hdecomp : Lval ℓ (gridUnit δ hδ0 hδ1 N hN (m + 1) hb) y -
              Lval ℓ (gridUnit δ hδ0 hδ1 N hN a (hab.trans hb)) y -
            ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
              (vLoss (midPt δ N k) (gridPt δ N (m + 1)) y - vLoss (midPt δ N k) (gridPt δ N a) y) =
            (Lval ℓ (gridUnit δ hδ0 hδ1 N hN m hmN.le) y -
              Lval ℓ (gridUnit δ hδ0 hδ1 N hN a (ham.trans hmN.le)) y -
              ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
                (vLoss (midPt δ N k) (gridPt δ N m) y - vLoss (midPt δ N k) (gridPt δ N a) y)) +
            (Lval ℓ (gridUnit δ hδ0 hδ1 N hN (m + 1) hmN) y -
              Lval ℓ (gridUnit δ hδ0 hδ1 N hN m hmN.le) y -
              ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
                (vLoss (midPt δ N k) (gridPt δ N (m + 1)) y - vLoss (midPt δ N k) (gridPt δ N m) y)) := by
          have hsum_add : ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
                (vLoss (midPt δ N k) (gridPt δ N (m + 1)) y - vLoss (midPt δ N k) (gridPt δ N a) y) =
              (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
                (vLoss (midPt δ N k) (gridPt δ N m) y - vLoss (midPt δ N k) (gridPt δ N a) y)) +
              (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
                (vLoss (midPt δ N k) (gridPt δ N (m + 1)) y - vLoss (midPt δ N k) (gridPt δ N m) y)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
          rw [hsum_add]
          ring
        rw [hdecomp, Finset.sum_Ico_succ_top ham, mul_add]
        exact (abs_add_le _ _).trans (add_le_add hprev hcurr)
  have hIco_le : ∀ a b : ℕ, b ≤ N →
      (gridStep δ N / 2) * ∑ m ∈ Finset.Ico a b, wStep ℓ δ hδ0 hδ1 N hN m ≤
        (gridStep δ N / 2) * ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k := by
    intro a b hb
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro m hm
      exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hm).2.trans_le hb)
    · intro k hk _
      have hkN := Finset.mem_range.mp hk
      unfold wStep
      rw [dif_pos hkN]
      have hle : gridPt δ N k ≤ gridPt δ N (k + 1) := by linarith [gridPt_succ_sub δ N k]
      exact (proper_step_bounds hprop hbot htop
        (gridPt_bounds hδ0 hδ1 hN hkN.le).2.2.1 hle (gridPt_bounds hδ0 hδ1 hN hkN).2.2.2.1).1
  rcases le_total j i with hji | hij
  · exact (hordered j i hji hi).trans (hIco_le j i hi)
  · have hneg : Lval ℓ (gridUnit δ hδ0 hδ1 N hN i hi) y -
          Lval ℓ (gridUnit δ hδ0 hδ1 N hN j hj) y -
        ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
          (vLoss (midPt δ N k) (gridPt δ N i) y - vLoss (midPt δ N k) (gridPt δ N j) y) =
        -(Lval ℓ (gridUnit δ hδ0 hδ1 N hN j hj) y -
          Lval ℓ (gridUnit δ hδ0 hδ1 N hN i hi) y -
        ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
          (vLoss (midPt δ N k) (gridPt δ N j) y - vLoss (midPt δ N k) (gridPt δ N i) y)) := by
      have hsum_neg : ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
            (vLoss (midPt δ N k) (gridPt δ N i) y - vLoss (midPt δ N k) (gridPt δ N j) y) =
          -∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
            (vLoss (midPt δ N k) (gridPt δ N j) y - vLoss (midPt δ N k) (gridPt δ N i) y) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [hsum_neg]; ring
    rw [hneg, abs_neg]
    exact (hordered i j hij hj).trans (hIco_le i j hj)

lemma discrete_variance_cancel {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ) {δ η p q : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    {N : ℕ} (hN : 0 < N) (hη0 : 0 < η) (hη1 : η ≤ 1 / 8)
    (hp_lo : δ ≤ p) (hp_hi : p ≤ 1 - δ)
    (hh_le : gridStep δ N ≤ 2 * η * p * (1 - p)) :
    (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
      (2 * η * p * (1 - p) * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q)) ≤
      9 * η ^ 2 / β := by
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  set r0 := 2 * η * p * (1 - p)
  have hr0_pos : 0 < r0 := by dsimp [r0]; positivity
  set a := p - (3 / 2) * r0
  set b := p + (3 / 2) * r0
  have ha_ge : (5 / 8) * p ≤ a := by
    have hprod_le : η * (1 - p) ≤ 1 / 8 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hprod_le hp0.le
    dsimp [a, r0]; linarith
  have h1mb_ge : (5 / 8) * (1 - p) ≤ 1 - b := by
    have hprod_le : η * p ≤ 1 / 8 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hprod_le (sub_pos.mpr hp1).le
    dsimp [b, r0]; linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha_ge
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb1 : b < 1 := by
    have : 0 < (5 / 8) * (1 - p) := by positivity
    linarith
  let cl (x : ℝ) : ℝ := max a (min b x)
  have hcl_bounds : ∀ x : ℝ, a ≤ cl x ∧ cl x ≤ b ∧ 0 < cl x ∧ cl x < 1 := by
    intro x
    have h1 : a ≤ cl x := le_max_left _ _
    have h2 : cl x ≤ b := max_le hab (min_le_left _ _)
    exact ⟨h1, h2, by linarith, by linarith⟩
  have hcl_mono : ∀ x y : ℝ, x ≤ y → cl x ≤ cl y := by
    intro x y hxy
    exact max_le_max le_rfl (min_le_min le_rfl hxy)
  let f (k : ℕ) : ℝ := deltaLoss ℓ (cl (gridPt δ N k))
    (hcl_bounds (gridPt δ N k)).2.2.1.le (hcl_bounds (gridPt δ N k)).2.2.2.le
  have hterm : ∀ k ∈ Finset.range N,
      wStep ℓ δ hδ0 hδ1 N hN k *
        (r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q) ≤
      r0 * (f k - f (k + 1)) := by
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hw_nonneg := (wStep_bounds hβ hprop hbot htop hmix hδ0 hδ1 hN hkN).1
    have hf_nonneg : 0 ≤ f k - f (k + 1) := by
      have hle : cl (gridPt δ N k) ≤ cl (gridPt δ N (k + 1)) :=
        hcl_mono _ _ (by linarith [gridPt_succ_sub δ N k, gridStep_pos hδ1 hN])
      exact (proper_step_bounds hprop hbot htop
        (hcl_bounds (gridPt δ N k)).2.2.1 hle (hcl_bounds (gridPt δ N (k + 1))).2.2.2).1
    by_cases hfar : r0 ≤ |midPt δ N k - p|
    · have hbr : r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q ≤ 0 := by
        unfold dVal
        have hb2 : 0 ≤ (bVal (midPt δ N k) p q) ^ 2 := sq_nonneg _
        nlinarith
      exact (mul_nonpos_of_nonneg_of_nonpos hw_nonneg hbr).trans (mul_nonneg hr0_pos.le hf_nonneg)
    · push_neg at hfar
      have habs := abs_lt.mp hfar
      have hvk_ge : a ≤ gridPt δ N k := by
        have : midPt δ N k = gridPt δ N k + gridStep δ N / 2 := rfl
        dsimp [a]; linarith
      have hvk1_le : gridPt δ N (k + 1) ≤ b := by
        have h1 := gridPt_succ_sub δ N k
        have h2 : midPt δ N k = gridPt δ N k + gridStep δ N / 2 := rfl
        dsimp [b]; linarith
      have hcl_k : cl (gridPt δ N k) = gridPt δ N k := by
        dsimp [cl]
        rw [min_eq_right (hvk1_le.trans' (by linarith [gridPt_succ_sub δ N k, gridStep_pos hδ1 hN])),
          max_eq_right hvk_ge]
      have hcl_k1 : cl (gridPt δ N (k + 1)) = gridPt δ N (k + 1) := by
        dsimp [cl]
        rw [min_eq_right hvk1_le,
          max_eq_right (hvk_ge.trans (by linarith [gridPt_succ_sub δ N k, gridStep_pos hδ1 hN]))]
      have hf_eq : f k - f (k + 1) = wStep ℓ δ hδ0 hδ1 N hN k := by
        unfold wStep
        rw [dif_pos hkN]
        dsimp [f]
        unfold deltaLoss
        have ek : mkUnit (cl (gridPt δ N k))
            (hcl_bounds (gridPt δ N k)).2.2.1.le (hcl_bounds (gridPt δ N k)).2.2.2.le =
          mkUnit (gridPt δ N k)
            (gridPt_bounds hδ0 hδ1 hN hkN.le).2.2.2.2.1
            (gridPt_bounds hδ0 hδ1 hN hkN.le).2.2.2.2.2 := Subtype.ext hcl_k
        have ek1 : mkUnit (cl (gridPt δ N (k + 1)))
            (hcl_bounds (gridPt δ N (k + 1))).2.2.1.le (hcl_bounds (gridPt δ N (k + 1))).2.2.2.le =
          mkUnit (gridPt δ N (k + 1))
            (gridPt_bounds hδ0 hδ1 hN hkN).2.2.2.2.1
            (gridPt_bounds hδ0 hδ1 hN hkN).2.2.2.2.2 := Subtype.ext hcl_k1
        rw [ek, ek1]
      rw [hf_eq]
      have hb2_le := (bVal_bounds (midPt δ N k) p q).2.2
      have hd_nonneg : 0 ≤ dVal (midPt δ N k) p q := by unfold dVal; positivity
      have hbr_le : r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q ≤ r0 := by
        nlinarith
      calc wStep ℓ δ hδ0 hδ1 N hN k *
            (r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q)
          ≤ wStep ℓ δ hδ0 hδ1 N hN k * r0 := mul_le_mul_of_nonneg_left hbr_le hw_nonneg
        _ = r0 * wStep ℓ δ hδ0 hδ1 N hN k := mul_comm _ _
  have hsum_le : (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
      (r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q)) ≤ r0 * (f 0 - f N) := by
    calc (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
          (r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q))
        ≤ ∑ k ∈ Finset.range N, r0 * (f k - f (k + 1)) := Finset.sum_le_sum hterm
      _ = r0 * ∑ k ∈ Finset.range N, (f k - f (k + 1)) := (Finset.mul_sum _ _ _).symm
      _ = r0 * (f 0 - f N) := by rw [Finset.sum_range_sub' f N]
  have hf_le_ab : f 0 - f N ≤ deltaLoss ℓ a ha0.le (hab.trans hb1.le) -
      deltaLoss ℓ b (ha0.trans_le hab).le hb1.le := by
    have hleft_anti := (proper_step_bounds hprop hbot htop ha0
      (hcl_bounds (gridPt δ N 0)).1 (hcl_bounds (gridPt δ N 0)).2.2.2).1
    have hright_anti := (proper_step_bounds hprop hbot htop
      (hcl_bounds (gridPt δ N N)).2.2.1 (hcl_bounds (gridPt δ N N)).2.1 hb1).1
    dsimp [f]
    linarith
  have hab_curv := (curvature_bound hβ hprop hbot htop hmix ha0 hab hb1).2
  have hlogit_ab : logit b - logit a ≤ 18 * η := by
    have h1 := logit_diff_le ha0 hab hb1
    have hba : b - a = 3 * r0 := by dsimp [a, b]; ring
    have hden : (1 / 3) * p * (1 - p) ≤ a * (1 - b) := by
      have : (25 / 64) * p * (1 - p) ≤ a * (1 - b) := by nlinarith
      nlinarith
    have hden_pos : 0 < (1 / 3) * p * (1 - p) := by positivity
    calc logit b - logit a ≤ (b - a) / (a * (1 - b)) := h1
      _ = (3 * r0) / (a * (1 - b)) := by rw [hba]
      _ ≤ (3 * r0) / ((1 / 3) * p * (1 - p)) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hden
      _ = 18 * η := by
          dsimp [r0]
          field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
          ring
  have hdelta_le : deltaLoss ℓ a ha0.le (hab.trans hb1.le) -
      deltaLoss ℓ b (ha0.trans_le hab).le hb1.le ≤ 18 * η / β := by
    calc deltaLoss ℓ a ha0.le (hab.trans hb1.le) - deltaLoss ℓ b (ha0.trans_le hab).le hb1.le
        ≤ (logit b - logit a) / β := hab_curv
      _ ≤ 18 * η / β := div_le_div_of_nonneg_right hlogit_ab hβ.le
  have hr0_le : r0 ≤ η / 2 := by
    dsimp [r0]
    have hp1mp : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    nlinarith
  calc (∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k *
        (r0 * (bVal (midPt δ N k) p q) ^ 2 - dVal (midPt δ N k) p q))
      ≤ r0 * (f 0 - f N) := hsum_le
    _ ≤ r0 * (deltaLoss ℓ a ha0.le (hab.trans hb1.le) -
        deltaLoss ℓ b (ha0.trans_le hab).le hb1.le) :=
        mul_le_mul_of_nonneg_left hf_le_ab hr0_pos.le
    _ ≤ (η / 2) * (18 * η / β) :=
        mul_le_mul hr0_le hdelta_le
          (proper_step_bounds hprop hbot htop ha0 hab hb1).1 (by positivity)
    _ = 9 * η ^ 2 / β := by ring

/-! ### Section 5: Explicit 2-Point Binary EVI Solver on the Grid -/

noncomputable def eviDist (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (N : ℕ) (hN : 0 < N)
    (G : ℝ → ℝ) : FinDist := by
  classical
  exact if h0 : G (gridPt δ N 0) ≤ 0 then
    FinDist.dirac (gridUnit δ hδ0 hδ1 N hN 0 (Nat.zero_le N))
  else if hlast : 0 ≤ G (gridPt δ N N) then
    FinDist.dirac (gridUnit δ hδ0 hδ1 N hN N le_rfl)
  else
    let hex : ∃ j : ℕ, j ≤ N ∧ G (gridPt δ N j) ≤ 0 := ⟨N, le_rfl, (not_le.mp hlast).le⟩
    let j := Nat.find hex
    have hj_le : j ≤ N := (Nat.find_spec hex).1
    have hj_nonpos : G (gridPt δ N j) ≤ 0 := (Nat.find_spec hex).2
    have hj_pos : 0 < j := by
      refine Nat.pos_of_ne_zero fun hj0 => ?_
      rw [hj0] at hj_nonpos
      exact h0 hj_nonpos
    let i := j - 1
    have hi_lt : i < N := by omega
    have hi1_eq : i + 1 = j := Nat.sub_add_cancel hj_pos
    have hi_pos : 0 < G (gridPt δ N i) := by
      have hnot := Nat.find_min hex (m := i) (by omega)
      push_neg at hnot
      exact hnot hi_lt.le
    let α := G (gridPt δ N i) / (G (gridPt δ N i) - G (gridPt δ N (i + 1)))
    have hgi1 : G (gridPt δ N (i + 1)) ≤ 0 := by rwa [hi1_eq]
    have hden : 0 < G (gridPt δ N i) - G (gridPt δ N (i + 1)) := by linarith
    have hα0 : 0 ≤ α := div_nonneg hi_pos.le hden.le
    have h1mα : 0 ≤ 1 - α := by
      dsimp [α]
      rw [sub_nonneg, div_le_one hden]
      linarith
    FinDist.pair (gridUnit δ hδ0 hδ1 N hN i hi_lt.le) (gridUnit δ hδ0 hδ1 N hN (i + 1) hi_lt)
      (1 - α) α h1mα hα0 (by ring)

lemma eviDist_spec {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ} (hN : 0 < N)
    (hh_le_δ : gridStep δ N ≤ δ) (G : ℝ → ℝ)
    (hG : ∀ i ≤ N, ∀ y : Bool, 0 ≤ 1 + G (gridPt δ N i) * (yVal y - gridPt δ N i)) :
    (∀ p ∈ (eviDist δ hδ0 hδ1 N hN G).wt.support, ∃ i : ℕ, ∃ hi : i ≤ N,
      p = gridUnit δ hδ0 hδ1 N hN i hi) ∧
    (∀ y : Bool, ∑ p ∈ (eviDist δ hδ0 hδ1 N hN G).wt.support,
      (eviDist δ hδ0 hδ1 N hN G).wt p * (G (p : ℝ) * (yVal y - (p : ℝ))) ≤ δ / (1 - δ)) := by
  unfold eviDist
  by_cases h0 : G (gridPt δ N 0) ≤ 0
  · simp only [dif_pos h0]
    refine ⟨fun p hp => ⟨0, Nat.zero_le N, FinDist.mem_support_dirac hp⟩, fun y => ?_⟩
    rw [FinDist.sum_dirac_mul]
    have hv0 : ((gridUnit δ hδ0 hδ1 N hN 0 (Nat.zero_le N) : unitInterval) : ℝ) = δ :=
      gridPt_zero δ N
    rw [hv0]
    cases y
    · have hb := hG 0 (Nat.zero_le N) true
      rw [gridPt_zero] at hb
      unfold yVal at hb ⊢
      simp only [↓reduceIte, Bool.false_eq_true] at hb ⊢
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    · unfold yVal
      simp only [↓reduceIte]
      have h0' : G δ ≤ 0 := by rwa [gridPt_zero] at h0
      have hnonpos : G δ * (1 - δ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0' (by linarith)
      exact hnonpos.trans (div_nonneg hδ0.le (by linarith))
  · simp only [dif_neg h0]
    by_cases hlast : 0 ≤ G (gridPt δ N N)
    · simp only [dif_pos hlast]
      refine ⟨fun p hp => ⟨N, le_rfl, FinDist.mem_support_dirac hp⟩, fun y => ?_⟩
      rw [FinDist.sum_dirac_mul]
      have hvN : ((gridUnit δ hδ0 hδ1 N hN N le_rfl : unitInterval) : ℝ) = 1 - δ :=
        gridPt_last δ hN
      rw [hvN]
      cases y
      · unfold yVal
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hlast' : 0 ≤ G (1 - δ) := by rwa [gridPt_last δ hN] at hlast
        have hnonpos : G (1 - δ) * (0 - (1 - δ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlast' (by linarith)
        exact hnonpos.trans (div_nonneg hδ0.le (by linarith))
      · have hb := hG N le_rfl false
        rw [gridPt_last δ hN] at hb
        unfold yVal at hb ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
        rw [le_div_iff₀ (by linarith)]
        nlinarith
    · simp only [dif_neg hlast]
      set hex : ∃ j : ℕ, j ≤ N ∧ G (gridPt δ N j) ≤ 0 := ⟨N, le_rfl, (not_le.mp hlast).le⟩
      set j := Nat.find hex
      have hj_le : j ≤ N := (Nat.find_spec hex).1
      have hj_nonpos : G (gridPt δ N j) ≤ 0 := (Nat.find_spec hex).2
      have hj_pos : 0 < j := by
        refine Nat.pos_of_ne_zero fun hj0 => ?_
        rw [hj0] at hj_nonpos
        exact h0 hj_nonpos
      set i := j - 1
      have hi_lt : i < N := by omega
      have hi1_eq : i + 1 = j := Nat.sub_add_cancel hj_pos
      have hi_pos : 0 < G (gridPt δ N i) := by
        have hnot := Nat.find_min hex (m := i) (by omega)
        push_neg at hnot
        exact hnot hi_lt.le
      have hgi1 : G (gridPt δ N (i + 1)) ≤ 0 := by rwa [hi1_eq]
      set g0 := G (gridPt δ N i)
      set g1 := -G (gridPt δ N (i + 1))
      have hg1_nonneg : 0 ≤ g1 := by dsimp [g1]; linarith
      have hden : 0 < g0 + g1 := by linarith
      refine ⟨fun p hp => ?_, fun y => ?_⟩
      · rcases FinDist.mem_support_pair hp with rfl | rfl
        · exact ⟨i, hi_lt.le, rfl⟩
        · exact ⟨i + 1, hi_lt, rfl⟩
      · rw [FinDist.sum_pair_mul]
        have hvi : ((gridUnit δ hδ0 hδ1 N hN i hi_lt.le : unitInterval) : ℝ) = gridPt δ N i := rfl
        have hvi1 : ((gridUnit δ hδ0 hδ1 N hN (i + 1) hi_lt : unitInterval) : ℝ) =
            gridPt δ N (i + 1) := rfl
        rw [hvi, hvi1]
        have hstep := gridPt_succ_sub δ N i
        have hh_pos := gridStep_pos hδ1 hN
        have hsim : (1 - g0 / (g0 - G (gridPt δ N (i + 1)))) *
              (g0 * (yVal y - gridPt δ N i)) +
            (g0 / (g0 - G (gridPt δ N (i + 1)))) *
              (G (gridPt δ N (i + 1)) * (yVal y - gridPt δ N (i + 1))) =
            (g0 * g1 / (g0 + g1)) * gridStep δ N := by
          have hden_eq : g0 - G (gridPt δ N (i + 1)) = g0 + g1 := by dsimp [g1]; ring
          have hg1_def : G (gridPt δ N (i + 1)) = -g1 := by dsimp [g1]; ring
          have hstep' : gridPt δ N (i + 1) = gridPt δ N i + gridStep δ N := by linarith [hstep]
          rw [hden_eq, hg1_def, hstep']
          field_simp [hden.ne']
          ring
        change (1 - g0 / (g0 - G (gridPt δ N (i + 1)))) *
              (g0 * (yVal y - gridPt δ N i)) +
            (g0 / (g0 - G (gridPt δ N (i + 1)))) *
              (G (gridPt δ N (i + 1)) * (yVal y - gridPt δ N (i + 1))) ≤ δ / (1 - δ)
        rw [hsim]
        have hb0 := hG i hi_lt.le false
        have hb1 := hG (i + 1) hi_lt true
        unfold yVal at hb0 hb1
        simp only [Bool.false_eq_true, ↓reduceIte] at hb0 hb1
        have hb0' : g0 * gridPt δ N i ≤ 1 := by dsimp [g0]; linarith
        have hb1' : g1 * (1 - gridPt δ N (i + 1)) ≤ 1 := by dsimp [g1]; linarith
        have hprod : g0 * g1 * (1 - gridStep δ N) ≤ g0 + g1 := by
          have m0 := mul_le_mul_of_nonneg_left hb0' hg1_nonneg
          have m1 := mul_le_mul_of_nonneg_left hb1' hi_pos.le
          nlinarith
        have h1mh : 0 < 1 - gridStep δ N := by linarith
        have hle_h : (g0 * g1 / (g0 + g1)) * gridStep δ N ≤ gridStep δ N / (1 - gridStep δ N) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hden h1mh]
          nlinarith
        have hh_le : gridStep δ N / (1 - gridStep δ N) ≤ δ / (1 - δ) := by
          rw [div_le_div_iff₀ h1mh (by linarith)]
          nlinarith
        exact hle_h.trans hh_le

/-! ### Section 6: Discrete Algorithm 2, Regret Analysis, and Theorem 1.2 -/

noncomputable def expFactor (η p b : ℝ) (y : Bool) : ℝ :=
  Real.exp (η * b * (yVal y - p) - 2 * η ^ 2 * p * (1 - p) * b ^ 2)

noncomputable def sFactor (η p b : ℝ) : ℝ :=
  expFactor η p b true - expFactor η p b false

lemma factor_bound {η p b : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 8)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1) (y : Bool) :
    expFactor η p b y ≤ 1 + sFactor η p b * (yVal y - p) ∧
      0 ≤ 1 + sFactor η p b * (yVal y - p) := by
  have hexp_pos : 0 < expFactor η p b y := Real.exp_pos _
  suffices hmain : expFactor η p b y ≤ 1 + sFactor η p b * (yVal y - p) by
    exact ⟨hmain, hexp_pos.le.trans hmain⟩
  have hlin_id : expFactor η p b y - sFactor η p b * (yVal y - p) =
      (1 - p) * expFactor η p b false + p * expFactor η p b true := by
    unfold sFactor yVal
    cases y <;> simp <;> ring
  suffices hbern : (1 - p) * expFactor η p b false + p * expFactor η p b true ≤ 1 by linarith
  set x0 := -η * b * p
  set x1 := η * b * (1 - p)
  have hηb_lo : -η ≤ η * b := by nlinarith
  have hηb_hi : η * b ≤ η := by nlinarith
  have hx0_le : x0 ≤ 1 / 2 := by dsimp [x0]; nlinarith
  have hx1_le : x1 ≤ 1 / 2 := by dsimp [x1]; nlinarith
  have hq0 := exp_le_quad_of_le_half hx0_le
  have hq1 := exp_le_quad_of_le_half hx1_le
  have hcomb_raw : (1 - p) * Real.exp x0 + p * Real.exp x1 ≤
      Real.exp (2 * η ^ 2 * p * (1 - p) * b ^ 2) := by
    have h1mp : 0 ≤ 1 - p := by linarith
    have hpoly : (1 - p) * (1 + x0 + 2 * x0 ^ 2) + p * (1 + x1 + 2 * x1 ^ 2) =
        1 + 2 * η ^ 2 * p * (1 - p) * b ^ 2 := by
      dsimp [x0, x1]; ring
    have h1 : (1 - p) * Real.exp x0 + p * Real.exp x1 ≤
        1 + 2 * η ^ 2 * p * (1 - p) * b ^ 2 := by nlinarith
    have h2 := Real.add_one_le_exp (2 * η ^ 2 * p * (1 - p) * b ^ 2)
    linarith
  set c := 2 * η ^ 2 * p * (1 - p) * b ^ 2
  have hmul := mul_le_mul_of_nonneg_right hcomb_raw (Real.exp_pos (-c)).le
  have hf0 : Real.exp x0 * Real.exp (-c) = expFactor η p b false := by
    unfold expFactor yVal
    rw [← Real.exp_add]
    congr 1
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp [x0, c]; ring
  have hf1 : Real.exp x1 * Real.exp (-c) = expFactor η p b true := by
    unfold expFactor yVal
    rw [← Real.exp_add]
    congr 1
  have hrhs : Real.exp c * Real.exp (-c) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 - p) * expFactor η p b false + p * expFactor η p b true
      = ((1 - p) * Real.exp x0 + p * Real.exp x1) * Real.exp (-c) := by
        rw [← hf0, ← hf1]; ring
    _ ≤ Real.exp c * Real.exp (-c) := hmul
    _ = 1 := hrhs

lemma EReal_add_ne_bot {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a + b ≠ ⊥ := by
  induction a using EReal.rec <;> induction b using EReal.rec <;> simp [← EReal.coe_add] at ha hb ⊢

lemma EReal_sum_ne_bot {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (h : ∀ i ∈ s, g i ≠ ⊥) : ∑ i ∈ s, g i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal_add_ne_bot (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma EReal_sum_eq_top_of_exists_top {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (hbot : ∀ i ∈ s, g i ≠ ⊥) (htop : ∃ i ∈ s, g i = ⊤) :
    ∑ i ∈ s, g i = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rcases htop with ⟨i, hi, _⟩
    exact absurd hi (Finset.notMem_empty i)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hs_ne_bot : ∑ i ∈ s, g i ≠ ⊥ :=
      EReal_sum_ne_bot s g (fun i hi => hbot i (Finset.mem_insert_of_mem hi))
    have ha_ne_bot : g a ≠ ⊥ := hbot a (Finset.mem_insert_self a s)
    rcases htop with ⟨i, hi, hitop⟩
    rcases Finset.mem_insert.mp hi with rfl | his
    · rw [hitop]
      exact EReal.top_add_of_ne_bot hs_ne_bot
    · have hstop := ih (fun j hj => hbot j (Finset.mem_insert_of_mem hj)) ⟨i, his, hitop⟩
      rw [hstop]
      exact EReal.add_top_of_ne_bot ha_ne_bot

lemma EReal_coe_sub_le_aux {A B : ℝ} {x : EReal}
    (hx : ((A - B : ℝ) : EReal) ≤ x) :
    ((A : ℝ) : EReal) - x ≤ ((B : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => exact absurd hx (not_le_of_gt (EReal.bot_lt_coe _))
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at hx
    linarith
  | top =>
    rw [EReal.sub_top]
    exact bot_le

lemma EReal_coe_sub_biInf_le {α : Type*} (F : Finset α) (A B : ℝ) (g : α → EReal)
    (h : ∀ f ∈ F, ((A - B : ℝ) : EReal) ≤ g f) :
    ((A : ℝ) : EReal) - (⨅ f ∈ F, g f) ≤ ((B : ℝ) : EReal) :=
  EReal_coe_sub_le_aux (le_iInf₂ h)

lemma EReal_sub_self_le_zero {x : EReal} (hx : x ≠ ⊥) : x - x ≤ 0 := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe r => rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
  | top =>
    rw [EReal.sub_top]
    exact bot_le

lemma log_two_T_add_one_gt_one {T : ℕ} (hT : 1 ≤ T) :
    1 < Real.log (2 * (T : ℝ) + 1) := by
  have hT_cast : (1 : ℝ) ≤ (T : ℝ) := Nat.one_le_cast.mpr hT
  have hexp : Real.exp 1 < 2 * (T : ℝ) + 1 := by
    have := Real.exp_one_lt_d9
    linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log (2 * (T : ℝ) + 1) := Real.log_lt_log (Real.exp_pos 1) hexp

lemma log_card_gt_half {n : ℕ} (hn : 2 ≤ n) :
    1 / 2 < Real.log (n : ℝ) := by
  have hexp_half : Real.exp (1 / 2) < 2 := by
    have hsq : (Real.exp (1 / 2)) ^ 2 < (2 : ℝ) ^ 2 := by
      rw [sq, ← Real.exp_add]
      norm_num
      linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos (1 / 2)]
  have hn_cast : (2 : ℝ) ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
    _ < Real.log (n : ℝ) := Real.log_lt_log (Real.exp_pos _) (hexp_half.trans_le hn_cast)

section Algo2

variable {X : Type u}

noncomputable def priorK (δ M : ℝ) (N k : ℕ) : ℝ :=
  (logit (gridPt δ N (k + 1)) - logit (gridPt δ N k)) / M

noncomputable def priorFK (F : Finset (X → unitInterval)) (δ M : ℝ) (N : ℕ)
    (_f : X → unitInterval) (k : ℕ) : ℝ :=
  priorK δ M N k / (F.card : ℝ)

lemma priorK_pos {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hM : 0 < M)
    {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) :
    0 < priorK δ M N k := by
  unfold priorK
  refine div_pos ?_ hM
  have hh := gridStep_pos hδ1 hN
  have hlt : gridPt δ N k < gridPt δ N (k + 1) := by linarith [gridPt_succ_sub δ N k]
  exact logit_diff_pos (gridPt_bounds hδ0 hδ1 hN hk.le).2.2.1 hlt
    (gridPt_bounds hδ0 hδ1 hN hk).2.2.2.1

lemma sum_priorK_eq_one {T N : ℕ} (hT : 1 ≤ T) (hN : 0 < N) :
    let δ := 1 / (2 * (T : ℝ) + 2)
    let M := 2 * Real.log (2 * (T : ℝ) + 1)
    ∑ k ∈ Finset.range N, priorK δ M N k = 1 := by
  intro δ M
  have hM_pos : 0 < M := by
    have := log_two_T_add_one_gt_one hT
    dsimp [M]; linarith
  unfold priorK
  rw [← Finset.sum_div, sum_logit_gridPt, gridPt_last δ hN, gridPt_zero]
  have hrange : logit (1 - δ) - logit δ = M := logit_range_eq_M
  rw [hrange, div_self hM_pos.ne']

lemma priorFK_pos {F : Finset (X → unitInterval)} (hF : 0 < F.card)
    {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hM : 0 < M)
    {N : ℕ} (hN : 0 < N) (f : X → unitInterval) {k : ℕ} (hk : k < N) :
    0 < priorFK F δ M N f k :=
  div_pos (priorK_pos hδ0 hδ1 hM hN hk) (Nat.cast_pos.mpr hF)

lemma sum_priorFK_eq_one {F : Finset (X → unitInterval)} (hF : 0 < F.card)
    {T N : ℕ} (hT : 1 ≤ T) (hN : 0 < N) :
    let δ := 1 / (2 * (T : ℝ) + 2)
    let M := 2 * Real.log (2 * (T : ℝ) + 1)
    ∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k = 1 := by
  intro δ M
  unfold priorFK
  have hinner : ∀ f ∈ F, ∑ k ∈ Finset.range N, priorK δ M N k / (F.card : ℝ) =
      1 / (F.card : ℝ) := by
    intro f _
    rw [← Finset.sum_div, sum_priorK_eq_one hT hN]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul,
    mul_one_div_cancel (Nat.cast_ne_zero.mpr hF.ne')]

noncomputable def phiPot (F : Finset (X → unitInterval)) (δ M : ℝ) (N : ℕ)
    (E : (X → unitInterval) → ℕ → ℝ) : ℝ :=
  ∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k)

lemma phiPot_pos {F : Finset (X → unitInterval)} (hF : 0 < F.card)
    {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hM : 0 < M) {N : ℕ} (hN : 0 < N)
    (E : (X → unitInterval) → ℕ → ℝ) :
    0 < phiPot F δ M N E := by
  obtain ⟨f₀, hf₀⟩ := Finset.card_pos.mp hF
  unfold phiPot
  refine Finset.sum_pos' (fun f _ => Finset.sum_nonneg fun k hk =>
    mul_nonneg (priorFK_pos hF hδ0 hδ1 hM hN f (Finset.mem_range.mp hk)).le (Real.exp_pos _).le)
    ⟨f₀, hf₀, ?_⟩
  refine Finset.sum_pos' (fun k hk =>
    mul_nonneg (priorFK_pos hF hδ0 hδ1 hM hN f₀ (Finset.mem_range.mp hk)).le (Real.exp_pos _).le)
    ⟨0, Finset.mem_range.mpr hN, mul_pos (priorFK_pos hF hδ0 hδ1 hM hN f₀ hN) (Real.exp_pos _)⟩

noncomputable def testFn (F : Finset (X → unitInterval)) (δ M η : ℝ) (N : ℕ)
    (E : (X → unitInterval) → ℕ → ℝ) (xt : X) (p : ℝ) : ℝ :=
  (∑ f ∈ F, ∑ k ∈ Finset.range N,
    priorFK F δ M N f k * Real.exp (E f k) * sFactor η p (bVal (midPt δ N k) p (f xt : ℝ))) /
  phiPot F δ M N E

lemma testFn_evi_cond {F : Finset (X → unitInterval)} (hF : 0 < F.card)
    {δ M η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hM : 0 < M)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 8) {N : ℕ} (hN : 0 < N)
    (E : (X → unitInterval) → ℕ → ℝ) (xt : X)
    {i : ℕ} (hi : i ≤ N) (y : Bool) :
    0 ≤ 1 + testFn F δ M η N E xt (gridPt δ N i) * (yVal y - gridPt δ N i) := by
  set p := gridPt δ N i
  have hp := gridPt_bounds hδ0 hδ1 hN hi
  have hphi := phiPot_pos hF hδ0 hδ1 hM hN E
  have hnum_eq : 1 + testFn F δ M η N E xt p * (yVal y - p) =
      (∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
        (1 + sFactor η p (bVal (midPt δ N k) p (f xt : ℝ)) * (yVal y - p))) /
      phiPot F δ M N E := by
    unfold testFn
    rw [div_mul_eq_mul_div, one_add_div hphi.ne']
    congr 1
    unfold phiPot
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hnum_eq]
  refine div_nonneg ?_ hphi.le
  refine Finset.sum_nonneg fun f _ => Finset.sum_nonneg fun k hk => ?_
  have hkN := Finset.mem_range.mp hk
  have hw := mul_pos (priorFK_pos hF hδ0 hδ1 hM hN f hkN) (Real.exp_pos (E f k))
  have hb := bVal_bounds (midPt δ N k) p (f xt : ℝ)
  have hfac := (factor_bound hη0 hη1 hp.2.2.2.2.1 hp.2.2.2.2.2 hb.1 hb.2.1 y).2
  exact mul_nonneg hw.le hfac

noncomputable def stepDist (F : Finset (X → unitInterval)) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (M η : ℝ) (N : ℕ) (hN : 0 < N) (E : (X → unitInterval) → ℕ → ℝ) (xt : X) : FinDist :=
  eviDist δ hδ0 hδ1 N hN (testFn F δ M η N E xt)

noncomputable def stepExp (δ η : ℝ) (N : ℕ) (D : FinDist) (xt : X) (yt : Bool)
    (f : X → unitInterval) (k : ℕ) : ℝ :=
  ∑ p ∈ D.wt.support, D.wt p *
    (η * bVal (midPt δ N k) (p : ℝ) (f xt : ℝ) * (yVal yt - (p : ℝ)) -
      2 * η ^ 2 * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) ^ 2)

noncomputable def cumExp (F : Finset (X → unitInterval)) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (M η : ℝ) (N : ℕ) (hN : 0 < N) :
    (n : ℕ) → (Fin n → X × Bool) → (X → unitInterval) → ℕ → ℝ
  | 0, _, _, _ => 0
  | m + 1, hist, f, k =>
      let prevHist : Fin m → X × Bool := fun s => hist s.castSucc
      let E := cumExp F δ hδ0 hδ1 M η N hN m prevHist
      let xm := (hist (Fin.last m)).1
      let ym := (hist (Fin.last m)).2
      let Dm := stepDist F δ hδ0 hδ1 M η N hN E xm
      E f k + stepExp δ η N Dm xm ym f k

noncomputable def algo2Forecaster (F : Finset (X → unitInterval)) (T : ℕ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (M η : ℝ) (N : ℕ) (hN : 0 < N) :
    Forecaster X T :=
  fun t hist xt =>
    stepDist F δ hδ0 hδ1 M η N hN (cumExp F δ hδ0 hδ1 M η N hN t.val hist) xt

def prefixHist {T : ℕ} (x : Fin T → X) (y : Fin T → Bool) (n : ℕ) (hn : n ≤ T) :
    Fin n → X × Bool :=
  fun s => (x ⟨s.val, s.isLt.trans_le hn⟩, y ⟨s.val, s.isLt.trans_le hn⟩)

lemma phiPot_step_le {F : Finset (X → unitInterval)} (hF : 0 < F.card)
    {δ M η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hM : 0 < M)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 8) {N : ℕ} (hN : 0 < N)
    (hh_le_δ : gridStep δ N ≤ δ)
    (E : (X → unitInterval) → ℕ → ℝ) (xt : X) (yt : Bool) :
    let D := stepDist F δ hδ0 hδ1 M η N hN E xt
    phiPot F δ M N (fun f k => E f k + stepExp δ η N D xt yt f k) ≤
      phiPot F δ M N E * (1 + δ / (1 - δ)) := by
  intro D
  have hEVI := eviDist_spec hδ0 hδ1 hN hh_le_δ (testFn F δ M η N E xt)
    (fun i hi y => testFn_evi_cond hF hδ0 hδ1 hM hη0 hη1 hN E xt hi y)
  have hD_eq : D = eviDist δ hδ0 hδ1 N hN (testFn F δ M η N E xt) := rfl
  have hterm : ∀ f ∈ F, ∀ k ∈ Finset.range N,
      priorFK F δ M N f k * Real.exp (E f k + stepExp δ η N D xt yt f k) ≤
      priorFK F δ M N f k * Real.exp (E f k) *
        (1 + ∑ p ∈ D.wt.support, D.wt p *
          (sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) *
            (yVal yt - (p : ℝ)))) := by
    intro f _ k hk
    have hkN := Finset.mem_range.mp hk
    have hw_pos := mul_pos (priorFK_pos hF hδ0 hδ1 hM hN f hkN) (Real.exp_pos (E f k))
    rw [Real.exp_add, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hw_pos.le
    have hjensen := exp_convex_finset D.wt.support D.wt
      (fun p => η * bVal (midPt δ N k) (p : ℝ) (f xt : ℝ) * (yVal yt - (p : ℝ)) -
        2 * η ^ 2 * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) ^ 2)
      (fun p _ => D.nonneg p) (FinDist.sum_wt D)
    have hpt : ∀ p ∈ D.wt.support,
        D.wt p * expFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) yt ≤
        D.wt p * (1 + sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) *
          (yVal yt - (p : ℝ))) := by
      intro p hp
      have hb := bVal_bounds (midPt δ N k) (p : ℝ) (f xt : ℝ)
      have hfac := (factor_bound hη0 hη1 p.2.1 p.2.2 hb.1 hb.2.1 yt).1
      exact mul_le_mul_of_nonneg_left hfac (D.nonneg p)
    have hsum_pt := Finset.sum_le_sum hpt
    have hrhs_split : ∑ p ∈ D.wt.support, D.wt p *
        (1 + sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))) =
        1 + ∑ p ∈ D.wt.support, D.wt p *
          (sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))) := by
      have h1 : ∑ p ∈ D.wt.support, D.wt p *
          (1 + sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))) =
          ∑ p ∈ D.wt.support, D.wt p + ∑ p ∈ D.wt.support, D.wt p *
            (sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      rw [h1, FinDist.sum_wt D]
    unfold stepExp expFactor at *
    exact hjensen.trans (hsum_pt.trans_eq hrhs_split)
  have hsum_fk : phiPot F δ M N (fun f k => E f k + stepExp δ η N D xt yt f k) ≤
      ∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
        (1 + ∑ p ∈ D.wt.support, D.wt p *
          (sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ)))) := by
    unfold phiPot
    exact Finset.sum_le_sum fun f hf => Finset.sum_le_sum fun k hk => hterm f hf k hk
  have hswap : (∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
        (1 + ∑ p ∈ D.wt.support, D.wt p *
          (sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))))) =
      phiPot F δ M N E * (1 + ∑ p ∈ D.wt.support,
        D.wt p * (testFn F δ M η N E xt (p : ℝ) * (yVal yt - (p : ℝ)))) := by
    have hphi := phiPot_pos hF hδ0 hδ1 hM hN E
    unfold testFn
    have h1 : (∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
          (1 + ∑ p ∈ D.wt.support, D.wt p *
            (sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))))) =
        phiPot F δ M N E + ∑ f ∈ F, ∑ k ∈ Finset.range N, ∑ p ∈ D.wt.support,
          priorFK F δ M N f k * Real.exp (E f k) * D.wt p *
            sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ)) := by
      unfold phiPot
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    have h2 : (∑ f ∈ F, ∑ k ∈ Finset.range N, ∑ p ∈ D.wt.support,
          priorFK F δ M N f k * Real.exp (E f k) * D.wt p *
            sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ))) =
        ∑ p ∈ D.wt.support, D.wt p *
          ((∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
            sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ))) * (yVal yt - (p : ℝ))) := by
      trans (∑ f ∈ F, ∑ p ∈ D.wt.support, ∑ k ∈ Finset.range N,
          priorFK F δ M N f k * Real.exp (E f k) * D.wt p *
            sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ)) * (yVal yt - (p : ℝ)))
      · refine Finset.sum_congr rfl fun f _ => Finset.sum_comm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      have h3 : (∑ f ∈ F, D.wt p * ((∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
            sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ))) * (yVal yt - (p : ℝ)))) =
          D.wt p * ((∑ f ∈ F, ∑ k ∈ Finset.range N, priorFK F δ M N f k * Real.exp (E f k) *
            sFactor η (p : ℝ) (bVal (midPt δ N k) (p : ℝ) (f xt : ℝ))) * (yVal yt - (p : ℝ))) := by
        rw [Finset.sum_mul, Finset.mul_sum]
      rw [← h3]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h1, h2, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp [hphi.ne']
  rw [hswap] at hsum_fk
  have hphi := phiPot_pos hF hδ0 hδ1 hM hN E
  have hevi_yt := hEVI.2 yt
  rw [← hD_eq] at hevi_yt
  exact hsum_fk.trans (mul_le_mul_of_nonneg_left (by linarith) hphi.le)

lemma phiPot_le_exp_one {F : Finset (X → unitInterval)} (hF : 0 < F.card)
    {T N : ℕ} (hT : 1 ≤ T) (hN : 0 < N)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 8)
    (hh_le_δ : gridStep (1 / (2 * (T : ℝ) + 2)) N ≤ 1 / (2 * (T : ℝ) + 2))
    (x : Fin T → X) (y : Fin T → Bool) :
    let δ := 1 / (2 * (T : ℝ) + 2)
    let M := 2 * Real.log (2 * (T : ℝ) + 1)
    let hδ0 : 0 < δ := by dsimp [δ]; positivity
    let hδ1 : δ ≤ 1 / 4 := by
      dsimp [δ]
      have : (1 : ℝ) ≤ (T : ℝ) := Nat.one_le_cast.mpr hT
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    phiPot F δ M N (cumExp F δ hδ0 hδ1 M η N hN T (prefixHist x y T le_rfl)) ≤ Real.exp 1 := by
  intro δ M hδ0 hδ1
  have hM_pos : 0 < M := by
    have := log_two_T_add_one_gt_one hT
    dsimp [M]; linarith
  have hT_pos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hδ_ratio : δ / (1 - δ) ≤ 1 / (T : ℝ) := by
    have hT1_pos : 0 < 2 * (T : ℝ) + 1 := by positivity
    have hT2_pos : 0 < 2 * (T : ℝ) + 2 := by positivity
    have hδ_mul : δ * (2 * (T : ℝ) + 2) = 1 := one_div_mul_cancel hT2_pos.ne'
    have h1mδ_pos : 0 < 1 - δ := by
      have : (1 - δ) * (2 * (T : ℝ) + 2) = 2 * (T : ℝ) + 1 := by linarith
      nlinarith
    have heq : δ / (1 - δ) = 1 / (2 * (T : ℝ) + 1) := by
      rw [div_eq_div_iff h1mδ_pos.ne' hT1_pos.ne']
      linarith
    rw [heq]
    exact div_le_div_of_nonneg_left zero_le_one hT_pos (by linarith)
  have hind : ∀ (n : ℕ) (hn : n ≤ T),
      phiPot F δ M N (cumExp F δ hδ0 hδ1 M η N hN n (prefixHist x y n hn)) ≤
        Real.exp ((n : ℝ) / (T : ℝ)) := by
    intro n hn
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_div, Real.exp_zero]
      unfold phiPot cumExp
      simp only [Real.exp_zero, mul_one]
      exact (sum_priorFK_eq_one hF hT hN).le
    | succ m ih =>
      have hm : m ≤ T := Nat.le_of_succ_le hn
      have hprev := ih hm
      have hcast_eq : (fun s : Fin m => prefixHist x y (m + 1) hn s.castSucc) =
          prefixHist x y m hm := rfl
      have hlast_x : (prefixHist x y (m + 1) hn (Fin.last m)).1 = x ⟨m, hn⟩ := rfl
      have hlast_y : (prefixHist x y (m + 1) hn (Fin.last m)).2 = y ⟨m, hn⟩ := rfl
      have hstep := phiPot_step_le hF hδ0 hδ1 hM_pos hη0 hη1 hN hh_le_δ
        (cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm)) (x ⟨m, hn⟩) (y ⟨m, hn⟩)
      have hexp_1T : 1 + δ / (1 - δ) ≤ Real.exp (1 / (T : ℝ)) := by
        linarith [Real.add_one_le_exp (1 / (T : ℝ))]
      have hphi_pos := phiPot_pos hF hδ0 hδ1 hM_pos hN
        (cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm))
      calc phiPot F δ M N (cumExp F δ hδ0 hδ1 M η N hN (m + 1) (prefixHist x y (m + 1) hn))
          = phiPot F δ M N (fun f k =>
              cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm) f k +
              stepExp δ η N
                (stepDist F δ hδ0 hδ1 M η N hN
                  (cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm)) (x ⟨m, hn⟩))
                (x ⟨m, hn⟩) (y ⟨m, hn⟩) f k) := rfl
        _ ≤ phiPot F δ M N (cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm)) *
              (1 + δ / (1 - δ)) := hstep
        _ ≤ Real.exp ((m : ℝ) / (T : ℝ)) * Real.exp (1 / (T : ℝ)) :=
              mul_le_mul hprev hexp_1T
                (add_nonneg zero_le_one (div_nonneg hδ0.le (by linarith))) (Real.exp_pos _).le
        _ = Real.exp ((m : ℝ) / (T : ℝ) + 1 / (T : ℝ)) := (Real.exp_add _ _).symm
        _ = Real.exp (((m + 1 : ℕ) : ℝ) / (T : ℝ)) := by
              congr 1; push_cast; ring
  simpa [div_self hT_pos.ne'] using hind T le_rfl

lemma discrete_potential_kl {F : Finset (X → unitInterval)} (hF2 : 2 ≤ F.card)
    {T N : ℕ} (hT : 1 ≤ T) (hN : 0 < N)
    {ℓ : Loss} {β : ℝ} (hβ : 0 < β) (hprop : IsProper ℓ)
    (hbot : ∀ p y, ℓ p y ≠ ⊥)
    (htop : ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤)
    (hmix : IsMixable β ℓ)
    {E : (X → unitInterval) → ℕ → ℝ}
    (hphi_le : phiPot F (1 / (2 * (T : ℝ) + 2)) (2 * Real.log (2 * (T : ℝ) + 1)) N E ≤ Real.exp 1)
    {f₀ : X → unitInterval} (hf₀ : f₀ ∈ F) :
    let δ := 1 / (2 * (T : ℝ) + 2)
    let M := 2 * Real.log (2 * (T : ℝ) + 1)
    let hδ0 : 0 < δ := by dsimp [δ]; positivity
    let hδ1 : δ ≤ 1 / 4 := by
      dsimp [δ]
      have : (1 : ℝ) ≤ (T : ℝ) := Nat.one_le_cast.mpr hT
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    ∑ k ∈ Finset.range N, wStep ℓ δ hδ0 hδ1 N hN k * E f₀ k ≤
      5 * M * Real.log (F.card : ℝ) / β := by
  intro δ M hδ0 hδ1
  have hF_pos : 0 < F.card := by omega
  have hLF : 1 / 2 < Real.log (F.card : ℝ) := log_card_gt_half hF2
  have hM_pos : 0 < M := by
    have := log_two_T_add_one_gt_one hT
    dsimp [M]; linarith
  set w := fun k => wStep ℓ δ hδ0 hδ1 N hN k
  set m := ∑ k ∈ Finset.range N, w k
  have hw_nonneg : ∀ k ∈ Finset.range N, 0 ≤ w k := fun k hk =>
    (wStep_bounds hβ hprop hbot htop hmix hδ0 hδ1 hN (Finset.mem_range.mp hk)).1
  have hw_prior : ∀ k ∈ Finset.range N, w k ≤ (M / β) * priorK δ M N k := by
    intro k hk
    have hb := (wStep_bounds hβ hprop hbot htop hmix hδ0 hδ1 hN (Finset.mem_range.mp hk)).2
    have heq : (logit (gridPt δ N (k + 1)) - logit (gridPt δ N k)) / β =
        (M / β) * priorK δ M N k := by
      unfold priorK
      field_simp [hM_pos.ne', hβ.ne']
    exact hb.trans_eq heq
  have hm_nonneg : 0 ≤ m := Finset.sum_nonneg hw_nonneg
  have hm_le : m ≤ M / β := by
    have h := sum_wStep_le hβ hprop hbot htop hmix hδ0 hδ1 hN
    have hrange : logit (1 - δ) - logit δ = M := logit_range_eq_M
    rwa [hrange] at h
  rcases eq_or_lt_of_le hm_nonneg with hm0 | hm_pos
  · have hall0 : ∀ k ∈ Finset.range N, w k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hw_nonneg).mp hm0.symm
    have hsum0 : ∑ k ∈ Finset.range N, w k * E f₀ k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hall0 k hk, zero_mul]
    rw [hsum0]
    positivity
  · set C := (F.card : ℝ) * Real.exp 1 * M / (β * m)
    have hF_cast_pos : 0 < (F.card : ℝ) := Nat.cast_pos.mpr hF_pos
    have hC_pos : 0 < C := by dsimp [C]; positivity
    have hterm : ∀ k ∈ Finset.range N,
        w k * E f₀ k ≤ w k * Real.log C +
          m * (priorFK F δ M N f₀ k * Real.exp (E f₀ k) / Real.exp 1) - w k := by
      intro k hk
      have hkN := Finset.mem_range.mp hk
      have hpfk_pos := priorFK_pos hF_pos hδ0 hδ1 hM_pos hN f₀ hkN
      rcases eq_or_lt_of_le (hw_nonneg k hk) with hwk0 | hwk_pos
      · rw [← hwk0, zero_mul, zero_mul, zero_add, sub_zero]
        exact mul_nonneg hm_pos.le (div_nonneg (mul_nonneg hpfk_pos.le (Real.exp_pos _).le)
          (Real.exp_pos 1).le)
      · set qk := w k / m
        have hqk_pos : 0 < qk := div_pos hwk_pos hm_pos
        set Yk := priorFK F δ M N f₀ k * Real.exp (E f₀ k) / (qk * Real.exp 1)
        have hYk_pos : 0 < Yk := by dsimp [Yk]; positivity
        have hexp_le : Real.exp (E f₀ k) ≤ C * Yk := by
          have hw_le := hw_prior k hk
          have hCY : C * Yk = (((M / β) * priorK δ M N k) / w k) * Real.exp (E f₀ k) := by
            dsimp [C, Yk, qk]
            unfold priorFK
            field_simp [hF_cast_pos.ne', (Real.exp_pos 1).ne', hβ.ne', hm_pos.ne', hwk_pos.ne']
          rw [hCY]
          have hrat : 1 ≤ ((M / β) * priorK δ M N k) / w k := (one_le_div hwk_pos).mpr hw_le
          exact (one_mul (Real.exp (E f₀ k))).symm.trans_le
            (mul_le_mul_of_nonneg_right hrat (Real.exp_pos _).le)
        have hlog_le : E f₀ k ≤ Real.log C + Yk - 1 := by
          have h1 : E f₀ k ≤ Real.log (C * Yk) := by
            rw [← Real.log_exp (E f₀ k)]
            exact Real.log_le_log (Real.exp_pos _) hexp_le
          rw [Real.log_mul hC_pos.ne' hYk_pos.ne'] at h1
          linarith [Real.log_le_sub_one_of_pos hYk_pos]
        have hmul := mul_le_mul_of_nonneg_left hlog_le hwk_pos.le
        have hY_simp : w k * Yk = m * (priorFK F δ M N f₀ k * Real.exp (E f₀ k) / Real.exp 1) := by
          dsimp [Yk, qk]
          field_simp [hm_pos.ne', hwk_pos.ne', (Real.exp_pos 1).ne']
        linarith
    have hsum_le := Finset.sum_le_sum hterm
    have hrhs_eq : ∑ k ∈ Finset.range N, (w k * Real.log C +
          m * (priorFK F δ M N f₀ k * Real.exp (E f₀ k) / Real.exp 1) - w k) =
        m * Real.log C + m * ((∑ k ∈ Finset.range N,
          priorFK F δ M N f₀ k * Real.exp (E f₀ k)) / Real.exp 1) - m := by
      have h1 : ∑ k ∈ Finset.range N, (w k * Real.log C +
            m * (priorFK F δ M N f₀ k * Real.exp (E f₀ k) / Real.exp 1) - w k) =
          (∑ k ∈ Finset.range N, w k) * Real.log C +
            m * ((∑ k ∈ Finset.range N, priorFK F δ M N f₀ k * Real.exp (E f₀ k)) / Real.exp 1) -
            ∑ k ∈ Finset.range N, w k := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
          Finset.sum_div, ← Finset.mul_sum]
      rw [h1]
    rw [hrhs_eq] at hsum_le
    have hf0_le_phi : ∑ k ∈ Finset.range N, priorFK F δ M N f₀ k * Real.exp (E f₀ k) ≤
        phiPot F δ M N E := by
      unfold phiPot
      exact Finset.single_le_sum (fun f _ => Finset.sum_nonneg fun k hk =>
        mul_nonneg (priorFK_pos hF_pos hδ0 hδ1 hM_pos hN f (Finset.mem_range.mp hk)).le
          (Real.exp_pos _).le) hf₀
    have hmid_le_m : m * ((∑ k ∈ Finset.range N,
        priorFK F δ M N f₀ k * Real.exp (E f₀ k)) / Real.exp 1) ≤ m := by
      have hdiv_le : (∑ k ∈ Finset.range N,
          priorFK F δ M N f₀ k * Real.exp (E f₀ k)) / Real.exp 1 ≤ 1 := by
        rw [div_le_one (Real.exp_pos 1)]
        exact hf0_le_phi.trans hphi_le
      nlinarith
    have hsum_le_mlogC : ∑ k ∈ Finset.range N, w k * E f₀ k ≤ m * Real.log C := by linarith
    have hlogC_eq : Real.log C =
        Real.log (F.card : ℝ) + 1 + Real.log (M / (β * m)) := by
      have hC_split : C = ((F.card : ℝ) * Real.exp 1) * (M / (β * m)) := by dsimp [C]; ring
      rw [hC_split, Real.log_mul (mul_pos hF_cast_pos (Real.exp_pos 1)).ne'
        (div_pos hM_pos (mul_pos hβ hm_pos)).ne',
        Real.log_mul hF_cast_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have hratio_log : m * Real.log (M / (β * m)) ≤ M / β := by
      have hr_pos : 0 < M / (β * m) := div_pos hM_pos (mul_pos hβ hm_pos)
      have h1 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr_pos) hm_pos.le
      have h2 : m * (M / (β * m) - 1) = M / β - m := by
        field_simp [hβ.ne', hm_pos.ne']
      linarith
    have hm_part : m * (Real.log (F.card : ℝ) + 1) ≤ (M / β) * (Real.log (F.card : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hm_le (by linarith)
    calc ∑ k ∈ Finset.range N, w k * E f₀ k
        ≤ m * Real.log C := hsum_le_mlogC
      _ = m * (Real.log (F.card : ℝ) + 1) + m * Real.log (M / (β * m)) := by
          rw [hlogC_eq]; ring
      _ ≤ (M / β) * (Real.log (F.card : ℝ) + 1) + M / β := add_le_add hm_part hratio_log
      _ = M * (2 + Real.log (F.card : ℝ)) / β := by ring
      _ ≤ 5 * M * Real.log (F.card : ℝ) / β := by
          have h5 : 2 + Real.log (F.card : ℝ) ≤ 5 * Real.log (F.card : ℝ) := by linarith
          have hnum : M * (2 + Real.log (F.card : ℝ)) ≤ 5 * M * Real.log (F.card : ℝ) := by
            nlinarith
          exact div_le_div_of_nonneg_right hnum hβ.le

lemma cumExp_eq_sum_forecasts {F : Finset (X → unitInterval)} {T : ℕ}
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {M η : ℝ} {N : ℕ} (hN : 0 < N)
    (x : Fin T → X) (y : Fin T → Bool) (f₀ : X → unitInterval) (k : ℕ) :
    cumExp F δ hδ0 hδ1 M η N hN T (prefixHist x y T le_rfl) f₀ k =
      ∑ t : Fin T, stepExp δ η N
        (forecasts (algo2Forecaster F T δ hδ0 hδ1 M η N hN) x y t) (x t) (y t) f₀ k := by
  have hind : ∀ (n : ℕ) (hn : n ≤ T),
      cumExp F δ hδ0 hδ1 M η N hN n (prefixHist x y n hn) f₀ k =
        ∑ t : Fin n, stepExp δ η N
          (forecasts (algo2Forecaster F T δ hδ0 hδ1 M η N hN) x y ⟨t.val, t.isLt.trans_le hn⟩)
          (x ⟨t.val, t.isLt.trans_le hn⟩) (y ⟨t.val, t.isLt.trans_le hn⟩) f₀ k := by
    intro n hn
    induction n with
    | zero => simp [cumExp]
    | succ m ih =>
      have hm : m ≤ T := Nat.le_of_succ_le hn
      rw [Fin.sum_univ_castSucc]
      have hprev := ih hm
      change cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm) f₀ k +
        stepExp δ η N
          (stepDist F δ hδ0 hδ1 M η N hN
            (cumExp F δ hδ0 hδ1 M η N hN m (prefixHist x y m hm)) (x ⟨m, hn⟩))
          (x ⟨m, hn⟩) (y ⟨m, hn⟩) f₀ k = _
      rw [hprev]
      congr 1
  exact hind T le_rfl

lemma rate_balance_bound {nF T : ℕ} (hF2 : 2 ≤ nF) (hT : 1 ≤ T) {β : ℝ} (hβ : 0 < β) :
    let M := 2 * Real.log (2 * (T : ℝ) + 1)
    let A0 := M * Real.log (nF : ℝ)
    let η := (A0 / (T : ℝ)) ^ (1 / 3 : ℝ)
    5 * A0 / (β * η) + (9 * (T : ℝ) * η ^ 2 + M + 2) / β ≤
      1024 * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (nF : ℝ) ^ (2 / 3 : ℝ) / β := by
  intro M A0 η
  have hT_pos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT_ge1 : (1 : ℝ) ≤ (T : ℝ) := Nat.one_le_cast.mpr hT
  have hLT : 1 < Real.log (2 * (T : ℝ) + 1) := log_two_T_add_one_gt_one hT
  have hLF : 1 / 2 < Real.log (nF : ℝ) := log_card_gt_half hF2
  have hM_gt2 : 2 < M := by dsimp [M]; linarith
  have hM_pos : 0 < M := by linarith
  have hA0_pos : 0 < A0 := mul_pos hM_pos (by linarith)
  have hη0 : 0 < η := Real.rpow_pos_of_pos (div_pos hA0_pos hT_pos) _
  have hη3 : η ^ 3 = A0 / (T : ℝ) := by
    calc η ^ (3 : ℕ) = η ^ (3 : ℝ) := (Real.rpow_natCast η 3).symm
      _ = ((A0 / (T : ℝ)) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := rfl
      _ = (A0 / (T : ℝ)) ^ ((1 / 3 : ℝ) * 3) := (Real.rpow_mul (by positivity) _ _).symm
      _ = A0 / (T : ℝ) := by norm_num
  have hA0_div_η : A0 / η = (T : ℝ) * η ^ 2 := by
    rw [div_eq_iff hη0.ne']
    calc A0 = (T : ℝ) * (A0 / (T : ℝ)) := (mul_div_cancel₀ A0 hT_pos.ne').symm
      _ = (T : ℝ) * η ^ 3 := by rw [hη3]
      _ = (T : ℝ) * η ^ 2 * η := by ring
  have hTη2_eq : (T : ℝ) * η ^ 2 = (T : ℝ) ^ (1 / 3 : ℝ) * A0 ^ (2 / 3 : ℝ) := by
    have hη2 : η ^ 2 = (A0 / (T : ℝ)) ^ (2 / 3 : ℝ) := by
      calc η ^ (2 : ℕ) = η ^ (2 : ℝ) := (Real.rpow_natCast η 2).symm
        _ = ((A0 / (T : ℝ)) ^ (1 / 3 : ℝ)) ^ (2 : ℝ) := rfl
        _ = (A0 / (T : ℝ)) ^ ((1 / 3 : ℝ) * 2) := (Real.rpow_mul (by positivity) _ _).symm
        _ = (A0 / (T : ℝ)) ^ (2 / 3 : ℝ) := by norm_num
    have hT_split : (T : ℝ) = (T : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hT_pos]; norm_num
    have h1 : (T : ℝ) * η ^ 2 =
        ((T : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) * (A0 / (T : ℝ)) ^ (2 / 3 : ℝ) := by
      rw [← hT_split, hη2]
    calc (T : ℝ) * η ^ 2
        = (T : ℝ) ^ (1 / 3 : ℝ) * ((T : ℝ) ^ (2 / 3 : ℝ) * (A0 / (T : ℝ)) ^ (2 / 3 : ℝ)) := by
          rw [h1]; ring
      _ = (T : ℝ) ^ (1 / 3 : ℝ) * ((T : ℝ) * (A0 / (T : ℝ))) ^ (2 / 3 : ℝ) := by
          rw [← Real.mul_rpow hT_pos.le (by positivity)]
      _ = (T : ℝ) ^ (1 / 3 : ℝ) * A0 ^ (2 / 3 : ℝ) := by
          rw [mul_div_cancel₀ A0 hT_pos.ne']
  have hA0_23 : A0 ^ (2 / 3 : ℝ) ≤ M * Real.log (nF : ℝ) ^ (2 / 3 : ℝ) := by
    calc A0 ^ (2 / 3 : ℝ)
        = M ^ (2 / 3 : ℝ) * Real.log (nF : ℝ) ^ (2 / 3 : ℝ) :=
          Real.mul_rpow hM_pos.le (by linarith)
      _ ≤ M ^ (1 : ℝ) * Real.log (nF : ℝ) ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by positivity)
      _ = M * Real.log (nF : ℝ) ^ (2 / 3 : ℝ) := by rw [Real.rpow_one]
  set R := Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) * Real.log (nF : ℝ) ^ (2 / 3 : ℝ)
  have hTη2_le : (T : ℝ) * η ^ 2 ≤ 2 * R := by
    rw [hTη2_eq]
    have h1 := mul_le_mul_of_nonneg_left hA0_23
      (Real.rpow_pos_of_pos hT_pos (1 / 3 : ℝ)).le
    have h2 : (T : ℝ) ^ (1 / 3 : ℝ) * (M * Real.log (nF : ℝ) ^ (2 / 3 : ℝ)) = 2 * R := by
      dsimp [R, M]; ring
    linarith
  have hT13_ge1 : 1 ≤ (T : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hT_ge1 (by norm_num)
  have hLF23_ge : 1 / 2 ≤ Real.log (nF : ℝ) ^ (2 / 3 : ℝ) := by
    calc (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / 2 : ℝ) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ ≤ Real.log (nF : ℝ) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hLF.le (by norm_num)
  have hprod_ge : 1 ≤ 2 * ((T : ℝ) ^ (1 / 3 : ℝ) * Real.log (nF : ℝ) ^ (2 / 3 : ℝ)) := by
    have := mul_le_mul hT13_ge1 hLF23_ge (by norm_num) (by positivity)
    linarith
  have hM2_le : M + 2 ≤ 8 * R := by
    have hM2 : M + 2 ≤ 4 * Real.log (2 * (T : ℝ) + 1) := by dsimp [M]; linarith
    have hmul := mul_le_mul_of_nonneg_left hprod_ge
      (by linarith : 0 ≤ 4 * Real.log (2 * (T : ℝ) + 1))
    have heq : 4 * Real.log (2 * (T : ℝ) + 1) *
        (2 * ((T : ℝ) ^ (1 / 3 : ℝ) * Real.log (nF : ℝ) ^ (2 / 3 : ℝ))) = 8 * R := by
      dsimp [R]; ring
    linarith
  have hnum_total : 5 * (A0 / η) + 9 * (T : ℝ) * η ^ 2 + M + 2 ≤ 1024 * R := by
    rw [hA0_div_η]
    have hR_nonneg : 0 ≤ R := by dsimp [R]; positivity
    linarith
  have hcomb_div : 5 * A0 / (β * η) + (9 * (T : ℝ) * η ^ 2 + M + 2) / β =
      (5 * (A0 / η) + 9 * (T : ℝ) * η ^ 2 + M + 2) / β := by
    field_simp [hβ.ne', hη0.ne']
    ring
  rw [hcomb_div]
  calc (5 * (A0 / η) + 9 * (T : ℝ) * η ^ 2 + M + 2) / β
      ≤ (1024 * R) / β := div_le_div_of_nonneg_right hnum_total hβ.le
    _ = 1024 * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (nF : ℝ) ^ (2 / 3 : ℝ) / β := by dsimp [R]; ring

lemma algo2_case_bound {F : Finset (X → unitInterval)} (hF2 : 2 ≤ F.card)
    {T : ℕ} (hT : 1 ≤ T)
    (hsmall : 512 * (2 * Real.log (2 * (T : ℝ) + 1)) * Real.log (F.card : ℝ) < (T : ℝ)) :
    ∃ A : Forecaster X T, ∀ (ℓ : Loss) (β : ℝ), 0 < β → IsProper ℓ →
      (∀ p y, ℓ p y ≠ ⊥) → (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) →
      IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool),
        regret ℓ F A x y ≤ ((1024 * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) / β : ℝ) : EReal) := by
  have hF_pos : 0 < F.card := by omega
  have hT_pos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT_ge1 : (1 : ℝ) ≤ (T : ℝ) := Nat.one_le_cast.mpr hT
  have hLT : 1 < Real.log (2 * (T : ℝ) + 1) := log_two_T_add_one_gt_one hT
  have hLF : 1 / 2 < Real.log (F.card : ℝ) := log_card_gt_half hF2
  set δ := 1 / (2 * (T : ℝ) + 2)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 / 4 := by
    dsimp [δ]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  set M := 2 * Real.log (2 * (T : ℝ) + 1)
  have hM_gt2 : 2 < M := by dsimp [M]; linarith
  have hM_pos : 0 < M := by linarith
  set A0 := M * Real.log (F.card : ℝ)
  have hA0_gt1 : 1 < A0 := by dsimp [A0]; nlinarith
  have hA0_pos : 0 < A0 := by linarith
  set η := (A0 / (T : ℝ)) ^ (1 / 3 : ℝ)
  have hη0 : 0 < η := Real.rpow_pos_of_pos (div_pos hA0_pos hT_pos) _
  have hη1 : η ≤ 1 / 8 := by
    have hdiv_le : A0 / (T : ℝ) ≤ (1 / 8 : ℝ) ^ (3 : ℝ) := by
      have h8 : (1 / 8 : ℝ) ^ (3 : ℝ) = 1 / 512 := by norm_num
      rw [h8, div_le_div_iff₀ hT_pos (by norm_num)]
      dsimp [A0]; linarith
    calc η = (A0 / (T : ℝ)) ^ (1 / 3 : ℝ) := rfl
      _ ≤ ((1 / 8 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hdiv_le (by norm_num)
      _ = (1 / 8 : ℝ) ^ ((3 : ℝ) * (1 / 3 : ℝ)) :=
          (Real.rpow_mul (by norm_num) _ _).symm
      _ = 1 / 8 := by norm_num
  have hη_lb : 1 / ((T : ℝ) + 1) ≤ η := by
    have hcube : (1 / ((T : ℝ) + 1)) ^ (3 : ℝ) ≤ A0 / (T : ℝ) := by
      rw [Real.rpow_ofNat]
      have h1 : (1 / ((T : ℝ) + 1)) ^ 3 ≤ 1 / ((T : ℝ) + 1) := by
        have hu0 : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
        have hu1 : 1 / ((T : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
        nlinarith [sq_nonneg (1 / ((T : ℝ) + 1))]
      have h2 : 1 / ((T : ℝ) + 1) ≤ A0 / (T : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hT_pos]
        nlinarith
      exact h1.trans h2
    calc 1 / ((T : ℝ) + 1)
        = ((1 / ((T : ℝ) + 1)) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ (A0 / (T : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hcube (by norm_num)
  obtain ⟨N, hN_def⟩ : ∃ N : ℕ, N = 64 * (T + 1) ^ 3 := ⟨64 * (T + 1) ^ 3, rfl⟩
  have hN : 0 < N := by rw [hN_def]; positivity
  have hh_ub : gridStep δ N ≤ 1 / (64 * ((T : ℝ) + 1) ^ 3) := by
    unfold gridStep
    have hN_cast : (N : ℝ) = 64 * ((T : ℝ) + 1) ^ 3 := by rw [hN_def]; push_cast; ring
    rw [hN_cast]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hh_le_δ : gridStep δ N ≤ δ := by
    have h1 : 1 / (64 * ((T : ℝ) + 1) ^ 3) ≤ δ := by
      dsimp [δ]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((T : ℝ) + 1)]
    exact hh_ub.trans h1
  have hh_le_var : ∀ p : ℝ, δ ≤ p → p ≤ 1 - δ → gridStep δ N ≤ 2 * η * p * (1 - p) := by
    intro p hp_lo hp_hi
    have hp_prod : δ * (1 - δ) ≤ p * (1 - p) := by nlinarith
    have hδ_prod : 1 / (4 * ((T : ℝ) + 1)) ≤ δ * (1 - δ) := by
      have h1mδ : 1 / 2 ≤ 1 - δ := by linarith
      have hmul := mul_le_mul_of_nonneg_left h1mδ hδ0.le
      have heq : δ * (1 / 2) = 1 / (4 * ((T : ℝ) + 1)) := by
        dsimp [δ]; field_simp; ring
      linarith
    have hvar_lb : 1 / (2 * ((T : ℝ) + 1) ^ 2) ≤ 2 * η * p * (1 - p) := by
      have h1 : 1 / (4 * ((T : ℝ) + 1)) ≤ p * (1 - p) := hδ_prod.trans hp_prod
      have hmul := mul_le_mul hη_lb h1 (by positivity) hη0.le
      calc 1 / (2 * ((T : ℝ) + 1) ^ 2)
          = 2 * ((1 / ((T : ℝ) + 1)) * (1 / (4 * ((T : ℝ) + 1)))) := by
            field_simp; ring
        _ ≤ 2 * (η * (p * (1 - p))) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * η * p * (1 - p) := by ring
    have hstep_le : 1 / (64 * ((T : ℝ) + 1) ^ 3) ≤ 1 / (2 * ((T : ℝ) + 1) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((T : ℝ) + 1)]
    exact hh_ub.trans (hstep_le.trans hvar_lb)
  refine ⟨algo2Forecaster F T δ hδ0 hδ1 M η N hN, ?_⟩
  intro ℓ β hβ hprop hbot htop hmix x y
  set A := algo2Forecaster F T δ hδ0 hδ1 M η N hN
  set B := 1024 * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
    Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) / β
  have hD_supp : ∀ t : Fin T, ∀ p ∈ (forecasts A x y t).wt.support,
      ∃ i : ℕ, ∃ hi : i ≤ N, p = gridUnit δ hδ0 hδ1 N hN i hi := by
    intro t p hp
    have hEVI := eviDist_spec hδ0 hδ1 hN hh_le_δ
      (testFn F δ M η N (cumExp F δ hδ0 hδ1 M η N hN t.val
        (fun s => (x ⟨s.val, s.isLt.trans t.isLt⟩, y ⟨s.val, s.isLt.trans t.isLt⟩))) (x t))
      (fun i hi yb => testFn_evi_cond hF_pos hδ0 hδ1 hM_pos hη0 hη1 hN _ (x t) hi yb)
    exact hEVI.1 p hp
  have hexp_t : ∀ t : Fin T,
      (forecasts A x y t).expect (fun p => ℓ p (y t)) =
        ((∑ p ∈ (forecasts A x y t).wt.support,
          (forecasts A x y t).wt p * Lval ℓ p (y t) : ℝ) : EReal) := by
    intro t
    refine FinDist.expect_eq_coe_sum _ _ _ fun p hp => ?_
    obtain ⟨i, hi, rfl⟩ := hD_supp t p hp
    have hbnd := gridPt_bounds hδ0 hδ1 hN hi
    exact (coe_Lval_eq (hbot _ _) (htop _ hbnd.2.2.1 hbnd.2.2.2.1 _)).symm
  have hsum_A : (∑ t : Fin T, (forecasts A x y t).expect (fun p => ℓ p (y t))) =
      ((∑ t : Fin T, ∑ p ∈ (forecasts A x y t).wt.support,
        (forecasts A x y t).wt p * Lval ℓ p (y t) : ℝ) : EReal) := by
    rw [Finset.sum_congr rfl (fun t _ => hexp_t t), EReal_sum_coe]
  unfold regret
  rw [hsum_A]
  refine EReal_coe_sub_biInf_le F _ B _ fun f₀ hf₀ => ?_
  by_cases htop_ex : ∃ t : Fin T, ℓ (f₀ (x t)) (y t) = ⊤
  · rcases htop_ex with ⟨t₀, ht₀⟩
    have htop_sum := EReal_sum_eq_top_of_exists_top Finset.univ (fun t : Fin T => ℓ (f₀ (x t)) (y t))
      (fun t _ => hbot _ _) ⟨t₀, Finset.mem_univ t₀, ht₀⟩
    rw [htop_sum]
    exact le_top
  · push_neg at htop_ex
    have hsum_f0 : (∑ t : Fin T, ℓ (f₀ (x t)) (y t)) =
        ((∑ t : Fin T, Lval ℓ (f₀ (x t)) (y t) : ℝ) : EReal) := by
      have hcongr : ∀ t ∈ (Finset.univ : Finset (Fin T)),
          ℓ (f₀ (x t)) (y t) = ((Lval ℓ (f₀ (x t)) (y t) : ℝ) : EReal) :=
        fun t _ => (coe_Lval_eq (hbot _ _) (htop_ex t)).symm
      rw [Finset.sum_congr rfl hcongr, EReal_sum_coe]
    rw [hsum_f0, EReal.coe_le_coe_iff]
    suffices hreal : (∑ t : Fin T, ∑ p ∈ (forecasts A x y t).wt.support,
        (forecasts A x y t).wt p * Lval ℓ p (y t)) -
        ∑ t : Fin T, Lval ℓ (f₀ (x t)) (y t) ≤ B by linarith
    set w := fun k => wStep ℓ δ hδ0 hδ1 N hN k
    have hm_le : ∑ k ∈ Finset.range N, w k ≤ M / β := by
      have h := sum_wStep_le hβ hprop hbot htop hmix hδ0 hδ1 hN
      have hrange : logit (1 - δ) - logit δ = M := logit_range_eq_M
      rwa [hrange] at h
    set Cround := 9 * η ^ 2 / β + (gridStep δ N / 2) * (M / β) +
      gridStep δ N / (β * δ ^ 2) + 2 * δ / β
    have hround : ∀ t : Fin T,
        (∑ p ∈ (forecasts A x y t).wt.support, (forecasts A x y t).wt p * Lval ℓ p (y t)) -
          Lval ℓ (f₀ (x t)) (y t) ≤
        (1 / η) * (∑ k ∈ Finset.range N, w k * stepExp δ η N (forecasts A x y t) (x t) (y t) f₀ k) +
          Cround := by
      intro t
      set Dt := forecasts A x y t
      set qt := f₀ (x t)
      set j := snapIdx δ N (qt : ℝ)
      have hj : j ≤ N := snapIdx_le δ N (qt : ℝ)
      have hclip := clip_loss_bound hβ hprop hbot htop hmix hδ0 hδ1 qt (y t) (htop_ex t)
      have hsnap_dist : |gridPt δ N j - clipVal δ (qt : ℝ)| ≤ gridStep δ N := by
        rw [abs_sub_comm]
        exact clipVal_sub_gridPt_snapIdx_le hδ0 hδ1 hN (qt : ℝ)
      have hsnap := snap_loss_bound hβ hprop hbot htop hmix (h := gridStep δ N) hδ0 hδ1
        (gridPt_bounds hδ0 hδ1 hN hj).1 (gridPt_bounds hδ0 hδ1 hN hj).2.1
        (clipVal_bounds hδ0 hδ1 (qt : ℝ)).1 (clipVal_bounds hδ0 hδ1 (qt : ℝ)).2.1
        hsnap_dist (y t)
      have hsnap_le : Lval ℓ (gridUnit δ hδ0 hδ1 N hN j hj) (y t) -
          Lval ℓ (mkUnit (clipVal δ (qt : ℝ)) (clipVal_bounds hδ0 hδ1 (qt : ℝ)).2.2.1
            (clipVal_bounds hδ0 hδ1 (qt : ℝ)).2.2.2) (y t) ≤ gridStep δ N / (β * δ ^ 2) :=
        (le_abs_self _).trans hsnap
      have hpt_bound : ∀ p ∈ Dt.wt.support,
          Lval ℓ p (y t) - Lval ℓ qt (y t) ≤
            (∑ k ∈ Finset.range N, w k *
              (bVal (midPt δ N k) (p : ℝ) (qt : ℝ) * (yVal (y t) - (p : ℝ)) -
                2 * η * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (qt : ℝ)) ^ 2)) +
            Cround := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := hD_supp t p hp
        set pi := gridUnit δ hδ0 hδ1 N hN i hi
        have hpi_val : (pi : ℝ) = gridPt δ N i := rfl
        have hvapprox := discrete_vLoss_approx hβ hprop hbot htop hδ0 hδ1 hN hi hj (y t)
        have hv_le : Lval ℓ pi (y t) - Lval ℓ (gridUnit δ hδ0 hδ1 N hN j hj) (y t) ≤
            (∑ k ∈ Finset.range N, w k *
              (vLoss (midPt δ N k) (gridPt δ N i) (y t) -
                vLoss (midPt δ N k) (gridPt δ N j) (y t))) +
            (gridStep δ N / 2) * ∑ k ∈ Finset.range N, w k := by
          have := (le_abs_self _).trans hvapprox
          linarith
        have hv_eq_bd : ∑ k ∈ Finset.range N, w k *
              (vLoss (midPt δ N k) (gridPt δ N i) (y t) -
                vLoss (midPt δ N k) (gridPt δ N j) (y t)) =
            ∑ k ∈ Finset.range N, w k *
              (bVal (midPt δ N k) (pi : ℝ) (qt : ℝ) * (yVal (y t) - (pi : ℝ)) -
                dVal (midPt δ N k) (pi : ℝ) (qt : ℝ)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkN := Finset.mem_range.mp hk
          rw [vLoss_diff_eq]
          have hbd := bVal_dVal_snap_eq hδ1 hN (pi : ℝ) (qt : ℝ) hkN
          rw [hpi_val] at hbd ⊢
          rw [← hbd.1, ← hbd.2]
        have hsplit_var : (∑ k ∈ Finset.range N, w k *
              (bVal (midPt δ N k) (pi : ℝ) (qt : ℝ) * (yVal (y t) - (pi : ℝ)) -
                dVal (midPt δ N k) (pi : ℝ) (qt : ℝ))) =
            (∑ k ∈ Finset.range N, w k *
              (bVal (midPt δ N k) (pi : ℝ) (qt : ℝ) * (yVal (y t) - (pi : ℝ)) -
                2 * η * (pi : ℝ) * (1 - (pi : ℝ)) *
                  (bVal (midPt δ N k) (pi : ℝ) (qt : ℝ)) ^ 2)) +
            (∑ k ∈ Finset.range N, w k *
              (2 * η * (pi : ℝ) * (1 - (pi : ℝ)) *
                  (bVal (midPt δ N k) (pi : ℝ) (qt : ℝ)) ^ 2 -
                dVal (midPt δ N k) (pi : ℝ) (qt : ℝ))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        have hp_bnds := gridPt_bounds hδ0 hδ1 hN hi
        have hvar_le := discrete_variance_cancel hβ hprop hbot htop hmix hδ0 hδ1 hN hη0 hη1
          hp_bnds.1 hp_bnds.2.1 (hh_le_var (gridPt δ N i) hp_bnds.1 hp_bnds.2.1)
          (q := (qt : ℝ))
        have hmid_err : (gridStep δ N / 2) * ∑ k ∈ Finset.range N, w k ≤
            (gridStep δ N / 2) * (M / β) :=
          mul_le_mul_of_nonneg_left hm_le (by linarith [gridStep_pos hδ1 hN])
        rw [hv_eq_bd, hsplit_var] at hv_le
        rw [hpi_val] at hv_le ⊢
        dsimp [Cround]
        linarith
      have hw_pt : ∀ p ∈ Dt.wt.support,
          Dt.wt p * (Lval ℓ p (y t) - Lval ℓ qt (y t)) ≤
          Dt.wt p * ((∑ k ∈ Finset.range N, w k *
              (bVal (midPt δ N k) (p : ℝ) (qt : ℝ) * (yVal (y t) - (p : ℝ)) -
                2 * η * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (qt : ℝ)) ^ 2)) +
            Cround) :=
        fun p hp => mul_le_mul_of_nonneg_left (hpt_bound p hp) (Dt.nonneg p)
      have hsum_wt := Finset.sum_le_sum hw_pt
      have hlhs_wt : ∑ p ∈ Dt.wt.support, Dt.wt p * (Lval ℓ p (y t) - Lval ℓ qt (y t)) =
          (∑ p ∈ Dt.wt.support, Dt.wt p * Lval ℓ p (y t)) - Lval ℓ qt (y t) := by
        have h1 : ∑ p ∈ Dt.wt.support, Dt.wt p * (Lval ℓ p (y t) - Lval ℓ qt (y t)) =
            (∑ p ∈ Dt.wt.support, Dt.wt p * Lval ℓ p (y t)) -
              (∑ p ∈ Dt.wt.support, Dt.wt p) * Lval ℓ qt (y t) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
        rw [h1, FinDist.sum_wt Dt, one_mul]
      have hrhs_wt : ∑ p ∈ Dt.wt.support, Dt.wt p * ((∑ k ∈ Finset.range N, w k *
              (bVal (midPt δ N k) (p : ℝ) (qt : ℝ) * (yVal (y t) - (p : ℝ)) -
                2 * η * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (qt : ℝ)) ^ 2)) +
            Cround) =
          (1 / η) * (∑ k ∈ Finset.range N, w k * stepExp δ η N Dt (x t) (y t) f₀ k) + Cround := by
        have h1 : ∑ p ∈ Dt.wt.support, Dt.wt p * ((∑ k ∈ Finset.range N, w k *
                (bVal (midPt δ N k) (p : ℝ) (qt : ℝ) * (yVal (y t) - (p : ℝ)) -
                  2 * η * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (qt : ℝ)) ^ 2)) +
              Cround) =
            (∑ p ∈ Dt.wt.support, ∑ k ∈ Finset.range N, Dt.wt p * w k *
              (bVal (midPt δ N k) (p : ℝ) (qt : ℝ) * (yVal (y t) - (p : ℝ)) -
                2 * η * (p : ℝ) * (1 - (p : ℝ)) * (bVal (midPt δ N k) (p : ℝ) (qt : ℝ)) ^ 2)) +
            (∑ p ∈ Dt.wt.support, Dt.wt p) * Cround := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [mul_add, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [h1, FinDist.sum_wt Dt, one_mul, Finset.sum_comm, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        unfold stepExp
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        dsimp [qt]
        field_simp [hη0.ne']
      linarith
    have hsum_T := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hround t)
    rw [Finset.sum_sub_distrib] at hsum_T
    have hrhs_T : (∑ t : Fin T, ((1 / η) *
          (∑ k ∈ Finset.range N, w k * stepExp δ η N (forecasts A x y t) (x t) (y t) f₀ k) +
          Cround)) =
        (1 / η) * (∑ k ∈ Finset.range N, w k *
          cumExp F δ hδ0 hδ1 M η N hN T (prefixHist x y T le_rfl) f₀ k) +
        (T : ℝ) * Cround := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, cumExp_eq_sum_forecasts]
    rw [hrhs_T] at hsum_T
    have hphi_T := phiPot_le_exp_one hF_pos hT hN hη0 hη1 hh_le_δ x y
    have hkl := discrete_potential_kl hF2 hT hN hβ hprop hbot htop hmix hphi_T hf₀
    have hterm1 : (1 / η) * (∑ k ∈ Finset.range N, w k *
        cumExp F δ hδ0 hδ1 M η N hN T (prefixHist x y T le_rfl) f₀ k) ≤
        5 * A0 / (β * η) := by
      calc (1 / η) * (∑ k ∈ Finset.range N, w k *
            cumExp F δ hδ0 hδ1 M η N hN T (prefixHist x y T le_rfl) f₀ k)
          ≤ (1 / η) * (5 * M * Real.log (F.card : ℝ) / β) :=
            mul_le_mul_of_nonneg_left hkl (by positivity)
        _ = 5 * A0 / (β * η) := by dsimp [A0]; ring
    have hTh_half : (T : ℝ) * (gridStep δ N / 2) ≤ 1 := by
      have h0 : (T : ℝ) * gridStep δ N ≤ (T : ℝ) * (1 / (64 * ((T : ℝ) + 1) ^ 3)) :=
        mul_le_mul_of_nonneg_left hh_ub hT_pos.le
      have h1 : (T : ℝ) * (1 / (64 * ((T : ℝ) + 1) ^ 3)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        nlinarith [sq_nonneg ((T : ℝ) + 1)]
      have hpos : 0 < (T : ℝ) * gridStep δ N := mul_pos hT_pos (gridStep_pos hδ1 hN)
      linarith
    have hTh_snap : (T : ℝ) * gridStep δ N / δ ^ 2 ≤ 1 := by
      have hδ_sq : δ ^ 2 = (4 * ((T : ℝ) + 1) ^ 2)⁻¹ := by
        have h1 : δ = 1 / (2 * (T : ℝ) + 2) := rfl
        rw [h1, div_pow, one_pow, one_div]
        congr 1; ring
      rw [hδ_sq, div_inv_eq_mul]
      have h1 : (T : ℝ) * gridStep δ N ≤ (T : ℝ) / (64 * ((T : ℝ) + 1) ^ 3) := by
        have := mul_le_mul_of_nonneg_left hh_ub hT_pos.le
        rwa [mul_one_div] at this
      have h2 : (T : ℝ) / (64 * ((T : ℝ) + 1) ^ 3) * (4 * ((T : ℝ) + 1) ^ 2) ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one (by positivity)]
        nlinarith [sq_nonneg ((T : ℝ) + 1)]
      exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2
    have hT2δ : (T : ℝ) * (2 * δ) ≤ 1 := by
      have heq : (T : ℝ) * (2 * δ) = (2 * (T : ℝ)) / (2 * (T : ℝ) + 2) := by
        have h1 : δ = 1 / (2 * (T : ℝ) + 2) := rfl
        rw [h1]; ring
      rw [heq, div_le_one (by positivity)]
      linarith
    have hTCround : (T : ℝ) * Cround ≤ (9 * (T : ℝ) * η ^ 2 + M + 2) / β := by
      have hc1 : (T : ℝ) * ((gridStep δ N / 2) * (M / β)) ≤ M / β := by
        calc (T : ℝ) * ((gridStep δ N / 2) * (M / β))
            = ((T : ℝ) * (gridStep δ N / 2)) * (M / β) := by ring
          _ ≤ 1 * (M / β) := mul_le_mul_of_nonneg_right hTh_half (by positivity)
          _ = M / β := one_mul _
      have hc2 : (T : ℝ) * (gridStep δ N / (β * δ ^ 2)) ≤ 1 / β := by
        have heq : (T : ℝ) * (gridStep δ N / (β * δ ^ 2)) =
            ((T : ℝ) * gridStep δ N / δ ^ 2) * (1 / β) := by
          field_simp [hβ.ne', hδ0.ne']
        rw [heq]
        exact (mul_le_mul_of_nonneg_right hTh_snap (by positivity)).trans_eq (one_mul _)
      have hc3 : (T : ℝ) * (2 * δ / β) ≤ 1 / β := by
        have heq : (T : ℝ) * (2 * δ / β) = ((T : ℝ) * (2 * δ)) * (1 / β) := by ring
        rw [heq]
        exact (mul_le_mul_of_nonneg_right hT2δ (by positivity)).trans_eq (one_mul _)
      have hdist_C : (T : ℝ) * Cround =
          9 * (T : ℝ) * η ^ 2 / β + (T : ℝ) * ((gridStep δ N / 2) * (M / β)) +
          (T : ℝ) * (gridStep δ N / (β * δ ^ 2)) + (T : ℝ) * (2 * δ / β) := by
        dsimp [Cround]; ring
      have hrhs_C : (9 * (T : ℝ) * η ^ 2 + M + 2) / β =
          9 * (T : ℝ) * η ^ 2 / β + M / β + 1 / β + 1 / β := by ring
      linarith
    have hstep1 : (∑ t : Fin T, ∑ p ∈ (forecasts A x y t).wt.support,
          (forecasts A x y t).wt p * Lval ℓ p (y t)) -
        ∑ t : Fin T, Lval ℓ (f₀ (x t)) (y t) ≤
        5 * A0 / (β * η) + (9 * (T : ℝ) * η ^ 2 + M + 2) / β :=
      hsum_T.trans (add_le_add hterm1 hTCround)
    exact hstep1.trans (rate_balance_bound hF2 hT hβ)

end Algo2

theorem theorem_1_2_proof : ∃ K : ℝ, 0 < K ∧ ∀ (X : Type u) (F : Finset (X → unitInterval)) (T : ℕ),
    ∃ A : Forecaster X T, ∀ (ℓ : Loss) (β : ℝ), 0 < β → IsProper ℓ →
      (∀ p y, ℓ p y ≠ ⊥) → (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) →
      IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool),
        regret ℓ F A x y ≤ ((K * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) / β : ℝ) : EReal) := by
  refine ⟨1024, by norm_num, ?_⟩
  intro X F T
  rcases eq_or_lt_of_le (Nat.zero_le T) with hT0 | hT_pos
  · subst hT0
    refine ⟨fun _ _ _ => FinDist.dirac halfPt, ?_⟩
    intro ℓ β hβ _ _ _ _ x y
    unfold regret
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, mul_zero, zero_add,
      Real.log_one, zero_mul, zero_div, EReal.coe_zero]
    rcases F.eq_empty_or_nonempty with rfl | ⟨f₀, hf₀⟩
    · simp [EReal.sub_top]
    · have hinf : (⨅ f ∈ F, (0 : EReal)) = 0 :=
        le_antisymm (iInf₂_le f₀ hf₀) (le_iInf₂ fun _ _ => le_rfl)
      rw [hinf]
      simp
  · rcases eq_or_lt_of_le (Nat.zero_le F.card) with hF0 | hF_pos
    · have hF_emp : F = ∅ := Finset.card_eq_zero.mp hF0.symm
      subst hF_emp
      refine ⟨fun _ _ _ => FinDist.dirac halfPt, ?_⟩
      intro ℓ β _ _ _ _ _ x y
      unfold regret
      simp [EReal.sub_top]
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hF_pos) with hF1 | hF2
      · obtain ⟨f₀, hf₀_eq⟩ := Finset.card_eq_one.mp hF1.symm
        subst hf₀_eq
        refine ⟨fun _ _ xt => FinDist.dirac (f₀ xt), ?_⟩
        intro ℓ β hβ _ hbot _ _ x y
        unfold regret
        have hexp_eq : ∀ t : Fin T,
            (forecasts (fun _ _ xt => FinDist.dirac (f₀ xt)) x y t).expect (fun p => ℓ p (y t)) =
              ℓ (f₀ (x t)) (y t) := by
          intro t
          unfold forecasts
          exact FinDist.expect_dirac (f₀ (x t)) (fun p => ℓ p (y t))
        rw [Finset.sum_congr rfl (fun t _ => hexp_eq t)]
        have hinf : (⨅ f ∈ ({f₀} : Finset (X → unitInterval)), ∑ t : Fin T, ℓ (f (x t)) (y t)) =
            ∑ t : Fin T, ℓ (f₀ (x t)) (y t) := by simp
        rw [hinf]
        have hrhs0 : (1024 * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
            Real.log (({f₀} : Finset (X → unitInterval)).card : ℝ) ^ (2 / 3 : ℝ) / β : ℝ) = 0 := by
          simp [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
        rw [hrhs0, EReal.coe_zero]
        exact EReal_sub_self_le_zero (EReal_sum_ne_bot Finset.univ _ (fun t _ => hbot _ _))
      · -- Now T ≥ 1 and F.card ≥ 2
        by_cases hlarge : (T : ℝ) ≤ 512 * (2 * Real.log (2 * (T : ℝ) + 1)) * Real.log (F.card : ℝ)
        · refine ⟨fun _ _ _ => FinDist.dirac halfPt, ?_⟩
          intro ℓ β hβ hprop hbot htop hmix x y
          unfold regret
          have hexp_half : ∀ t : Fin T,
              (forecasts (fun _ _ _ => FinDist.dirac halfPt) x y t).expect (fun p => ℓ p (y t)) =
                ((Lval ℓ halfPt (y t) : ℝ) : EReal) := by
            intro t
            unfold forecasts
            rw [FinDist.expect_dirac]
            exact (coe_Lval_eq (hbot _ _)
              (htop halfPt (by norm_num [halfPt, mkUnit]) (by norm_num [halfPt, mkUnit]) _)).symm
          rw [Finset.sum_congr rfl (fun t _ => hexp_half t), EReal_sum_coe]
          refine EReal_coe_sub_biInf_le F _ _ _ fun f₀ hf₀ => ?_
          by_cases htop_ex : ∃ t : Fin T, ℓ (f₀ (x t)) (y t) = ⊤
          · rcases htop_ex with ⟨t₀, ht₀⟩
            have htop_sum := EReal_sum_eq_top_of_exists_top Finset.univ
              (fun t : Fin T => ℓ (f₀ (x t)) (y t))
              (fun t _ => hbot _ _) ⟨t₀, Finset.mem_univ t₀, ht₀⟩
            rw [htop_sum]
            exact le_top
          · push_neg at htop_ex
            have hsum_f0 : (∑ t : Fin T, ℓ (f₀ (x t)) (y t)) =
                ((∑ t : Fin T, Lval ℓ (f₀ (x t)) (y t) : ℝ) : EReal) := by
              rw [Finset.sum_congr rfl (fun t _ => (coe_Lval_eq (hbot _ _) (htop_ex t)).symm),
                EReal_sum_coe]
            rw [hsum_f0, EReal.coe_le_coe_iff]
            have hpt : ∀ t ∈ (Finset.univ : Finset (Fin T)),
                Lval ℓ halfPt (y t) - Lval ℓ (f₀ (x t)) (y t) ≤ 1 / β :=
              fun t _ => half_point_loss_bound hβ hprop hbot htop hmix (f₀ (x t)) (y t) (htop_ex t)
            have hsum_diff : (∑ t : Fin T, Lval ℓ halfPt (y t)) -
                ∑ t : Fin T, Lval ℓ (f₀ (x t)) (y t) ≤ (T : ℝ) / β := by
              have h1 := Finset.sum_le_sum hpt
              rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul, mul_one_div] at h1
              exact h1
            have hT_cast_pos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT_pos
            have hLT : 1 < Real.log (2 * (T : ℝ) + 1) := log_two_T_add_one_gt_one hT_pos
            have hLF : 1 / 2 < Real.log (F.card : ℝ) := log_card_gt_half hF2
            have hT_split : (T : ℝ) = (T : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ) := by
              rw [← Real.rpow_add hT_cast_pos]; norm_num
            have hT23 : (T : ℝ) ^ (2 / 3 : ℝ) ≤
                1024 * Real.log (2 * (T : ℝ) + 1) * Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) := by
              have hle1024 : (T : ℝ) ≤
                  (1024 * Real.log (2 * (T : ℝ) + 1)) * Real.log (F.card : ℝ) := by linarith
              calc (T : ℝ) ^ (2 / 3 : ℝ)
                  ≤ ((1024 * Real.log (2 * (T : ℝ) + 1)) * Real.log (F.card : ℝ)) ^ (2 / 3 : ℝ) :=
                    Real.rpow_le_rpow hT_cast_pos.le hle1024 (by norm_num)
                _ = (1024 * Real.log (2 * (T : ℝ) + 1)) ^ (2 / 3 : ℝ) *
                      Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) :=
                    Real.mul_rpow (by linarith) (by linarith)
                _ ≤ (1024 * Real.log (2 * (T : ℝ) + 1)) ^ (1 : ℝ) *
                      Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) :=
                    mul_le_mul_of_nonneg_right
                      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
                      (by positivity)
                _ = 1024 * Real.log (2 * (T : ℝ) + 1) * Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) := by
                    rw [Real.rpow_one]
            have hT_le_num : (T : ℝ) ≤ 1024 * Real.log (2 * (T : ℝ) + 1) *
                (T : ℝ) ^ (1 / 3 : ℝ) * Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) := by
              have hmul := mul_le_mul_of_nonneg_left hT23
                (Real.rpow_pos_of_pos hT_cast_pos (1 / 3 : ℝ)).le
              calc (T : ℝ) = (T : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ) := hT_split
                _ ≤ (T : ℝ) ^ (1 / 3 : ℝ) * (1024 * Real.log (2 * (T : ℝ) + 1) *
                      Real.log (F.card : ℝ) ^ (2 / 3 : ℝ)) := hmul
                _ = 1024 * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
                      Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) := by ring
            have hdiv := div_le_div_of_nonneg_right hT_le_num hβ.le
            linarith
        · push_neg at hlarge
          exact algo2_case_bound hF2 hT_pos hlarge

end OmniMix_Theorem12_Proof

open OmniMix

theorem solution : ∃ K : ℝ, 0 < K ∧ ∀ (X : Type u) (F : Finset (X → unitInterval)) (T : ℕ),
    ∃ A : Forecaster X T, ∀ (ℓ : Loss) (β : ℝ), 0 < β → IsProper ℓ →
      (∀ p y, ℓ p y ≠ ⊥) → (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) →
      IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool),
        regret ℓ F A x y ≤ ((K * Real.log (2 * (T : ℝ) + 1) * (T : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (F.card : ℝ) ^ (2 / 3 : ℝ) / β : ℝ) : EReal) :=
  OmniMix_Theorem12_Proof.theorem_1_2_proof

