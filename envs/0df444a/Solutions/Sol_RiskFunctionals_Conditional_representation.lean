-- Prove2me | solution 1 for RiskFunctionals.Conditional.representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T04:00:41.789964+00:00
-- url     : https://prove2.me/submissions/b02b3bff-a54f-44a0-8d83-1df17725a57c

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_Mappings
import Theorems.Thm_RiskFunctionals_Conditional_fenchel_step

open MeasureTheory Filter Topology ENNReal

set_option linter.unusedSectionVars false

namespace CondRepRed

open RiskFunctionals.Conditional

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
  {p : ENNReal} [hp1 : Fact (1 ≤ p)]

lemma integrable_Lp (Y : Lp ℝ p P) : Integrable (Y : Ω → ℝ) P :=
  (Lp.memLp Y).integrable hp1.out

lemma hB_mono (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (B : Set Ω) (Y Y' : Lp ℝ p P) (hle : ∀ᵐ ω ∂P, Y ω ≤ Y' ω) :
    ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P ≤ ∫ ω in B, (A Y' : Lp ℝ p P) ω ∂P :=
  setIntegral_mono_ae (integrable_Lp _).integrableOn (integrable_Lp _).integrableOn
    (hA.monotone Y Y' hle)

lemma hB_translation (A : Lp ℝ p P → lpMeas ℝ ℝ m p P)
    (hA : IsConditionalAcceptabilityMapping A) (B : Set Ω) (Y : Lp ℝ p P)
    (Y₁ : lpMeas ℝ ℝ m p P) :
    ∫ ω in B, (A (Y + (Y₁ : Lp ℝ p P)) : Lp ℝ p P) ω ∂P
      = ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P + ∫ ω in B, (Y₁ : Lp ℝ p P) ω ∂P := by
  rw [← integral_add (integrable_Lp _).integrableOn (integrable_Lp _).integrableOn]
  exact integral_congr_ae (ae_restrict_of_ae (hA.translation Y Y₁))

lemma integral_indicatorConstLp_mul {s : Set Ω} (hs : MeasurableSet[mΩ] s) (hμs : P s ≠ ∞)
    (c : ℝ) (g : Ω → ℝ) :
    ∫ x, (indicatorConstLp p hs hμs c : Ω → ℝ) x * g x ∂P = c * ∫ x in s, g x ∂P := by
  have h1 : (indicatorConstLp p hs hμs c : Ω → ℝ) =ᵐ[P] s.indicator (fun _ => c) :=
    indicatorConstLp_coeFn
  rw [← integral_const_mul, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [h1] with x h1
  rw [h1]
  by_cases hx : x ∈ s <;> simp [hx]

lemma pairing_zero {q : ENNReal} (Z : Lp ℝ q P) : pairing (0 : Lp ℝ p P) Z = 0 := by
  unfold pairing
  rw [integral_eq_zero_of_ae]
  filter_upwards [Lp.coeFn_zero ℝ p P] with x hx
  rw [hx]
  simp

lemma pairing_smul {q : ENNReal} (t : ℝ) (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (t • Y) Z = t * pairing Y Z := by
  unfold pairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul t Y] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- If `t * a ≥ L` for all `t > 0` then `a ≥ 0`. -/
lemma nonneg_of_forall_pos {a L : ℝ} (h : ∀ t : ℝ, 0 < t → L ≤ t * a) : 0 ≤ a := by
  by_contra hneg
  push_neg at hneg
  have ht : 0 < (|L| + 1) / (-a) := div_pos (by positivity) (by linarith)
  have := h _ ht
  rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self (ne_of_lt hneg), mul_one] at this
  linarith [le_abs_self L, neg_abs_le L]

/-- If `t * a ≥ L` for all real `t` then `a = 0`. -/
lemma eq_zero_of_forall {a L : ℝ} (h : ∀ t : ℝ, L ≤ t * a) : a = 0 := by
  have h1 : 0 ≤ a := nonneg_of_forall_pos (fun t _ => h t)
  have h2 : 0 ≤ -a := nonneg_of_forall_pos (fun t _ => by have := h (-t); linarith)
  linarith

lemma exists_lower_of_ne_bot {d : EReal} (hd : d ≠ ⊥) : ∃ L : ℝ, (L : EReal) ≤ d := by
  by_contra hcon
  push_neg at hcon
  exact hd ((EReal.eq_bot_iff_forall_lt d).2 hcon)

/-- A dual element with `A_B(Z) > -∞` is a conditional density. -/
lemma density_of_ne_bot (hm : m ≤ mΩ) {q : ENNReal} [p.HolderConjugate q]
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (B : Set Ω) (hB : MeasurableSet[m] B) (Z : Lp ℝ q P)
    (hd : dualFunction A B Z ≠ ⊥) : IsConditionalDensity m P B Z := by
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨L, hL⟩ := exists_lower_of_ne_bot hd
  set h : Lp ℝ p P → ℝ := fun Y => ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P with hh
  have hLX : ∀ X : Lp ℝ p P, L ≤ pairing X Z - h X := by
    intro X
    have := hL.trans (iInf_le (fun X => ((pairing X Z - h X : ℝ) : EReal)) X)
    exact EReal.coe_le_coe_iff.mp this
  have hZint : Integrable (Z : Ω → ℝ) P := (Lp.memLp Z).integrable (Fact.out)
  refine ⟨?_, ?_⟩
  · -- nonnegativity
    refine ae_nonneg_of_forall_setIntegral_nonneg hZint (fun s hs _ => ?_)
    refine nonneg_of_forall_pos (L := L + h 0) (fun t ht => ?_)
    have hX := hLX (indicatorConstLp p hs (measure_ne_top P s) t)
    have hmono : h 0 ≤ h (indicatorConstLp p hs (measure_ne_top P s) t) := by
      apply hB_mono A hA B
      have h3 : (indicatorConstLp p hs (measure_ne_top P s) t : Ω → ℝ) =ᵐ[P]
          s.indicator fun _ => t := indicatorConstLp_coeFn
      filter_upwards [Lp.coeFn_zero ℝ p P, h3] with ω h1 h3
      rw [h1, h3]
      exact Set.indicator_nonneg (fun _ _ => ht.le) ω
    have hp : pairing (indicatorConstLp p hs (measure_ne_top P s) t) Z = t * ∫ x in s, Z x ∂P :=
      integral_indicatorConstLp_mul hs _ t _
    rw [hp] at hX
    linarith
  · -- conditional expectation
    refine (ae_eq_condExp_of_forall_setIntegral_eq hm hZint (fun s _ _ => ?_) (fun s hs _ => ?_)
      ((@stronglyMeasurable_const _ _ m _ _).indicator hB).aestronglyMeasurable).symm
    · exact (integrable_const (1:ℝ)).integrableOn.indicator (hm B hB)
    · have hint : ∀ t : ℝ, L + h 0 ≤ t * ((∫ x in s, Z x ∂P) -
          ∫ x in s, B.indicator (fun _ => (1:ℝ)) x ∂P) := by
        intro t
        let Y₁ : lpMeas ℝ ℝ m p P :=
          ⟨indicatorConstLp p (hm s hs) (measure_ne_top P s) t,
            mem_lpMeas_indicatorConstLp hm hs (measure_ne_top P s)⟩
        have hX := hLX (Y₁ : Lp ℝ p P)
        have htr := hB_translation A hA B 0 Y₁
        rw [zero_add] at htr
        have hY₁ : ((Y₁ : Lp ℝ p P) : Ω → ℝ) =
            (indicatorConstLp p (hm s hs) (measure_ne_top P s) t : Ω → ℝ) := rfl
        have hp : pairing (Y₁ : Lp ℝ p P) Z = t * ∫ x in s, Z x ∂P := by
          unfold pairing
          rw [hY₁]
          exact integral_indicatorConstLp_mul (hm s hs) _ t _
        have hB1 : ∫ ω in B, (Y₁ : Lp ℝ p P) ω ∂P =
            t * ∫ x in s, B.indicator (fun _ => (1:ℝ)) x ∂P := by
          rw [hY₁, ← integral_indicatorConstLp_mul (p := p) (hm s hs) (measure_ne_top P s) t _,
            ← integral_indicator (hm B hB)]
          apply integral_congr_ae
          filter_upwards with x
          by_cases hx : x ∈ B <;> simp [hx]
        have : h (Y₁ : Lp ℝ p P) = h 0 + t * ∫ x in s, B.indicator (fun _ => (1:ℝ)) x ∂P := by
          simp only [h]; rw [htr, hB1]
        rw [hp, this] at hX
        linarith
      have := eq_zero_of_forall hint
      linarith

end CondRepRed

open RiskFunctionals.Conditional CondRepRed

theorem solution {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) [p.HolderConjugate q]
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (husc : IsUpperSemicontinuousMapping A) :
    (∀ (Y : Lp ℝ p P) (B : Set Ω), MeasurableSet[m] B →
      ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
        = ⨅ (Z : Lp ℝ q P) (_ : IsConditionalDensity m P B Z),
            ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z) ∧
    (IsPositivelyHomogeneous A →
      ∀ B : Set Ω, MeasurableSet[m] B →
        (∀ Z ∈ dualSet q A B, dualFunction A B Z = 0) ∧
        (∀ Z : Lp ℝ q P, Z ∉ dualSet q A B → dualFunction A B Z = ⊥) ∧
        (∀ Y : Lp ℝ p P,
          ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
            = ⨅ Z ∈ dualSet q A B, ⨅ (_ : IsConditionalDensity m P B Z),
                ((pairing Y Z : ℝ) : EReal))) := by
  have part1 : ∀ (Y : Lp ℝ p P) (B : Set Ω), MeasurableSet[m] B →
      ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
        = ⨅ (Z : Lp ℝ q P) (_ : IsConditionalDensity m P B Z),
            ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z := by
    intro Y B hB
    rw [fenchel_step hm P p q hp A hA husc B hB Y]
    apply iInf_congr
    intro Z
    by_cases hdens : IsConditionalDensity m P B Z
    · rw [iInf_pos hdens]
    · rw [iInf_neg hdens]
      have hbot : dualFunction A B Z = ⊥ := by
        by_contra hne
        exact hdens (density_of_ne_bot hm A hA B hB Z hne)
      rw [hbot, EReal.coe_sub_bot]
  refine ⟨part1, fun hPH B hB => ?_⟩
  set h : Lp ℝ p P → ℝ := fun Y => ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P with hh
  -- `h 0 = 0`
  have hA0 : ∀ᵐ ω ∂P, (A 0 : Lp ℝ p P) ω = 0 := by
    filter_upwards [hPH 0 2 two_pos] with ω hω
    rw [smul_zero] at hω
    linarith
  have h0 : h 0 = 0 := by
    simp only [h]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae hA0)
  have hscale : ∀ (t : ℝ), 0 < t → ∀ Y : Lp ℝ p P, h (t • Y) = t * h Y := by
    intro t ht Y
    simp only [h]
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_restrict_of_ae (hPH Y t ht))
  have hle0 : ∀ Z : Lp ℝ q P, dualFunction A B Z ≤ 0 := by
    intro Z
    refine (iInf_le (fun X => ((pairing X Z - h X : ℝ) : EReal)) 0).trans ?_
    rw [pairing_zero, h0, sub_zero, EReal.coe_zero]
  have hS1 : ∀ Z ∈ dualSet q A B, dualFunction A B Z = 0 :=
    fun Z hZ => le_antisymm (hle0 Z) hZ
  have hS2 : ∀ Z : Lp ℝ q P, Z ∉ dualSet q A B → dualFunction A B Z = ⊥ := by
    intro Z hZ
    have hlt : dualFunction A B Z < 0 := lt_of_not_ge hZ
    obtain ⟨Y, hY⟩ := iInf_lt_iff.mp hlt
    have hv : pairing Y Z - h Y < 0 := by exact_mod_cast hY
    rw [EReal.eq_bot_iff_forall_lt]
    intro M
    set v := pairing Y Z - h Y with hvdef
    set t := (|M| + 1) / (-v) with htdef
    have ht : 0 < t := div_pos (by positivity) (by linarith)
    have htv : t * v = -(|M| + 1) := by
      rw [htdef, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self (ne_of_lt hv), mul_one]
    have hterm : pairing (t • Y) Z - h (t • Y) = t * v := by
      rw [pairing_smul, hscale t ht, hvdef]; ring
    calc dualFunction A B Z ≤ ((pairing (t • Y) Z - h (t • Y) : ℝ) : EReal) :=
          iInf_le (fun X => ((pairing X Z - h X : ℝ) : EReal)) (t • Y)
      _ < (M : EReal) := by
          rw [EReal.coe_lt_coe_iff, hterm, htv]
          linarith [neg_abs_le M]
  refine ⟨hS1, hS2, fun Y => ?_⟩
  rw [part1 Y B hB]
  apply iInf_congr
  intro Z
  by_cases hS : Z ∈ dualSet q A B
  · rw [iInf_pos hS, hS1 Z hS, sub_zero]
  · rw [iInf_neg hS, hS2 Z hS, EReal.coe_sub_bot]
    simp
