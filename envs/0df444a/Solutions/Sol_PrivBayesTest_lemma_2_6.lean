-- Prove2me | solution 1 for PrivBayesTest.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T20:35:38.127237+00:00
-- url     : https://prove2.me/submissions/3caf6c87-e059-4058-bbaa-d7c112da958c

import Mathlib
import Definitions.Def_PrivBayesTest_lapLaw
import Definitions.Def_PrivBayesTest_klTvValue
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace

namespace Community0
noncomputable section
open MeasureTheory
section Moments
open ProbabilityTheory Filter Set
open scoped Topology
/-- **Local moment generating function of the Laplace law**: for `β > 0` and `|w| < β`, the
function `s ↦ e^{ws} (β/2) e^{-β|s|}` is integrable with integral `β² / (β² - w²)`. -/
theorem solution {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    MeasureTheory.Integrable (fun s => Real.exp (w * s) * FunctionalInequalities.Probability.Line.laplaceDensity β s) ∧
      ∫ s, Real.exp (w * s) * FunctionalInequalities.Probability.Line.laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2) := by
    have hw₁ : -β < w := (abs_lt.mp hw).1
    have hw₂ : w < β := (abs_lt.mp hw).2
    have hnegRate : w - β < 0 := by linarith
    have hposRate : 0 < w + β := by linarith
    have hβw : 0 < β - w := by linarith
    have hwβ : 0 < β + w := by linarith
    have hden : 0 < β ^ 2 - w ^ 2 := by
      nlinarith [mul_pos hβw hwβ]

    let f : ℝ → ℝ :=
      fun s => Real.exp (w * s) * FunctionalInequalities.Probability.Line.laplaceDensity β s

    have hpos_eq :
        ∀ s ∈ Set.Ioi (0 : ℝ),
          f s = (β / 2) * Real.exp ((w - β) * s) := by
      intro s hs
      dsimp [f, FunctionalInequalities.Probability.Line.laplaceDensity]
      rw [abs_of_pos hs]
      calc
        Real.exp (w * s) * (β / 2 * Real.exp (-(β * s))) =
            β / 2 * (Real.exp (w * s) * Real.exp (-(β * s))) := by
              ring
        _ = β / 2 * Real.exp (w * s + -(β * s)) := by
              rw [← Real.exp_add]
        _ = β / 2 * Real.exp ((w - β) * s) := by
              congr 2
              ring

    have hneg_eq :
        ∀ s ∈ Set.Iic (0 : ℝ),
          f s = (β / 2) * Real.exp ((w + β) * s) := by
      intro s hs
      dsimp [f, FunctionalInequalities.Probability.Line.laplaceDensity]
      rw [abs_of_nonpos hs]
      calc
        Real.exp (w * s) * (β / 2 * Real.exp (-(β * -s))) =
            β / 2 * (Real.exp (w * s) * Real.exp (-(β * -s))) := by
              ring
        _ = β / 2 * Real.exp (w * s + -(β * -s)) := by
              rw [← Real.exp_add]
        _ = β / 2 * Real.exp ((w + β) * s) := by
              congr 2
              ring

    have hpos_exp :
        MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((w - β) * s)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := w - β) hnegRate 0

    have hneg_exp :
        MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((w + β) * s)) (Set.Iic 0) :=
      integrableOn_exp_mul_Iic (a := w + β) hposRate 0

    have hpos : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
      have h := hpos_exp.const_mul (β / 2)
      apply h.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hpos_eq s hs).symm

    have hneg : MeasureTheory.IntegrableOn f (Set.Iic 0) := by
      have h := hneg_exp.const_mul (β / 2)
      apply h.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with s hs
      exact (hneg_eq s hs).symm

    have hglob : MeasureTheory.Integrable f := by
      have h := hneg.union hpos
      simpa [Set.Iic_union_Ioi] using h

    have hpos_val :
        ∫ s in Set.Ioi (0 : ℝ), f s =
          (β / 2) * (1 / (β - w)) := by
      calc
        ∫ s in Set.Ioi (0 : ℝ), f s =
            ∫ s in Set.Ioi (0 : ℝ),
              (β / 2) * Real.exp ((w - β) * s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
          exact hpos_eq s hs
        _ = (β / 2) *
            ∫ s in Set.Ioi (0 : ℝ), Real.exp ((w - β) * s) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul
              (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (β / 2) (fun s : ℝ => Real.exp ((w - β) * s)))
        _ = (β / 2) * (1 / (β - w)) := by
          rw [integral_exp_mul_Ioi (a := w - β) hnegRate (0 : ℝ)]
          simp only [mul_zero, Real.exp_zero]
          field_simp [ne_of_lt hnegRate]
          ring

    have hneg_val :
        ∫ s in Set.Iic (0 : ℝ), f s =
          (β / 2) * (1 / (β + w)) := by
      calc
        ∫ s in Set.Iic (0 : ℝ), f s =
            ∫ s in Set.Iic (0 : ℝ),
              (β / 2) * Real.exp ((w + β) * s) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem measurableSet_Iic] with s hs
          exact hneg_eq s hs
        _ = (β / 2) *
            ∫ s in Set.Iic (0 : ℝ), Real.exp ((w + β) * s) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul
              (μ := MeasureTheory.volume.restrict (Set.Iic (0 : ℝ)))
              (β / 2) (fun s : ℝ => Real.exp ((w + β) * s)))
        _ = (β / 2) * (1 / (β + w)) := by
          rw [integral_exp_mul_Iic (a := w + β) hposRate (0 : ℝ)]
          simp only [mul_zero, Real.exp_zero]
          field_simp [ne_of_gt hposRate]
          ring

    refine ⟨?_, ?_⟩
    · simpa [f] using hglob
    · change ∫ s, f s = β ^ 2 / (β ^ 2 - w ^ 2)
      have hsplit :=
        MeasureTheory.integral_add_compl
          (μ := MeasureTheory.volume) (s := Set.Iic (0 : ℝ))
          measurableSet_Iic hglob
      rw [← hsplit, Set.compl_Iic, hneg_val, hpos_val]
      field_simp [ne_of_gt hβw, ne_of_gt hwβ, ne_of_gt hden]
      ring

end Moments
end
end Community0

noncomputable def FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_readable := @Community0.solution

namespace Community1
noncomputable section
open MeasureTheory
section Moments
open ProbabilityTheory Filter Set
open scoped Topology
/-- The law-level moment generating function on `|w| < β`. -/
theorem solution {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (FunctionalInequalities.Probability.Line.laplaceMeasure β) ∧
      mgf id (FunctionalInequalities.Probability.Line.laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s)) := by
    unfold FunctionalInequalities.Probability.Line.laplaceDensity
    fun_prop
  have hfin : ∀ᵐ s : ℝ ∂volume, ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hnn (s : ℝ) : 0 ≤ FunctionalInequalities.Probability.Line.laplaceDensity β s := by
    unfold FunctionalInequalities.Probability.Line.laplaceDensity
    positivity
  have h := FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_readable hβ hw
  constructor
  · unfold FunctionalInequalities.Probability.Line.laplaceMeasure
    rw [integrable_withDensity_iff hm hfin]
    simpa only [ENNReal.toReal_ofReal (hnn _)] using h.1
  · change (∫ s : ℝ, Real.exp (w * id s) ∂volume.withDensity
      (fun s => ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
    simpa only [id_eq, ENNReal.toReal_ofReal (hnn _), smul_eq_mul, mul_comm] using h.2

end Moments
end
end Community1

open MeasureTheory ProbabilityTheory
namespace PrivateLaplaceMoment
noncomputable section

lemma laplace_eq (s : ℝ) (hs : 0 < s) :
    PrivLearn.Generic.laplace s = FunctionalInequalities.Probability.Line.laplaceMeasure s⁻¹ := by
  unfold PrivLearn.Generic.laplace FunctionalInequalities.Probability.Line.laplaceMeasure
  congr 1
  funext x
  congr 1
  unfold FunctionalInequalities.Probability.Line.laplaceDensity
  have he : -|x| / s = -(s⁻¹ * |x|) := by ring
  rw [he]
  ring


lemma laplace_rate_moment (β t : ℝ) (hβ : 0 < β) (ht : |t| < β) :
    Integrable (fun x => Real.exp (t*x)) (PrivLearn.Generic.laplace β⁻¹) ∧
    (∫ x, Real.exp (t*x) ∂PrivLearn.Generic.laplace β⁻¹) = β^2/(β^2-t^2) := by
  rw [laplace_eq _ (inv_pos.mpr hβ),inv_inv]
  simpa only [mgf,id_eq] using Community1.solution hβ ht

lemma exp_integrable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (c : ℝ) :
    Integrable (fun x => Real.exp (c*f x)) P := by
  obtain ⟨C,hC⟩ := hb
  apply (integrable_const (Real.exp (|c| * C))).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc c*f x ≤ |c*f x| := le_abs_self _
       _ = |c| * |f x| := abs_mul _ _
       _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma exp_jensen {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (c γ : ℝ) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) :
    (∫ x, Real.exp (γ*c*f x) ∂P) ≤ (∫ x, Real.exp (c*f x) ∂P)^γ := by
  have he : (fun x => (Real.exp (c*f x))^γ) = (fun x => Real.exp (γ*c*f x)) := by
    funext x
    rw [← Real.exp_mul]
    congr 1
    ring
  have hi := exp_integrable P f hf hb (γ*c)
  have h := (Real.concaveOn_rpow hγ.1.le hγ.2.le).le_map_integral
    (Real.continuous_rpow_const hγ.1.le).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (c*f x)).le)
    (exp_integrable P f hf hb c) (by simpa only [Function.comp_def,he] using hi)
  simpa only [he] using h

lemma sample_bound {X : Type*} [MeasurableSpace X] (f : X → ℝ)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (n : ℕ) :
    ∃ C : ℝ, ∀ x : Fin n → X, |∑ i, f (x i)| ≤ C := by
  obtain ⟨C,hC⟩ := hb
  refine ⟨n*C,fun x => ?_⟩
  calc |∑ i, f (x i)| ≤ ∑ i, |f (x i)| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => hC (x i)
       _ = n*C := by simp

lemma sample_moment {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (n : ℕ) (c : ℝ) :
    Integrable (fun x : Fin n → X => Real.exp (c * ∑ i, f (x i))) (Measure.pi fun _ => P) ∧
    (∫ x : Fin n → X, Real.exp (c * ∑ i, f (x i)) ∂Measure.pi (fun _ => P)) =
      (∫ x, Real.exp (c*f x) ∂P)^n := by
  constructor
  · exact exp_integrable _ _ (by fun_prop) (sample_bound f hb n) c
  · have he : (fun x : Fin n → X => Real.exp (c * ∑ i, f (x i))) =
        (fun x => ∏ i, Real.exp (c*f (x i))) := by
      funext x
      rw [Finset.mul_sum,Real.exp_sum]
    rw [he]
    simpa using (integral_fintype_prod_eq_prod (μ := fun _ : Fin n => P)
      (fun _ : Fin n => fun x : X => Real.exp (c*f x)))

lemma lapLaw_moment {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (n : ℕ) (β t : ℝ) (hβ : 0 < β) (ht : |t| < β) :
    Integrable (fun y => Real.exp (t*y)) (PrivBayesTest.lapLaw f β⁻¹ n P) ∧
    (∫ y, Real.exp (t*y) ∂PrivBayesTest.lapLaw f β⁻¹ n P) =
      (∫ x, Real.exp (t*f x) ∂P)^n * (β^2/(β^2-t^2)) := by
  have hn := laplace_rate_moment β t hβ ht
  have hs := sample_moment P f hf hb n t
  letI : IsProbabilityMeasure (PrivLearn.Generic.laplace β⁻¹) := by
    rw [laplace_eq _ (inv_pos.mpr hβ),inv_inv]
    exact FunctionalInequalities.Probability.Line.isProbabilityMeasure_laplaceMeasure hβ
  have he : (fun p : (Fin n → X) × ℝ => Real.exp (t*((∑ i, f (p.1 i))+p.2))) =
      (fun p => Real.exp (t*∑ i,f (p.1 i))*Real.exp (t*p.2)) := by
    funext p
    rw [mul_add,Real.exp_add]
  constructor
  · unfold PrivBayesTest.lapLaw
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    change Integrable (fun p : (Fin n → X) × ℝ => Real.exp (t*((∑ i,f (p.1 i))+p.2))) _
    rw [he]
    exact hs.1.mul_prod hn.1
  · unfold PrivBayesTest.lapLaw
    rw [integral_map (by fun_prop) (by fun_prop)]
    change (∫ p : (Fin n → X) × ℝ, Real.exp (t*((∑ i,f (p.1 i))+p.2)) ∂_) = _
    rw [he,integral_prod_mul (fun x : Fin n → X => Real.exp (t*∑ i,f (x i)))
      (fun z : ℝ => Real.exp (t*z)),hs.2,hn.2]

lemma exp_moment_pos {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (c : ℝ) :
    0 < ∫ x, Real.exp (c*f x) ∂P := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (exp_integrable P f hf hb c)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma lapLaw_bound {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (n : ℕ) (β c γ : ℝ) (hβ : 0 < β) (hc : |c| ≤ β) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (γ*c*y)) ∂PrivBayesTest.lapLaw f β⁻¹ n P) ≤
      ENNReal.ofReal (Real.exp (γ*n*Real.log (∫ x,Real.exp (c*f x) ∂P))/(1-γ^2)) := by
  have hab : |γ*c| ≤ γ*β := by
    rw [abs_mul,abs_of_pos hγ.1]
    exact mul_le_mul_of_nonneg_left hc hγ.1.le
  have ht : |γ*c| < β := hab.trans_lt (by nlinarith [mul_pos hβ (sub_pos.mpr hγ.2)])
  have hden : 0 < β^2-(γ*c)^2 := by
    nlinarith [mul_pos (sub_pos.mpr ht) (add_pos_of_pos_of_nonneg hβ (abs_nonneg (γ*c))),sq_abs (γ*c)]
  have hgden : 0 < 1-γ^2 := by nlinarith [mul_pos hγ.1 (sub_pos.mpr hγ.2)]
  have hnoise : β^2/(β^2-(γ*c)^2) ≤ 1/(1-γ^2) := by
    apply (div_le_div_iff₀ hden hgden).mpr
    have hh := mul_self_le_mul_self (abs_nonneg (γ*c)) hab
    nlinarith [sq_abs (γ*c)]
  have hlaw := lapLaw_moment P f hf hb n β (γ*c) hβ ht
  rw [← ofReal_integral_eq_lintegral_ofReal hlaw.1
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  have hj := exp_jensen (Measure.pi fun _ : Fin n => P) (fun x => ∑ i,f (x i))
    (by fun_prop) (sample_bound f hb n) c γ hγ
  rw [(sample_moment P f hf hb n c).2] at hj
  have hM := exp_moment_pos P f hf hb c
  have he : ((∫ x,Real.exp (c*f x) ∂P)^n)^γ =
      Real.exp (γ*n*Real.log (∫ x,Real.exp (c*f x) ∂P)) := by
    rw [Real.rpow_def_of_pos (pow_pos hM n),Real.log_pow]
    congr 1
    ring
  rw [he] at hj
  rw [(sample_moment P f hf hb n (γ*c)).2] at hj
  rw [hlaw.2]
  calc (∫ x, Real.exp (γ*c*f x) ∂P)^n * (β^2/(β^2-(γ*c)^2)) ≤
      Real.exp (γ*n*Real.log (∫ x,Real.exp (c*f x) ∂P)) * (1/(1-γ^2)) :=
        mul_le_mul hj hnoise (div_nonneg (sq_nonneg _) hden.le) (Real.exp_pos _).le
       _ = _ := by ring

end
end PrivateLaplaceMoment

theorem solution {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ℓbar : X → ℝ)
    (hℓm : Measurable ℓbar) (hℓb : ∃ C : ℝ, ∀ x, |ℓbar x| ≤ C)
    (hbal : ∫ x, Real.exp ((α - 1) * ℓbar x) ∂P = ∫ x, Real.exp (α * ℓbar x) ∂Q)
    (n : ℕ) (hn : 1 ≤ n) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (γ * α * y)) ∂(PrivBayesTest.lapLaw ℓbar (1 / (1 - PrivBayesTest.alphaTilde α)) n Q) ≤
        ENNReal.ofReal (Real.exp (-γ * n * -Real.log (∫ x, Real.exp (α * ℓbar x) ∂Q)) / (1 - γ ^ 2)) ∧
      ∫⁻ y, ENNReal.ofReal (Real.exp (-γ * (1 - α) * y)) ∂(PrivBayesTest.lapLaw ℓbar (1 / (1 - PrivBayesTest.alphaTilde α)) n P) ≤
        ENNReal.ofReal (Real.exp (-γ * n * -Real.log (∫ x, Real.exp (α * ℓbar x) ∂Q)) / (1 - γ ^ 2)) := by
  let β := 1-PrivBayesTest.alphaTilde α
  have hβ : 0 < β := by
    dsimp [β,PrivBayesTest.alphaTilde]
    have hh := min_le_left α (1-α)
    linarith [hα.2]
  have hca : |α| ≤ β := by
    rw [abs_of_pos hα.1]
    have hh := min_le_right α (1-α)
    dsimp [β,PrivBayesTest.alphaTilde]
    linarith
  have hcb : |α-1| ≤ β := by
    rw [abs_of_neg (sub_neg.mpr hα.2)]
    have hh := min_le_left α (1-α)
    dsimp [β,PrivBayesTest.alphaTilde]
    linarith
  constructor
  · have h := PrivateLaplaceMoment.lapLaw_bound Q ℓbar hℓm hℓb n β α γ hβ hca hγ
    simpa only [β,one_div,neg_mul,neg_neg,mul_neg] using h
  · have h := PrivateLaplaceMoment.lapLaw_bound P ℓbar hℓm hℓb n β (α-1) γ hβ hcb hγ
    rw [hbal] at h
    have he : γ*(α-1) = -γ*(1-α) := by ring
    simpa only [β,one_div,he,neg_mul,neg_neg,mul_neg] using h

/-- With a zero statistic and symmetric scale, the noise bound is attained. -/
theorem zero_statistic_control {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) :
    (∫ y, Real.exp ((1/4)*y) ∂PrivBayesTest.lapLaw (fun _ : X => 0) 2 n P) = 4/3 := by
  have h := PrivateLaplaceMoment.lapLaw_moment P (fun _ : X => 0) measurable_const
    ⟨0,fun _ => by norm_num⟩ n (1/2) (1/4) (by norm_num) (by norm_num)
  norm_num at h
  exact h.2
