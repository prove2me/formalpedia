-- Prove2me | solution 1 for WorstCaseVaR.Entropy.dual_function_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:44:09.741416+00:00
-- url     : https://prove2.me/submissions/d9fbadb9-6d84-466b-ab92-72722bbe1977

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

set_option autoImplicit false

open MeasureTheory

namespace DualCF974

lemma key_pt (q a lam : ℝ) (hq : 0 ≤ q) (hlam : 0 < lam) :
    q * (a - lam * Real.log q) ≤ lam * Real.exp (a / lam - 1) := by
  rcases hq.eq_or_lt with h | h
  · subst h; simp; positivity
  · have hu := Real.add_one_le_exp (a / lam - 1 - Real.log q)
    have he : Real.exp (a / lam - 1) = q * Real.exp (a / lam - 1 - Real.log q) := by
      rw [Real.exp_sub (a / lam - 1) (Real.log q), Real.exp_log h]; field_simp
    rw [he]
    have : q * (a - lam * Real.log q) = lam * (q * (a / lam - 1 - Real.log q + 1)) := by
      field_simp; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hlam.le
    exact mul_le_mul_of_nonneg_left hu h.le

variable {α : Type*} [MeasurableSpace α]

lemma ind_meas (S : Set α) (hS : MeasurableSet S) : Measurable (S.indicator (1 : α → ℝ)) :=
  measurable_const.indicator hS

lemma ind_int (ν : Measure α) [IsFiniteMeasure ν] (S : Set α) (hS : MeasurableSet S) :
    Integrable (S.indicator (1 : α → ℝ)) ν :=
  (integrable_const (1 : ℝ)).indicator hS

lemma f_eq (S : Set α) (lam0 lam : ℝ) (x : α) :
    Real.exp ((S.indicator 1 x - lam0) / lam - 1) =
      Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * S.indicator 1 x + 1) := by
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx, Pi.one_apply]
    rw [mul_one, sub_add_cancel, ← Real.exp_add]; congr 1; ring
  · simp only [Set.indicator_of_notMem hx]
    simp; congr 1; ring

lemma f_int (ν : Measure α) [IsFiniteMeasure ν] (S : Set α) (hS : MeasurableSet S)
    (lam0 lam : ℝ) :
    Integrable (fun x => Real.exp ((S.indicator 1 x - lam0) / lam - 1)) ν := by
  simp_rw [f_eq]
  exact (((ind_int ν S hS).const_mul _).add (integrable_const _)).const_mul _

lemma f_integral (ν : Measure α) [IsProbabilityMeasure ν] (S : Set α) (hS : MeasurableSet S)
    (lam0 lam : ℝ) :
    ∫ x, Real.exp ((S.indicator 1 x - lam0) / lam - 1) ∂ν =
      Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * ν.real S + 1) := by
  simp_rw [f_eq]
  rw [integral_const_mul, integral_add ((ind_int ν S hS).const_mul _) (integrable_const _),
    integral_const_mul, integral_indicator_one hS]
  simp

lemma L_repr (ν : Measure α) [IsProbabilityMeasure ν] (S : Set α) (hS : MeasurableSet S)
    (d lam0 lam : ℝ) (Q : Measure α) [IsFiniteMeasure Q] (hQ : Q ≪ ν)
    (hint : Integrable (llr Q ν) Q) :
    Integrable (fun x => (Q.rnDeriv ν x).toReal *
      (S.indicator 1 x - lam0 - lam * llr Q ν x)) ν ∧
    Q.real S + lam0 * (1 - Q.real Set.univ) + lam * (d - ∫ x, llr Q ν x ∂Q) =
      lam0 + lam * d + ∫ x, (Q.rnDeriv ν x).toReal *
        (S.indicator 1 x - lam0 - lam * llr Q ν x) ∂ν := by
  have hg : Integrable (fun x => S.indicator 1 x - lam0 - lam * llr Q ν x) Q :=
    ((ind_int Q S hS).sub (integrable_const _)).sub (hint.const_mul _)
  refine ⟨(integrable_toReal_rnDeriv_mul_iff hQ).2 hg, ?_⟩
  have i1 : Integrable (fun x => S.indicator 1 x - lam0) Q :=
    (ind_int Q S hS).sub (integrable_const _)
  have i2 : Integrable (fun x => lam * llr Q ν x) Q := hint.const_mul _
  rw [integral_toReal_rnDeriv_mul hQ, integral_sub i1 i2, integral_sub (ind_int Q S hS) (integrable_const _),
    integral_const_mul, integral_indicator_one hS, integral_const]
  simp only [smul_eq_mul]
  ring

theorem gen (ν : Measure α) [IsProbabilityMeasure ν] (S : Set α) (hS : MeasurableSet S)
    (d lam0 lam : ℝ) (hlam : 0 < lam) :
    let L : Measure α → ℝ := fun Q =>
      Q.real S + lam0 * (1 - Q.real Set.univ) + lam * (d - ∫ x, llr Q ν x ∂Q)
    let Admissible : Measure α → Prop := fun Q =>
      IsFiniteMeasure Q ∧ Q ≪ ν ∧ Integrable (llr Q ν) Q
    let Qstar : Measure α :=
      ν.withDensity fun x => ENNReal.ofReal (Real.exp ((S.indicator 1 x - lam0) / lam - 1))
    let θ : ℝ := lam0 + lam * d +
      lam * Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * ν.real S + 1)
    Admissible Qstar ∧ L Qstar = θ ∧ (∀ Q, Admissible Q → L Q ≤ θ) ∧
      lam0 + lam * d + lam * ∫ x, Real.exp ((S.indicator 1 x - lam0) / lam - 1) ∂ν = θ := by
  intro L Admissible Qstar θ
  set f : α → ℝ := fun x => Real.exp ((S.indicator 1 x - lam0) / lam - 1) with hf_def
  have hfm : Measurable f :=
    Real.measurable_exp.comp ((((ind_meas S hS).sub_const lam0).div_const lam).sub_const 1)
  have hfi : Integrable f ν := f_int ν S hS lam0 lam
  have hlast : lam0 + lam * d + lam * ∫ x, f x ∂ν = θ := by
    rw [f_integral ν S hS]; simp only [θ]; ring
  have hQfin : IsFiniteMeasure Qstar :=
    isFiniteMeasure_withDensity_ofReal hfi.hasFiniteIntegral
  have hQac : Qstar ≪ ν := withDensity_absolutelyContinuous _ _
  have hrn : ∀ᵐ x ∂ν, (Qstar.rnDeriv ν x).toReal = f x := by
    filter_upwards [Measure.rnDeriv_withDensity ν hfm.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hllr : ∀ᵐ x ∂ν, llr Qstar ν x = (S.indicator 1 x - lam0) / lam - 1 := by
    filter_upwards [hrn] with x hx
    rw [llr, hx, hf_def, Real.log_exp]
  have hllrint : Integrable (llr Qstar ν) Qstar := by
    refine Integrable.congr ?_ (hQac.ae_le (Filter.EventuallyEq.symm hllr))
    exact (((ind_int Qstar S hS).sub (integrable_const _)).div_const _).sub (integrable_const _)
  have hadm : Admissible Qstar := ⟨hQfin, hQac, hllrint⟩
  have hbound : ∀ Q, Admissible Q → L Q ≤ θ := by
    rintro Q ⟨hQf, hQ, hint⟩
    obtain ⟨hI, hrep⟩ := L_repr ν S hS d lam0 lam Q hQ hint
    show _ ≤ _
    simp only [L]
    rw [hrep, ← hlast, ← integral_const_mul]
    gcongr ?_ + ?_
    · exact le_rfl
    · refine integral_mono hI (hfi.const_mul lam) (fun x => ?_)
      have := key_pt (Q.rnDeriv ν x).toReal (S.indicator 1 x - lam0) lam ENNReal.toReal_nonneg hlam
      simpa [llr, f] using this
  refine ⟨hadm, ?_, hbound, hlast⟩
  obtain ⟨_, hrep⟩ := L_repr ν S hS d lam0 lam Qstar hQac hllrint
  simp only [L]
  rw [hrep, ← hlast, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hrn, hllr] with x h1 h2
  rw [h1, h2]
  simp only [f]
  field_simp
  ring

end DualCF974

open MeasureTheory WorstCaseVaR.Entropy in
theorem solution {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (d γ lam0 lam : ℝ) (hlam : 0 < lam) :
    let P₀ := refGaussian xhat Γ
    let S := lossSet w γ
    let L : Measure (Returns n) → ℝ := fun Q =>
      Q.real S + lam0 * (1 - Q.real Set.univ) + lam * (d - ∫ x, llr Q P₀ x ∂Q)
    let Admissible : Measure (Returns n) → Prop := fun Q =>
      IsFiniteMeasure Q ∧ Q ≪ P₀ ∧ Integrable (llr Q P₀) Q
    let Qstar : Measure (Returns n) := P₀.withDensity fun x => ENNReal.ofReal (Real.exp ((S.indicator 1 x - lam0) / lam - 1))
    let θ : ℝ := lam0 + lam * d +
      lam * Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * P₀.real S + 1)
    Admissible Qstar ∧ L Qstar = θ ∧ (∀ Q, Admissible Q → L Q ≤ θ) ∧
      lam0 + lam * d + lam * ∫ x, Real.exp ((S.indicator 1 x - lam0) / lam - 1) ∂P₀ = θ := by
  have : IsProbabilityMeasure (refGaussian xhat Γ) := by
    unfold refGaussian; infer_instance
  have hS : MeasurableSet (lossSet w γ) := by
    unfold lossSet
    exact measurableSet_le measurable_const
      ((continuous_id.inner continuous_const).neg.measurable)
  exact DualCF974.gen (refGaussian xhat Γ) (lossSet w γ) hS d lam0 lam hlam
