-- Prove2me | solution 1 for WorstCaseCVaR.Mixture.eq_53
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:11:11.890502+00:00
-- url     : https://prove2.me/submissions/d675032d-69d2-4f93-9598-5ff50c4a4a20

import Definitions.Def_WorstCaseCVaR_Mixture_Setting

section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma hinge_integrable {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : Integrable (f x) P) (α : ℝ) : Integrable (fun y ↦ max (f x y-α) 0) P :=
  (hf.sub (integrable_const α)).pos_part

lemma mixture_integrable {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    (g : (Fin m → ℝ) → ℝ) (hg : ∀ i, Integrable g (P i)) (lam : Fin l → ℝ) :
    Integrable g (mixture P lam) := by
  unfold mixture
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (hg i).smul_measure ENNReal.ofReal_ne_top

lemma mixture_isProbability {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) : IsProbabilityMeasure (mixture P lam) := by
  constructor
  unfold mixture
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ h.1 i),h.2]
  simp

lemma mixture_hinge_integral {l m n : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) (lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) (α : ℝ) :
    (∫ y, max (f x y-α) 0 ∂(mixture P lam)) =
      ∑ i, lam i * ∫ y, max (f x y-α) 0 ∂P i := by
  unfold mixture
  rw [integral_finsetSum_measure (fun i hi ↦
    (hinge_integrable (P i) f x (hf i) α).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_measure,ENNReal.toReal_ofReal (h.1 i),smul_eq_mul]

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
namespace MixtureCodex

theorem eq_53 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∀ lam ∈ stdSimplex ℝ (Fin l), ∀ α : ℝ,
      Hfun P f β x α lam = ∑ i, lam i * Fi P f β x i α := by
  intro lam hlam α
  simp only [Hfun,Fi,ruFun]
  rw [mixture_hinge_integral P f x hf lam hlam α]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hlam.2,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring


end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
theorem solution {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    ∀ lam ∈ stdSimplex ℝ (Fin l), ∀ α : ℝ,
      Hfun P f β x α lam = ∑ i, lam i * Fi P f β x i α := by
  exact MixtureCodex.eq_53 P f β hβ0 hβ1 x hf

end

#print axioms solution
