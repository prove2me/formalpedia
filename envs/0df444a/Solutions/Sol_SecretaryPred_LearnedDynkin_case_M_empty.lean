-- Prove2me | solution 1 for SecretaryPred.LearnedDynkin.case_M_empty
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:09.700758+00:00
-- url     : https://prove2.me/submissions/9133281e-7c1a-42a6-8776-8b356fff52cb

import Definitions.Def_SecretaryPred_LearnedDynkin_Setting
import Init
import Mathlib


section
namespace Queelius.SecretaryPred
open SecretaryPred.LearnedDynkin MeasureTheory

 theorem no_deviates {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (i : Fin n) : ¬ Deviates theta v vhat i := by
  have hn : i ∉ Mset theta v vhat := by rw [hM]; simp
  simpa [Mset] using hn

 theorem no_secretary {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (t : Fin n → ℝ) (i : Fin n) :
    ¬ SecretaryAt theta v vhat t i := by
  rintro ⟨j,_,hj⟩
  exact no_deviates hM j hj

 theorem stops_iff {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) (i : Fin n) :
    Stops theta tau v vhat ihat t i ↔ i=ihat := by
  simp [Stops,no_secretary hM]

 theorem hired_iff {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) (i : Fin n) :
    Hired theta tau v vhat ihat t i ↔ i=ihat := by
  simp only [Hired,stops_iff hM]
  constructor
  · exact And.left
  · intro h
    subst i
    refine ⟨rfl,?_⟩
    intro j hj he
    subst j
    exact lt_irrefl _ hj

 theorem value_eq {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) :
    algValue theta tau v vhat ihat t = v ihat := by
  classical
  simp [algValue,hired_iff hM]

 theorem arrival_probability (n : ℕ) : IsProbabilityMeasure (arrivalLaw n) := by
  constructor
  simp [arrivalLaw,Measure.restrict_apply,Real.volume_Icc_pi]

 theorem expected_eq {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau : ℝ) (ihat : Fin n) :
    expectedValue theta tau v vhat ihat = v ihat := by
  letI := arrival_probability n
  simp [expectedValue,value_eq hM]

 theorem consistency {n : ℕ} (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hihat : ∀ j,vhat j≤vhat ihat) (eps : ℝ) (heps : 0≤eps)
    (herr : ∀ i,|v i-vhat i|≤eps*v i) (j : Fin n) :
    (1-eps)/(1+eps)*v j ≤ v ihat := by
  have hl := (abs_le.mp (herr j)).2
  have hr := (abs_le.mp (herr ihat)).1
  have hpred := hihat j
  have hden : 0 < 1+eps := by linarith
  rw [div_mul_eq_mul_div,div_le_iff₀ hden]
  nlinarith
end Queelius.SecretaryPred

end

section
namespace Queelius.SecretaryPred.Controls
open SecretaryPred.LearnedDynkin

theorem exact_predictions {n : ℕ} (theta : ℝ) (htheta : 0≤theta)
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) : Mset theta v v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i
  simp only [Mset,Finset.mem_filter,Finset.mem_univ,true_and,Deviates,sub_self,abs_zero,not_lt]
  exact mul_nonneg htheta (hv i)

theorem zero_values {n : ℕ} (theta tau : ℝ) (ihat : Fin n) (t : Fin n → ℝ) :
    algValue theta tau (fun _ => 0) (fun _ => 0) ihat t = 0 := by
  simp [algValue]

theorem simultaneous_unique {n : ℕ} {theta : ℝ} {v vhat : Fin n → ℝ}
    (hM : Mset theta v vhat = ∅) (tau time : ℝ) (ihat i : Fin n) :
    Hired theta tau v vhat ihat (fun _ => time) i ↔ i=ihat :=
  hired_iff hM tau ihat (fun _=>time) i

noncomputable def tightValues : Fin 2 → ℝ := ![1/2,1]
noncomputable def tightPredictions : Fin 2 → ℝ := ![2/3,2/3]

theorem tight_no_deviation : Mset (1/3) tightValues tightPredictions = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i
  fin_cases i <;> norm_num [Mset,Deviates,tightValues,tightPredictions]

theorem tight_errors : ∀ i, |tightValues i-tightPredictions i| = (1/3)*tightValues i := by
  intro i
  fin_cases i <;> norm_num [tightValues,tightPredictions]

theorem tight_predicted_max : ∀ i, tightPredictions i ≤ tightPredictions 0 := by
  intro i
  fin_cases i <;> norm_num [tightPredictions]

theorem tight_value (tau : ℝ) (t : Fin 2 → ℝ) :
    algValue (1/3) tau tightValues tightPredictions 0 t =
      ((1-(1/3:ℝ))/(1+(1/3:ℝ)))*tightValues 1 := by
  rw [value_eq tight_no_deviation]
  norm_num [tightValues]
end Queelius.SecretaryPred.Controls

open SecretaryPred.LearnedDynkin

theorem solution (n : ℕ) (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (hM : Mset theta v vhat = ∅) :
    (∀ t : Fin n → ℝ, algValue theta tau v vhat ihat t = v ihat) ∧
      expectedValue theta tau v vhat ihat = v ihat ∧
      ∀ eps : ℝ, 0 ≤ eps → (∀ i, |v i - vhat i| ≤ eps * v i) →
        ∀ j, (1 - eps) / (1 + eps) * v j ≤ v ihat := by
  exact ⟨Queelius.SecretaryPred.value_eq hM tau ihat,
    Queelius.SecretaryPred.expected_eq hM tau ihat,
    fun eps he herr => Queelius.SecretaryPred.consistency v vhat ihat hihat eps he herr⟩

end
