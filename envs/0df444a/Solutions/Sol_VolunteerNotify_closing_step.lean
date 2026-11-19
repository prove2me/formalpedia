-- Prove2me | solution 1 for VolunteerNotify.closing_step
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:18:30.015875+00:00
-- url     : https://prove2.me/submissions/3a183749-32af-4101-8bd4-4ca8ec23efe0

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte
import Definitions.Def_VolunteerNotify_IsDP
import Definitions.Def_VolunteerNotify_Process
import Theorems.Thm_VolunteerNotify_lemma_1
import Theorems.Thm_VolunteerNotify_lemma_2
import Theorems.Thm_VolunteerNotify_lemma_3
import Theorems.Thm_VolunteerNotify_exAnte_feasible

open MeasureTheory


namespace VNAux

open VolunteerNotify

variable {V S T : ℕ}

open scoped Classical in
/-- Exactly one respondent, the lowest-indexed one, completes a task that has respondents. -/
lemma sum_priority (R : Finset (Fin V)) :
    ∑ v, (if v ∈ R ∧ ∀ u < v, u ∉ R then (1 : ℝ) else 0) = if R.Nonempty then 1 else 0 := by
  by_cases h : R.Nonempty
  · rw [if_pos h]
    have key : ∀ v, (v ∈ R ∧ ∀ u < v, u ∉ R) ↔ v = R.min' h := by
      intro v
      constructor
      · rintro ⟨hv, hmin⟩
        rcases (R.min'_le v hv).lt_or_eq with hlt | heq
        · exact absurd (R.min'_mem h) (hmin _ hlt)
        · exact heq.symm
      · rintro rfl
        exact ⟨R.min'_mem h, fun u hu huR => absurd (R.min'_le u huR) (not_le.2 hu)⟩
    simp only [key]
    simp
  · rw [if_neg h]
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h]

lemma completedCount_eq (a : Prim V S T → ℕ) :
    completedCount a = ∑ v, completedBy a v := by
  classical
  unfold completedCount completedBy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_priority]

lemma completedBy_bound (a : Prim V S T → ℕ) (v : Fin V) :
    0 ≤ completedBy a v ∧ completedBy a v ≤ T := by
  classical
  unfold completedBy
  constructor
  · exact Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num
  · calc _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => by split_ifs <;> norm_num
      _ = T := by simp

end VNAux

open VolunteerNotify VNAux

theorem solution {V S T : ℕ} (I : Instance V S T) (xstar xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : IsExAnte I xstar) (hdp : IsDP I xstar xt J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Process I xt μ) : 1 / (2 - mdhr I.g) * f I xstar ≤ POL P := by
  have hfeas : xstar ∈ feasibleSet I := (exAnte_feasible I).2.2.2 xstar hx
  have h01 : ∀ v s t, xstar v s t ∈ Set.Icc (0 : ℝ) 1 :=
    fun v s t => ⟨((hfeas v).1 s t).1, ((hfeas v).1 s t).2⟩
  -- Linearity of expectation: `POL = ∑_v contribution_v`.
  have hmeasΦ : Measurable fun ω => fun i => P.prim i ω :=
    measurable_pi_lambda _ P.measurable_prim
  have hint : ∀ v ∈ Finset.univ, Integrable (fun ω => completedBy (fun i => P.prim i ω) v) μ := by
    intro v _
    refine (integrable_const (T : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((measurable_of_countable (fun a : Prim V S T → ℕ => completedBy a v)).comp
        hmeasΦ).aestronglyMeasurable
    · have := completedBy_bound (fun i => P.prim i ω) v
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  have hPOL : POL P = ∑ v, contribution P v := by
    unfold POL contribution
    simp only [completedCount_eq]
    exact integral_finsetSum _ hint
  rw [lemma_1 I xstar h01, Finset.mul_sum, hPOL]
  exact Finset.sum_le_sum fun v _ =>
    (lemma_3 I xstar xt J hfeas hdp v).trans (lemma_2 I xstar xt J h01 hdp μ P v)
