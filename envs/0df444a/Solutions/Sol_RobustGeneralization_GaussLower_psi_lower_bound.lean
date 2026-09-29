-- Prove2me | solution 1 for RobustGeneralization.GaussLower.psi_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:38:46.646872+00:00
-- url     : https://prove2.me/submissions/d7c93bad-2009-43d1-a4bc-cfb9225b203d

import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem aux_psl_bound {d : ℕ} (f : E d → Bool) (m : E d) (s ε : ℝ)
    (hm : ∀ i, |m i| ≤ ε) :
    (1 / 2 : ℝ≥0∞) ≤ robustErr (gaussModel m s) f ε := by
  let γ := stdGaussian (E d)
  let A : Set (E d × Bool) := {p | ∃ x' ∈ linfBall p.1 ε, f x' ≠ p.2}
  let B : Set (E d) := {v | f (s • v) = false}
  have h1 : γ B ≤ gaussVec m s ((fun x => (x, true)) ⁻¹' A) := by
    unfold gaussVec
    refine le_trans (measure_mono ?_) (Measure.le_map_apply (by fun_prop) _)
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq, A]
    refine ⟨s • v, ?_, ?_⟩
    · intro i
      simp [hm i]
    · simpa [B] using hv
  have h2 : γ Bᶜ ≤ gaussVec (-m) s ((fun x => (x, false)) ⁻¹' A) := by
    unfold gaussVec
    refine le_trans (measure_mono ?_) (Measure.le_map_apply (by fun_prop) _)
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq, A]
    refine ⟨s • v, ?_, ?_⟩
    · intro i
      simp [hm i]
    · simpa [B] using hv
  have h3 : (1 : ℝ≥0∞) ≤ γ B + γ Bᶜ := by
    calc (1 : ℝ≥0∞) = γ (B ∪ Bᶜ) := by simp [Set.union_compl_self, γ]
      _ ≤ γ B + γ Bᶜ := measure_union_le _ _
  have h4 : gaussVec m s ((fun x => (x, true)) ⁻¹' A) ≤
      ((gaussVec m s).map (fun x => (x, true))) A :=
    Measure.le_map_apply (by fun_prop) _
  have h5 : gaussVec (-m) s ((fun x => (x, false)) ⁻¹' A) ≤
      ((gaussVec (-m) s).map (fun x => (x, false))) A :=
    Measure.le_map_apply (by fun_prop) _
  unfold robustErr gaussModel
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  calc (1/2 : ℝ≥0∞) = 1/2 * 1 := by simp
    _ ≤ 1/2 * (γ B + γ Bᶜ) := by gcongr
    _ = 1/2 * γ B + 1/2 * γ Bᶜ := by rw [mul_add]
    _ ≤ _ := by
      gcongr
      · exact h1.trans h4
      · exact h2.trans h5

end RobustGeneralization.GaussLower

open RobustGeneralization.GaussLower
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {d : ℕ} (f : E d → Bool) (m : E d) (s ε : ℝ) (hs : 0 < s)
    (hm : ∀ i, |m i| ≤ ε) :
    (1 / 2 : ℝ≥0∞) ≤ robustErr (gaussModel m s) f ε :=
  aux_psl_bound f m s ε hm
