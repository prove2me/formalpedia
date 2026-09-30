-- Prove2me | solution 1 for UnderstandingML.em_alternate_max
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:33:03.384304+00:00
-- url     : https://prove2.me/submissions/091ee8ed-e664-4b8d-ad95-f03aef3029df

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- Pointwise Gibbs bound: for `q ≥ 0`, `a > 0`, `S > 0`,
`q log a − q log q − q log S ≤ a / S − q` (from `log t ≤ t − 1`). -/
private lemma em_term_bound {q a S : ℝ} (hq : 0 ≤ q) (ha : 0 < a) (hS : 0 < S) :
    q * Real.log a - q * Real.log q - q * Real.log S ≤ a / S - q := by
  rcases hq.eq_or_lt with h | h
  · subst h; simp; positivity
  · have key := Real.log_le_sub_one_of_pos (show 0 < a / (q * S) by positivity)
    rw [Real.log_div ha.ne' (by positivity), Real.log_mul h.ne' hS.ne'] at key
    have : q * (a / (q * S) - 1) = a / S - q := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left key hq]

/-- One row of Lemma 24.2 (i). -/
private lemma em_row_bound {k : ℕ} (a q : Fin k → ℝ) (ha : ∀ y, 0 < a y) (hq : ∀ y, 0 ≤ q y)
    (hsum : ∑ y, q y = 1) :
    ∑ y, q y * Real.log (a y) - ∑ y, q y * Real.log (q y) ≤ Real.log (∑ y, a y) := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hsum
    · exact h
  have hS : 0 < ∑ y, a y :=
    Finset.sum_pos (fun y _ ↦ ha y) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have h1 : ∀ y, q y * Real.log (a y) - q y * Real.log (q y) - q y * Real.log (∑ y, a y) ≤
      a y / (∑ y, a y) - q y := fun y ↦ em_term_bound (hq y) (ha y) hS
  have h2 := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) ↦ h1 y)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hsum,
    div_self hS.ne'] at h2
  linarith

end UnderstandingML

open UnderstandingML

theorem solution {Θ X : Type*} {k m : ℕ} (p : Θ → X → Fin k → ℝ)
    (hp : ∀ θ x y, 0 < p θ x y) (x : Fin m → X) :
    (∀ (Q : Fin m → Fin k → ℝ) (θ : Θ), IsRowStochastic Q → emG p x Q θ ≤ latentLogLik p x θ) ∧
    (∀ θ : Θ, emG p x (fun i y ↦ posterior p θ (x i) y) θ = latentLogLik p x θ) ∧
    (∀ (Q : Fin m → Fin k → ℝ) (θ θ' : Θ), emG p x Q θ ≤ emG p x Q θ' ↔ emF p x Q θ ≤ emF p x Q θ') := by
  refine ⟨?_, ?_, ?_⟩
  · rintro Q θ ⟨hnn, hrow⟩
    unfold emG emF latentLogLik
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ ↦ em_row_bound _ _ (fun y ↦ hp θ (x i) y) (hnn i) (hrow i)
  · intro θ
    unfold emG emF latentLogLik posterior
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hS : 0 < ∑ y, p θ (x i) y :=
      Finset.sum_pos (fun y _ ↦ hp θ (x i) y) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    have : ∀ y, p θ (x i) y / (∑ y', p θ (x i) y') * Real.log (p θ (x i) y) -
        p θ (x i) y / (∑ y', p θ (x i) y') * Real.log (p θ (x i) y / ∑ y', p θ (x i) y') =
        p θ (x i) y / (∑ y', p θ (x i) y') * Real.log (∑ y', p θ (x i) y') := by
      intro y
      rw [Real.log_div (hp θ (x i) y).ne' hS.ne']
      ring
    simp only [this, ← Finset.sum_mul, ← Finset.sum_div, div_self hS.ne', one_mul]
  · intro Q θ θ'
    unfold emG
    constructor <;> intro h <;> linarith
