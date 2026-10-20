-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.multipleTime_conditionalBorn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:50:41.931868+00:00
-- url     : https://prove2.me/submissions/9a790d40-b0da-4b67-93ea-4dad40a8ceab

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_rank_tr {I : Type*} [Fintype I] (u m : I → ℂ) :
    ((rankOne u).transpose * rankOne m).trace = ((Complex.normSq (∑ x, m x * u x) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, rankOne,
    map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring


/-- PDF p.20, Eqs.(92)–(94): both the Kraus-amplitude and trace forms, and a normalized
conditional distribution. Conditioning on successful postselection requires positive denominator. -/
theorem solution (s : Signature) (n k q : ℕ) (hn : 0 < n)
    (prep : (j : ℕ) → Fin (s.input j) → ℂ)
    (post : (j : ℕ) → Fin (s.output j) → ℂ)
    (hprep : ∀ j < n, (∑ a, Complex.normSq (prep j a)) = 1)
    (hpost : ∀ j < n, (∑ a, Complex.normSq (post j a)) = 1)
    (K : Fin k → Fin q → Basis s n → ℂ)
    (hK : CombInstrument s n k (fun i => ∑ a, rankOne (K i a)))
    (hden : 0 < ∑ i, QAlgorithms.effectProb (∑ a, rankOne (K i a)).transpose
      (rankOne (multiTimeVector s prep post n))) :
    let R := fun i => ∑ a, rankOne (K i a)
    let S := rankOne (multiTimeVector s prep post n)
    (∀ i, conditionalBorn R S i =
      (∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K i a x)) /
      (∑ j, ∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K j a x))) ∧
    (∀ i, 0 ≤ conditionalBorn R S i) ∧ (∑ i, conditionalBorn R S i) = 1 := by
  intro R S
  have hnum : ∀ i, QAlgorithms.effectProb (∑ a, rankOne (K i a)).transpose
      (rankOne (multiTimeVector s prep post n)) =
      ∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K i a x) := by
    intro i
    simp only [QAlgorithms.effectProb, Matrix.transpose_sum, Finset.sum_mul, Matrix.trace_sum,
      g52b_rank_tr, Complex.re_sum, Complex.ofReal_re]
  simp only [hnum] at hden
  have hc : ∀ i, conditionalBorn R S i =
      (∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K i a x)) /
      (∑ j, ∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K j a x)) := by
    intro i
    simp only [conditionalBorn, R, S, hnum]
  refine ⟨hc, fun i => ?_, ?_⟩
  · rw [hc]
    exact div_nonneg (Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _) hden.le
  · simp only [hc]
    rw [← Finset.sum_div, div_self hden.ne']


end

