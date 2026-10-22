-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P49.canonicalCompositionTable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:29:15.60508+00:00
-- url     : https://prove2.me/submissions/62d6bac3-e501-4605-ba4b-5b893abf32b1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49
noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open QAlgorithms.Papers.Independent.Claimed50.P49
open QAlgorithms.Papers.Independent.Frontier30.P07

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

lemma g68m_zero_iff (M : RealMatrix) : M = 0 ↔ (M 0 0 = 0 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = 0) := by
  constructor
  · rintro rfl; simp
  · rintro ⟨a, b, c, d⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [a, b, c, d]

lemma g68m_classOf (g : GaussianData) : classOf g =
    (if g.K 0 0 * g.K 1 1 - g.K 0 1 * g.K 1 0 = 0 then
      (if (g.K 0 0 = 0 ∧ g.K 0 1 = 0 ∧ g.K 1 0 = 0 ∧ g.K 1 1 = 0) then .A1 else .A2)
    else if g.K 0 0 * g.K 1 1 - g.K 0 1 * g.K 1 0 = 1 then
      (if ¬ (g.alpha 0 0 = 0 ∧ g.alpha 0 1 = 0 ∧ g.alpha 1 0 = 0 ∧ g.alpha 1 1 = 0) ∧
          g.alpha 0 0 * g.alpha 1 1 - g.alpha 0 1 * g.alpha 1 0 = 0 then .B1 else .B2)
    else if g.K 0 0 * g.K 1 1 - g.K 0 1 * g.K 1 0 < 0 then .D else .C) := by
  simp only [classOf, Matrix.det_fin_two, ← g68m_zero_iff, ne_eq]

/-- Equation (2.18), PDF p.11: all table entries for the fixed canonical axes.
Printed D composed D=C is corrected to B2/C at product-one gain, as forced by
(2.6). The exact product-one branch is retained. Independent moderation required. -/
theorem solution (c1 c2 : CanonicalClass) (k1 k2 N1 N2 : ℝ)
    (h1 : ValidSourceCanonical c1 k1 N1) (h2 : ValidSourceCanonical c2 k2 N2) :
    classOf (composeData (canonicalData c1 k1 N1) (canonicalData c2 k2 N2)) ∈
      compositionClasses c2 c1 ∧
    (c1 = .D → c2 = .D →
      (classOf (composeData (canonicalData c1 k1 N1) (canonicalData c2 k2 N2)) = .B2 ↔
        k1 * k2 = 1)) := by
  have n1 : 0 ≤ N1 := by cases c1 <;> simp [ValidSourceCanonical] at h1 <;> tauto
  have n2 : 0 ≤ N2 := by cases c2 <;> simp [ValidSourceCanonical] at h2 <;> tauto
  have p1 : c1 = .C ∨ c1 = .D → 0 < k1 ∧ k1 ≠ 0 := by
    rintro (rfl | rfl) <;> simp [ValidSourceCanonical, ValidCanonical] at h1 <;>
      exact ⟨h1.2.1, h1.2.1.ne'⟩
  have p2 : c2 = .C ∨ c2 = .D → 0 < k2 ∧ k2 ≠ 0 := by
    rintro (rfl | rfl) <;> simp [ValidSourceCanonical, ValidCanonical] at h2 <;>
      exact ⟨h2.2.1, h2.2.1.ne'⟩
  have q1 : c1 = .C → k1 * k1 ≠ 1 := by
    rintro rfl; simp [ValidSourceCanonical, ValidCanonical] at h1
    intro h; apply h1.2.2.1; nlinarith
  have q2 : c2 = .C → k2 * k2 ≠ 1 := by
    rintro rfl; simp [ValidSourceCanonical, ValidCanonical] at h2
    intro h; apply h2.2.2.1; nlinarith
  clear h1 h2
  have a1 : N1 + 2⁻¹ ≠ 0 := by positivity
  have a1' : 2⁻¹ + N1 ≠ 0 := by positivity
  have a2 : N2 + 2⁻¹ ≠ 0 := by positivity
  have a2' : 2⁻¹ + N2 ≠ 0 := by positivity
  rw [g68m_classOf]
  refine ⟨?_, ?_⟩
  swap
  · rintro rfl rfl
    obtain ⟨hk1, -⟩ := p1 (Or.inr rfl)
    obtain ⟨hk2, -⟩ := p2 (Or.inr rfl)
    have hp := mul_pos hk1 hk2
    simp [composeData, canonicalData, sigmaThree, Matrix.mul_apply, Fin.sum_univ_two]
    constructor
    · intro h
      by_contra hne
      have h' : ¬ (k1 * k2 * (k1 * k2) = 1) := by
        intro h''; apply hne; nlinarith
      simp [h', hk1.ne', hk2.ne'] at h
      split_ifs at h <;> simp_all
    · intro h
      have h' : k1 * k2 * (k1 * k2) = 1 := by rw [h]; norm_num
      simp [h', hk1.ne', hk2.ne']
  cases c1 <;> cases c2 <;> simp at p1 p2 q1 q2 <;>
    simp [composeData, canonicalData, compositionClasses, sigmaThree, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try split_ifs) <;> (try simp_all) <;>
    (try (by_cases hN : N1 = 0 <;> by_cases hN' : N2 = 0 <;> simp_all)) <;>
    (try nlinarith [sq_nonneg k1, sq_nonneg k2]) <;>
    (try (obtain ⟨hk1, -⟩ := p1; obtain ⟨hk2, -⟩ := p2; nlinarith [mul_pos hk1 hk2])) <;>
    (try (intro h; rw [h] at *; simp_all))



end
