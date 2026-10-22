-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P01.qubitCG_three_logical_operations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:35:52.733649+00:00
-- url     : https://prove2.me/submissions/f3d11dfc-2f1f-4275-a773-ab84aeb05603

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01
noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

theorem g73e_lhs (j m : ℤ) (b : Bool) :
    addSpin (rotateBranch (addMagnetic (Finsupp.single (j, m, b) 1))) =
      Finsupp.single (j - 1, m + spinSign b, false)
        (if b then -(rotationSin j (m + spinSign b) : ℂ) else (rotationCos j (m + spinSign b) : ℂ)) +
      Finsupp.single (j + 1, m + spinSign b, true)
        (if b then (rotationCos j (m + spinSign b) : ℂ) else (rotationSin j (m + spinSign b) : ℂ)) := by
  cases b <;> simp [addMagnetic, rotateBranch, addSpin, spinSign, sub_eq_add_neg]

theorem solution (j : ℕ) (m : ℤ) (b : Bool)
    (hm : QAlgorithms.Papers.Independent.Renew46.P01.MagneticAdmissible j m) :
    addSpin (rotateBranch (addMagnetic (Finsupp.single ((j : ℤ), m, b) 1))) =
      qubitCGTarget j m b := by
  rw [g73e_lhs]
  obtain ⟨h1, h2, h3⟩ := hm
  have hj : (0:ℝ) < 2 * ((j:ℝ) + 1) := by positivity
  unfold qubitCGTarget
  simp only
  cases b
  · -- b = false, M = m - 1
    congr 2
    · unfold QAlgorithms.Papers.Independent.Renew46.P01.addHalfCG
        QAlgorithms.Papers.Independent.Renew46.P01.MagneticAdmissible rotationCos
      simp only [spinSign, Bool.false_eq_true, if_false]
      by_cases hj0 : j = 0
      · subst hj0
        have : m = 0 := by omega
        subst this
        norm_num
      by_cases hmj : m = -(j:ℤ)
      · subst hmj
        rw [if_neg (by push_cast; omega)]
        norm_num
      rw [if_pos ⟨⟨h1, h2, h3⟩, ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega⟩, trivial⟩]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 2
      push_cast; ring_nf
    · unfold QAlgorithms.Papers.Independent.Renew46.P01.addHalfCG
        QAlgorithms.Papers.Independent.Renew46.P01.MagneticAdmissible rotationSin
      simp only [spinSign, Bool.false_eq_true, if_false]
      rw [if_pos ⟨⟨h1, h2, h3⟩, ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega⟩, trivial⟩]
      try simp only [if_true, ite_true]
      congr 2
      push_cast; ring_nf
  · congr 2
    · unfold QAlgorithms.Papers.Independent.Renew46.P01.addHalfCG
        QAlgorithms.Papers.Independent.Renew46.P01.MagneticAdmissible rotationSin
      simp only [spinSign, if_true]
      by_cases hj0 : j = 0
      · subst hj0
        have : m = 0 := by omega
        subst this
        norm_num
      by_cases hmj : m = (j:ℤ)
      · subst hmj
        rw [if_neg (by push_cast; omega)]
        norm_num
      rw [if_pos ⟨⟨h1, h2, h3⟩, ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega⟩, trivial⟩]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 2
      push_cast; ring_nf
    · unfold QAlgorithms.Papers.Independent.Renew46.P01.addHalfCG
        QAlgorithms.Papers.Independent.Renew46.P01.MagneticAdmissible rotationCos
      simp only [spinSign, if_true]
      rw [if_pos ⟨⟨h1, h2, h3⟩, ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega⟩, trivial⟩]
      try simp only [if_true, ite_true]
      congr 2
      push_cast; ring_nf
