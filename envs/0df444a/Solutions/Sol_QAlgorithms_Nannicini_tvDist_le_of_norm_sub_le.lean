-- Prove2me | solution 1 for QAlgorithms.Nannicini.tvDist_le_of_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:02:06.078297+00:00
-- url     : https://prove2.me/submissions/c9882c59-bd45-492d-98ab-e862e4e04c2a

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini.A3TV
open QAlgorithms

lemma prob_eq {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (z : Qubits q) : prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

lemma sum_norm_sq {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) : ∑ z, ‖ψ z‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem main (q : ℕ) (ψ φ : EuclideanSpace ℂ (Qubits q))
    (hψ : IsState ψ) (hφ : IsState φ) (ε : ℝ) (h : ‖ψ - φ‖ ≤ ε) :
    tvDist (prob ψ) (prob φ) ≤ ε := by
  unfold tvDist
  simp only [prob_eq]
  set a : Qubits q → ℝ := fun z => ‖ψ z - φ z‖
  have hpt : ∀ z, |‖ψ z‖ ^ 2 - ‖φ z‖ ^ 2| ≤ a z * ‖ψ z‖ + a z * ‖φ z‖ := by
    intro z
    have h1 : |‖ψ z‖ - ‖φ z‖| ≤ a z := abs_norm_sub_norm_le _ _
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖ψ z‖ + ‖φ z‖)]
    have h2 : 0 ≤ ‖ψ z‖ + ‖φ z‖ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hCS : ∀ χ : EuclideanSpace ℂ (Qubits q), ‖χ‖ = 1 → ∑ z, a z * ‖χ z‖ ≤ ‖ψ - φ‖ := by
    intro χ hχ
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun z => ‖χ z‖)
    have ha : ∑ z, a z ^ 2 = ‖ψ - φ‖ ^ 2 := by
      rw [← sum_norm_sq]; rfl
    rw [ha, sum_norm_sq, hχ] at this
    have h0 : 0 ≤ ‖ψ - φ‖ := norm_nonneg _
    nlinarith [abs_le_of_sq_le_sq' (by nlinarith : (∑ z, a z * ‖χ z‖) ^ 2 ≤ ‖ψ - φ‖ ^ 2) h0]
  have hsum : ∑ z, |‖ψ z‖ ^ 2 - ‖φ z‖ ^ 2| ≤ 2 * ‖ψ - φ‖ := by
    calc ∑ z, |‖ψ z‖ ^ 2 - ‖φ z‖ ^ 2| ≤ ∑ z, (a z * ‖ψ z‖ + a z * ‖φ z‖) :=
          Finset.sum_le_sum fun z _ => hpt z
      _ = ∑ z, a z * ‖ψ z‖ + ∑ z, a z * ‖φ z‖ := Finset.sum_add_distrib
      _ ≤ ‖ψ - φ‖ + ‖ψ - φ‖ := add_le_add (hCS ψ hψ) (hCS φ hφ)
      _ = _ := by ring
  linarith

end QAlgorithms.Nannicini.A3TV

theorem solution (q : ℕ) (ψ φ : EuclideanSpace ℂ (QAlgorithms.Qubits q))
    (hψ : QAlgorithms.IsState ψ) (hφ : QAlgorithms.IsState φ) (ε : ℝ) (h : ‖ψ - φ‖ ≤ ε) :
    QAlgorithms.tvDist (QAlgorithms.prob ψ) (QAlgorithms.prob φ) ≤ ε :=
  QAlgorithms.Nannicini.A3TV.main q ψ φ hψ hφ ε h
