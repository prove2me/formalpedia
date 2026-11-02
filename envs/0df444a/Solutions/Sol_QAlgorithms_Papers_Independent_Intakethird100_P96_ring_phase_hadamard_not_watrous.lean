-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P96.ring_phase_hadamard_not_watrous
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:06:59.07725+00:00
-- url     : https://prove2.me/submissions/1e452ac7-8d26-4d55-a92c-3b3ef65aed0e

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P96

namespace QCAWitnessExact

/-- Every Watrous matrix has rank-one two-site slices at a fixed input. -/
theorem watrous_cross (extra : ℕ)
    (W : Matrix (RingConfiguration extra) (RingConfiguration extra) ℂ)
    (hw : IsWatrous extra W) (b a c : RingConfiguration extra)
    (hdis : ∀ x, a x = true → c x = false) :
    W (fun _ => false) b * W (fun x => a x || c x) b = W a b * W c b := by
  obtain ⟨u, hu⟩ := hw
  simp only [hu, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _
  cases ha : a x <;> cases hc : c x <;> simp_all [mul_comm]

private theorem phase_single_zero (extra : ℕ) :
    (∏ x : Fin (extra + 5),
      if (x == 0) = true ∧ (x + 1 == 0) = true then (-1 : ℂ) else 1) = 1 := by
  apply Finset.prod_eq_one
  intro x _
  by_cases hx : x = 0
  · subst x
    simp
  · simp [hx]

private theorem phase_single_one (extra : ℕ) :
    (∏ x : Fin (extra + 5),
      if (x == 1) = true ∧ (x + 1 == 1) = true then (-1 : ℂ) else 1) = 1 := by
  apply Finset.prod_eq_one
  intro x _
  by_cases hx : x = 1
  · subst x
    simp
  · simp [hx]

private theorem phase_both (extra : ℕ) :
    (∏ x : Fin (extra + 5),
      if (x == 0 || x == 1) = true ∧ (x + 1 == 0 || x + 1 == 1) = true
      then (-1 : ℂ) else 1) = -1 := by
  rw [Finset.prod_eq_single (0 : Fin (extra + 5))]
  · simp
  · intro x _ hx
    by_cases h : x = 1
    · subst x
      have htwo : (1 : Fin (extra + 5)) + 1 ≠ 0 := by
        intro heq
        have hv := congrArg Fin.val heq
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < extra + 5 by omega)] at hv
      simp [htwo]
    · simp [hx, h]
  · simp

theorem ring_not_watrous (extra : ℕ) :
    ¬ IsWatrous extra (ringPhase extra * ringHadamard extra) := by
  intro hw
  have h := watrous_cross extra (ringPhase extra * ringHadamard extra) hw
    (fun _ => false) (fun x => x == 0) (fun x => x == 1) (by
      intro x hx
      simp only [beq_iff_eq] at hx
      simp [hx])
  simp only [ringPhase, Matrix.diagonal_mul, ringHadamard] at h
  rw [phase_both, phase_single_zero, phase_single_one] at h
  simp at h
  have hroot : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  have hz : ((Real.sqrt 2 : ℂ) ^ (extra + 5))⁻¹ *
      ((Real.sqrt 2 : ℂ) ^ (extra + 5))⁻¹ = 0 := by
    linear_combination (-1 / 2 : ℂ) * h
  exact (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hroot))
    (inv_ne_zero (pow_ne_zero _ hroot))) hz

end QCAWitnessExact

open QAlgorithms.Papers.Independent.Intakethird100.P96

theorem solution (extra : ℕ) :
    ¬ IsWatrous extra (ringPhase extra * ringHadamard extra) :=
  QCAWitnessExact.ring_not_watrous extra
