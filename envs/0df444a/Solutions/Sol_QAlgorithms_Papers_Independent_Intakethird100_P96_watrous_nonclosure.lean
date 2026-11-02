-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P96.watrous_nonclosure
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:21:10.970971+00:00
-- url     : https://prove2.me/submissions/fdf9d428-febc-4a84-828b-1b8b4636d4ab

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped BigOperators
open QAlgorithms.Papers.Independent.Intakethird100.P96

namespace QCAHadamard

def localEntry (a b : Bool) : ℂ :=
  (if a = true ∧ b = true then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ)

theorem local_orthogonal (a b : Bool) :
    (∑ c : Bool, localEntry a c * star (localEntry b c)) =
      if a = b then 1 else 0 := by
  have hsquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hroot : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  cases a <;> cases b
  all_goals simp [localEntry]
  all_goals field_simp
  all_goals norm_num [hsquare]

theorem hadamard_unitary (extra : ℕ) :
    ringHadamard extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, ringHadamard, Matrix.one_apply]
  change (∑ j : RingConfiguration extra,
    (∏ x, localEntry (a x) (j x)) * star (∏ x, localEntry (b x) (j x))) = _
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (x : Fin (extra + 5)) (v : Bool) =>
    localEntry (a x) v * star (localEntry (b x) v))]
  simp only [local_orthogonal]
  by_cases hab : a = b
  · subst a
    simp
  · obtain ⟨x, hx⟩ : ∃ x, a x ≠ b x :=
      not_forall.mp (fun hall => hab (funext hall))
    have hz : (∏ i, if a i = b i then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])
    simpa [hab] using hz

end QCAHadamard

namespace QCAUnitary

theorem phase_unitary (extra : ℕ) :
    ringPhase extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [ringPhase, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  simp only [Pi.star_apply, star_prod, apply_ite, star_neg, star_one,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro x _
  split_ifs <;> norm_num

end QCAUnitary

namespace QCAIndividual

theorem hadamard_isWatrous (extra : ℕ) :
    IsWatrous extra (ringHadamard extra) := by
  refine ⟨fun bit input =>
    (if bit = true ∧ input 0 = true then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ), ?_⟩
  intro a b
  simp [ringHadamard]

theorem phase_isWatrous (extra : ℕ) :
    IsWatrous extra (ringPhase extra) := by
  refine ⟨fun bit input =>
    if bit = input 0 then
      if input 0 = true ∧ input 1 = true then (-1 : ℂ) else 1
    else 0, ?_⟩
  intro a b
  by_cases h : a = b
  · subst a
    simp [ringPhase]
  · simp only [ringPhase, Matrix.diagonal_apply, if_neg h]
    symm
    obtain ⟨x, hx⟩ : ∃ x, a x ≠ b x :=
      not_forall.mp (fun hall => h (funext hall))
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

end QCAIndividual

namespace QCAAdjoint

theorem adjoint_isWatrous (extra : ℕ) :
    IsWatrous extra (star (ringPhase extra * ringHadamard extra)) := by
  refine ⟨fun bit input =>
    ((if bit = true ∧ input 0 = true then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ)) *
      (if input 0 = true ∧ input 1 = true then (-1 : ℂ) else 1), ?_⟩
  intro a b
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ringPhase,
    Matrix.diagonal_mul, ringHadamard, Finset.prod_mul_distrib]
  simp [star_mul, star_prod, apply_ite, and_comm, mul_comm]

end QCAAdjoint

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

/-- Exact six-conjunct finite-ring Watrous milestone. -/
theorem solution (extra : ℕ) :
    ringHadamard extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ ∧
    ringPhase extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ ∧
    IsWatrous extra (ringHadamard extra) ∧
    IsWatrous extra (ringPhase extra) ∧
    ¬ IsWatrous extra (ringPhase extra * ringHadamard extra) ∧
    IsWatrous extra (star (ringPhase extra * ringHadamard extra)) :=
  ⟨QCAHadamard.hadamard_unitary extra, QCAUnitary.phase_unitary extra,
   QCAIndividual.hadamard_isWatrous extra, QCAIndividual.phase_isWatrous extra,
   QCAWitnessExact.ring_not_watrous extra, QCAAdjoint.adjoint_isWatrous extra⟩
