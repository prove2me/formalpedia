-- Prove2me | solution 1 for PI.Mk.eq_one_of_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:37.530593+00:00
-- url     : https://prove2.me/submissions/e47b44e0-399a-4fe8-b8df-62c80605fe7b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (n : ℕ) (hn : 0 < n)
    (h : A ^ n = 1) (hu : (A - 1) ^ N = 0) : A = 1 := by
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin N) (Fin N) ℚ, S = ∑ i ∈ Finset.range n, A ^ i :=
    ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin N) (Fin N) ℚ,
      T = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, A ^ j := ⟨_, rfl⟩
  have hSB : S * (A - 1) = 0 := by rw [hSdef, geom_sum_mul, h, sub_self]
  have hST : S = (n : Matrix (Fin N) (Fin N) ℚ) + T * (A - 1) := by
    rw [hSdef, hTdef, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    abel
  have hcomm : Commute T (A - 1) := by
    rw [hTdef]
    refine Commute.sum_left _ _ _ (fun i _ => Commute.sum_left _ _ _ (fun j _ => ?_))
    exact ((Commute.refl A).sub_right (Commute.one_right A)).pow_left j
  have hnil : IsNilpotent (T * (A - 1)) := ⟨N, by rw [hcomm.mul_pow, hu, mul_zero]⟩
  have hnu : IsUnit (n : Matrix (Fin N) (Fin N) ℚ) := by
    have : IsUnit (n : ℚ) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using this.map (algebraMap ℚ (Matrix (Fin N) (Fin N) ℚ))
  have hSu : IsUnit S := by
    rw [hST]
    exact hnil.isUnit_add_left_of_commute hnu (Nat.cast_commute n _).symm
  exact sub_eq_zero.1 (hSu.mul_right_eq_zero.1 hSB)
end PI.Mk
