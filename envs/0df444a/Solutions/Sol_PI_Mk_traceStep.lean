-- Prove2me | solution 1 for PI.Mk.traceStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:20.825653+00:00
-- url     : https://prove2.me/submissions/ebb917d2-6b08-4137-a472-92ac2b33f05b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
import Theorems.Thm_PI_Mk_charpoly_dvd_of_pow_eq_one
import Theorems.Thm_PI_Mk_good_of_dvd
import Theorems.Thm_PI_Mk_eq_one_of_unipotent

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
theorem _root_.solution : TraceStep := by
  intro N ℓ a hℓ g hg
  have h2 : 2 ≤ ℓ := hℓ.two_le
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin N) (Fin N) ℚ, A = (Int.castRingHom ℚ).mapMatrix g :=
    ⟨_, rfl⟩
  have hAn : A ^ (ℓ ^ a) = 1 := by rw [hA, ← map_pow, hg, map_one]
  have hdvd := charpoly_dvd_of_pow_eq_one A _ hAn
  obtain ⟨y, hy1, hy2, hy3⟩ :=
    (good_of_dvd ℓ hℓ a N A.charpoly (charpoly_monic A) hdvd).2
  have hdeg : A.charpoly.natDegree = N := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have htr : A.trace = -A.charpoly.nextCoeff := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [Matrix.trace, nextCoeff]
    · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      rw [trace_eq_neg_charpoly_coeff, nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hN),
        hdeg, Fintype.card_fin]
  have htrg : A.trace = ((g.trace : ℤ) : ℚ) := by
    rw [hA]; simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply]
  have hT : ((g.trace : ℤ) : ℚ) = (N : ℚ) - (ℓ : ℚ) * (y : ℚ) := by
    rw [← htrg, htr, hy2, hdeg]
  refine ⟨y, ?_, by exact_mod_cast hT, ?_⟩
  · rw [hdeg] at hy1
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hy1)
  · intro hy0
    have hcp := hy3 hy0
    rw [hdeg] at hcp
    have hch := aeval_self_charpoly A
    rw [hcp] at hch
    simp only [map_pow, map_sub, aeval_X, map_one] at hch
    have hA1 := eq_one_of_unipotent A (ℓ ^ a) (pow_pos hℓ.pos a) hAn hch
    ext i j
    have hij := congrFun (congrFun hA1 i) j
    rw [hA, RingHom.mapMatrix_apply, Matrix.map_apply] at hij
    rw [Matrix.one_apply] at hij ⊢
    split_ifs at hij ⊢ <;> simpa using hij
end PI.Mk
