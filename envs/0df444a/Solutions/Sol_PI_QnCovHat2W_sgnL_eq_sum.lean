-- Prove2me | solution 1 for PI.QnCovHat2W.sgnL_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:03.033182+00:00
-- url     : https://prove2.me/submissions/56fc0b14-63a7-482b-81b9-9cf84da88a38

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) :
    sgnL x e = ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if x = e ∘ σ.symm then 1 else 0) := by
  unfold sgnL
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  simp only [Matrix.of_apply]
  rw [Finset.prod_boole]
  by_cases h : x = e ∘ σ.symm
  · rw [if_pos h, if_pos]
    intro i _
    rw [h]
    simp
  · rw [if_neg h, if_neg]
    intro H
    apply h
    funext j
    have h1 := H (σ.symm j) (Finset.mem_univ _)
    simpa using h1
end PI.QnCovHat2W
