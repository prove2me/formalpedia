-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.hpk_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:02.539495+00:00
-- url     : https://prove2.me/submissions/4eeb7c4f-59ab-4b36-9393-396aa1618951

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Theorems.Thm_PI_ComplexConjugateDerivative_hpk_apply
import Theorems.Thm_PI_ComplexConjugateDerivative_sgI_lt
import Theorems.Thm_PI_ComplexConjugateDerivative_sgI_sgI
import Theorems.Thm_PI_ComplexConjugateDerivative_sgI_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
variable {k r : ℕ}
namespace PI.ComplexConjugateDerivative
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨sgI k r i.val, sgI_lt i⟩ : Fin (2 * r + k + 1))]
  · rw [hpk_apply, hpk_apply]
    simp only [Fin.val_mk, sgI_sgI, sgI_eq_iff, eq_self_iff_true, if_true]
    by_cases hij : i = j
    · subst hij
      simp only [eq_self_iff_true, if_true]
      split_ifs <;> norm_num
    · have hji : j.val ≠ i.val := fun h => hij (Fin.ext h).symm
      simp [hij, hji]
  · intro l _ hl
    rw [hpk_apply i l, if_neg, zero_mul]
    intro h
    exact hl (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.ComplexConjugateDerivative
