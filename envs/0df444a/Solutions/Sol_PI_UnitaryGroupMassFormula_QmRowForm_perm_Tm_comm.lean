-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.perm_Tm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:20.04185+00:00
-- url     : https://prove2.me/submissions/087313ae-3493-4ba1-8175-46a226e64b46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x y : ℂ)
    (a b c d : Fin n) :
    Tm E x a b * Tm E y c d - Tm E y c d * Tm E x a b = E a b * E c d - E c d * E a b := by
  have cen : ∀ (u : ℂ) (p q : Fin n) (z : A),
      (if p = q then algebraMap ℂ A u else 0) * z = z * (if p = q then algebraMap ℂ A u else 0) := by
    intro u p q z
    split_ifs
    · exact Algebra.commutes u z
    · simp
  unfold Tm
  have h1 := cen x a b (E c d)
  have h2 := cen y c d (E a b)
  have h3 := cen x a b (if c = d then algebraMap ℂ A y else 0)
  generalize (if a = b then algebraMap ℂ A x else 0) = c1 at h1 h3 ⊢
  generalize (if c = d then algebraMap ℂ A y else 0) = c2 at h2 h3 ⊢
  simp only [add_mul, mul_add]
  rw [h1, h2, h3]
  abel
end PI.UnitaryGroupMassFormula.QmRowForm
