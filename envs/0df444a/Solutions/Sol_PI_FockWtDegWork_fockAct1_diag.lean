-- Prove2me | solution 1 for PI.FockWtDegWork.fockAct1_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:26.47666+00:00
-- url     : https://prove2.me/submissions/4818a352-673e-4062-88d6-5aba83b66738

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_P2M_PI_FockWtDegWork_omAct_apply__e42e4646d9f5
import Theorems.Thm_PI_FockWtDegWork_sum_diag_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution (p q r s : ℕ) (a : Ix p q) :
    fockAct1 p q r s (Eab a a) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (a, c) := by
  have hM : ∀ l l' : FockH1Action.Ln p q r s,
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : FockH1Action.Mat r s)
        (FockH1Action.Eab a a)) l l' = if l = l' ∧ l.1 = a then 1 else 0 := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    show FockH1Action.Eab a a x x' * (1 : FockH1Action.Mat r s) y y' = _
    first
      | simp only [FockH1Action.Eab, Matrix.single_apply, Matrix.one_apply, Prod.mk.injEq]
      | simp only [FockH1Action.Eab, Matrix.single, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> first | (simp_all; done) | aesop
  rw [show FockH1Action.fockAct1 p q r s (FockH1Action.Eab a a) = FockH1Action.omAct p q r s
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : FockH1Action.Mat r s)
        (FockH1Action.Eab a a)) from rfl, omAct_apply',
    sum_diag_of _ (fun l => l.1 = a) hM, Fintype.sum_prod_type,
    Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ a) h
end PI.FockWtDegWork
