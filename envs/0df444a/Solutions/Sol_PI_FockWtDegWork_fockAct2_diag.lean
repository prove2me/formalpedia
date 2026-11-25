-- Prove2me | solution 1 for PI.FockWtDegWork.fockAct2_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:28.372325+00:00
-- url     : https://prove2.me/submissions/26d30929-68ec-461c-9f47-b06198ce3f69

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
theorem _root_.solution (p q r s : ℕ) (c : Ix r s) :
    fockAct2 p q r s (Eab c c) = ∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, c) := by
  have hM : ∀ l l' : FockH1Action.Ln p q r s,
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : FockH1Action.Mat p q)
        (FockH1Action.Eab c c)) l l' = if l = l' ∧ l.2 = c then 1 else 0 := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    show (1 : FockH1Action.Mat p q) x x' * FockH1Action.Eab c c y y' = _
    first
      | simp only [FockH1Action.Eab, Matrix.single_apply, Matrix.one_apply, Prod.mk.injEq]
      | simp only [FockH1Action.Eab, Matrix.single, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> first | (simp_all; done) | aesop
  rw [show FockH1Action.fockAct2 p q r s (FockH1Action.Eab c c) = FockH1Action.omAct p q r s
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : FockH1Action.Mat p q)
        (FockH1Action.Eab c c)) from rfl, omAct_apply',
    sum_diag_of _ (fun l => l.2 = c) hM, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single c]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ c) h
end PI.FockWtDegWork
