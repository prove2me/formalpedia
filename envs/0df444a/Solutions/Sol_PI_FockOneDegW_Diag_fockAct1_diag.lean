-- Prove2me | solution 1 for PI.FockOneDegW.Diag.fockAct1_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:37.693205+00:00
-- url     : https://prove2.me/submissions/9803007d-7168-4a1e-be2e-99a20132afe4

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Theorems.Thm_P2M_PI_FockOneDegW_Diag_omAct_apply__14bba05dafb0
import Theorems.Thm_PI_FockOneDegW_Diag_sum_diag_of

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
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution (p q r s : ℕ) (a : Ix p q) :
    fockAct1 p q r s (Eab a a) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (a, c) := by
  classical
  unfold FockH1Action.fockAct1
  rw [LinearMap.comp_apply, LinearMap.flip_apply, Matrix.kroneckerMapBilinear_apply_apply, omAct_apply']
  rw [sum_diag_of _ (fun l : FockH1Action.Ln p q r s => l.1 = a)]
  · rw [show (∑ l : FockH1Action.Ln p q r s, if l.1 = a then FockH1Action.omE l l else 0) =
        ∑ x : FockH1Action.Ix p q, ∑ y : FockH1Action.Ix r s,
          if x = a then FockH1Action.omE ((x, y) : FockH1Action.Ln p q r s) (x, y) else 0 from Fintype.sum_prod_type _]
    rw [Fintype.sum_eq_single a (fun x hx => by simp [hx])]
    simp
  · intro l l'
    obtain ⟨x, y⟩ := l
    obtain ⟨x', y'⟩ := l'
    simp only [Matrix.kroneckerMap_apply, LinearMap.mul_apply', FockH1Action.Eab, Matrix.single_apply,
      Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> aesop
end PI.FockOneDegW.Diag
