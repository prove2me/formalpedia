-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_value_eq_fcf9e3525991
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:48.848024+00:00
-- url     : https://prove2.me/submissions/f725f8d2-8ce9-4612-98f6-e2b5b8e9fd3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_invSelf_f00771d14dee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_algebraMap_cb6f25d46c78

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero
namespace GroundTheory.Heights₂.Heights.ProjChowNonzero
theorem _root_.solution {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) =
      toK e (aeval (locPar A) f) := by
  rw [Vertical.specRest, eval₂_comp_left, aeval_def, eval₂_comp_left]
  congr 1
  · ext a
    simp [toK_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, projPar, map_mul, toK_algebraMap, toK_invSelf, div_eq_mul_inv]
    | succ i =>
      simp [locPar, projPar, toK, IsLocalization.Away.lift_eq, projVar,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ)
          (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)), mul_comm]
end GroundTheory.Heights₂.Heights.ProjChowNonzero
