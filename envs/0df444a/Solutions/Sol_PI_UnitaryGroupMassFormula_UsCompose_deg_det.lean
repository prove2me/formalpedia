-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.deg_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:10.894538+00:00
-- url     : https://prove2.me/submissions/265f7b0c-8eba-42c8-9e18-435359339064

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {σ : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : ∀ a b, (M a b).totalDegree ≤ 1) : M.det.totalDegree ≤ n := by
  rw [Matrix.det_apply']
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun τ _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ ℂ).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp
  have h2 : (∏ i, M (τ i) i).totalDegree ≤ n := by
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (M (τ i) i).totalDegree ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => hM _ _
      _ = n := by simp
  omega
end PI.UnitaryGroupMassFormula.UsCompose
