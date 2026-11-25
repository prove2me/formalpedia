-- Prove2me | solution 1 for PI.FockWtDegWork.half2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:31.479604+00:00
-- url     : https://prove2.me/submissions/90957205-5ca7-4075-92f3-9bed0f792cce

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_PI_FockWtDegWork_fockAct2_monomial
import Theorems.Thm_PI_FockWtDegWork_exists_monomial_weight
import Theorems.Thm_PI_FockWtDegWork_wt_of_isHW
import Theorems.Thm_PI_FockWtDegWork_shift2_le

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
theorem _root_.solution (p q r s : ℕ) : ∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d →
    IsHW (fockAct2 p q r s) μ P → degW (cPair p q) μ ≤ d := by
  intro d μ P hP hH
  obtain ⟨h0, hw⟩ := wt_of_isHW (FockH1Action.fockAct2 p q r s) μ P hH
  obtain ⟨α, hd, hμ⟩ := exists_monomial_weight (fun c => FockH1Action.fockAct2 p q r s (FockH1Action.Eab c c))
    (fun c β => W2 c β) (fun c β => fockAct2_monomial p q r s c β) μ d P hP h0 hw
  have hμ' : μ = fun b => W2 b α := funext hμ
  subst hμ'
  calc FockH1Action.degW (FockH1Action.cPair p q) (fun b => W2 b α)
      = ∑ c, |FockH1Action.shiftNu (FockH1Action.cPair p q) (fun b => W2 b α) c| := rfl
    _ ≤ ∑ c : FockH1Action.Ix r s, ∑ a : FockH1Action.Ix p q, (α (a, c) : ℚ) :=
        Finset.sum_le_sum fun c _ => shift2_le α c
    _ = ((∑ i, α i : ℕ) : ℚ) := by rw [Nat.cast_sum, Fintype.sum_prod_type, Finset.sum_comm]
    _ = d := by rw [hd]
end PI.FockWtDegWork
