-- Prove2me | solution 1 for PI.FockWtDegWork.half1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:33.923107+00:00
-- url     : https://prove2.me/submissions/72bd31ec-4809-4274-9784-fcc61f0cc080

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_PI_FockWtDegWork_fockAct1_monomial
import Theorems.Thm_PI_FockWtDegWork_exists_monomial_weight
import Theorems.Thm_PI_FockWtDegWork_wt_of_isHW
import Theorems.Thm_PI_FockWtDegWork_shift1_le

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
theorem _root_.solution (p q r s : ℕ) : ∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d →
    IsHW (fockAct1 p q r s) μ P → degW (cPair r s) μ ≤ d := by
  intro d μ P hP hH
  obtain ⟨h0, hw⟩ := wt_of_isHW (FockH1Action.fockAct1 p q r s) μ P hH
  obtain ⟨α, hd, hμ⟩ := exists_monomial_weight (fun a => FockH1Action.fockAct1 p q r s (FockH1Action.Eab a a))
    (fun a β => W1 a β) (fun a β => fockAct1_monomial p q r s a β) μ d P hP h0 hw
  have hμ' : μ = fun b => W1 b α := funext hμ
  subst hμ'
  calc FockH1Action.degW (FockH1Action.cPair r s) (fun b => W1 b α)
      = ∑ a, |FockH1Action.shiftNu (FockH1Action.cPair r s) (fun b => W1 b α) a| := rfl
    _ ≤ ∑ a : FockH1Action.Ix p q, ∑ c : FockH1Action.Ix r s, (α (a, c) : ℚ) :=
        Finset.sum_le_sum fun a _ => shift1_le α a
    _ = ((∑ i, α i : ℕ) : ℚ) := by rw [Nat.cast_sum, Fintype.sum_prod_type]
    _ = d := by rw [hd]
end PI.FockWtDegWork
