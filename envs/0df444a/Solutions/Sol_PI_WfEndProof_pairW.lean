-- Prove2me | solution 1 for PI.WfEndProof.pairW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:02.26221+00:00
-- url     : https://prove2.me/submissions/88a86627-ebf6-48df-bd96-8d8443079db7

import Definitions.Def_Formalism_PeriodIntegrals_W2pair
import Definitions.Def_Formalism_PeriodIntegrals_WfRing
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_FlogConstantCoeff
import Theorems.Thm_PI_WfEndProof_coprime_sq_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfEndProof
open PI
namespace PI.WfEndProof
theorem _root_.solution : PairW := by
  intro p _ α hα
  have hpos : 0 < p ^ 2 - 1 := by
    have := (Fact.out : p.Prime).two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have hle : Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} ≤
      (Wp p).comap (RingHom.fst ℂ_[p] ℂ_[p]) := by
    rw [Subring.closure_le]
    rintro _ ⟨ζ, hζ, rfl⟩
    show ζ ∈ (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure
    exact Subring.le_topologicalClosure _ (Subring.subset_closure ⟨_, hpos, coprime_sq_sub_one p, hζ⟩)
  have hclosed : IsClosed (Prod.fst ⁻¹' (Wp p : Set ℂ_[p])) :=
    IsClosed.preimage (continuous_fst : Continuous (Prod.fst : ℂ_[p] × ℂ_[p] → ℂ_[p])) (show IsClosed (Wp p : Set ℂ_[p]) from Subring.isClosed_topologicalClosure _)
  exact closure_minimal (fun x hx => hle hx) hclosed hα
end PI.WfEndProof
