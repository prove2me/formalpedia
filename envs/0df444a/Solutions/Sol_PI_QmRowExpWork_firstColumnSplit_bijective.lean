-- Prove2me | solution 1 for PI.QmRowExpWork.firstColumnSplit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:54.138632+00:00
-- url     : https://prove2.me/submissions/0cb66f26-be4c-44aa-94dc-a5dc338ef97e

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
import Theorems.Thm_PI_QmRowExpWork_cycle_perm_zero
import Theorems.Thm_PI_QmRowExpWork_matrixExtendByZero_zero
import Theorems.Thm_PI_QmRowExpWork_extByZero_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmRowExpWork
open Formalism.REAL
namespace PI.QmRowExpWork
theorem _root_.solution (m : ℕ) : Function.Bijective (phi0 m) := by
  have hinj : Function.Injective (phi0 m) := by
    rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    simp only [phi0] at h
    have hj : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero] using this
    subst hj
    have h2 : ext0 τ = ext0 τ' := mul_left_cancel h
    have hτ : τ = τ' := by
      ext k
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h2
      simp only [extByZero_succ, Fin.succ_inj] at this
      rw [this]
    rw [hτ]
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]
end PI.QmRowExpWork
