-- Prove2me | solution 1 for PI.QmColExpWork.firstColumnSplit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:11.580118+00:00
-- url     : https://prove2.me/submissions/b5221472-89db-4249-8b92-9d0ec5dfa1ba

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
import Theorems.Thm_PI_QmColExpWork_cycle_perm_zero
import Theorems.Thm_PI_QmColExpWork_matrixExtendByZero_zero
import Theorems.Thm_PI_QmColExpWork_extByZero_succ

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
open PI PI.QmColExpWork
open Formalism.REAL
namespace PI.QmColExpWork
theorem _root_.solution (m : ℕ) : Function.Bijective (phi0 m) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    have h0 : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [phi0, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero] using this
    subst h0
    have h1 : ext0 τ = ext0 τ' :=
      mul_left_cancel (show cyc0 m j * ext0 τ = cyc0 m j * ext0 τ' from h)
    have h2 : τ = τ' := by
      refine Equiv.ext fun k => ?_
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h1
      simpa [extByZero_succ] using this
    subst h2
    rfl
  · simp [Fintype.card_perm, Fintype.card_prod, Fintype.card_fin, Nat.factorial_succ]
end PI.QmColExpWork
