-- Prove2me | solution 1 for PI.QmRowExpWork.qminorRow_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:12.474573+00:00
-- url     : https://prove2.me/submissions/291db668-6ef8-4a74-88e3-f6a0365b9a72

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin (m + 1) => Tm E (u - (m : ℂ) + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod := by
  have e : ∀ k : ℕ, u - ((m + 1 : ℕ) : ℂ) + 1 + (k : ℂ) = u - (m : ℂ) + (k : ℂ) := by
    intro k
    push_cast
    ring
  simp only [qminorRow, e]
end PI.QmRowExpWork
