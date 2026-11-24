-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.eta_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:26.441033+00:00
-- url     : https://prove2.me/submissions/21ab1df3-50b1-46ce-9e5b-9352aefc7195

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (η : ℤˣ) : ((η : ℤ) : E) * ((η : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
end PositivityTheory.ThKF0.Chr
