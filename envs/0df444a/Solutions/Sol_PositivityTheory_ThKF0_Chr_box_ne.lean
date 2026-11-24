-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.box_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:21.72619+00:00
-- url     : https://prove2.me/submissions/528b8f46-0a0e-4685-bd87-2d6b417f0b6b

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel

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
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {φ₁ : (κ → R) → ℂ} {φ₂ : (κ₁ → R) → ℂ} (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) : boxFun φ₁ φ₂ ≠ 0 := fun e => by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h₁
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h₂
  exact mul_ne_zero hx hy (congrFun e (Sum.elim x y))
end PositivityTheory.ThKF0.Chr
