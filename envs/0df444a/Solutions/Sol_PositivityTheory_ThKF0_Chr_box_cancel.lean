-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.box_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:26.20991+00:00
-- url     : https://prove2.me/submissions/c4b42c7d-5833-46d1-a9a4-e2c6be1497b4

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
theorem _root_.solution {φ₁ φ₁' : (κ → R) → ℂ} {φ₂ : (κ₁ → R) → ℂ} (h₂ : φ₂ ≠ 0) (h : boxFun φ₁ φ₂ = boxFun φ₁' φ₂) : φ₁ = φ₁' := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h₂
  exact funext fun x => mul_right_cancel₀ hy (congrFun h (Sum.elim x y))
end PositivityTheory.ThKF0.Chr
