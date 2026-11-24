-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.fac_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:00.591527+00:00
-- url     : https://prove2.me/submissions/08c814e5-3903-4339-a378-bd73bc7a7a61

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock

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
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
omit [Invertible (2 : R)]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (χ : Eˣ →* Circle) (n : ℕ) (z : Eˣ) : fac C χ n z ≠ 0 := by
  refine mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne')
  exact_mod_cast pos_iff_ne_zero.2 ((Group.isUnit _).map C.modu).ne_zero
end PositivityTheory.ThKF0.Chr
