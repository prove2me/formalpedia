-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.schr_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:44.240796+00:00
-- url     : https://prove2.me/submissions/d0bb940d-ddaa-4ced-97b5-49269a622bf8

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
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {κ' : Type} [Fintype κ'] (w : V R κ) (w' : V R κ') (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ (Sum.elim w.1 w'.1, Sum.elim w.2 w'.2) (boxFun φ₁ φ₂) = boxFun (schr ψ w φ₁) (schr ψ w' φ₂) := by
  funext x
  rw [← Sum.elim_comp_inl_inr x]
  simp only [schr, boxFun, sumElim_dotProduct_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring
end PositivityTheory.ThKF0.Chr
