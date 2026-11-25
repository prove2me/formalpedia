-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.ext_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:42.833557+00:00
-- url     : https://prove2.me/submissions/cbcb72c6-f0e6-470e-97ce-ef24fbc0ddcd

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
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (x : κ₁ → R) : Function.extend (Sum.inr : κ₁ → κ ⊕ κ₁) x 0 = Sum.elim (0 : κ → R) x := by
  funext k
  rcases k with k | k
  · rw [Function.extend_apply' _ _ _ (by simp)]; rfl
  · exact Sum.inr_injective.extend_apply _ _ _
end PositivityTheory.ThKF0.Chr
