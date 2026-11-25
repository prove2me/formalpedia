-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.extend_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:46.568744+00:00
-- url     : https://prove2.me/submissions/f8a39d6e-a9f1-48a5-b015-02d00d661c2c

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst

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
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
omit [Invertible (2 : R)]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {j : κ₁ → κ} (hj : Function.Injective j) (a : κ₁ → R) (y : κ → R) :
    Function.extend j a 0 ⬝ᵥ y = a ⬝ᵥ (y ∘ j) := by
  classical
  refine (Fintype.sum_of_injective j hj _ _ (fun k hk => ?_) fun i => ?_).symm
  · rw [Function.extend_apply' _ _ _ hk]; simp
  · rw [hj.extend_apply]; rfl
end PositivityTheory.ThKF0.Chr
