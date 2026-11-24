-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.rel_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:37.877906+00:00
-- url     : https://prove2.me/submissions/6923c05c-6c63-4b32-ac2b-eb599c1a09d9

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
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} (hj : Function.Injective j) (w₁ : V R κ₁) :
    Rel S j (S.symm (Function.extend j w₁.1 0, Function.extend j w₁.2 0)) w₁ := by
  rw [Rel, S.apply_symm_apply]
  exact ⟨rfl, Function.extend_comp hj _ _⟩
end PositivityTheory.ThKF0.Chr
