-- Prove2me | solution 1 for P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:31.559516+00:00
-- url     : https://prove2.me/submissions/92512830-d2fc-4a54-8b91-cdeef01d6262

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
theorem _root_.solution {j : κ₁ → κ} (hj : Function.Injective j) : Function.extend j (0 : κ₁ → R) 0 = 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]
end PositivityTheory.ThKF0.Chr
