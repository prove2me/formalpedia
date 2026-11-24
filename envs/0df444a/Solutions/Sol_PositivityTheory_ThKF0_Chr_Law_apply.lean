-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Law.apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:55.220463+00:00
-- url     : https://prove2.me/submissions/73141bc5-0737-4604-8fcb-b29ef8435a22

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_translate_apply
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_lift

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
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e e' : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
namespace PositivityTheory.ThKF0.Chr
namespace Law
theorem _root_.solution (he : Law C ψ S j e) (hj : Function.Injective j) (y : κ₁ → R) : ∃ w, ∀ e', Law C ψ S j e' →
    ∀ φ ∈ C.sp κ, e' φ y = e' (schr ψ w φ) 0 :=
  ⟨_, fun e' he' φ hφ => by rw [he' _ (y, 0) (rel_lift hj _) φ hφ, schrodinger_translate_apply]; simp⟩
end Law
end PositivityTheory.ThKF0.Chr
