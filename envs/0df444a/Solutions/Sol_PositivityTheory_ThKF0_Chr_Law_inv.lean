-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Law.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:55.22548+00:00
-- url     : https://prove2.me/submissions/ad5dd7d7-6504-4c8b-8518-0f670d6b7598

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_apply_zero_of_fst
import Theorems.Thm_P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea

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
theorem _root_.solution (he : Law C ψ S j e) (hj : Function.Injective j) (w : V R κ) (hw : (S w).1 = 0) (φ : (κ → R) → ℂ)
    (hφ : φ ∈ C.sp κ) : (ev0 R κ₁ ∘ₗ e) (schr ψ w φ) = (ev0 R κ₁ ∘ₗ e) φ := by
  show e _ 0 = e φ 0
  rw [he w (0, (S w).2 ∘ j) ⟨by rw [hw, extend_zero' hj], rfl⟩ φ hφ, schrodinger_apply_zero_of_fst rfl]
end Law
end PositivityTheory.ThKF0.Chr
