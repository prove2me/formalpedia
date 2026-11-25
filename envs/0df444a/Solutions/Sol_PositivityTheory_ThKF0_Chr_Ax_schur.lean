-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:33.425949+00:00
-- url     : https://prove2.me/submissions/a51e01fa-3e05-4436-937a-c4eb11b6e717

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_translate_apply
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_apply_zero_of_fst

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
namespace PositivityTheory.ThKF0.Chr
namespace Ax
theorem _root_.solution (h : Ax C ψ) (T : Module.End ℂ ((κ → R) → ℂ)) (ha : Chr.ev0 R κ ∘ₗ T ∈ C.adm κ)
    (hc : ∀ w, ∀ φ ∈ C.sp κ, T (schr ψ w φ) = schr ψ w (T φ)) : ∃ a : ℂ, ∀ φ ∈ C.sp κ, T φ = a • φ := by
  obtain ⟨a, ha⟩ := h.delta κ _ ha fun y φ hφ => by
    show T _ 0 = T φ 0
    rw [hc _ _ hφ, schrodinger_apply_zero_of_fst rfl]
  refine ⟨a, fun φ hφ => funext fun x => ?_⟩
  have e : T (schr ψ (x, 0) φ) 0 = a * schr ψ (x, 0) φ 0 := ha _ (h.schr κ _ φ hφ)
  rw [hc _ _ hφ, schrodinger_translate_apply, schrodinger_translate_apply] at e
  simpa using e
end Ax
end PositivityTheory.ThKF0.Chr
