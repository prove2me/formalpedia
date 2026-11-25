-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:36.624858+00:00
-- url     : https://prove2.me/submissions/d99504c9-5a47-4a21-a348-0e271ea0f9c5

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_apply_zero_of_fst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_AxImp_ex
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsImp_cyc
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_cyc

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
theorem _root_.solution (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) : ∃ l ∈ C.adm κ,
    (∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ) ∧ Cyc C ψ l := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  refine ⟨_, hT.adm _ (h.ev0 κ), fun w hw φ hφ => ?_, fun φ hφ h0 => hT.cyc hφ h0⟩
  show T _ 0 = T φ 0
  rw [hT.law _ _ hφ, schrodinger_apply_zero_of_fst hw]
end Ax
end PositivityTheory.ThKF0.Chr
