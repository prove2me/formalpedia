-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:07.467114+00:00
-- url     : https://prove2.me/submissions/bf2514de-a50a-4b51-bb5c-fd2806256422

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_AxImp_ex
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_line
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsImp_cyc

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
theorem _root_.solution (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S)
    {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm κ) (hinv : ∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ C.sp κ, l φ ≠ 0) : Cyc C ψ l := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  obtain ⟨a, ha⟩ := h.line hS hT hl hinv
  obtain ⟨φ₀, h₀, hne⟩ := hne
  have ha0 : a ≠ 0 := fun e => hne (by rw [ha _ h₀, e, zero_mul])
  intro φ hφ h0
  obtain ⟨w, hw⟩ := hT.cyc hφ h0
  exact ⟨w, by rw [ha _ (h.schr κ w φ hφ)]; exact mul_ne_zero ha0 hw⟩
end Ax
end PositivityTheory.ThKF0.Chr
