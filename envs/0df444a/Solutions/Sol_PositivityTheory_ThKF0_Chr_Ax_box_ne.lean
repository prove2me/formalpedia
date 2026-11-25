-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.box_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:22.491735+00:00
-- url     : https://prove2.me/submissions/76d94741-5d4d-4e83-bc29-03ae52900cde

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schr_dv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_box_ne
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_comp_cyc


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
namespace PositivityTheory.ThKF0.Chr
namespace Ax
theorem _root_.solution (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (hE : IsE C ψ (dbS S) (Sum.map j j) E)
    {l : ((κ₁ ⊕ κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∃ φ₁ ∈ C.sp κ, ∃ φ₂ ∈ C.sp κ, l (E (boxFun φ₁ φ₂)) ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, w', hw⟩ := h.comp_cyc hS.dbS (hj.sumMap hj) hE hl _ (h.box _ _ _ hφ _ hφ) (Chr.box_ne h0 h0)
  obtain ⟨a, b, rfl⟩ := exists_dv w
  obtain ⟨a', b', rfl⟩ := exists_dv w'
  rw [schr_dv, schr_dv] at hw
  exact ⟨_, h.schr _ _ _ (h.schr _ _ _ hφ), _, h.schr _ _ _ (h.schr _ _ _ hφ), hw⟩
end Ax
end PositivityTheory.ThKF0.Chr
