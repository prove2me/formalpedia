-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:04.470966+00:00
-- url     : https://prove2.me/submissions/756d4388-455f-4c8b-a160-2f1194cdf0c4

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_AxImp_ex
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_schur

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
theorem _root_.solution (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T)
    {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm κ) (hinv : ∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ) :
    ∃ a : ℂ, ∀ φ ∈ C.sp κ, l φ = a * T φ 0 := by
  obtain ⟨T', hT'⟩ := h.imp.ex hS.symm
  obtain ⟨a, ha⟩ := h.delta κ _ (hT'.adm l hl) fun y φ hφ => by
    show l (T' _) = l (T' φ)
    rw [hT'.law _ _ hφ, hinv _ (by simp) _ (hT'.maps φ hφ)]
  obtain ⟨b, hb⟩ := h.schur (T' ∘ₗ T) (hT.adm _ (hT'.adm _ (h.ev0 κ))) fun w φ hφ => by
    show T' (T _) = schr ψ w (T' (T φ))
    rw [hT.law _ _ hφ, hT'.law _ _ (hT.maps φ hφ), S.symm_apply_apply]
  have hb0 : b ≠ 0 := fun e => by
    obtain ⟨φ, hφ, h0⟩ := h.ne κ
    have := hb φ hφ
    rw [e, zero_smul] at this
    exact h0 (hT.inj φ hφ (hT'.inj _ (hT.maps φ hφ) this))
  refine ⟨b⁻¹ * a, fun φ hφ => ?_⟩
  have e : l (T' (T φ)) = a * T φ 0 := ha _ (hT.maps φ hφ)
  rw [show T' (T φ) = b • φ from hb φ hφ, map_smul, smul_eq_mul] at e
  rw [mul_assoc, ← e, inv_mul_cancel_left₀ hb0]
end Ax
end PositivityTheory.ThKF0.Chr
