-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:39.549936+00:00
-- url     : https://prove2.me/submissions/440107f2-a0b3-445c-8d0c-676e31c377b2

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_AxImp_ex
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_line
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Law_inv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Law_apply
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_E_cyc

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
namespace Ax
theorem _root_.solution (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e) (he' : Law C ψ S j e')
    (ha : Chr.ev0 R κ₁ ∘ₗ e' ∈ C.adm κ) : ∃ c : ℂ, ∀ φ ∈ C.sp κ, e' φ = c • e φ := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  obtain ⟨a, ha⟩ := h.line hS hT ha (he'.inv hj)
  obtain ⟨b, hb⟩ := h.line hS hT (he.adm _ (h.ev0 _)) (he.law.inv hj)
  obtain ⟨φ₀, h₀, hne⟩ := (h.E_cyc hS hj he).ne h
  have hb0 : b ≠ 0 := fun e => hne (by rw [hb _ h₀, e, zero_mul])
  refine ⟨a / b, fun φ hφ => funext fun y => ?_⟩
  obtain ⟨w, hw⟩ := he'.apply hj y
  have hs := h.schr κ w φ hφ
  rw [Pi.smul_apply, hw e' he' φ hφ, hw e he.law φ hφ, show e' _ 0 = _ from ha _ hs, show e _ 0 = _ from hb _ hs, smul_eq_mul]
  field_simp
end Ax
end PositivityTheory.ThKF0.Chr
