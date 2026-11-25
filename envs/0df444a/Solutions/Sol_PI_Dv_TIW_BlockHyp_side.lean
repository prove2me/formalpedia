-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:28.554664+00:00
-- url     : https://prove2.me/submissions/b210bb46-bbe9-4486-950f-63c844d6f9fb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockMain
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db
import Theorems.Thm_PI_Dv_TIW_BlockHyp_map_phi
import Theorems.Thm_PI_Dv_TIW_BlockHyp_map_psi
import Theorems.Thm_PI_Dv_TIW_BlockHyp_phi_mem
import Theorems.Thm_PI_Dv_TIW_BlockHyp_psiPhi
import Theorems.Thm_PI_Dv_TIW_BlockHyp_psi_inj
import Theorems.Thm_PI_Dv_TIW_cut_span
import Theorems.Thm_PI_Dv_TIW_fg_cut
import Theorems.Thm_PI_Dv_TIW_idx_chain
import Theorems.Thm_PI_Dv_TIW_idx_map_inj
import Theorems.Thm_PI_Dv_TIW_idx_matV
import Theorems.Thm_PI_Dv_TIW_idx_nonneg_of_le
import Theorems.Thm_PI_Dv_TIW_span_latPow
import Theorems.Thm_PI_Dv_TIW_span_map_matV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ} {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V}
  {Γ : Matrix (Fin n) (Fin n) K}
namespace PI.Dv.TIW
namespace BlockHyp
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (H : BlockHyp X Y Φ Ψ Γ)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hLsp : Submodule.span K (L : Set V) = ⊤)
    (hΦL : ∀ i, ∀ x ∈ L, x ∈ X → Φ i x ∈ L) (hΨL : ∀ j, ∀ y ∈ L, y ∈ Y → Ψ j y ∈ L) :
    (latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K)) ≤
        L ⊓ Y.restrictScalars (𝓞 K) ∧
      Submodule.span K (((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map
        ((Φt Φ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = Y ∧
      0 ≤ idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ∧
      idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ≤
        (Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) : ℤ) * vAdd w Γ.det := by
  set LX := L ⊓ X.restrictScalars (𝓞 K) with hLXd
  set LY := L ⊓ Y.restrictScalars (𝓞 K) with hLYd
  have hLX : Submodule.span K (LX : Set V) = X := cut_span L hLsp X
  have hLY : Submodule.span K (LY : Set V) = Y := cut_span L hLsp Y
  have fgLX : LX.FG := fg_cut L hL X
  have fgLY : LY.FG := fg_cut L hL Y
  set LP := latPow (Fin n) LX with hLPd
  have fgLP : LP.FG := Submodule.fg_pi fun _ => fgLX
  have hLPsp : Submodule.span K (LP : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hLPd, span_latPow, hLX]
  have hLPX : ∀ x ∈ LP, x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  set A := LP.map ((Φt Φ).restrictScalars (𝓞 K)) with hAd
  have fgA : A.FG := fgLP.map _
  have hAle : A ≤ LY := by
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, H.phi_mem x (hLPX x hx)⟩
    simp only [LinearMap.coe_restrictScalars, Φt_apply]
    exact L.sum_mem fun i _ => hΦL i (x i) (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).1
      (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have hAsp : Submodule.span K (A : Set V) = Y := by
    rw [hAd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLPsp, H.map_phi]
  refine ⟨hAle, hAsp, idx_nonneg_of_le hI w LY A fgLY fgA (hLY.trans hAsp.symm) hAle, ?_⟩

  set Bt := LY.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) with hBtd
  have fgBt : Bt.FG := fgLY.map _
  have hBle : Bt ≤ LP := by
    rintro _ ⟨y, hy, rfl⟩ j _
    have hy' := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨hΨL j y hy'.1 hy'.2, H.h3 j y hy'.2⟩
  have hBsp : Submodule.span K (Bt : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hBtd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLY, H.map_psi]
  have hΨA : A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) = LP.map ((matV Γ).restrictScalars (𝓞 K)) := by
    rw [hAd, ← Submodule.map_comp]
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (H.psiPhi x (hLPX x hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, H.psiPhi x (hLPX x hx)⟩
  have hmat := idx_matV hI w LX fgLX Γ H.det
  rw [← hLPd, ← hΨA] at hmat
  have hΨAsp : Submodule.span K ((A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → V)) :
      Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hΨA]; exact span_map_matV Γ H.det LP X hLPsp
  have hch := idx_chain hI w LP Bt (A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K))) fgLP fgBt (fgA.map _)
    (by rw [hLPsp, hBsp]) (by rw [hΨAsp, hBsp])
  have hinj := idx_map_inj hI w (LinearMap.pi Ψ) LY A fgLY fgA (hLY.trans hAsp.symm)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp hy).2 h0)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp (hAle hy)).2 h0)
  have hnn := idx_nonneg_of_le hI w LP Bt fgLP fgBt (by rw [hLPsp, hBsp]) hBle
  rw [← hBtd] at hinj
  rw [hmat, ← hinj] at hch
  linarith
end BlockHyp
end PI.Dv.TIW
