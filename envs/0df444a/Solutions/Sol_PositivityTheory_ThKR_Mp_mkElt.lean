-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.mkElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:45.637867+00:00
-- url     : https://prove2.me/submissions/d92e5ce6-290b-430c-8b9d-c211191dff5b

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpA_ext_sch
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_continuous
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho
import Theorems.Thm_PositivityTheory_ThKF_E_exists_rho
import Theorems.Thm_PositivityTheory_ThKF_E_toLp_rho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open MpA
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution : MkElt l := by
  intro s U hU hI hN
  obtain ⟨V, rfl⟩ := hU
  have hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖ := fun f => hI.norm f
  have hsurj : Function.Surjective ⇑(V : Sch l →L[ℂ] Sch l) := fun f => ⟨V⁻¹.1 f, by
    show (V.1 * V⁻¹.1) f = f
    rw [V.mul_inv]; rfl⟩
  have hI' : Impl (⇑(Matrix.mulVecLin s.1)) (V : Sch l →L[ℂ] Sch l).toLinearMap := hI
  have hd : ∀ w f, V.1 (dRho w f) = dRho (s.1 *ᵥ w) (V.1 f) := fun w f => hI'.dRho hsurj w f
  set u := ext V hn with hu
  have hc : ∀ f, u (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := fun f => ext_sch V hn f
  have hrho : ∀ w F, u (rho w F) = rho (s.1 *ᵥ w) (u F) := fun w F => by
    refine dense_sch.induction_on (p := fun F => u (rho w F) = rho (s.1 *ᵥ w) (u F)) F
      (isClosed_eq (u.continuous.comp (rho w).continuous) ((rho _).continuous.comp u.continuous)) fun f => ?_
    obtain ⟨g, hg⟩ := exists_rho w f
    have hg' := hI.impl w f g hg
    calc u (rho w (schwartzToL2 l f)) = u (schwartzToL2 l g) := by rw [schwartzToL2_apply, schwartzToL2_apply, toLp_rho hg]
      _ = schwartzToL2 l (V.1 g) := hc g
      _ = rho (s.1 *ᵥ w) (schwartzToL2 l (V.1 f)) := by
        rw [schwartzToL2_apply, schwartzToL2_apply]; exact toLp_rho hg'
      _ = rho (s.1 *ᵥ w) (u (schwartzToL2 l f)) := by rw [hc]
  have hm : Mem ((s, u, V) : Amb l) := ⟨hc, hrho, hd, hN⟩
  exact ⟨(⟨((s, u, V) : Amb l), hm⟩ : sub l), rfl, rfl⟩
end PositivityTheory.ThKR.Mp
