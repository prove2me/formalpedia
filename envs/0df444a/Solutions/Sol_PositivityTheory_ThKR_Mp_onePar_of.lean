-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.onePar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:48.543665+00:00
-- url     : https://prove2.me/submissions/27224bce-cbff-49e4-b297-21cfeb5d9f3a

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
import Theorems.Thm_PositivityTheory_ThKR_Mp_qd_sum
import Theorems.Thm_PositivityTheory_ThKR_Mp_exp_mem_sp
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_continuous
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_hasDerivAt
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_hasDerivAt_lin_exp
import Theorems.Thm_PositivityTheory_ThKR_LL_quad_eq
import Theorems.Thm_PositivityTheory_ThKR_Mp_om_sch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution (h1 : TopG l) (h2 : Cover l) (h3 : NearOne l) (h4 : SecDer l) : OnePar l := by
  have : IsTopologicalGroup (G l) := h1
  intro X hX
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ := fun t =>
    exp_mem_sp (SMulMemClass.smul_mem t hX)
  have hcont : Continuous fun t : ℝ => (NormedSpace.exp (t • X) : Mat l) :=
    continuous_pi fun a => continuous_pi fun b => continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X t).continuousAt
  let p : C(ℝ, Sp l) := ⟨fun t => ⟨NormedSpace.exp (t • X), hmem t⟩, hcont.subtype_mk _⟩
  have hp : ∀ t, (p t).1 = NormedSpace.exp (t • X) := fun t => rfl
  have hpadd : ∀ s t, p (s + t) = p s * p t := fun s t => Subtype.ext (by
    show NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)
    rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have he : pr (1 : G l) = p 0 := by
    rw [map_one]
    exact Subtype.ext (by simp [hp])
  obtain ⟨Γ, ⟨hΓ0, hΓp⟩, -⟩ := h2.existsUnique_continuousMap_lifts p 0 1 he
  have hpr : ∀ t, pr (Γ t) = p t := fun t => congrFun hΓp t
  refine ⟨Γ, Γ.continuous, hΓ0, fun s t => ?_, fun t => by rw [hpr]; rfl, fun f => ?_⟩
  · have := h2.eq_of_comp_eq (g₁ := fun t => Γ (s + t)) (g₂ := fun t => Γ s * Γ t)
      (Γ.continuous.comp (continuous_const.add continuous_id)) (continuous_const.mul Γ.continuous)
      (funext fun t => by simp only [Function.comp, map_mul, hpr, hpadd]) 0 (by simp [hΓ0])
    exact congrFun this t
  · have h3' : ∀ᶠ g in 𝓝 (Γ 0), omS g = sec (pr g).1 := by rw [hΓ0]; exact h3
    have hev := (Γ.continuous.tendsto 0).eventually h3'
    have hd : ∀ a b, HasFDerivAt (fun x : ℝ => NormedSpace.exp (x • X) a b)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X a b)) 0 := fun a b => by
      have := hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X 0
      simp only [zero_smul, NormedSpace.exp_zero, one_mul, Matrix.entryLinearMap_apply] at this
      exact this.hasFDerivAt
    have hS := (h4 ℝ (fun x => NormedSpace.exp (x • X)) (fun a b => (1 : ℝ →L[ℝ] ℝ).smulRight (X a b)) 0
      (by simp) hd f).hasDerivAt
    have hval : (∑ a, ∑ b, ((1 : ℝ →L[ℝ] ℝ).smulRight (X a b)).smulRight
        (schwartzToL2 l (Qd (Matrix.single a b 1) f))) 1 = (quad X f).toLp 2 := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, one_smul]
      rw [show quad X f = Qd X f from quad_eq hX f, ← qd_sum X f]
      show _ = schwartzToL2 l _
      simp only [map_sum, ContinuousLinearMap.map_smul_of_tower]
    rw [hval] at hS
    refine hS.congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    show om (Γ t) (schwartzToL2 l f) = _
    rw [om_sch, ht, hpr t]
    rfl
end PositivityTheory.ThKR.Mp
