-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.LD.differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:03.170231+00:00
-- url     : https://prove2.me/submissions/09625e3d-731c-4dd1-b25f-32dd37295ddd

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Theorems.Thm_PositivityTheory_ThKR_LL_weyl_step
import Theorems.Thm_GlobalTheory_RealWeil_exists_factor
import Theorems.Thm_GlobalTheory_RealWeil_weylAlg_induction
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace PositivityTheory.ThKR.LL
namespace LD
theorem _root_.solution {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (hV : LD V Q t₀)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv : ∀ w a, DifferentiableAt ℝ (fun t => v t w a) t₀)
    (h : ∀ᶠ t in 𝓝 t₀, ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    DifferentiableAt ℝ (fun t => lam (V t f)) t₀ := by
  have key : ∀ A ∈ weylAlg l, ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀ := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀)
      (fun f => (hV f).differentiableAt) ?_ (fun f => by simp) ?_ ?_ hA
    · intro A w ih f
      refine (DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_of_eventuallyEq ?_
      filter_upwards [h] with t ht
      exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).differentiableAt.comp t₀ (differentiableAt_pi.2 fun i => key _ (hA i) f)
end LD
end PositivityTheory.ThKR.LL
