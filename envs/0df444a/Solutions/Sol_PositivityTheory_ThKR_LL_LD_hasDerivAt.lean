-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.LD.hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:44.253627+00:00
-- url     : https://prove2.me/submissions/dc613276-b30c-4c45-89d8-d8d83a96b187

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Theorems.Thm_PositivityTheory_ThKR_LL_csmul
import Theorems.Thm_PositivityTheory_ThKR_LL_weyl_step
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum
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
theorem _root_.solution {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l →L[ℂ] Sch l} (hV : LD V Q 0) (h0 : ∀ f, V 0 f = f)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (v' : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv0 : ∀ w, v 0 w = w)
    (hv : ∀ w a, HasDerivAt (fun t => v t w a) (-v' w a) 0) (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (v' w))
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    HasDerivAt (fun t => lam (V t f)) (lam (Q f)) 0 := by
  have key : ∀ A ∈ weylAlg l, ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0 := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0)
      hV ?_ (fun f => by simpa using hasDerivAt_const _ _) ?_ ?_ hA
    · intro A w ih f
      refine ((HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_deriv ?_).congr_of_eventuallyEq ?_
      · have e : dRho w * Q = Q * dRho w - dRho (v' w) := by rw [← hQ, sub_sub_cancel]
        rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (dRho w), e, dRho_eq_sum w,
          dRho_eq_sum (v' w)]
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, hv0, h0,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub, neg_smul, ← sub_eq_add_neg,
          Finset.sum_sub_distrib]
        simp only [csmul]
      · filter_upwards [h] with t ht
        exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.2 fun i => key _ (hA i) f)
end LD
end PositivityTheory.ThKR.LL
