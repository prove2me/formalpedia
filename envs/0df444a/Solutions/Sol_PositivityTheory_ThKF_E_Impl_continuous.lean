-- Prove2me | solution 1 for PositivityTheory.ThKF.E.Impl.continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:56.824878+00:00
-- url     : https://prove2.me/submissions/ac5ae0ec-b06a-409c-a29c-4135a073819e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_EqOfInner
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho
import Theorems.Thm_GlobalTheory_RealWeil_exists_seminorm_le
import Theorems.Thm_GlobalTheory_RealWeil_weylAlg_induction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKF.E
namespace Impl
theorem _root_.solution {s : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) : Continuous S := by
  have hA : ∀ A ∈ weylAlg l, ∃ A' : Sch l →L[ℂ] Sch l, ∀ f, A (S f) = S (A' f) := fun A hA => by
    refine weylAlg_induction (P := fun A => ∃ A' : Sch l →L[ℂ] Sch l, ∀ f, A (S f) = S (A' f)) ⟨1, fun _ => rfl⟩ ?_
      ⟨0, fun f => by simp⟩ ?_ ?_ hA
    · rintro A w ⟨A', h'⟩
      refine ⟨A' * GlobalTheory.RealWeil.dRho (s.symm w), fun f => ?_⟩
      have := Impl.dRho (s := s.toLinearMap) h hs (s.symm w) f
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← this, h']
    · rintro A B ⟨A', h1⟩ ⟨B', h2⟩
      exact ⟨A' + B', fun f => by simp [h1, h2]⟩
    · rintro c A ⟨A', h1⟩
      exact ⟨c • A', fun f => by simp [h1]⟩
  refine (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_of_continuous_comp S fun kn => ?_
  obtain ⟨A, hAm, hb⟩ := exists_seminorm_le (l := l) kn.1 kn.2
  choose A' hA' using fun r => hA _ (hAm r)
  refine Seminorm.continuous_of_continuousAt_zero (𝕝 := ℂ) ?_
  have hc : Continuous fun f : Sch l => ∑ r, ‖schwartzToL2 l (A' r f)‖ := by fun_prop
  have h0 := hc.tendsto 0
  simp only [map_zero, norm_zero, Finset.sum_const_zero] at h0
  rw [ContinuousAt, map_zero]
  refine squeeze_zero (fun f => apply_nonneg _ _) (fun f => ?_) h0
  have := hb (S f)
  simp only [hA', h.norm] at this
  exact this
end Impl
end PositivityTheory.ThKF.E
