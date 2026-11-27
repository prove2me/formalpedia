-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.speciso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:19:26.01022+00:00
-- url     : https://prove2.me/submissions/e756fb26-5e8e-4d7e-a29a-0543c0047f44

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Speciso
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Speciso_norm_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open Speciso
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : SpecIso := by
  intro K _ _ _ S _ _ _ _ _ π v ν _ _ hν
  set e : C(S, ℂ) →L[ℂ] Lp ℂ 2 ν := ContinuousMap.toLp (E := ℂ) 2 ν ℂ with he
  have hd : DenseRange e := ContinuousMap.toLp_denseRange ℂ ν ℂ (p := 2) (by simp)
  have hcoe : ∀ g, (e g : S → ℂ) =ᵐ[ν] g := fun g =>
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) g
  have hn : ∀ f, ‖Lmap π v f‖ = ‖e.toLinearMap f‖ := fun f => norm_L π v ν hν f
  have hb : ∃ C, ∀ f, ‖Lmap π v f‖ ≤ C * ‖e.toLinearMap f‖ := ⟨1, fun f => by rw [hn, one_mul]⟩
  have hdl : DenseRange e.toLinearMap := hd
  let V : Lp ℂ 2 ν →L[ℂ] K := (Lmap π v).extendOfNorm e.toLinearMap
  have hVe : ∀ f, V (e f) = π f v := fun f => LinearMap.extendOfNorm_eq hdl hb f
  refine ⟨V, fun h => ?_, fun f h h' hh' => ?_⟩
  · refine hd.induction_on (p := fun h => ‖V h‖ = ‖h‖) h
      (isClosed_eq (continuous_norm.comp V.continuous) continuous_norm) ?_
    intro g
    show ‖V (e g)‖ = ‖e g‖
    rw [hVe]
    exact hn g
  · let F : Lp ℂ ∞ ν := ContinuousMap.toLp (E := ℂ) ∞ ν ℂ f
    have hF : (F : S → ℂ) =ᵐ[ν] f := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (μ := ν) f
    let M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 F
    have hM : ∀ g, (M g : S → ℂ) =ᵐ[ν] fun s => f s * g s := by
      intro g
      have h1 : (M g : S → ℂ) =ᵐ[ν] fun s => (ContinuousLinearMap.mul ℂ ℂ) (F s) (g s) :=
        (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) F g
      filter_upwards [h1, hF] with s hs hFs
      rw [hs, ContinuousLinearMap.mul_apply', hFs]
    have key : ∀ g, V (M g) = π f (V g) := by
      intro g
      refine hd.induction_on (p := fun g => V (M g) = π f (V g)) g
        (isClosed_eq (V.continuous.comp M.continuous) ((π f).continuous.comp V.continuous)) ?_
      intro g
      have : M (e g) = e (f * g) := by
        apply Lp.ext
        filter_upwards [hM (e g), hcoe g, hcoe (f * g)] with s h1 h2 h3
        rw [h1, h2, h3]
        rfl
      show V (M (e g)) = π f (V (e g))
      rw [this, hVe, hVe, map_mul, ContinuousLinearMap.mul_apply]
    have : h' = M h := by
      apply Lp.ext
      filter_upwards [hh', hM h] with s h1 h2
      rw [h1, h2]
    rw [this, key]
end PositivityTheory.Rg.BcB.E2.P
