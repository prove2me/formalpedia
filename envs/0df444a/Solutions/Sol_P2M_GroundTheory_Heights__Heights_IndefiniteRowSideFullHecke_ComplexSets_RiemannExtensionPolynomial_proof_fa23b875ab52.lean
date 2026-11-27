-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionPolynomial_proof_fa23b875ab52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:40.288326+00:00
-- url     : https://prove2.me/submissions/c84a2e99-9a5a-4ca5-9b19-cf3af9477f55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableOn_of_continuousOn_of_separately_6a0a05f148b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_frame_lines_not_in_zeroSet_ce830c4b1c26


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Set
open scoped Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RiemannExtensionPolynomial
theorem _root_.solution : RiemannExtensionPolynomial.Statement := by
  intro k P O f hP hO hc hd
  obtain ⟨M, hM, hlines⟩ := exists_frame_lines_not_in_zeroSet hP
  set A : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' M) with hAdef
  have hAapp : ∀ x, A x = M *ᵥ x := fun x => rfl
  set U := A ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage A.continuous
  have hgc : ContinuousOn (f ∘ A) U := hc.comp A.continuous.continuousOn fun z hz => hz
  have hPc : Continuous fun y : Fin k → ℂ => eval y P := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact (AnalyticOnNhd.eval_mvPolynomial P y (mem_univ y)).continuousAt
  have hopen : IsOpen (O ∩ {y | eval y P ≠ 0}) := hO.inter (isOpen_ne_fun hPc continuous_const)
  have hA : ∀ (z : Fin k → ℂ) (i : Fin k) (t : ℂ),
      A (Function.update z i t) = A z + (t - z i) • fun j => M j i := by
    intro z i t
    have hupd : Function.update z i t = z + (t - z i) • Pi.single i 1 := by
      ext l
      by_cases h : l = i
      · subst h
        simp
      · simp [h]
    rw [hupd, hAapp, hAapp, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    rfl
  have hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => (f ∘ A) (Function.update z i t)) (z i) := by
    intro z hz i
    set v : Fin k → ℂ := fun j => M j i with hv
    set q : ℂ → ℂ := fun t => eval (A z + (t - z i) • v) P with hqdef
    have hqa : AnalyticOnNhd ℂ q univ := fun t _ =>
      (AnalyticOnNhd.eval_mvPolynomial P _ (mem_univ _)).comp
        (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul analyticAt_const))
    have hq : ∀ᶠ t in 𝓝[≠] (z i), q t ≠ 0 := by
      by_contra hfreq
      rw [Filter.not_eventually] at hfreq
      simp only [ne_eq, not_not] at hfreq
      have hz0 := hqa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (mem_univ (z i)) hfreq
      obtain ⟨t, ht⟩ := hlines i (A z)
      apply ht
      have h1 := hz0 (mem_univ (t + z i))
      simpa [hqdef] using h1
    have hline : Continuous fun t : ℂ => Function.update z i t := continuous_const.update i continuous_id
    have hUev : (fun t : ℂ => Function.update z i t) ⁻¹' U ∈ 𝓝 (z i) :=
      hline.continuousAt.preimage_mem_nhds (by rw [Function.update_eq_self]; exact hU.mem_nhds hz)
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [hq, mem_nhdsWithin_of_mem_nhds hUev] with t hqt htU
      have hmem : A (Function.update z i t) ∈ O ∩ {y | eval y P ≠ 0} := by
        refine ⟨htU, ?_⟩
        show eval (A (Function.update z i t)) P ≠ 0
        rw [hA]
        exact hqt
      have hfd : DifferentiableAt ℂ f (A (Function.update z i t)) := hd.differentiableAt (hopen.mem_nhds hmem)
      exact hfd.comp t (A.differentiableAt.comp t (hasFDerivAt_update z t).differentiableAt)
    · exact ContinuousAt.comp_of_eq (g := f ∘ A) (f := fun t : ℂ => Function.update z i t) (hgc.continuousAt (hU.mem_nhds hz)) hline.continuousAt
        (Function.update_eq_self i z)
  have hgd : DifferentiableOn ℂ (f ∘ A) U := differentiableOn_of_continuousOn_of_separately hU hgc hs
  set B : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' M⁻¹) with hBdef
  have hAB : ∀ y, A (B y) = y := by
    intro y
    show M *ᵥ (M⁻¹ *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (Ne.isUnit hM), Matrix.one_mulVec]
  intro y hy
  have hBy : B y ∈ U := by
    show A (B y) ∈ O
    rw [hAB]
    exact hy
  have h1 : DifferentiableAt ℂ ((f ∘ A) ∘ B) y :=
    (hgd.differentiableAt (hU.mem_nhds hBy)).comp y B.differentiableAt
  have h2 : (f ∘ A) ∘ B = f := funext fun y => by simp only [Function.comp, hAB]
  rw [h2] at h1
  exact h1.differentiableWithinAt
end RiemannExtensionPolynomial
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
