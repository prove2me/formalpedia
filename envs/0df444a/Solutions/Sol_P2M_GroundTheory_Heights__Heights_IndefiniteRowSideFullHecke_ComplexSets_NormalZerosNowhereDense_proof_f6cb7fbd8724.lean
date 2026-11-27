-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalZerosNowhereDense_proof_f6cb7fbd8724
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:59:48.606125+00:00
-- url     : https://prove2.me/submissions/07995aec-93f2-4119-85ec-7c66d0eb3b50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalZerosNowhereDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAnalyticNear_zeroSetIn_bad128f4c290
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_scalar_fin_983e343b1d19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germIrreducibleAt_zeroSetIn_of_integrallyClosed_f694e1143fa1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_regLocus_subset_369db4101cd9


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
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalZerosNowhereDense
theorem _root_.solution (hic : NormalGermIntegrallyClosed.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement) (hdense : RegularLocusDense.Statement) :
    NormalZerosNowhereDense.Statement := by
  intro σ _ I w N G hI hn hw hN hwN hG hne
  have han := isAnalyticNear_zeroSetIn I w
  have hirr := germIrreducibleAt_zeroSetIn_of_integrallyClosed hic I w hI hn hw
  set X := zeroSetIn I with hX
  obtain ⟨N₀, hN₀, hwN₀, hd⟩ := hdense σ X w han
  obtain ⟨B, hB, hwB, hBU, hpc⟩ :=
    hconn σ X w han hirr (N ∩ N₀) (Filter.inter_mem (hN.mem_nhds hwN) (hN₀.mem_nhds hwN₀))
  have hBN : B ⊆ N := hBU.trans Set.inter_subset_left
  have hdB : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hd B hB (hBU.trans Set.inter_subset_right)
  refine ⟨B, hB, hwB, hBN, ?_⟩
  intro z hz V hV
  by_contra hall
  push Not at hall
  set R := regLocus (X ∩ B) with hR
  set T : Set (σ → ℂ) := {y | y ∈ X → G y = 0} with hT

  have hloc : ∀ x ∈ R, ∃ M : Set (σ → ℂ), IsOpen M ∧ x ∈ M ∧ ((∃ p ∈ X ∩ M, T ∈ 𝓝 p) → M ⊆ T) := by
    intro x hx
    have hx' : IsRegularPointOf (X ∩ B) x := hx
    obtain ⟨hxXB, d, A, O, W, g, hO, hW, hxW, hg, hAg, hYW⟩ := hx'
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := by rw [← hYW]; exact ⟨hxXB, hxW⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y₀ hy₀O
    have hgO : ∀ y ∈ O, g y ∈ X ∩ B := by
      intro y hy
      have hy' : g y ∈ (X ∩ B) ∩ W := by rw [hYW]; exact Set.mem_image_of_mem g hy
      exact hy'.1
    have hxA : A x ∈ Metric.ball y₀ r := by
      rw [← hgy₀, hAg y₀ hy₀O]
      exact Metric.mem_ball_self hr
    refine ⟨W ∩ B ∩ A ⁻¹' Metric.ball y₀ r,
      (hW.inter hB).inter (Metric.isOpen_ball.preimage A.continuous), ⟨⟨hxW, hxXB.2⟩, hxA⟩, ?_⟩
    have hcov : ∀ p ∈ X ∩ (W ∩ B ∩ A ⁻¹' Metric.ball y₀ r), ∃ y ∈ Metric.ball y₀ r, g y = p := by
      rintro p ⟨hpX, ⟨hpW, hpB⟩, hpA⟩
      obtain ⟨y, hyO, rfl⟩ : p ∈ g '' O := by rw [← hYW]; exact ⟨⟨hpX, hpB⟩, hpW⟩
      refine ⟨y, ?_, rfl⟩
      have hpA' : A (g y) ∈ Metric.ball y₀ r := hpA
      rwa [hAg y hyO] at hpA'
    have hF : AnalyticOnNhd ℂ (fun y => G (g y)) (Metric.ball y₀ r) := by
      refine analyticOnNhd_of_differentiableOn_scalar_fin Metric.isOpen_ball (fun y hy => ?_)
      have hyO := hrO hy
      exact ((hG.differentiableAt (hN.mem_nhds (hBN (hgO y hyO).2))).comp y
        (hg y hyO).differentiableAt).differentiableWithinAt
    rintro ⟨p, hpXM, hpT⟩
    obtain ⟨y₁, hy₁, rfl⟩ := hcov p hpXM
    have hev : (fun y => G (g y)) =ᶠ[𝓝 y₁] 0 := by
      filter_upwards [(hg y₁ (hrO hy₁)).continuousAt.preimage_mem_nhds hpT,
        Metric.isOpen_ball.mem_nhds hy₁] with y hyT hyb
      exact hyT (hgO y (hrO hyb)).1
    have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y₀ r).isPreconnected hy₁ hev
    intro q hq hqX
    obtain ⟨y, hy, rfl⟩ := hcov q ⟨hqX, hq⟩
    exact hzero hy
  choose! M hMo hxM hMT using hloc

  have hallR : ∀ x ∈ R, T ∈ 𝓝 x := by
    obtain ⟨x₀, hx₀V, hx₀R⟩ := mem_closure_iff_nhds.mp (hdB hz) (interior V) (interior_mem_nhds.mpr hV)
    have hx₀T : T ∈ 𝓝 x₀ :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx₀V) (fun y hy hyX => hall y ⟨hyX, interior_subset hy⟩)
    by_contra hbad
    push Not at hbad
    obtain ⟨x₁, hx₁R, hx₁T⟩ := hbad
    have hu : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hv : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hcover : R ⊆ (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) ∪ (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := by
      intro x hx
      by_cases h : T ∈ 𝓝 x
      · exact Or.inl (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
      · exact Or.inr (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
    obtain ⟨q, hqR, hqu, hqv⟩ := hpc _ _ hu hv hcover
      ⟨x₀, hx₀R, Set.mem_biUnion (x := x₀) ⟨hx₀R, hx₀T⟩ (hxM x₀ hx₀R)⟩
      ⟨x₁, hx₁R, Set.mem_biUnion (x := x₁) ⟨hx₁R, hx₁T⟩ (hxM x₁ hx₁R)⟩
    obtain ⟨a, ⟨haR, haT⟩, hqa⟩ := Set.mem_iUnion₂.mp hqu
    obtain ⟨b, ⟨hbR, hbT⟩, hqb⟩ := Set.mem_iUnion₂.mp hqv
    have hqX : q ∈ X := (regLocus_subset _ hqR).1
    have hMa : M a ⊆ T := hMT a haR ⟨a, ⟨(regLocus_subset _ haR).1, hxM a haR⟩, haT⟩
    have hqT : T ∈ 𝓝 q := Filter.mem_of_superset ((hMo a haR).mem_nhds hqa) hMa
    have hMb : M b ⊆ T := hMT b hbR ⟨q, ⟨hqX, hqb⟩, hqT⟩
    exact hbT (Filter.mem_of_superset ((hMo b hbR).mem_nhds (hxM b hbR)) hMb)

  have hzeroB : ∀ y ∈ X ∩ B, G y = 0 := by
    intro y hy
    by_contra hGy
    have hc : ContinuousAt G y := (hG.differentiableAt (hN.mem_nhds (hBN hy.2))).continuousAt
    obtain ⟨x, hxG, hxR⟩ := mem_closure_iff_nhds.mp (hdB hy) _ (hc.eventually_ne hGy)
    exact hxG (mem_of_mem_nhds (hallR x hxR) (regLocus_subset _ hxR).1)
  exact hne (Filter.mem_of_superset (hB.mem_nhds hwB) fun y hyB hyX => hzeroB y ⟨hyX, hyB⟩)
end NormalZerosNowhereDense
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
