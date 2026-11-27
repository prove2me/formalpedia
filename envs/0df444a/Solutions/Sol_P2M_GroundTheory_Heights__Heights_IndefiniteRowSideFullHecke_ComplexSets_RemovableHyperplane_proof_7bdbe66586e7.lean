-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_proof_7bdbe66586e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:35.986027+00:00
-- url     : https://prove2.me/submissions/30516c84-3b30-4159-8faf-dab05745467e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRemovableHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRemovableHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_update_mem_ball_one_5f61701915c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4


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
open Metric Filter Topology Set
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RemovableHyperplane
theorem _root_.solution : RemovableHyperplane.Statement := by
  intro k n R f hf hb
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨f, ?_, fun t _ => rfl⟩
    rw [ball_eq_empty.mpr hR]
    exact differentiableOn_empty
  have hSo : IsOpen (ball (0 : Fin (k + 1) → ℂ) R ∩ {t | t 0 ≠ 0}) :=
    isOpen_ball.inter (isOpen_ne_fun (continuous_apply 0) continuous_const)
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hsc : ∀ z ∈ ball (0 : Fin (k + 1) → ℂ) 1, (R : ℂ) • z ∈ ball (0 : Fin (k + 1) → ℂ) R := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    calc R * ‖z‖ < R * 1 := mul_lt_mul_of_pos_left hz hR
      _ = R := mul_one R
  have hsc0 : ∀ z : Fin (k + 1) → ℂ, z 0 ≠ 0 → ((R : ℂ) • z) 0 ≠ 0 := fun z hz0 => by
    simp [hRc, hz0]
  have key : ∀ j : Fin n, ∃ G' : (Fin (k + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ G' (ball 0 1) ∧
      ∀ z ∈ ball (0 : Fin (k + 1) → ℂ) 1, z 0 ≠ 0 → G' z = f ((R : ℂ) • z) j := by
    intro j
    set G : (Fin (k + 1) → ℂ) → ℂ := fun z => f ((R : ℂ) • z) j with hG
    have hGd : ∀ z ∈ ball (0 : Fin (k + 1) → ℂ) 1, z 0 ≠ 0 → DifferentiableAt ℂ G z := by
      intro z hz hz0
      have h1 : DifferentiableAt ℂ f ((R : ℂ) • z) :=
        hf.differentiableAt (hSo.mem_nhds ⟨hsc z hz, hsc0 z hz0⟩)
      exact differentiableAt_pi.1 (h1.comp z (differentiableAt_id.const_smul (R : ℂ))) j
    have hGb : ∀ z ∈ ball (0 : Fin (k + 1) → ℂ) 1, z 0 ≠ 0 → ‖G z‖ ≤ C := fun z hz hz0 =>
      (norm_le_pi_norm _ j).trans (hC _ (mem_image_of_mem f ⟨hsc z hz, hsc0 z hz0⟩))
    have hlim : ∀ z ∈ ball (0 : Fin (k + 1) → ℂ) 1, ∀ i : Fin (k + 1), (∀ j, j ≠ i → z j ≠ 0) →
        ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c) := by
      intro z hz i hi
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under ?_ ?_⟩
        · filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with x hx0 hx1
          have hx1' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx1
          refine (hGd _ (RemovableHyperplane.update_mem_ball_one hz 0 hx1')
            (by simpa using hx0)).comp x ?_
          exact (hasFDerivAt_update z x).differentiableAt
        · refine isBoundedUnder_of_eventually_le (a := C + ‖G (Function.update z 0 0)‖) ?_
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with x hx0 hx1
          have hx1' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx1
          exact norm_sub_le_of_le
            (hGb _ (RemovableHyperplane.update_mem_ball_one hz 0 hx1') (by simpa using hx0)) le_rfl
      · have hz0 : Function.update z i 0 0 ≠ 0 := by
          rw [Function.update_of_ne (Ne.symm hi0)]
          exact hi 0 (Ne.symm hi0)
        have hm := RemovableHyperplane.update_mem_ball_one hz i (x := 0) (by simp)
        refine ⟨G (Function.update z i 0), ?_⟩
        have hc : Continuous (fun x : ℂ => Function.update z i x) :=
          (continuous_const (y := z)).update i continuous_id
        exact (((hGd _ hm hz0).continuousAt.tendsto).comp (hc.tendsto 0)).mono_left
          nhdsWithin_le_nhds
    obtain ⟨G', hG'a, hG'G⟩ := GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices.proof (k + 1) G
      (fun z hz => (hGd z hz.1 (hz.2 0)).differentiableWithinAt) hlim
    refine ⟨G', hG'a, fun z hz hz0 => ?_⟩
    have hWd : Dense {w : Fin (k + 1) → ℂ | ∀ i, w i ≠ 0} := by
      have h := dense_pi (α := fun _ : Fin (k + 1) => ℂ) (s := fun _ => ({0}ᶜ : Set ℂ)) univ
        (fun i _ => dense_compl_singleton 0)
      convert h using 1
      ext w
      simp
    have : (𝓝[{w : Fin (k + 1) → ℂ | ∀ i, w i ≠ 0}] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hWd z)
    have hev : G' =ᶠ[𝓝[{w : Fin (k + 1) → ℂ | ∀ i, w i ≠ 0}] z] G := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)]
        with w hwW hwb
      exact hG'G w hwb hwW
    exact tendsto_nhds_unique
      (((hG'a z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
      ((hGd z hz hz0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  choose G' hG'a hG'G using key
  have hinv : ∀ t ∈ ball (0 : Fin (k + 1) → ℂ) R, (R : ℂ)⁻¹ • t ∈ ball (0 : Fin (k + 1) → ℂ) 1 := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (inv_mul_lt_one₀ hR).2 ht
  refine ⟨fun t j => G' j ((R : ℂ)⁻¹ • t), fun t ht => ?_, fun t ht => ?_⟩
  · refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun j => ?_)
    have hs : DifferentiableAt ℂ (fun x : Fin (k + 1) → ℂ => (R : ℂ)⁻¹ • x) t := by fun_prop
    exact ((hG'a j _ (hinv t ht)).differentiableAt).comp t hs
  · funext j
    have h0 : ((R : ℂ)⁻¹ • t) 0 ≠ 0 := by simpa [hRc] using ht.2
    show G' j ((R : ℂ)⁻¹ • t) = f t j
    rw [hG'G j _ (hinv t ht.1) h0, smul_inv_smul₀ hRc]
end RemovableHyperplane
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
