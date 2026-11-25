-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SliceImmersiveGeneral_proof_cdd465da10a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:23.642543+00:00
-- url     : https://prove2.me/submissions/4eadfc59-341d-48ab-8f61-67e4b84fbcb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceImmersiveGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_dim_component_linForm_8c41886dbd0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hyperplaneEmb_apply_4e79d7655eba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hyperplaneEmb_tail_2783fa70efbb

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
open MvPolynomial Filter Topology MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace SliceImmersiveGeneral
theorem _root_.solution (hcrit : CriticalImageNull.Statement)
    (hmass : ZeroSetOpenMass.Statement) : SliceImmersiveGeneral.Statement := by
  intro n d J W u p m γ hJ hdim hu hW hp hN
  obtain ⟨N, hN, hsl⟩ := hN
  have hWd := dim_component_linForm hJ hdim hu hW

  have hball : ∀ b, ∀ s ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      Fin.tail s ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius := by
    intro b s hs
    rw [ball_pi _ (γ b).radius_pos] at hs ⊢
    exact fun j _ => hs j.succ (Set.mem_univ _)
  have hmaps : ∀ b, Set.MapsTo (hyperplaneEmb d) (Metric.ball 0 (γ b).radius)
      (Metric.ball 0 (γ b).radius) := by
    intro b t ht
    rw [ball_pi _ (γ b).radius_pos] at ht ⊢
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hyperplaneEmb_apply, (γ b).radius_pos]
    · simpa [hyperplaneEmb_apply] using ht j (Set.mem_univ _)

  have hnull : ∀ b, μH[((2 * d : ℕ) : ℝ)] (sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
      ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}) = 0 := fun b =>
    hcrit d n _ _ Metric.isOpen_ball
      ((γ b).differentiableOn.comp (hyperplaneEmb d).differentiableOn (hmaps b))
  refine ⟨interior N, interior_mem_nhds.2 hN, ?_⟩
  rintro x ⟨hxW, hxN⟩
  rw [mem_closure_iff]
  intro o ho hxo
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne

  have hsub : GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ (o ∩ interior N) ⊆
      ⋃ b, sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
        ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)} := by
    rintro y ⟨hyW, hyo, hyN⟩
    by_contra hy
    simp only [Set.mem_iUnion, not_exists] at hy
    have hyG : y ∈ o ∩ {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
          ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0} := by
      refine ⟨hyo, hyW, fun b => ?_⟩
      obtain ⟨s, ⟨hs, hs0⟩, hsy⟩ := hsl b ⟨hyW, interior_subset hyN⟩
      have hs0' : s 0 = 0 := hs0
      refine ⟨s, hs, hs0', hsy, fun v hv0 hv => ?_⟩
      have hst := hyperplaneEmb_tail hs0'
      have hinj : Function.Injective (fderiv ℂ (sliceMap (γ b)) (Fin.tail s)) := by
        by_contra hni
        exact hy b ⟨Fin.tail s, ⟨hball b s hs, hni⟩, by simp only [sliceMap, hst, hsy]⟩
      have hγd : DifferentiableAt ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s)) := by
        rw [hst]
        exact (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hs)
      have hchain : fderiv ℂ (sliceMap (γ b)) (Fin.tail s) =
          (fderiv ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))).comp (hyperplaneEmb d) := by
        have h := fderiv_comp (Fin.tail s) hγd (hyperplaneEmb d).differentiableAt
        rw [ContinuousLinearMap.fderiv] at h
        exact h
      have hvt := hyperplaneEmb_tail hv0
      have : Fin.tail v = 0 := hinj (by
        rw [hchain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvt, hst, hv,
          map_zero, map_zero])
      rw [← hvt, this, map_zero]
    rw [hne] at hyG
    exact hyG
  have hpos := hmass n d W hW.1.1 hWd x (o ∩ interior N) (ho.inter isOpen_interior) ⟨hxo, hxN⟩ hxW
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hnull))
end SliceImmersiveGeneral
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
