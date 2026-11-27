-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchIntDecompose_proof_c16e3216022f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:29.357791+00:00
-- url     : https://prove2.me/submissions/7f037ec4-c828-4954-b4ff-c8e367023eb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchIntDecompose
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntSumOffHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchIntDecompose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace BranchIntDecompose
theorem _root_.solution (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hGen : ComplexSets.GenericProjectionFinite.Statement) (hSum : ChartIntSumOffHyperplane.Statement)
    (hBr : BranchChartInt.Statement) : BranchIntDecompose.Statement := by
  intro n d J u q m γ ord hJ hdim hu hcov hdisj _
  obtain ⟨N₀, hN₀, hcovN⟩ := hcov
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu ⟨N₀, hN₀, hcovN⟩ hdisj b 0
      (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _
      (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨N₀ ∩ ⋂ b, Metric.ball q (e b),
    inter_mem hN₀ (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)),
    fun f ψ hf _ hfN hψ => ?_⟩
  have hex : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A :=
    (hGen n (d + 1) J hJ hdim).2.1
  have hAf : IsFiniteProjection J hex.choose := hex.choose_spec
  have hvar : varInt J (d + 1) f ψ = chartInt J hex.choose f ψ := by
    rw [varInt, dif_pos hex]
  have hbr : ∀ b, Integrable (chartDens J hex.choose ((γ b).image.indicator f) ψ) ∧
      chartInt J hex.choose ((γ b).image.indicator f) ψ =
        ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
          (Metric.ball 0 (γ b).radius) := by
    intro b
    refine hBr n (d + 1) J hex.choose q (γ b) f ψ hJ hdim hAf hf.continuous hψ
      ⟨Metric.closedBall 0 ((γ b).radius / 2), isCompact_closedBall _ _,
        Metric.closedBall_subset_ball (half_lt_self (γ b).radius_pos), fun t ht htK => ?_⟩
    by_contra hne
    have hx := hfN (subset_tsupport f hne)
    exact htK (Metric.ball_subset_closedBall (hpe b t ht (Set.mem_iInter.1 hx.2 b)))
  have hpt : ∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, (γ b).image.indicator f x := by
    intro x hxZ hux
    by_cases hfx : f x = 0
    · rw [hfx]
      exact (Finset.sum_eq_zero fun b _ => by by_cases hb : x ∈ (γ b).image <;> simp [hb, hfx]).symm
    · have hxN := hfN (subset_tsupport f hfx)
      obtain ⟨b₀, hb₀⟩ := Set.mem_iUnion.1 (hcovN ⟨hxZ, hxN.1⟩)
      rw [Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun hxb => hux (hdisj b b₀ hb ⟨hxb, hb₀⟩)) _)
        (fun h => absurd (Finset.mem_univ b₀) h), Set.indicator_of_mem hb₀]
  rw [hvar, hSum n (d + 1) J hex.choose u m f (fun b => (γ b).image.indicator f) ψ hJ hdim hAf hu hpt
    (fun b => (hbr b).1)]
  exact Finset.sum_congr rfl fun b _ => (hbr b).2
end BranchIntDecompose
end GroundTheory.Heights₂.Heights
