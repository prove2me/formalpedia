-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isGraphChart_of_isSheetAt_24cdf41fadc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:00.291181+00:00
-- url     : https://prove2.me/submissions/ac5db7bc-6dda-4fe3-99ad-063519acdbcb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_d56f1b066651

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
open MvPolynomial MeasureTheory Filter Topology Matrix
noncomputable section
variable {n d : ℕ}
variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {s : (Fin d → ℂ) → Fin n → ℂ}
    (h : GroundTheory.Heights₂.Heights.IsSheetAt J A x s) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x s := by
  obtain ⟨W, hW, hAxW, hsd, hsx, hsec, N, hN, hloc⟩ := h
  obtain ⟨U0, hU0N, hU0, hxU0⟩ := mem_nhds_iff.mp hN
  let V := W ∩ s ⁻¹' U0
  have hVo : IsOpen V := hsd.continuousOn.isOpen_inter_preimage hW hU0
  have hAxV : A *ᵥ x ∈ V := ⟨hAxW, by show s (A *ᵥ x) ∈ U0; rw [hsx]; exact hxU0⟩
  have hxZ : x ∈ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J := by
    have := (hsec _ hAxW).2
    rw [hsx] at this
    exact this
  let U := U0 ∩ (fun z => A *ᵥ z) ⁻¹' V
  have hUo : IsOpen U :=
    hU0.inter (hVo.preimage (Continuous.matrix_mulVec continuous_const continuous_id))
  refine ⟨hxZ, U, V, hUo, ⟨hxU0, hAxV⟩, hVo,
    analyticOnNhd_of_differentiableOn hVo (hsd.mono Set.inter_subset_left), ⟨?_, ?_, ?_⟩,
    fun w hw => (hsec w hw.1).1⟩
  · intro y hy
    refine ⟨(hsec y hy.1).2, hy.2, ?_⟩
    show A *ᵥ s y ∈ V
    rw [(hsec y hy.1).1]
    exact hy
  · intro y hy y' hy' hyy'
    have := congrArg (fun z => A *ᵥ z) hyy'
    rwa [(hsec y hy.1).1, (hsec y' hy'.1).1] at this
  · rintro x' ⟨hx'Z, hx'U0, hx'V⟩
    exact ⟨A *ᵥ x', hx'V, (hloc x' ⟨hx'Z, hU0N hx'U0⟩ hx'V.1).symm⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
