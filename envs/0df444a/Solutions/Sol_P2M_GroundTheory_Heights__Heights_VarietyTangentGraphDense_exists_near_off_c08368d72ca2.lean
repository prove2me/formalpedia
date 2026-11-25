-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_near_off_c08368d72ca2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:22.805159+00:00
-- url     : https://prove2.me/submissions/7eb44838-ba10-4631-baf5-b56d9310b6dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyTangentGraphDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_proof_f41f288e0b9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameGraphGeneric_proof_0d2e8b72cdc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_proof_b5407db643ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianGeneric_proof_1ca593bfb056
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FramePlaneGraph_proof_80ec7a065eb8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_proof_63329d51f704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NullSmaller_proof_15fa22cfb07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_proof_0dafe800e45e
import Theorems.Thm_UpperTheory_Reformulated_B_Qf34_proof


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
open MvPolynomial Topology Filter MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
namespace GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
theorem _root_.solution {n d : ℕ} {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    (hO : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hJ' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') < d) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ zeroSetEuc J) {ε : ℝ} (hε : 0 < ε) :
    ∃ z₁ ∈ zeroSetEuc J \ zeroSetEuc J', dist z₁ z < ε := by
  by_contra hcon
  push Not at hcon
  set O : Set (Fin n → ℂ) := WithLp.toLp 2 ⁻¹' Metric.ball z ε with hOdef
  have hOo : IsOpen O := Metric.isOpen_ball.preimage (PiLp.continuous_toLp 2 _)
  have hxO : WithLp.ofLp z ∈ O := by simp [hOdef, hε]
  have hxZ : WithLp.ofLp z ∈ ComplexSets.zeroSet J := fun q hq => hz q hq
  have hpos := hO n d J hJ hd (WithLp.ofLp z) O hOo hxO hxZ
  have hsub : ComplexSets.zeroSet J ∩ O ⊆ WithLp.ofLp '' zeroSetEuc J' := by
    rintro y ⟨hy, hyO⟩
    refine ⟨WithLp.toLp 2 y, ?_, by simp⟩
    by_contra hnot
    have h1 : WithLp.toLp 2 y ∈ zeroSetEuc J := fun q hq => hy q hq
    have h2 := hcon _ ⟨h1, hnot⟩
    have h3 : dist (WithLp.toLp 2 y) z < ε := hyO
    linarith
  have hnull : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') = 0 := NullSmaller.proof n d J' hJ'
  have himg : μH[((2 * d : ℕ) : ℝ)] (WithLp.ofLp '' zeroSetEuc J' : Set (Fin n → ℂ)) = 0 := by
    have := ((PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℂ)).lipschitzOnWith
      (s := zeroSetEuc J')).hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity)
    rw [hnull, mul_zero] at this
    exact nonpos_iff_eq_zero.1 this
  have := (MeasureTheory.measure_mono hsub).trans_eq himg
  exact hpos.ne' (nonpos_iff_eq_zero.1 this)
end GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
