-- Prove2me | solution 1 for QEC.Coding.BDL26QubitBallBounds.real_ball_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:47:22.070188+00:00
-- url     : https://prove2.me/submissions/d58ad090-7e99-4865-a842-3a12333a138d

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_integer_ball_card
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26QubitBallBounds
theorem _root_.solution (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space) :
    (qubitHits (state S n).presentation J (Metric.closedBall center R)).card ≤ ballBudget t R := by
  have sub : qubitHits (state S n).presentation J (Metric.closedBall center R) ⊆
      qubitHits (state S n).presentation J (Metric.closedBall center (Nat.ceil R)) := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp (Finset.mem_filter.mp hq).2).trans (Nat.le_ceil R))
  have cover := integer_ball_card S n J geometry (Nat.ceil R) center
  have ceiling : ((2*Nat.ceil R+1 : Nat) : ℝ)^3*(2*t) ≤ (ballBudget t R : ℝ) :=
    Nat.le_ceil (((2*Nat.ceil R+1 : Nat) : ℝ)^3*(2*t))
  have cast : ((qubitHits (state S n).presentation J (Metric.closedBall center R)).card : ℝ) ≤
      (ballBudget t R : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card sub)).trans (cover.trans ceiling)
  exact_mod_cast cast
end QEC.Coding.BDL26QubitBallBounds
