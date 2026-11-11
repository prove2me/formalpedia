-- Prove2me | solution 1 for QEC.Coding.BDL26QubitBallBounds.mask_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:57:09.726124+00:00
-- url     : https://prove2.me/submissions/74650836-a921-4791-bef9-3ef5440c62f2

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_real_ball_card
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
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space)
    (A : Finset (state S n).presentation.Q)
    (inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R) : A.card ≤ ballBudget t R := by
  apply (Finset.card_le_card (show A ⊆
    qubitHits (state S n).presentation J (Metric.closedBall center R) from ?_)).trans
      (real_ball_card S n J geometry R center)
  intro q hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Metric.mem_closedBall.mpr (inside q hq)⟩
end QEC.Coding.BDL26QubitBallBounds
