-- Prove2me | solution 1 for QEC.Coding.BDL26QubitBallBounds.integer_ball_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:37:40.962599+00:00
-- url     : https://prove2.me/submissions/1bbbd1c9-f8f8-4184-b626-e1a81dd9f2bc

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_qubitHits_singletons
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_familyHits_integer_ball_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26QubitBallBounds
theorem _root_.solution (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (K : Nat) (center : Space) :
    ((qubitHits (state S n).presentation J (Metric.closedBall center K)).card : ℝ) ≤
      ((2*K+1 : Nat)^3 : ℝ)*(2*t) := by
  have h := familyHits_integer_ball_le
    (fun q : (state S n).presentation.Q => {J (.q q)}) (2*t)
    (fun c => by rw [← qubitHits_singletons]; exact geometry.1 c) K center
  rw [← qubitHits_singletons] at h
  exact h
end QEC.Coding.BDL26QubitBallBounds
