-- Prove2me | solution 1 for QEC.Coding.BDL26QubitBallBounds.supported_word_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:06:11.736939+00:00
-- url     : https://prove2.me/submissions/9b586894-f8e2-4143-bfaa-09accaca6740

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_mask_card_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26QubitBallBounds
theorem _root_.solution {F : Type*} [Zero F] [DecidableEq F]
    (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space)
    (w : QEC.Coding.Word F (state S n).presentation.Q)
    (inside : ∀ q ∈ QEC.Coding.hammingSupport w, dist (J (.q q)) center ≤ R) :
    QEC.Coding.HammingWeight w ≤ ballBudget t R := by
  rw [QEC.Coding.HammingWeight_eq_card_hammingSupport]
  exact mask_card_le S n J geometry R center (QEC.Coding.hammingSupport w) inside
end QEC.Coding.BDL26QubitBallBounds
