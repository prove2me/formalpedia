-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.localPool_card_le_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:35:57.183238+00:00
-- url     : https://prove2.me/submissions/5e58f406-843b-41da-8721-c242de807a80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (K M : ℕ)
    (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ)) (a : Triangle P) :
    (localPool P J K a).card ≤ M := by
  exact_mod_cast (localPool_card_le P J t hJ K a).trans hM
end QEC.Coding.BDL26RandomPerturbation
