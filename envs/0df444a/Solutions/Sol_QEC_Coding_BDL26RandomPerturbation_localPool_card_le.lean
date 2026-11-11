-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.localPool_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:30:05.072453+00:00
-- url     : https://prove2.me/submissions/3c2b9f2c-55cc-43ba-8a44-c7a927543235

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_subset_hits
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_familyHits_integer_ball_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_half_triangle_density
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (K : ℕ) (a : Triangle P) :
    ((localPool P J K a).card : ℝ) ≤ (2*K+1 : ℕ)^3*(250*t) := by
  have hc := Finset.card_le_card (localPool_subset_hits P J K a)
  have hc' : ((localPool P J K a).card : ℝ) ≤
      ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
        (Metric.closedBall (oldAnchor P J a) K)).card : ℝ) := by exact_mod_cast hc
  exact hc'.trans (familyHits_integer_ball_le _ (250*t)
    (half_triangle_density P J t hJ) K (oldAnchor P J a))
end QEC.Coding.BDL26RandomPerturbation
