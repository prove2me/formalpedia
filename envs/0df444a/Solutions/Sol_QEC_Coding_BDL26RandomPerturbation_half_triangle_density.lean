-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.half_triangle_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:53:57.79472+00:00
-- url     : https://prove2.me/submissions/0d21875b-ab62-41e0-92e2-67cfff15097b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_familyHits_integer_ball_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_half_triangle_hit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (center : Space) :
    ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)).card : ℝ) ≤ 250*t := by
  classical
  let squares := familyHits (tannerFaceImage P J) (Metric.closedBall ((2 : ℝ) • center) 2)
  have hsub : familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1) ⊆ squares ×ˢ (Finset.univ : Finset Two) := by
    intro s hs
    exact Finset.mem_product.mpr ⟨half_triangle_hit P J center s hs,Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  have htwo : (Finset.univ : Finset Two).card = 2 := by decide
  rw [Finset.card_product,htwo] at hc
  have hc' : ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)).card : ℝ) ≤ (squares.card : ℝ)*2 := by exact_mod_cast hc
  have hd := familyHits_integer_ball_le (tannerFaceImage P J) t hJ.2.2 2 ((2 : ℝ) • center)
  change (squares.card : ℝ) ≤ _ at hd
  norm_num at hd
  linarith
end QEC.Coding.BDL26RandomPerturbation
