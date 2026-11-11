-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.common_hits_anchor_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:33:37.594305+00:00
-- url     : https://prove2.me/submissions/8e4c732a-ff76-4bea-ac22-2027c91ed0e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_HitGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_hit_center_near_anchor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t alpha lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ alpha*lambda) (a b : Triangle P) (z : Space)
    (ha : (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty)
    (hb : (oldTriangleImage P (perturbedMap P J lambda p) b ∩ Metric.closedBall z 1).Nonempty) :
    dist (oldAnchor P J a) (oldAnchor P J b) ≤ 2*alpha+4 := by
  have hl0 : 0 ≤ lambda := by linarith
  have hza := hit_center_near_anchor P J p t (alpha*lambda) lambda hJ hl0 hp a z ha
  have hzb := hit_center_near_anchor P J p t (alpha*lambda) lambda hJ hl0 hp b z hb
  have hd := dist_triangle (lambda • oldAnchor P J a) z (lambda • oldAnchor P J b)
  rw [dist_comm (lambda • oldAnchor P J a) z] at hd
  rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hl0,
    ← dist_eq_norm] at hd
  have hlpos : 0 < lambda := by linarith
  apply (mul_le_mul_iff_right₀ hlpos).mp
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
