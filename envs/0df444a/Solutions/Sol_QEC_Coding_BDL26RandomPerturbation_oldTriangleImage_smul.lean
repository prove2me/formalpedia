-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:37:42.658278+00:00
-- url     : https://prove2.me/submissions/4e9d3ad3-9962-4f1e-8d83-099b304a9152

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_eq
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : ℝ) (t : Triangle P) :
    oldTriangleImage P (fun v => a • J v) t =
      (fun p => a • p) '' oldTriangleImage P J t := by
  rw [oldTriangleImage_eq,oldTriangleImage_eq]
  have h := (LinearMap.lsmul ℝ Space a).image_convexHull
    (Set.range fun i => J (triangleVertex P t i))
  change (fun p : Space => a • p) '' convexHull ℝ (Set.range fun i => J (triangleVertex P t i)) =
    convexHull ℝ ((fun p : Space => a • p) '' Set.range fun i => J (triangleVertex P t i)) at h
  rw [← Set.range_comp'] at h
  exact h.symm
end QEC.Coding.BDL26RandomPerturbation
