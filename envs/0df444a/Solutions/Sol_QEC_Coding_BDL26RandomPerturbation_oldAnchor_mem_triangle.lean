-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.oldAnchor_mem_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:17:01.616347+00:00
-- url     : https://prove2.me/submissions/cf9afc23-3aff-42a3-a148-2eb7e27daed8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : Triangle P) :
    oldAnchor P J a ∈ oldTriangleImage P (fun v => (1/2 : ℝ) • J v) a := by
  rw [oldTriangleImage_eq]
  exact subset_convexHull ℝ _ ⟨0,rfl⟩
end QEC.Coding.BDL26RandomPerturbation
