-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleSupport_disjoint_of_color
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:50:18.779992+00:00
-- url     : https://prove2.me/submissions/47aa32b4-4197-4b8b-8c4f-544107dad943

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleColor_same_vertex
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
noncomputable section
variable (P : TannerSquarePresentation)
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {a b : Triangle P} (hne : a ≠ b)
    (hc : triangleColor P a = triangleColor P b) :
    Disjoint (triangleSupport P a) (triangleSupport P b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
  exact hne (triangleColor_same_vertex P hc (hi.trans hj.symm))
end QEC.Coding.BDL26RandomPerturbation
