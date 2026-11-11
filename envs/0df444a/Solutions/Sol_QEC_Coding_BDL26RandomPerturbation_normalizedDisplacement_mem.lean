-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.normalizedDisplacement_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:49:50.947269+00:00
-- url     : https://prove2.me/submissions/52e68c03-10ec-4ee0-ab7f-1a4c7308d216

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_normalizedDisplacement_smul
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacementCap_preimage


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (p : Space) {R c : ℝ} (hR : 0 < R) (u : Sphere)
    (hp : p ∈ displacementCap R u c) : normalizedDisplacement p hR hp.1 ∈ cap u c := by
  have hi : R • (normalizedDisplacement p hR hp.1 : Space) ∈ displacementCap R u c := by
    rwa [normalizedDisplacement_smul]
  have he := displacementCap_preimage hR u c
  change normalizedDisplacement p hR hp.1 ∈
    ((fun s : Sphere => R • (s : Space)) ⁻¹' displacementCap R u c) at hi
  rwa [he] at hi
end QEC.Coding.BDL26RandomPerturbation
