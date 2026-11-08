-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gridPointQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:54.489655+00:00
-- url     : https://prove2.me/submissions/a123e6f3-7f7c-4b5b-8ec1-7ad4fb710ee2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_intRealQuery_value
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) (g : Grid K) : (gridPointQuery K g).1 = gridPoint K g := by
  ext j
  fin_cases j <;> simp [gridPointQuery,gridPoint,intRealQuery_value]
end QEC.Coding.BDL26RandomPerturbation
