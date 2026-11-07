-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.intRealQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:16.355175+00:00
-- url     : https://prove2.me/submissions/c02f1dd4-22e7-4ef6-a7a4-31844de90f78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_natRealQuery_value
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (z : ℤ) : (intRealQuery z).1 = (z : ℝ) := by
  cases z <;> simp [intRealQuery,natRealQuery_value]
end QEC.Coding.BDL26RandomPerturbation
