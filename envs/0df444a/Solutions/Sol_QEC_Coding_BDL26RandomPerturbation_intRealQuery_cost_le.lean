-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.intRealQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:03.984671+00:00
-- url     : https://prove2.me/submissions/1541da87-49f9-40fb-9805-1d0eac9e3d01

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_natRealQuery_cost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (z : ℤ) : (intRealQuery z).2 ≤ z.natAbs+2 := by
  cases z <;> simp [intRealQuery,natRealQuery_cost]
end QEC.Coding.BDL26RandomPerturbation
