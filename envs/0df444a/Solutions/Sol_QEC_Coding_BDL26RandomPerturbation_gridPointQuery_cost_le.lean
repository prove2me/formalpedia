-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gridPointQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:15.040266+00:00
-- url     : https://prove2.me/submissions/3dfffa82-893f-456d-bfe3-9228de5405aa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_intRealQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridCoordinate_abs_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) (g : Grid K) : (gridPointQuery K g).2 ≤ 3*K+9 := by
  have h0 := (intRealQuery_cost_le (g 0).val).trans (Nat.add_le_add_right (gridCoordinate_abs_le K (g 0)) 2)
  have h1 := (intRealQuery_cost_le (g 1).val).trans (Nat.add_le_add_right (gridCoordinate_abs_le K (g 1)) 2)
  have h2 := (intRealQuery_cost_le (g 2).val).trans (Nat.add_le_add_right (gridCoordinate_abs_le K (g 2)) 2)
  dsimp only [gridPointQuery]
  omega
end QEC.Coding.BDL26RandomPerturbation
