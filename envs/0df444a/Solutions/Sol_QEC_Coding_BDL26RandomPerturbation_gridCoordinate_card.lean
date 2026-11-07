-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gridCoordinate_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:19.492532+00:00
-- url     : https://prove2.me/submissions/bdba2325-1f4c-43b3-b4fc-440ca02e9165

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) : Fintype.card (GridCoordinate K) = 2*K+1 := by
  simp [GridCoordinate,Int.card_Icc]
  omega
end QEC.Coding.BDL26RandomPerturbation
