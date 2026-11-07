-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.grid_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:20.051466+00:00
-- url     : https://prove2.me/submissions/e2a68ff0-de87-4fe4-ae26-e83dde77d479

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridCoordinate_card
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) : Fintype.card (Grid K) = (2*K+1)^3 := by
  simp only [Grid,Fintype.card_fun,gridCoordinate_card,Fintype.card_fin]
end QEC.Coding.BDL26RandomPerturbation
