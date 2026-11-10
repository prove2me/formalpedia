-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.scaled_grid_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:00:18.343103+00:00
-- url     : https://prove2.me/submissions/dba36d50-18ec-4379-aae3-df5b62c5c2d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_grid_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a lambda : ℕ) (hl : 1 ≤ lambda) :
    Fintype.card (Grid (a*lambda)) ≤ (2*a+1)^3*lambda^3 := by
  rw [grid_card]
  have hb : 2*(a*lambda)+1 ≤ (2*a+1)*lambda := by nlinarith
  calc
    _ ≤ ((2*a+1)*lambda)^3 := Nat.pow_le_pow_left hb 3
    _ = _ := by rw [mul_pow]
end QEC.Coding.BDL26RandomPerturbation
