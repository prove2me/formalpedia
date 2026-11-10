-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.GeometricParameters.probability_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:14:18.785635+00:00
-- url     : https://prove2.me/submissions/cea736c8-2ebc-4d8d-b2fc-996bdd24384d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
namespace GeometricParameters
theorem _root_.solution {densityLower : ℝ}
    (p : GeometricParameters densityLower) :
    probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) ≤
      1/(4*((dependencyBound p.M : ℝ)+1)) := by
  have hl : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hd : 0 < 4*((dependencyBound p.M : ℝ)+1) := by positivity
  apply (div_le_div_iff₀ hl hd).mpr
  nlinarith [p.probability]
end GeometricParameters
end QEC.Coding.BDL26RandomPerturbation
