-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.geometricParameters_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:21:44.533998+00:00
-- url     : https://prove2.me/submissions/f721c6e0-065e-488b-82e8-0a30ae538763

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_cap_integer
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_input_density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_integer_scale
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_local_pool_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (densityLower : ℝ) :
    Nonempty (GeometricParameters densityLower) := by
  obtain ⟨m,hm,hw⟩ := exists_cap_integer
  obtain ⟨t,ht,htp,hth⟩ := exists_input_density
    (max densityLower triangleDensityBound) (densityHandoff m)
  obtain ⟨M,hM⟩ := exists_local_pool_bound t (anchorRadius m)
  obtain ⟨lambda,hl,hr,hprob⟩ := exists_integer_scale
    (alpha := 6*(m : ℝ))
    (probabilityConstant := probabilityCoefficient (6*m) (capCutoff m))
    (by positivity) (dependencyBound M)
  exact ⟨⟨m,t,M,lambda,hm,hw,ht,
    (le_max_left _ _).trans_lt htp,(le_max_right _ _).trans_lt htp,
    hth,hM,hl,hr,hprob⟩⟩
end QEC.Coding.BDL26RandomPerturbation
