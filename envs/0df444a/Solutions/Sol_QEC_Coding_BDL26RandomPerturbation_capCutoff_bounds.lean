-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.capCutoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:07:47.288706+00:00
-- url     : https://prove2.me/submissions/3f96cd74-f875-4344-bcb9-4846a664f635

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cos_mem_open_unit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    -1 < capCutoff m ∧ capCutoff m < 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 1/(12*(m : ℝ)) := by positivity
  have hsmall : 1/(12*(m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 12*(m : ℝ))).mpr
    linarith
  have hpi := Real.two_le_pi
  exact cos_mem_open_unit hp (by linarith)
end QEC.Coding.BDL26RandomPerturbation
