-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.cap_integer_narrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:50:00.803469+00:00
-- url     : https://prove2.me/submissions/954cf584-7ad3-462a-b141-4f7afc52f544

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    0 < (1 : ℝ)/(12*m) ∧ (1 : ℝ)/(12*m) ≤ 1/24 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (12 : ℝ)*m := by positivity
  refine ⟨by positivity, ?_⟩
  apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 24)).mpr
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
