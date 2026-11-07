-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gram_residual_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:47.43476+00:00
-- url     : https://prove2.me/submissions/0240ccec-7a9b-4372-9c5a-ae3b6a4b75cb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c : Space) (hb : b ≠ 0) :
    ‖b‖^2*‖c-(inner ℝ b c/‖b‖^2) • b‖^2 = gramDet b c := by
  have hQ : ‖b‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm b c,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold gramDet
  field_simp [hQ]
  <;> ring
end QEC.Coding.BDL26RandomPerturbation
