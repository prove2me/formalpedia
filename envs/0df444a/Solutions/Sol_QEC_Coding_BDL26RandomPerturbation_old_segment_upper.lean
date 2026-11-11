-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.old_segment_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:47:03.508916+00:00
-- url     : https://prove2.me/submissions/5c3023d7-000a-4298-8653-7490b0768bf7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a b c : E) {lambda t : ℝ}
    (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖a - ((1-t) • b + t • c)‖ ≤ lambda := by
  have he : a - ((1-t) • b + t • c) = (1-t) • (a-b) + t • (a-c) := by module
  rw [he]
  calc
    _ ≤ ‖(1-t) • (a-b)‖ + ‖t • (a-c)‖ := norm_add_le _ _
    _ = (1-t) * ‖a-b‖ + t * ‖a-c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1-t) * lambda + t * lambda :=
      add_le_add (mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hac ht0)
    _ = lambda := by ring
end QEC.Coding.BDL26RandomPerturbation
