-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.radial_segment_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:50:25.109879+00:00
-- url     : https://prove2.me/submissions/9d6ff618-2144-4945-a2a3-5f32535eb326

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
theorem _root_.solution (p q s : E) {R c t : ℝ} (hR : 0 < R)
    (hp : ‖p‖ = R) (hpq : ⟪p, q⟫_ℝ ≤ R ^ 2 * c)
    (hps : ⟪p, s⟫_ℝ ≤ R ^ 2 * c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R * (1 - c) ≤ ‖p - ((1 - t) • q + t • s)‖ := by
  have hq := mul_le_mul_of_nonneg_left hpq (sub_nonneg.mpr ht1)
  have hs := mul_le_mul_of_nonneg_left hps ht0
  have hb := real_inner_le_norm p (p - ((1-t) • q + t • s))
  rw [inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hp] at hb
  have hh : R * (R * (1-c)) ≤ R * ‖p - ((1-t) • q + t • s)‖ := by nlinarith
  exact (mul_le_mul_iff_right₀ hR).mp hh
end QEC.Coding.BDL26RandomPerturbation
