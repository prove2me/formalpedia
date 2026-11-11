-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.perturbed_segment_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:57:00.933224+00:00
-- url     : https://prove2.me/submissions/c68c5aa4-ecdd-45cd-ae94-445682abbee5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_radial_segment_lower
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_old_segment_upper

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a b c p q s : E) {R k lambda t : ℝ}
    (hR : 0 < R) (hp : ‖p‖ = R) (hpq : ⟪p,q⟫_ℝ ≤ R^2*k)
    (hps : ⟪p,s⟫_ℝ ≤ R^2*k) (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R*(1-k)-lambda ≤ ‖(a+p)-((1-t) • (b+q)+t • (c+s))‖ := by
  have hr := radial_segment_lower p q s hR hp hpq hps ht0 ht1
  have ho := old_segment_upper a b c hab hac ht0 ht1
  have he : p-((1-t) • q+t • s) =
      ((a+p)-((1-t) • (b+q)+t • (c+s))) - (a-((1-t) • b+t • c)) := by module
  rw [he] at hr
  have hn := norm_sub_le ((a+p)-((1-t) • (b+q)+t • (c+s))) (a-((1-t) • b+t • c))
  linarith
end QEC.Coding.BDL26RandomPerturbation
