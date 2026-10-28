-- Prove2me | solution 1 for ProbabilityTheory.isBrownianReal_brownian_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:37:47.608213+00:00
-- url     : https://prove2.me/submissions/0266a114-28e5-4336-9b26-53dfefeb6927

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Theorems.Thm_ProbabilityTheory_IsPreBrownianReal_memHolder_mk_avram
import Mathlib.Tactic

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

theorem solution :
    ProbabilityTheory.IsBrownianReal ProbabilityTheory.brownian ProbabilityTheory.gaussianLimit := by
  have h := ProbabilityTheory.isPreBrownianReal_preBrownian
  show ProbabilityTheory.IsBrownianReal (h.mk ProbabilityTheory.preBrownian) ProbabilityTheory.gaussianLimit
  refine ⟨h.congr (fun t => (h.exists_continuous_modification.choose_spec.2.1 t).symm), ?_⟩
  refine Filter.Eventually.of_forall (fun ω => continuous_iff_continuousAt.2 (fun t => ?_))
  obtain ⟨U, hU, C, hC⟩ := ProbabilityTheory.IsPreBrownianReal.memHolder_mk_avram ProbabilityTheory.preBrownian h ω t (4⁻¹)
    (by norm_num) (by rw [inv_lt_inv₀ (by norm_num) (by norm_num)]; norm_num)
  exact (hC.continuousOn (by norm_num)).continuousAt hU
