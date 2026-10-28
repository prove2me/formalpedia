-- Prove2me | solution 1 for ProbabilityTheory.IsPreBrownianReal.isBrownianReal_mk_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:35:11.690821+00:00
-- url     : https://prove2.me/submissions/167de78a-0a83-4610-81b7-81cbfa6c206a

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Theorems.Thm_ProbabilityTheory_IsPreBrownianReal_memHolder_mk_avram
import Mathlib.Tactic

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : ProbabilityTheory.IsPreBrownianReal X P) :
    ProbabilityTheory.IsBrownianReal (h.mk X) P := by
  refine ⟨h.congr (fun t => (h.exists_continuous_modification.choose_spec.2.1 t).symm), ?_⟩
  refine Filter.Eventually.of_forall (fun ω => continuous_iff_continuousAt.2 (fun t => ?_))
  obtain ⟨U, hU, C, hC⟩ := ProbabilityTheory.IsPreBrownianReal.memHolder_mk_avram X h ω t (4⁻¹)
    (by norm_num) (by rw [inv_lt_inv₀ (by norm_num) (by norm_num)]; norm_num)
  exact (hC.continuousOn (by norm_num)).continuousAt hU
