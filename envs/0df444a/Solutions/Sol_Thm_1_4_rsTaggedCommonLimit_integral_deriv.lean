-- Prove2me | solution 1 for Thm_1_4.rsTaggedCommonLimit_integral_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:15:42.676603+00:00
-- url     : https://prove2.me/submissions/cd7130c5-2c73-4bd1-9413-aa3eb2b30948

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F002
import Theorems.Thm_Thm_1_4_rsTaggedCommonLimit_derivative_of_identity_tagged_limit
import Theorems.Thm_Thm_1_4_rsTaggedCommonLimit_intervalIntegral_id
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution
    {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b))
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) := by
  exact rsTaggedCommonLimit_derivative_of_identity_tagged_limit
    hab hf hαmono hαderiv hα'cont
    (rsTaggedCommonLimit_intervalIntegral_id hab
      (derivative_integrand_continuousOn hf hα'cont))
