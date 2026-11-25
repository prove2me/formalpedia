-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_eq_monomial_of_homog_8e8bef672e41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:06.310897+00:00
-- url     : https://prove2.me/submissions/7f066b6e-4e3f-405b-8fcc-3f0511f471b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_eq_6728c507711f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution [DecidableEq ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0)
    (h : ∀ x, ∃ d, IsWeightedHomogeneous (indW (· = x)) g d) :
    ∃ m, g = monomial m (coeff m g) ∧ coeff m g ≠ 0 := by
  choose d hd using h
  have key : ∀ m ∈ g.support, ∀ x, m x = d x := by
    intro m hm x
    have := hd x (mem_support_iff.mp hm)
    rwa [weight_indW_eq] at this
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hg
  refine ⟨m, ?_, mem_support_iff.mp hm⟩
  ext n
  rw [coeff_monomial]
  split_ifs with hmn
  · rw [hmn]
  · by_contra hne
    have hn : n ∈ g.support := mem_support_iff.mpr hne
    exact hmn (Finsupp.ext fun x => (key m hm x).trans (key n hn x).symm)
end GroundTheory.Heights₂.Heights.LogInt
