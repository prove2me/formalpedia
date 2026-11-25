-- Prove2me | solution 1 for PI.WGB.comp_zero_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:51.119527+00:00
-- url     : https://prove2.me/submissions/21ce73f2-669a-4ec1-a300-d3b29b241d34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ) (m : M)
    (hm : ∀ e ∈ f.support, Finsupp.weight w e ≠ m) : weightedHomogeneousComponent w m f = 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hne
    exact hm e (mem_support_iff.mpr hne) h
  · rfl
end PI.WGB
