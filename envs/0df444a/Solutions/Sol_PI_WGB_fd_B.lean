-- Prove2me | solution 1 for PI.WGB.fd_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:28.690772+00:00
-- url     : https://prove2.me/submissions/94f26308-11e3-400a-84e3-3c731a51f1b7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Theorems.Thm_PI_WGB_dualWeyl_le_homog_B

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
theorem _root_.solution (N : ℕ) (lam : DomWeight N) : FiniteDimensional ℂ (nablaSq ℂ N lam) := by
  have hle := dualWeyl_le_homog_B N N lam.natW
  have hfin : {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s}.Finite := by
    refine (Finset.finsuppAntidiag Finset.univ (∑ s, lam.natW s)).finite_toSet.subset fun d hd => ?_
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [← hd, Finsupp.degree_eq_sum]
  have hsub : homogeneousSubmodule (Fin N × Fin N) ℂ (∑ s, lam.natW s) ≤
      Submodule.span ℂ ((fun d => (MvPolynomial.monomial d (1 : ℂ))) ''
        {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s}) := by
    intro f hf
    rw [MvPolynomial.mem_homogeneousSubmodule] at hf
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hdeg : d.degree = ∑ s, lam.natW s := by
      have h2 := hf (MvPolynomial.mem_support_iff.mp hd)
      rw [Finsupp.degree_eq_weight_one]
      exact h2
    rw [show MvPolynomial.monomial d (f.coeff d) = f.coeff d • MvPolynomial.monomial d (1 : ℂ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hdeg, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ((fun d => (MvPolynomial.monomial d (1 : ℂ))) ''
      {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s})) :=
    FiniteDimensional.span_of_finite ℂ (hfin.image _)
  exact Submodule.finiteDimensional_of_le (hle.trans hsub)
end PI.WGB
