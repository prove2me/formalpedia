-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:25.084897+00:00
-- url     : https://prove2.me/submissions/3ba9d130-9617-42d2-9d7c-3da0054f3469

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreC PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
variable (w : (τ →₀ ℕ) → ℂ)
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (s t : τ →₀ ℕ) (a b : ℂ) :
    gf w (monomial s a) (monomial t b) = if s = t then star a * b * w s else 0 := by
  classical
  rw [gf_eq w {s, t} ((support_monomial_subset).trans (by simp)) ((support_monomial_subset).trans (by simp))]
  by_cases h : s = t
  · subst h; simp [coeff_monomial]
  · rw [Finset.sum_pair h]; simp [coeff_monomial, h, Ne.symm h]
end PositivityTheory.Rg.Sw.LC.CoreC.G
