-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:29.236083+00:00
-- url     : https://prove2.me/submissions/191e8de5-87f5-4032-b2a0-26f6598f9a99

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_flp_injective
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_degree_mapDomain
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_err_deg
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) (hc : 0 < c) : Function.Injective (fock (m := m) (n := n) c) := by
  classical
  intro p q hpq
  rw [← sub_eq_zero]
  have h0 : fock c (p - q) = 0 := by rw [fock_sub, hpq, sub_self]
  set r := p - q
  by_contra hr
  have hne : r.support.Nonempty := MvPolynomial.support_nonempty.mpr hr
  obtain ⟨s0, hs0, hmax⟩ := Finset.exists_max_image r.support Finsupp.degree hne
  have key := congrArg (MvPolynomial.coeff (Finsupp.mapDomain flp s0)) h0
  rw [fock_decomp, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, Finset.sum_eq_single s0] at key
  · rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial, if_pos rfl] at key
    have herr : MvPolynomial.coeff (Finsupp.mapDomain flp s0) (err c s0) = 0 := by
      by_contra hne'
      have := err_deg c _ s0 rfl _ (MvPolynomial.mem_support_iff.mpr hne')
      rw [degree_mapDomain] at this
      exact lt_irrefl _ this
    rw [herr, add_zero, smul_eq_mul] at key
    have hc' : (2 * c : ℂ) ≠ 0 := by
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      exact mul_ne_zero two_ne_zero this
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hs0) (pow_ne_zero _ hc')) key
  · intro s hs hne'
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial]
    have h1 : Finsupp.mapDomain flp s ≠ Finsupp.mapDomain flp s0 :=
      fun h => hne' (Finsupp.mapDomain_injective flp_injective h)
    rw [if_neg h1]
    have herr : MvPolynomial.coeff (Finsupp.mapDomain flp s0) (err c s) = 0 := by
      by_contra hne''
      have := err_deg c _ s rfl _ (MvPolynomial.mem_support_iff.mpr hne'')
      rw [degree_mapDomain] at this
      exact absurd (hmax s hs) (not_le.mpr this)
    rw [herr, add_zero, smul_zero]
  · intro h; exact absurd hs0 h
end PositivityTheory.Rg.Sw.LC.Basic
