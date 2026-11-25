-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:12.096142+00:00
-- url     : https://prove2.me/submissions/17af9cde-2100-43e0-be43-966bf17690b8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SecondOperatorMemSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_bf_mono_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_eq_bf
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mapDomain_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_first_family_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_monomial_mem_second_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partner_support_second_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_pos


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {h : PX m n} (hh : h ∈ F1 ε)
    (h0 : ∀ u : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ u.support, ¬ inF1 ε k) → contr c (h * monomial u 1) = 0) : h = 0 := by
  ext s
  rw [coeff_zero]
  by_cases hs : ∀ k ∈ s.support, inF1 ε k
  · have hu := partner_support_second_family ε hs
    have := h0 (s.mapDomain pE) hu
    rw [contr_eq_bf ε c hh (monomial_mem_second_family ε hu 1), rename_monomial, mapDomain_pE_pE, bf_mono_right] at this
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast (wt_pos hc s).ne')
  · by_contra hne
    exact hs ((mem_first_family_iff ε h).mp hh s (MvPolynomial.mem_support_iff.mpr hne))
end PositivityTheory.Rg.Sw.LC.CoreC
