-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_surj_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:44.229199+00:00
-- url     : https://prove2.me/submissions/224d3d09-7051-4f1a-8cfb-0f4add507905

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_degree_mapDomain
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_mapDomain_flp_flp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_err_deg

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
theorem _root_.solution (c : ℝ) (hc : 0 < c) :
    ∀ d : ℕ, ∀ Q : PX m n, DegLT d Q → ∃ p, fock c p = Q := by
  classical
  have hc' : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  intro d
  induction d with
  | zero =>
    intro Q hQ
    refine ⟨0, ?_⟩
    rw [fock_zero]
    symm
    by_contra hne
    obtain ⟨t, ht⟩ := MvPolynomial.support_nonempty.mpr hne
    exact Nat.not_lt_zero _ (hQ t ht)
  | succ d ih =>
    intro Q hQ
    set p0 : PX m n := ∑ t ∈ Q.support, (Q.coeff t / (2 * c : ℂ) ^ t.degree) • monomial (Finsupp.mapDomain flp t) 1
    have hp0 : fock c p0 = (∑ t ∈ Q.support, monomial t (Q.coeff t)) + ∑ t ∈ Q.support,
        (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t) := by
      rw [fock_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [fock_smul, fock_monomial, err, smul_sub, Sm, mapDomain_flp_flp, degree_mapDomain, smul_monomial,
        smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc')]
      abel
    have hR : DegLT d (∑ t ∈ Q.support,
        (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t)) := by
      refine DegLT.sum _ _ fun t ht => DegLT.smul _ ?_
      have h1 := err_deg c _ (Finsupp.mapDomain flp t) rfl
      rw [degree_mapDomain] at h1
      exact h1.mono (by have := hQ t ht; omega)
    obtain ⟨p1, hp1⟩ := ih _ hR
    exact ⟨p0 - p1, by rw [fock_sub, hp0, hp1, add_sub_cancel_right]; exact Q.as_sum.symm⟩
end PositivityTheory.Rg.Sw.LC.Basic
