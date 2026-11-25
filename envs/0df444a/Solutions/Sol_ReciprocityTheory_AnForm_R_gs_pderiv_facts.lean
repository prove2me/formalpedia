-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.gs_pderiv_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:18.125423+00:00
-- url     : https://prove2.me/submissions/fe843f7b-af8e-4935-b7fd-8b7db6490954

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type*} (p : MvPolynomial σ ℚ) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by
  classical

  have key : ∀ m ∈ (pderiv j p).support, ∃ m' ∈ p.support, m = m' - Finsupp.single j 1 := by
    intro m hm
    rw [p.as_sum, map_sum] at hm
    obtain ⟨m', hm', hmm⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
    rw [pderiv_monomial] at hmm
    exact ⟨m', hm', Finset.mem_singleton.1 (support_monomial_subset hmm)⟩
  have hdeg : ∀ m ∈ (pderiv j p).support, m j < degreeOf j p := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := key m hm
    have h1 := monomial_le_degreeOf j hm'
    have h2 : (m' - Finsupp.single j 1 : σ →₀ ℕ) j = m' j - 1 := by simp
    rw [h2]
    omega
  refine ⟨?_, (degreeOf_lt_iff hj).2 hdeg, ?_⟩
  · obtain ⟨m', hm', hm'j⟩ : ∃ m' ∈ p.support, 0 < m' j := by
      by_contra hcon
      push_neg at hcon
      have h3 : degreeOf j p < 1 :=
        (degreeOf_lt_iff one_pos).2 (fun m hm => by have := hcon m hm; omega)
      omega
    intro h0
    have hc : coeff (m' - Finsupp.single j 1) (pderiv j p) = coeff m' p * (m' j : ℚ) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum, coeff_sum]
      simp only [pderiv_monomial, coeff_monomial]
      rw [Finset.sum_eq_single m']
      · simp
      · intro b _ hne
        split_ifs with h
        · have hbj : b j = 0 := by
            by_contra hbj
            apply hne
            have e1 : b - Finsupp.single j 1 + Finsupp.single j 1 = b :=
              tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))
            have e2 : m' - Finsupp.single j 1 + Finsupp.single j 1 = m' :=
              tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))
            rw [← e1, ← e2, h]
          simp [hbj]
        · rfl
      · intro h
        exact absurd hm' h
    rw [h0, coeff_zero] at hc
    have hne : coeff m' p ≠ 0 := mem_support_iff.1 hm'
    have hne2 : (m' j : ℚ) ≠ 0 := by exact_mod_cast hm'j.ne'
    exact mul_ne_zero hne hne2 hc.symm
  · intro i hi
    rw [mem_vars] at hi ⊢
    obtain ⟨m, hm, him⟩ := hi
    obtain ⟨m', hm', rfl⟩ := key m hm
    refine ⟨m', hm', ?_⟩
    rw [Finsupp.mem_support_iff] at him ⊢
    intro h0
    apply him
    simp [h0]
end ReciprocityTheory.AnForm.R
