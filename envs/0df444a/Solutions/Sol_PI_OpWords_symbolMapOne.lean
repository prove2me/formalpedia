-- Prove2me | solution 1 for PI.OpWords.symbolMapOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:08.841432+00:00
-- url     : https://prove2.me/submissions/2f186ea9-5aef-499b-b948-d426db9748b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Theorems.Thm_PI_OpWords_coeff_kappa
import Theorems.Thm_PI_OpWords_mono_val
import Theorems.Thm_PI_OpWords_pol_ext
import Theorems.Thm_PI_OpWords_prodFact_fintype
import Theorems.Thm_PI_OpWords_sumElim_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Finsupp
noncomputable section
namespace PI.OpWords
private theorem coeff_sumElim_tt_pow (K : Type) [Field K] (k d : ℕ) (m g : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (tt K k ^ d) =
      if m = g ∧ g.degree = d then ((Nat.multinomial Finset.univ ⇑g : ℕ) : K) else 0 := by
  classical
  have hprod : ∀ f : Fin k → ℕ, ∏ i, (X (Sum.inl i) * X (Sum.inr i) : Pol K k) ^ f i =
      monomial (Finsupp.sumElim (Finsupp.equivFunOnFinite.symm f) (Finsupp.equivFunOnFinite.symm f)) 1 := by
    intro f
    rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
    simp [mul_pow, Finset.prod_mul_distrib]
  rw [tt, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp only [hprod, ← map_natCast (C : K →+* Pol K k), coeff_C_mul, coeff_monomial, sumElim_inj, mul_ite,
    mul_one, mul_zero]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [if_pos ⟨hmg, hd⟩, Finset.sum_eq_single (⇑g)]
    · simp [hmg]
    · intro f _ hf
      rw [if_neg]
      rintro ⟨_, h2⟩
      apply hf
      rw [← h2]
      simp
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.degree_eq_sum]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply h
    refine ⟨h1.symm.trans h2, ?_⟩
    rw [← h2, Finsupp.degree_eq_sum]
    have h3 := (Finset.mem_piAntidiag.1 hf).1
    simpa using h3
end PI.OpWords
end
end

set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution : KappaId := by
  intro K _ _ k d
  apply pol_ext
  intro m g
  rw [coeff_kappa, Module.End.one_apply, mono_val, coeff_smul, smul_eq_mul, coeff_sumElim_tt_pow]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [if_pos hd, if_pos ⟨hmg, hd⟩, coeff_monomial, if_pos hmg.symm, mul_one]
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin k)) ⇑g
    have hsum : ∑ i, g i = d := by rw [← hd, Finsupp.degree_eq_sum]
    rw [hsum] at hspec
    have hcast : ((d.factorial : ℕ) : K) =
        (∏ i, ((g i).factorial : K)) * (Nat.multinomial Finset.univ ⇑g : K) := by
      exact_mod_cast hspec.symm
    have hM : (Nat.multinomial Finset.univ ⇑g : K) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcast
      exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)) hcast
    unfold invFact
    rw [prodFact_fintype, hcast, mul_inv, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  · rw [if_neg h, mul_zero]
    split_ifs with hd
    · rw [coeff_monomial, if_neg (fun hgm => h ⟨hgm.symm, hd⟩), mul_zero]
    · rw [coeff_zero, mul_zero]
end PI.OpWords
