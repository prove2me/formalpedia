-- Prove2me | solution 1 for PI.OpWords.bihom_le_Sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:31.95861+00:00
-- url     : https://prove2.me/submissions/03f5cf66-8c12-42d5-9960-9c395b53e8ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange
import Theorems.Thm_PI_OpWords_mem_Sc
import Theorems.Thm_PI_OpWords_Wc_mono
import Theorems.Thm_PI_OpWords_Ed_mul_Wc
import Theorems.Thm_PI_OpWords_wtXSum
import Theorems.Thm_PI_OpWords_wtXiSum
import Theorems.Thm_PI_OpWords_bihom_zero_const
import Theorems.Thm_PI_OpWords_iwh_X_pderiv
import Theorems.Thm_PI_OpWords_pderiv_inl_tt
import Theorems.Thm_PI_OpWords_symbolMapMulLeft
import Theorems.Thm_PI_OpWords_symbolMapOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable (K : Type) [Field K] [CharZero K] (k d : ℕ)
namespace PI.OpWords
theorem _root_.solution : ∀ c, c ≤ d → Bihom K k c ≤ Sc K k d c
  | 0, _ => by
    intro g hg
    obtain ⟨r, rfl⟩ := bihom_zero_const K k g hg
    rw [mem_Sc]
    refine ⟨(r * (d.factorial : K)) • 1, Submodule.smul_mem _ _
      (Submodule.subset_span ⟨[], by simp, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩), ?_⟩
    rw [map_smul, symbolMapOne, smul_smul, mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)), mul_one, Nat.sub_zero,
      smul_eq_C_mul, mul_comm]
  | c + 1, hc => by
    have IH := solution c (by omega)
    obtain ⟨n, hn⟩ : ∃ n, d - c = n + 1 := ⟨d - c - 1, by omega⟩
    have hn2 : d - (c + 1) = n := by omega
    intro g hg
    have hg' := hg
    rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
      mem_weightedHomogeneousSubmodule] at hg'
    rw [as_sum g]
    apply Submodule.sum_mem
    intro m hmS
    have hne : coeff m g ≠ 0 := MvPolynomial.mem_support_iff.1 hmS
    have hw1 := hg'.1 hne
    have hw2 := hg'.2 hne
    rw [show monomial m (coeff m g) = coeff m g • monomial m (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one]]
    apply Submodule.smul_mem

    rw [wtXSum] at hw1
    rw [wtXiSum] at hw2
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; omega)
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw2]; omega)
    obtain ⟨m', rfl⟩ : ∃ m' : Fin k ⊕ Fin k →₀ ℕ,
        m = m' + single (Sum.inl a) 1 + single (Sum.inr b) 1 := by
      refine ⟨m - single (Sum.inl a) 1 - single (Sum.inr b) 1, ?_⟩
      ext i
      rcases i with i | i
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inl.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inr.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
    have hmono : X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K) =
        monomial (m' + single (Sum.inl a) 1 + single (Sum.inr b) 1) 1 := by
      simp only [X, monomial_mul, one_mul]
      congr 1
      abel
    have hw1' : weight (wx k) m' = c := by
      have := hw1
      rw [← wtXSum, map_add, map_add, weight_single, weight_single] at this
      have e1 : wx k (Sum.inl a) = 1 := rfl
      have e2 : wx k (Sum.inr b) = 0 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hw2' : weight (wxi k) m' = c := by
      have := hw2
      rw [← wtXiSum, map_add, map_add, weight_single, weight_single] at this
      have e1 : wxi k (Sum.inl a) = 0 := rfl
      have e2 : wxi k (Sum.inr b) = 1 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hh : monomial m' (1 : K) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule]
      exact ⟨isWeightedHomogeneous_monomial _ _ _ hw1', isWeightedHomogeneous_monomial _ _ _ hw2'⟩
    have hh' : X (Sum.inl a) * pderiv (Sum.inl b) (monomial m' (1 : K)) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule] at hh ⊢
      exact ⟨iwh_X_pderiv _ _ _ (by simp [wx]) hh.1, iwh_X_pderiv _ _ _ (by simp [wxi]) hh.2⟩
    obtain ⟨B, hB, hBk⟩ := (mem_Sc K k d c _).1 (IH hh)
    obtain ⟨B', hB', hB'k⟩ := (mem_Sc K k d c _).1 (IH hh')
    rw [hn] at hBk hB'k
    rw [mem_Sc, hn2, ← hmono]
    refine ⟨(((n + 1 : ℕ) : K)⁻¹) • (Formalism.MainNotions.TestSideCounting.Ed K k d a b * B - B'),
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (Ed_mul_Wc K k d c a b hB)
        (Wc_mono K k d (Nat.le_succ c) hB')), ?_⟩
    rw [map_smul, map_sub, symbolMapMulLeft, hBk, hB'k, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_inl_tt, Nat.add_sub_cancel, smul_eq_C_mul]
    simp only [smul_eq_mul, nsmul_eq_mul]
    have hC : (C (((n + 1 : ℕ) : K)⁻¹) : Pol K k) * ((n + 1 : ℕ) : Pol K k) = 1 := by
      rw [← map_natCast (C : K →+* Pol K k), ← map_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)), map_one]
    linear_combination (tt K k ^ n * (X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K))) * hC
end PI.OpWords
