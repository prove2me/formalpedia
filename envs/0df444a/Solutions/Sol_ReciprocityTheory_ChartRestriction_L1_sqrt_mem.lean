-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sqrt_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:11.767621+00:00
-- url     : https://prove2.me/submissions/7065645f-f1a5-40e1-a5ef-f0f11a0c0f85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hensel_mem
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_lt_one_complexPadic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : l ≠ 2) (c y : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (hy : ‖y‖ = 1) (h : y ^ 2 = c) : y ∈ MaximalUnramifiedExtension l := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hle : ‖(2 : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2
      exact_mod_cast this
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hl)
    have hg : Int.gcd 2 (l : ℤ) = 1 := by
      have := Int.gcd_natCast_natCast 2 l
      simpa [Nat.Coprime.gcd_eq_one hcop] using this
    have hz' : (1 : ℤ) = 2 * Int.gcdA 2 l + l * Int.gcdB 2 l := by
      rw [← Int.gcd_eq_gcd_ab, hg]
      rfl
    have h1 := congrArg (Int.cast : ℤ → ℂ_[l]) hz'
    push_cast at h1
    have hm := IsUltrametricDist.norm_add_le_max (2 * ((Int.gcdA 2 l : ℤ) : ℂ_[l]))
      ((l : ℂ_[l]) * ((Int.gcdB 2 l : ℤ) : ℂ_[l]))
    rw [← h1, norm_one, norm_mul, norm_mul] at hm
    have ha := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdA 2 l)
    have hb := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdB 2 l)
    have hl1 := norm_prime_lt_one_complexPadic (l := l)
    rcases le_max_iff.1 hm with h | h
    · nlinarith [norm_nonneg ((Int.gcdA 2 l : ℤ) : ℂ_[l]), norm_nonneg (2 : ℂ_[l])]
    · nlinarith [norm_nonneg ((Int.gcdB 2 l : ℤ) : ℂ_[l]), norm_nonneg (l : ℂ_[l])]
  have hc1 : ‖c‖ = 1 := by rw [← h, norm_pow, hy, one_pow]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.C c) (fun i => ?_) (fun i => ?_) y hy.le ?_ ?_
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem (MaximalUnramifiedExtension l).zero_mem
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem (MaximalUnramifiedExtension l).zero_mem
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs <;> first | (exfalso; omega) | simp [hc1]
  · simp [h]
  · simp [Polynomial.derivative_X_pow, norm_mul, hy]
    rw [one_add_one_eq_two]
    exact h2
end ReciprocityTheory.ChartRestriction.L1
