-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_even_coefficient_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:26:21.820225+00:00
-- url     : https://prove2.me/submissions/f47d73e0-53ad-419c-bf2a-1dfe48f4ddf7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_ne_degreePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_two_mul_card_psl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaEisensteinCorrection_even_power


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    (Fintype.card PSL(2,ZMod a.q):ℂ)*
      PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
        (lpsThetaEisensteinCorrection a.q (by intro h;have hm:=a.modFour;omega)))=
      2*(∑ i∈Finset.range (2*n+1),(p:ℂ)^i) := by
  have hp2 : p≠2 := by intro h;have hm:=a.degreeModFour;omega
  have hpq : ¬a.q∣p := fun h => a.ne_degreePrime ((Nat.dvd_prime a.degreePrime).mp h |>.resolve_left a.prime.ne_one)
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection_even_power p a.q _
    (a.degreePrime.odd_of_ne_two hp2) hpq n,ArithmeticFunction.sigma_one_apply_prime_pow a.degreePrime]
  have hqn : 1≤a.q^2 := by have h:=a.prime.one_lt;nlinarith
  have hcard : 2*(Fintype.card PSL(2,ZMod a.q):ℂ)=(a.q:ℂ)*((a.q:ℂ)^2-1) := by
    have h := congrArg (fun x : ℕ => (x:ℂ)) a.two_mul_card_psl
    push_cast [Nat.cast_sub hqn] at h
    exact h
  have hq : (a.q:ℂ)≠0 := by exact_mod_cast a.prime.ne_zero
  have hqs : (a.q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(a.q:ℝ) := by exact_mod_cast a.prime.one_lt
    have hs : (a.q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hs
  push_cast
  field_simp [hq,hqs]
  linear_combination 2*(∑ i∈Finset.range (2*n+1),(p:ℂ)^i)*hcard
end QEC.Coding.TannerLiftedProduct
