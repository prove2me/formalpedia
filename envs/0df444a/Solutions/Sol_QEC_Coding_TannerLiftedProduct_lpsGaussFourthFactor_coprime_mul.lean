-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGaussFourthFactor_coprime_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:06.008276+00:00
-- url     : https://prove2.me/submissions/8cd5c919-8b92-4b07-96c3-f4fb2ce34646

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ) (h : m.Coprime n) :
    lpsGaussFourthFactor (m*n)=lpsGaussFourthFactor m*lpsGaussFourthFactor n := by
  have hcommon : ¬(m%2=0 ∧ n%2=0) := by
    rintro ⟨hm,hn⟩
    have hd : 2 ∣ Nat.gcd m n := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero hm) (Nat.dvd_of_mod_eq_zero hn)
    rw [h.gcd_eq_one] at hd
    norm_num at hd
  have hm2 : m%2=(m%4)%2 := (Nat.mod_mod_of_dvd m (show 2 ∣ 4 by decide)).symm
  have hn2 : n%2=(n%4)%2 := (Nat.mod_mod_of_dvd n (show 2 ∣ 4 by decide)).symm
  have hml : m%4 < 4 := Nat.mod_lt _ (by decide)
  have hnl : n%4 < 4 := Nat.mod_lt _ (by decide)
  unfold lpsGaussFourthFactor
  rw [Nat.mul_mod m n 2,Nat.mul_mod m n 4]
  simp only [hm2,hn2]
  rw [hm2,hn2] at hcommon
  generalize hm : m%4=x at hml hcommon ⊢
  generalize hn : n%4=y at hnl hcommon ⊢
  interval_cases x <;> interval_cases y <;> norm_num at hcommon
  all_goals norm_num
end QEC.Coding.TannerLiftedProduct
