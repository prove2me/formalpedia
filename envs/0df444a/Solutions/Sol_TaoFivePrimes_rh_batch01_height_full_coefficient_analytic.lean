-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_full_coefficient_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:34:11.754982+00:00
-- url     : https://prove2.me/submissions/39989804-4d7f-4387-8db8-3f1c39db9d8a

import Definitions.Def_TaoFivePrimes_RHBatch01CoefficientFunctions
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_coefficient_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_grouped_analytic
import Theorems.Thm_TaoFivePrimes_rh_high_height_finite_dirichlet50000
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_taylor24
namespace RHBatch01FullCoefficientProof
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHBatch01DirichletArithmetic
export _root_.RHBatch01DirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHBatch01DirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHBatch01FullCoefficient
export _root_.RHBatch01FullCoefficient (F L W delta group weight)
end RHBatch01FullCoefficient
namespace RHBatch01GammaArithmetic
export _root_.RHBatch01GammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHBatch01GammaArithmetic
namespace RHBatch01GammaGuards
export _root_.RHBatch01GammaGuards (guard)
end RHBatch01GammaGuards
namespace RHBatch01GenericExpHorner
export _root_.RHBatch01GenericExpHorner (cn cp horner sn sp)
end RHBatch01GenericExpHorner
namespace RHHighGlobalBinTree
export _root_.RHHighGlobalBinTree (flatten get get_sound length_flatten size valid zeroWord)
end RHHighGlobalBinTree
namespace RHBatch01GlobalDirichletBins
export _root_.RHBatch01GlobalDirichletBins (coefficient coefficient_bound coefficients_checked flatten_checked groups tree valid_checked values word word_eq)
end RHBatch01GlobalDirichletBins
namespace RHBatch01GlobalDirichletBins00
export _root_.RHBatch01GlobalDirichletBins00 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHBatch01GlobalDirichletBins00
namespace RHBatch01GlobalDirichletBins01
export _root_.RHBatch01GlobalDirichletBins01 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHBatch01GlobalDirichletBins01
namespace RHBatch01GlobalDirichletBins02
export _root_.RHBatch01GlobalDirichletBins02 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHBatch01GlobalDirichletBins02
namespace RHBatch01GlobalDirichletBins03
export _root_.RHBatch01GlobalDirichletBins03 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 rows)
end RHBatch01GlobalDirichletBins03
namespace RHBatch01HomogeneousHorner
export _root_.RHBatch01HomogeneousHorner (hom)
end RHBatch01HomogeneousHorner
namespace RHBatch01LogData
export _root_.RHBatch01LogData (D F coefficients denominator log2 log2pi numerator rounded)
end RHBatch01LogData
namespace RHBatch01NegativeExp
export _root_.RHBatch01NegativeExp (denominator en ep numerator seed)
end RHBatch01NegativeExp
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
open scoped FourierTransform
namespace RHBatch01FullCoefficient
lemma log_identity (n : Nat) (hn:1 ≤ n) : Real.log ((n:ℝ)*Real.sqrt Real.pi)=L n := by
 rw [Real.log_mul (by exact_mod_cast (show n≠0 by omega)) (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)),Real.log_sqrt Real.pi_pos.le]
 rfl
lemma weight_norm (n : Nat) (hn:1 ≤ n) : ‖weight n‖≤1 := by
 have hnR:(1:ℝ)≤n:=by exact_mod_cast hn
 have hL:0 ≤ L n := add_nonneg (Real.log_nonneg hnR) (div_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three])) (by norm_num))
 rw [weight,Complex.norm_exp,Real.exp_le_one_iff]
 norm_num [Complex.mul_re,Complex.mul_im] <;> linarith only[hL]

lemma taylor_term (m n : Nat) (hn:1 ≤ n ∧ n≤50000) :
 ‖weight n*𝓕 (RHHighSamplingFunctions.gammaWindow 3289999808) ((m:ℝ)/512+L n/(2*Real.pi))-
  ∑k:Fin 24,(weight n*(delta n:ℂ)^k.val)*F m (RHBatch01DirichletArithmetic.bin n) k.val‖≤1/10^20 := by
 have hd:|delta n|≤1/2 := (TaoFivePrimes.rh_batch01_height_dirichlet_coefficient_enclosure n 0 hn (by decide)).2.1
 have h:=TaoFivePrimes.rh_high_height_gamma_fourier_taylor24 3289999808 (delta n)
  (((m+RHBatch01DirichletArithmetic.bin n:Nat):ℝ)/512) hd
 have he:(((m+RHBatch01DirichletArithmetic.bin n:Nat):ℝ)/512)+delta n/512=(m:ℝ)/512+L n/(2*Real.pi) := by
  unfold delta
  push_cast
  ring
 rw [he,Finset.sum_range] at h
 have heq:weight n*𝓕 (RHHighSamplingFunctions.gammaWindow 3289999808) ((m:ℝ)/512+L n/(2*Real.pi))-
  ∑k:Fin 24,(weight n*(delta n:ℂ)^k.val)*F m (RHBatch01DirichletArithmetic.bin n) k.val=
  weight n*(𝓕 (RHHighSamplingFunctions.gammaWindow 3289999808) ((m:ℝ)/512+L n/(2*Real.pi))-
   ∑k:Fin 24,(delta n:ℂ)^k.val*F m (RHBatch01DirichletArithmetic.bin n) k.val) := by
  rw [mul_sub,Finset.mul_sum]
  simp only [mul_assoc]
 rw [heq,norm_mul]
 exact (mul_le_mul (weight_norm n hn.1) h (norm_nonneg _) (by norm_num)).trans_eq (by ring)
lemma analytic_reduction (m : Nat) (hm:m≤1024) (G : Nat→Nat→ℂ)
 (hF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖F m b k‖≤65537)
 (heF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖F m b k-G b k‖≤1/10^15) :
 ‖(1/512:ℂ)*𝓕 W ((m:ℝ)/512)-(1/512:ℂ)*group G‖≤3/10^15 := by
 let A:ℂ:=∑n:Fin 50000,weight (n.val+1)*𝓕 (RHHighSamplingFunctions.gammaWindow 3289999808)
  ((m:ℝ)/512+L (n.val+1)/(2*Real.pi))
 let D:ℂ:=∑n:Fin 50000,∑k:Fin 24,
  (weight (n.val+1)*(delta (n.val+1):ℂ)^k.val)*F m (RHBatch01DirichletArithmetic.bin (n.val+1)) k.val
 have hf:‖𝓕 W ((m:ℝ)/512)-A‖≤1/10^16 := by
  have h:=TaoFivePrimes.rh_high_height_finite_dirichlet50000 3289999808 ((m:ℝ)/512) ⟨by norm_num,by norm_num⟩ (by positivity)
  change ‖𝓕 W ((m:ℝ)/512)-_‖≤_ at h
  rw [Finset.sum_range] at h
  norm_num only [Complex.ofReal_ofNat] at h
  have he:(∑n:Fin 50000,Complex.exp (-(1/2+I*(3289999808:ℂ))*(Real.log ((n.val+1:ℝ)*Real.sqrt Real.pi):ℂ))*
   𝓕 (RHHighSamplingFunctions.gammaWindow 3289999808)
    ((m:ℝ)/512+Real.log ((n.val+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi)))=A := by
   apply Finset.sum_congr rfl
   intro n hn
   have hl:=log_identity (n.val+1) (by omega)
   push_cast at hl
   rw [hl]
   rfl
  rw [he] at h
  simpa only [show (10:ℝ)^16=10000000000000000 by norm_num] using h
 have ht:‖A-D‖≤50000/10^20 := by
  dsimp only [A,D]
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
   _ ≤ ∑n:Fin 50000,(1/10^20:ℝ) := by
    exact Finset.sum_le_sum (fun n hn=>taylor_term m (n.val+1) ⟨by omega,by omega⟩)
   _ =_ :=by simp [div_eq_mul_inv]
 have hg:‖D-group G‖≤1/10^12 := by
  exact TaoFivePrimes.rh_batch01_height_dirichlet_grouped_analytic (F m) G hF heF
 have he:‖𝓕 W ((m:ℝ)/512)-group G‖≤1/10^16+50000/10^20+1/10^12 := by
  have h1:=norm_sub_le_norm_sub_add_norm_sub (𝓕 W ((m:ℝ)/512)) A (group G)
  have h2:=norm_sub_le_norm_sub_add_norm_sub A D (group G)
  linarith only[h1,h2,hf,ht,hg]
 rw [←mul_sub,norm_mul]
 norm_num only[norm_div,norm_one,norm_ofNat]
 exact (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤1/512)).trans (by norm_num)
end RHBatch01FullCoefficient
end
end RHBatch01FullCoefficientProof
open scoped FourierTransform
theorem solution (m : Nat) (hm:m≤1024) (G : Nat→Nat→ℂ)
 (hF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖RHBatch01FullCoefficient.F m b k‖≤65537)
 (heF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖RHBatch01FullCoefficient.F m b k-G b k‖≤1/10^15) :
 ‖(1/512:ℂ)*𝓕 RHBatch01FullCoefficient.W ((m:ℝ)/512)-(1/512:ℂ)*RHBatch01FullCoefficient.group G‖≤3/10^15 := by
 exact RHBatch01FullCoefficientProof.RHBatch01FullCoefficient.analytic_reduction m hm G hF heF
#print axioms solution
