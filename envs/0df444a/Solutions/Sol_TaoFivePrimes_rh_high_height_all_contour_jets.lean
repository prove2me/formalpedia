-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_all_contour_jets
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:30:23.433894+00:00
-- url     : https://prove2.me/submissions/50cbc28b-e01d-4829-b038-b42668ee5014

import Definitions.Def_TaoFivePrimes_RHHighContourGeometry
import Definitions.Def_TaoFivePrimes_RHHighContourGridV2
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k01
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k02
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k03
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k04
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k05
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k06
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k07
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_semantic
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k01
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k02
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k03
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k04
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k05
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k06
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k07
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k01
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k02
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k03
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k04
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k05
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k06
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k07
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k01
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k02
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k03
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k04
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k05
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k06
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k07
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_spectrum_bounds
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_kernel_interface
import Theorems.Thm_TaoFivePrimes_rh_high_height_fourier_polynomial_bounds
import Theorems.Thm_TaoFivePrimes_rh_high_height_upper_right_endpoint
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_jet_left_enclosure
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_jet_right_enclosure
namespace RHHighAllContourJetsProof
namespace RHHighContourGeometry
export _root_.RHHighContourGeometry (cells hi line lo orientation point start step)
end RHHighContourGeometry
namespace RHHighContourGrid
export _root_.RHHighContourGrid (cells horizontal horizontalRows jet verticalRows)
end RHHighContourGrid
namespace RHHighContourGridV2
export _root_.RHHighContourGridV2 (cells jet vertical)
end RHHighContourGridV2
namespace RHHighContourOutput00
export _root_.RHHighContourOutput00 (row00 row01 row02 row03 rows)
end RHHighContourOutput00
namespace RHHighContourOutputUpperNeg64K01
export _root_.RHHighContourOutputUpperNeg64K01 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K01
namespace RHHighContourOutputUpperNeg64K02
export _root_.RHHighContourOutputUpperNeg64K02 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K02
namespace RHHighContourOutputUpperNeg64K03
export _root_.RHHighContourOutputUpperNeg64K03 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K03
namespace RHHighContourOutputUpperNeg64K04
export _root_.RHHighContourOutputUpperNeg64K04 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K04
namespace RHHighContourOutputUpperNeg64K05
export _root_.RHHighContourOutputUpperNeg64K05 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K05
namespace RHHighContourOutputUpperNeg64K06
export _root_.RHHighContourOutputUpperNeg64K06 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K06
namespace RHHighContourOutputUpperNeg64K07
export _root_.RHHighContourOutputUpperNeg64K07 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K07
namespace RHHighContourOutputUpperPos64K00
export _root_.RHHighContourOutputUpperPos64K00 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K00
namespace RHHighContourOutputUpperPos64K01
export _root_.RHHighContourOutputUpperPos64K01 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K01
namespace RHHighContourOutputUpperPos64K02
export _root_.RHHighContourOutputUpperPos64K02 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K02
namespace RHHighContourOutputUpperPos64K03
export _root_.RHHighContourOutputUpperPos64K03 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K03
namespace RHHighContourOutputUpperPos64K04
export _root_.RHHighContourOutputUpperPos64K04 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K04
namespace RHHighContourOutputUpperPos64K05
export _root_.RHHighContourOutputUpperPos64K05 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K05
namespace RHHighContourOutputUpperPos64K06
export _root_.RHHighContourOutputUpperPos64K06 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K06
namespace RHHighContourOutputUpperPos64K07
export _root_.RHHighContourOutputUpperPos64K07 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K07
namespace RHHighContourOutputUpperZeroK00
export _root_.RHHighContourOutputUpperZeroK00 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK00
namespace RHHighContourOutputUpperZeroK01
export _root_.RHHighContourOutputUpperZeroK01 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK01
namespace RHHighContourOutputUpperZeroK02
export _root_.RHHighContourOutputUpperZeroK02 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK02
namespace RHHighContourOutputUpperZeroK03
export _root_.RHHighContourOutputUpperZeroK03 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK03
namespace RHHighContourOutputUpperZeroK04
export _root_.RHHighContourOutputUpperZeroK04 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK04
namespace RHHighContourOutputUpperZeroK05
export _root_.RHHighContourOutputUpperZeroK05 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK05
namespace RHHighContourOutputUpperZeroK06
export _root_.RHHighContourOutputUpperZeroK06 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK06
namespace RHHighContourOutputUpperZeroK07
export _root_.RHHighContourOutputUpperZeroK07 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK07
namespace RHHighContourVector
export _root_.RHHighContourVector (coefficient decode raw value vector)
end RHHighContourVector
namespace RHHighFourierPolynomial
export _root_.RHHighFourierPolynomial (coefficient imagInteger phase polynomial realInteger word)
end RHHighFourierPolynomial
namespace RHHighPolynomialJet
export _root_.RHHighPolynomialJet (generator jet)
end RHHighPolynomialJet
namespace RHHighVerticalJetsLeft
export _root_.RHHighVerticalJetsLeft (row00 row01 row02 rows)
end RHHighVerticalJetsLeft
namespace RHHighVerticalJetsRight
export _root_.RHHighVerticalJetsRight (row00 row01 row02 rows)
end RHHighVerticalJetsRight
namespace RHHighZetaFourierData
export _root_.RHHighZetaFourierData (row00 row01 row02 rows)
end RHHighZetaFourierData
namespace TaoFivePrimes
export _root_.TaoFivePrimes (rh_high_height_contour_actual_input_upper_zero_k00 rh_high_height_contour_actual_input_upper_zero_k01 rh_high_height_contour_actual_input_upper_zero_k02 rh_high_height_contour_actual_input_upper_zero_k03 rh_high_height_contour_actual_input_upper_zero_k04 rh_high_height_contour_actual_input_upper_zero_k05 rh_high_height_contour_actual_input_upper_zero_k06 rh_high_height_contour_actual_input_upper_zero_k07 rh_high_height_contour_fft_semantic rh_high_height_contour_fft_upper_zero_k00 rh_high_height_contour_fft_upper_zero_k01 rh_high_height_contour_fft_upper_zero_k02 rh_high_height_contour_fft_upper_zero_k03 rh_high_height_contour_fft_upper_zero_k04 rh_high_height_contour_fft_upper_zero_k05 rh_high_height_contour_fft_upper_zero_k06 rh_high_height_contour_fft_upper_zero_k07 rh_high_height_contour_jet_upper_neg64_k00 rh_high_height_contour_jet_upper_neg64_k01 rh_high_height_contour_jet_upper_neg64_k02 rh_high_height_contour_jet_upper_neg64_k03 rh_high_height_contour_jet_upper_neg64_k04 rh_high_height_contour_jet_upper_neg64_k05 rh_high_height_contour_jet_upper_neg64_k06 rh_high_height_contour_jet_upper_neg64_k07 rh_high_height_contour_reference_upper_zero_k00 rh_high_height_contour_reference_upper_zero_k01 rh_high_height_contour_reference_upper_zero_k02 rh_high_height_contour_reference_upper_zero_k03 rh_high_height_contour_reference_upper_zero_k04 rh_high_height_contour_reference_upper_zero_k05 rh_high_height_contour_reference_upper_zero_k06 rh_high_height_contour_reference_upper_zero_k07 rh_high_height_contour_spectrum_bounds rh_high_height_fft_kernel_interface rh_high_height_fourier_polynomial_bounds rh_high_height_upper_right_endpoint rh_high_height_vertical_jet_left_enclosure rh_high_height_vertical_jet_right_enclosure)
end TaoFivePrimes
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
open scoped ComplexConjugate
namespace RHHighFourierPolynomial
noncomputable def integerMass (m : Nat) : Nat := (realInteger m).natAbs+(imagInteger m).natAbs
noncomputable def mass : Nat := integerMass 0+2*∑ m∈Finset.range 1024,integerMass (m+1)
noncomputable def mass8 : Nat := 2*∑ m∈Finset.range 1024,integerMass (m+1)*(m+1)^8
lemma coefficient_norm (m : Nat) : ‖coefficient m‖≤(integerMass m:ℝ)/(2:ℝ)^80 := by
  unfold coefficient integerMass
  rw [norm_div,norm_pow,norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h:=norm_add_le (realInteger m:ℂ) ((imagInteger m:ℂ)*I)
  simp only [norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one,Int.cast_natCast] at h
  simpa only [Nat.cast_add,Nat.cast_natAbs,Int.cast_abs] using h
lemma coefficient_mass : ‖coefficient 0‖+2*∑m∈Finset.range 1024,‖coefficient (m+1)‖≤3/5 :=
 TaoFivePrimes.rh_high_height_fourier_polynomial_bounds.1
lemma coefficient_mass8 : 2*∑m∈Finset.range 1024,‖coefficient (m+1)‖*((m+1:ℝ)/1024)^8≤1/100 :=
 TaoFivePrimes.rh_high_height_fourier_polynomial_bounds.2.1
lemma constant_real : imagInteger 0=0 := TaoFivePrimes.rh_high_height_fourier_polynomial_bounds.2.2
lemma phase_norm (m : Nat) (z : ℂ) : ‖phase m z‖=Real.exp (-(2*Real.pi*(m:ℝ)/512)*z.im) := by
  unfold phase
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]
lemma phase_bound (m : Nat) (hm:m≤1024) (z : ℂ) : ‖phase m z‖≤Real.exp (4*Real.pi*|z.im|) := by
  rw [phase_norm]
  apply Real.exp_le_exp.mpr
  have hm':(m:ℝ)≤1024 := by exact_mod_cast hm
  have hcoef:0≤2*Real.pi*(m:ℝ)/512 ∧ 2*Real.pi*(m:ℝ)/512≤4*Real.pi := by
    constructor
    · positivity
    · nlinarith [Real.pi_pos]
  have hz1:-z.im≤|z.im| := neg_le_abs _
  nlinarith [mul_nonneg (sub_nonneg.mpr hcoef.2) (abs_nonneg z.im),
    mul_nonneg hcoef.1 (sub_nonneg.mpr hz1)]
lemma polynomial_entire : Differentiable ℂ polynomial := by
  unfold polynomial phase
  fun_prop
lemma polynomial_norm (z : ℂ) : ‖polynomial z‖≤Real.exp (4*Real.pi*|z.im|) := by
  let E:=Real.exp (4*Real.pi*|z.im|)
  have hE:1≤E := Real.one_le_exp_iff.mpr (by positivity)
  have hc0:‖coefficient 0‖≤‖coefficient 0‖*E := le_mul_of_one_le_right (norm_nonneg _) hE
  have hs:‖∑ m∈Finset.range 1024,(coefficient (m+1)*phase (m+1) z+
      conj (coefficient (m+1))*phase (m+1) (-z))‖≤
      (2*∑ m∈Finset.range 1024,‖coefficient (m+1)‖)*E := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m hm
    have hb: m+1≤1024 := by have h:=Finset.mem_range.mp hm;omega
    have hp:=phase_bound (m+1) hb z
    have hn:=phase_bound (m+1) hb (-z)
    simp only [neg_im,abs_neg] at hn
    have h1:=mul_le_mul_of_nonneg_left hp (norm_nonneg (coefficient (m+1)))
    have h2:=mul_le_mul_of_nonneg_left hn (norm_nonneg (coefficient (m+1)))
    have h:=norm_add_le (coefficient (m+1)*phase (m+1) z) (conj (coefficient (m+1))*phase (m+1) (-z))
    simp only [norm_mul,Complex.norm_conj] at h
    nlinarith
  unfold polynomial
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖coefficient 0‖*E+(2*∑ m∈Finset.range 1024,‖coefficient (m+1)‖)*E := add_le_add hc0 hs
    _ = (‖coefficient 0‖+2*∑ m∈Finset.range 1024,‖coefficient (m+1)‖)*E := by ring
    _ ≤ (3/5:ℝ)*E := mul_le_mul_of_nonneg_right coefficient_mass (by positivity)
    _ ≤ E := mul_le_of_le_one_left (by positivity) (by norm_num)
end RHHighFourierPolynomial

end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex CauSeq Finset
namespace RHHighTaylor
lemma exp_factorial_remainder (z : ℂ) (n : Nat) :
    ‖Complex.exp z-∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤
      (‖z‖^n/(n.factorial:ℝ))*Real.exp ‖z‖ := by
  rw [←CauSeq.lim_const (abv:=norm) (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)),
    Complex.exp,sub_eq_add_neg,←CauSeq.lim_neg]
  rw [CauSeq.lim_add (Complex.exp' z) (-CauSeq.const norm (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ))),
    ←Complex.lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n,fun j hj => ?_⟩)
  simp_rw [←sub_eq_add_neg]
  change ‖(∑ k ∈ Finset.range j, z^k/(k.factorial:ℂ))-
    ∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤_
  let m := j-n
  have he : j=n+m := (Nat.add_sub_of_le hj).symm
  rw [he,Finset.sum_range_add_sub_sum_range]
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖z^(n+k)/((n+k).factorial:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, (‖z‖^n/(n.factorial:ℝ))*(‖z‖^k/(k.factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_div,Complex.norm_pow,norm_natCast,pow_add,norm_mul]
      rw [div_mul_div_comm]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n k)
    _ = (‖z‖^n/(n.factorial:ℝ))*(∑ k ∈ Finset.range m, ‖z‖^k/(k.factorial:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg z) m) (by positivity)
end RHHighTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
open scoped ComplexConjugate
namespace RHHighFourierPolynomial
noncomputable def generator (m : Nat) : ℂ := ((2*Real.pi*(m:ℝ)/512:ℝ):ℂ)*I
noncomputable def expPolynomial8 (u : ℂ) : ℂ := ∑ k∈Finset.range 8,u^k/(k.factorial:ℂ)
noncomputable def taylor8 (z w : ℂ) : ℂ := coefficient 0+
  ∑ m∈Finset.range 1024,(coefficient (m+1)*phase (m+1) z*expPolynomial8 (generator (m+1)*w)+
    conj (coefficient (m+1))*phase (m+1) (-z)*expPolynomial8 (-generator (m+1)*w))
lemma phase_add_complex (m : Nat) (z w : ℂ) : phase m (z+w)=phase m z*Complex.exp (generator m*w) := by
  unfold phase generator
  rw [mul_add,Complex.exp_add]
lemma exp_small (u : ℂ) (hu:‖u‖≤2/5) : Real.exp ‖u‖≤2 := by
  have hsq:(Real.exp (1/2:ℝ))^2=Real.exp 1 := by rw [←Real.exp_nat_mul];norm_num
  have he:Real.exp (1/2:ℝ)≤2 := by nlinarith [Real.exp_one_lt_three,Real.exp_pos (1/2:ℝ)]
  exact (Real.exp_le_exp.mpr (by linarith)).trans he
lemma generator_bound (m : Nat) (w : ℂ) (hw:‖w‖≤1/32) :
    ‖generator m*w‖≤(2/5)*((m:ℝ)/1024) := by
  unfold generator
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
    abs_of_nonneg (by positivity : (0:ℝ)≤2*Real.pi*(m:ℝ)/512)]
  have h:=mul_le_mul_of_nonneg_left hw (by positivity : (0:ℝ)≤2*Real.pi*(m:ℝ)/512)
  have hp:Real.pi≤16/5:=by linarith [Real.pi_lt_d2]
  have hm:(0:ℝ)≤ m :=Nat.cast_nonneg m
  nlinarith
lemma phase_boundary_bound (m : Nat) (hm:m≤1024) (z : ℂ) (hz:|z.im|≤1/2) :
    ‖phase m z‖≤(11/4:ℝ)^7 := by
  apply (phase_bound m hm z).trans
  calc
    _ ≤ Real.exp 7 := Real.exp_le_exp.mpr (by
      have hp:Real.pi≤7/2:=by linarith [Real.pi_lt_d2]
      nlinarith [Real.pi_pos,abs_nonneg z.im])
    _ = (Real.exp 1)^7 := by simpa using (Real.exp_nat_mul (1:ℝ) (7:Nat)).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
lemma exponential_remainder (m : Nat) (hm:m≤1024) (w : ℂ) (hw:‖w‖≤1/32) :
    ‖Complex.exp (generator m*w)-expPolynomial8 (generator m*w)‖≤
      ((2/5:ℝ)^8*((m:ℝ)/1024)^8/(8:Nat).factorial)*2 := by
  have h:=RHHighTaylor.exp_factorial_remainder (generator m*w) 8
  have hb:=generator_bound m w hw
  have hm':(m:ℝ)/1024≤1 := (div_le_one (by norm_num)).mpr (by exact_mod_cast hm)
  have he:=exp_small (generator m*w) (by nlinarith)
  apply h.trans
  apply mul_le_mul _ he (Real.exp_pos _).le (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [←mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hb _
lemma polynomial_taylor_remainder (z w : ℂ) (hz:|z.im|≤1/2) (hw:‖w‖≤1/32) :
    ‖polynomial (z+w)-taylor8 z w‖≤1/10^6 := by
  let C:ℝ:=(11/4:ℝ)^7*(2/5:ℝ)^8*2/(8:Nat).factorial
  have hC:0≤C:=by dsimp [C];positivity
  have he:polynomial (z+w)-taylor8 z w=
      ∑ m∈Finset.range 1024,(
        coefficient (m+1)*phase (m+1) z*(Complex.exp (generator (m+1)*w)-expPolynomial8 (generator (m+1)*w))+
        conj (coefficient (m+1))*phase (m+1) (-z)*(Complex.exp (-generator (m+1)*w)-expPolynomial8 (-generator (m+1)*w))) := by
    unfold polynomial taylor8
    rw [add_sub_add_left_eq_sub,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [phase_add_complex,show -(z+w)=(-z)+(-w) by ring,phase_add_complex]
    rw [show generator (m+1)*(-w)= -generator (m+1)*w by ring]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  have hs:(∑ m∈Finset.range 1024,‖coefficient (m+1)*phase (m+1) z*(Complex.exp (generator (m+1)*w)-expPolynomial8 (generator (m+1)*w))+
        conj (coefficient (m+1))*phase (m+1) (-z)*(Complex.exp (-generator (m+1)*w)-expPolynomial8 (-generator (m+1)*w))‖)≤
      (2*∑ m∈Finset.range 1024,‖coefficient (m+1)‖*((m+1:ℝ)/1024)^8)*C := by
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m hm
    have hm0:m+1≤1024:=by have h:=Finset.mem_range.mp hm;omega
    have hp:=phase_boundary_bound (m+1) hm0 z hz
    have hn:=phase_boundary_bound (m+1) hm0 (-z) (by simpa using hz)
    have hr:=exponential_remainder (m+1) hm0 w hw
    have hnr:=exponential_remainder (m+1) hm0 (-w) (by simpa using hw)
    rw [show generator (m+1)*(-w)= -generator (m+1)*w by ring] at hnr
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_conj]
    have h1:=mul_le_mul (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hr (norm_nonneg _) (by positivity : (0:ℝ)≤‖coefficient (m+1)‖*(11/4:ℝ)^7)
    have h2:=mul_le_mul (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) hnr (norm_nonneg _) (by positivity : (0:ℝ)≤‖coefficient (m+1)‖*(11/4:ℝ)^7)
    exact (add_le_add h1 h2).trans_eq (by dsimp [C];push_cast;ring)
  exact hs.trans ((mul_le_mul_of_nonneg_right coefficient_mass8 hC).trans (by norm_num [C]))
end RHHighFourierPolynomial
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
open scoped ComplexConjugate
namespace RHHighFourierPolynomial
noncomputable def jet (z h : ℂ) (k : Nat) : ℂ := (if k=0 then coefficient 0 else 0)+
  ∑ m∈Finset.range 1024,(coefficient (m+1)*phase (m+1) z*(generator (m+1)*h)^k/(k.factorial:ℂ)+
    conj (coefficient (m+1))*phase (m+1) (-z)*(-generator (m+1)*h)^k/(k.factorial:ℂ))
lemma jet_zero (z h : ℂ) : jet z h 0=polynomial z := by simp [jet,polynomial]
lemma taylor_jet (z h s : ℂ) : taylor8 z (s*h)=∑ k∈Finset.range 8,jet z h k*s^k := by
  symm
  unfold jet
  simp only [add_mul,Finset.sum_mul]
  rw [Finset.sum_add_distrib]
  have hconst:(∑ k∈Finset.range 8,(if k=0 then coefficient 0 else 0)*s^k)=coefficient 0 := by simp
  rw [hconst,Finset.sum_comm]
  unfold taylor8
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  unfold expPolynomial8
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_pow]
  ring
lemma jet_sum_error (a b : Nat→ℂ) (s ε : ℝ) (hs:|s|≤1) (hε:0≤ε)
    (he:∀ k:Nat,k<8 → ‖a k-b k‖≤ε) :
    ‖(∑ k∈Finset.range 8,a k*(s:ℂ)^k)-(∑ k∈Finset.range 8,b k*(s:ℂ)^k)‖≤8*ε := by
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k∈Finset.range 8,ε := by
      apply Finset.sum_le_sum
      intro k hk
      rw [←sub_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul (he k (Finset.mem_range.mp hk))
        (pow_le_one₀ (abs_nonneg _) hs) (by positivity) hε).trans_eq (by ring)
    _ = _ := by simp
lemma polynomial_sum_radius (a : Nat→ℂ) (s : ℝ) (hs:|s|≤1) :
    ‖(∑ k∈Finset.range 8,a k*(s:ℂ)^k)-a 0‖≤∑ k∈Finset.range 7,‖a (k+1)‖ := by
  rw [show (8:Nat)=7+1 by rfl,Finset.sum_range_succ']
  simp only [pow_zero,mul_one,add_sub_cancel_right]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hs)
lemma boundary_disc (z h : ℂ) (a : Nat→ℂ) (ε s : ℝ)
    (hz:|z.im|≤1/2) (hh:‖h‖≤1/32) (hs:0≤ s ∧ s≤1) (hε:0≤ε)
    (ha:∀ k:Nat,k<8 → ‖jet z h k-a k‖≤ε) :
    ‖polynomial (z+(s:ℂ)*h)-a 0‖≤(∑ k∈Finset.range 7,‖a (k+1)‖)+8*ε+1/10^6 := by
  have hs':|s|≤1:=by rw [abs_of_nonneg hs.1];exact hs.2
  have hnorm:‖(s:ℂ)*h‖≤1/32 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul hs' hh (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have ht:=polynomial_taylor_remainder z ((s:ℂ)*h) hz hnorm
  rw [taylor_jet] at ht
  have he:=jet_sum_error (jet z h) a s ε hs' hε ha
  have hr:=polynomial_sum_radius a s hs'
  have h1:=norm_sub_le_norm_sub_add_norm_sub (polynomial (z+(s:ℂ)*h))
    (∑ k∈Finset.range 8,jet z h k*(s:ℂ)^k) (a 0)
  have h2:=norm_sub_le_norm_sub_add_norm_sub (∑ k∈Finset.range 8,jet z h k*(s:ℂ)^k)
    (∑ k∈Finset.range 8,a k*(s:ℂ)^k) (a 0)
  linarith
end RHHighFourierPolynomial
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
open scoped ComplexConjugate
namespace RHHighPolynomialSymmetry
open RHHighFourierPolynomial
lemma constant_conj : conj (coefficient 0)=coefficient 0 := by
 simp only[coefficient,constant_real,Int.cast_zero,zero_mul,add_zero,map_div₀,map_intCast,map_pow,Complex.conj_ofNat]
lemma phase_conj (m : Nat) (z : ℂ) : conj (phase m z)=phase m (-conj z) := by
 unfold phase
 rw[←Complex.exp_conj]
 congr 1
 simp only[map_mul,Complex.conj_ofReal,Complex.conj_I]
 ring
lemma generator_conj (m : Nat) : conj (generator m)= -generator m := by
 unfold generator
 simp only[map_mul,Complex.conj_ofReal,Complex.conj_I]
 ring
lemma jet_conj (z h : ℂ) (k : Nat) : RHHighPolynomialJet.jet (conj z) (conj h) k=conj (RHHighPolynomialJet.jet z h k) := by
 change jet (conj z) (conj h) k=conj (jet z h k)
 unfold jet
 simp only[apply_ite,map_zero,map_add,map_sum,map_mul,map_div₀,map_pow,map_natCast,
  phase_conj,generator_conj,map_neg,neg_neg,starRingEnd_self_apply,constant_conj]
 congr 1
 apply Finset.sum_congr rfl
 intro m hm
 ring
lemma value_conj (p : Int×Int) : RHHighContourVector.value (p.1,-p.2)=conj (RHHighContourVector.value p) := by
 unfold RHHighContourVector.value
 simp only[Prod.fst,Prod.snd,Int.cast_neg,map_div₀,map_add,map_mul,map_intCast,map_pow,Complex.conj_ofNat,Complex.conj_I]
 ring
lemma error_conj (z h : ℂ) (k : Nat) (p : Int×Int) :
 ‖RHHighPolynomialJet.jet (conj z) (conj h) k-RHHighContourVector.value (p.1,-p.2)‖=
 ‖RHHighPolynomialJet.jet z h k-RHHighContourVector.value p‖ := by
 rw[jet_conj,value_conj,←map_sub,Complex.norm_conj]
end RHHighPolynomialSymmetry
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma right_half_slit (z : ℂ) (hz : 0 < z.re) : z∈Complex.slitPlane := by
  exact Or.inl hz
lemma segment_log_derivative (f : ℂ→ℂ) (c z v : ℂ) (hc : c≠0) (t : ℝ)
    (hf : DifferentiableAt ℂ f (z+(t:ℂ)*v))
    (hz : 0 < (f (z+(t:ℂ)*v)/c).re) :
    HasDerivAt (fun u : ℝ => Complex.log (f (z+(u:ℂ)*v)/c))
      (logDeriv f (z+(t:ℂ)*v)*v) t := by
  have ha : HasDerivAt (fun u : ℝ => z+(u:ℂ)*v) v t := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using ((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const v).const_add z
  have hb := (hf.hasDerivAt.comp t ha).div_const c
  have hl := (Complex.hasDerivAt_log (right_half_slit _ hz)).comp t hb
  have hnon : f (z+(t:ℂ)*v)≠0 := by
    intro h
    rw [h,zero_div] at hz
    norm_num at hz
  have he : (f (z+(t:ℂ)*v)/c)⁻¹*(deriv f (z+(t:ℂ)*v)*v/c)=
      logDeriv f (z+(t:ℂ)*v)*v := by
    simp only [logDeriv,Pi.div_apply]
    field_simp [hc,hnon]
  rw [he] at hl
  exact hl
lemma segment_integral (f : ℂ→ℂ) (c z v : ℂ) (hc : c≠0) (a b : ℝ)
    (hf : ∀ t∈Set.uIcc a b, DifferentiableAt ℂ f (z+(t:ℂ)*v))
    (hz : ∀ t∈Set.uIcc a b, 0 < (f (z+(t:ℂ)*v)/c).re)
    (hi : IntervalIntegrable (fun t : ℝ => logDeriv f (z+(t:ℂ)*v)*v) volume a b) :
    (∫ t : ℝ in a..b, logDeriv f (z+(t:ℂ)*v)*v)=
      Complex.log (f (z+(b:ℂ)*v)/c)-Complex.log (f (z+(a:ℂ)*v)/c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact segment_log_derivative f c z v hc t (hf t ht) (hz t ht)
  · exact hi
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighContourLog
lemma disk_half_plane (f c : ℂ) (hc : c≠0) (he : ‖f-c‖<‖c‖) : 0 < (f/c).re := by
  have hn : ‖f/c-1‖<1 := by
    have hq : f/c-1=(f-c)/c := by field_simp
    rw [hq,norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hc)).mpr he
  have hr := (Complex.abs_re_le_norm (f/c-1)).trans_lt hn
  have hh := (abs_lt.mp hr).1
  simp only [sub_re,one_re] at hh
  linarith
lemma enclosure_half_plane (f p c : ℂ) (ε r : ℝ) (hc : c≠0)
    (he : ‖f-p‖≤ε) (hp : ‖p-c‖≤r) (hmargin : ε+r<‖c‖) : 0 < (f/c).re := by
  apply disk_half_plane f c hc
  exact ((norm_sub_le_norm_sub_add_norm_sub f p c).trans (add_le_add he hp)).trans_lt hmargin
lemma log_error_near_one (z : ℂ) (hz : ‖z-1‖≤1/2) :
    ‖Complex.log z‖≤(3/2:ℝ)*‖z-1‖ := by
  have h := Complex.norm_log_one_add_half_le_self hz
  simpa only [add_sub_cancel] using h
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma ratio_segment_integral (F G : ℂ→ℂ) (z v : ℂ) (a b : ℝ)
    (hF : ∀ t∈Set.uIcc a b, DifferentiableAt ℂ F (z+(t:ℂ)*v))
    (hG : ∀ t∈Set.uIcc a b, DifferentiableAt ℂ G (z+(t:ℂ)*v))
    (hGn : ∀ t∈Set.uIcc a b, G (z+(t:ℂ)*v)≠0)
    (he : ∀ t∈Set.uIcc a b, ‖F (z+(t:ℂ)*v)-G (z+(t:ℂ)*v)‖<‖G (z+(t:ℂ)*v)‖)
    (hi : IntervalIntegrable (fun t : ℝ => logDeriv (fun s => F s/G s) (z+(t:ℂ)*v)*v) volume a b) :
    (∫ t : ℝ in a..b, logDeriv (fun s => F s/G s) (z+(t:ℂ)*v)*v)=
      Complex.log (F (z+(b:ℂ)*v)/G (z+(b:ℂ)*v))-
      Complex.log (F (z+(a:ℂ)*v)/G (z+(a:ℂ)*v)) := by
  have h := segment_integral (fun s => F s/G s) 1 z v one_ne_zero a b
    (fun t ht => (hF t ht).div (hG t ht) (hGn t ht))
    (fun t ht => by simpa only [div_one] using disk_half_plane _ _ (hGn t ht) (he t ht)) hi
  simpa only [div_one] using h
lemma logDeriv_ratio (F G : ℂ→ℂ) (s : ℂ)
    (hF : DifferentiableAt ℂ F s) (hG : DifferentiableAt ℂ G s)
    (hn : G s≠0) (he : ‖F s-G s‖<‖G s‖) :
    logDeriv (fun z => F z/G z) s=logDeriv F s-logDeriv G s := by
  have hFn : F s≠0 := by
    intro h
    simpa only [h,zero_sub,norm_neg,lt_self_iff_false] using he
  exact logDeriv_div s hFn hn hF hG
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma halfplane_rectangle (F : ℂ→ℂ) (z w : ℂ)
    (hF : ∀ s∈RectangleBorder z w, DifferentiableAt ℂ F s)
    (hRe : ∀ s∈RectangleBorder z w, 0 < (F s).re)
    (hi : RectangleBorderIntegrable (logDeriv F) z w) :
    RectangleIntegral (logDeriv F) z w=0 := by
  have hb (x : ℝ) (hx : x∈Set.uIcc z.re w.re) : (x:ℂ)+(z.im:ℂ)*I∈RectangleBorder z w := by
    simp only [RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
    exact Or.inl (Or.inl (Or.inl ⟨by simpa using hx,by simp⟩))
  have ht (x : ℝ) (hx : x∈Set.uIcc z.re w.re) : (x:ℂ)+(w.im:ℂ)*I∈RectangleBorder z w := by
    simp only [RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
    exact Or.inl (Or.inr ⟨by simpa using hx,by simp⟩)
  have hr (y : ℝ) (hy : y∈Set.uIcc z.im w.im) : (w.re:ℂ)+(y:ℂ)*I∈RectangleBorder z w := by
    simp only [RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
    exact Or.inr ⟨by simp,by simpa using hy⟩
  have hl (y : ℝ) (hy : y∈Set.uIcc z.im w.im) : (z.re:ℂ)+(y:ℂ)*I∈RectangleBorder z w := by
    simp only [RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
    exact Or.inl (Or.inl (Or.inr ⟨by simp,by simpa using hy⟩))
  have hbottom := segment_integral F 1 ((z.im:ℂ)*I) 1 one_ne_zero z.re w.re
    (fun x hx => by simpa only [mul_one,add_comm] using hF _ (hb x hx))
    (fun x hx => by simpa only [div_one,mul_one,add_comm] using hRe _ (hb x hx))
    (by simpa only [mul_one,add_comm] using hi.1)
  have htop := segment_integral F 1 ((w.im:ℂ)*I) 1 one_ne_zero z.re w.re
    (fun x hx => by simpa only [mul_one,add_comm] using hF _ (ht x hx))
    (fun x hx => by simpa only [div_one,mul_one,add_comm] using hRe _ (ht x hx))
    (by simpa only [mul_one,add_comm] using hi.2.1)
  have hright := segment_integral F 1 (w.re:ℂ) I one_ne_zero z.im w.im
    (fun y hy => hF _ (hr y hy))
    (fun y hy => by simpa only [div_one] using hRe _ (hr y hy))
    (hi.2.2.1.mul_const I)
  have hleft := segment_integral F 1 (z.re:ℂ) I one_ne_zero z.im w.im
    (fun y hy => hF _ (hl y hy))
    (fun y hy => by simpa only [div_one] using hRe _ (hl y hy))
    (hi.2.2.2.mul_const I)
  simp only [mul_one,div_one] at hbottom htop hright hleft
  unfold RectangleIntegral HIntegral VIntegral
  simp only [smul_eq_mul]
  rw [show I*(∫ y:ℝ in z.im..w.im,logDeriv F ((w.re:ℂ)+(y:ℂ)*I))=
    ∫ y:ℝ in z.im..w.im,logDeriv F ((w.re:ℂ)+(y:ℂ)*I)*I by
      rw [intervalIntegral.integral_mul_const];ring,
    show I*(∫ y:ℝ in z.im..w.im,logDeriv F ((z.re:ℂ)+(y:ℂ)*I))=
    ∫ y:ℝ in z.im..w.im,logDeriv F ((z.re:ℂ)+(y:ℂ)*I)*I by
      rw [intervalIntegral.integral_mul_const];ring]
  rw [show (fun x:ℝ => logDeriv F ((x:ℂ)+(z.im:ℂ)*I))=
      (fun x:ℝ => logDeriv F ((z.im:ℂ)*I+(x:ℂ))) by funext x;rw [add_comm],hbottom,
    show (fun x:ℝ => logDeriv F ((x:ℂ)+(w.im:ℂ)*I))=
      (fun x:ℝ => logDeriv F ((w.im:ℂ)*I+(x:ℂ))) by funext x;rw [add_comm],htop,hright,hleft]
  rw [add_comm ((z.im:ℂ)*I) (w.re:ℂ),add_comm ((z.im:ℂ)*I) (z.re:ℂ),
    add_comm ((w.im:ℂ)*I) (w.re:ℂ),add_comm ((w.im:ℂ)*I) (z.re:ℂ)]
  ring
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma border_continuous_integrable (f : ℂ→ℂ) (z w : ℂ)
 (hf:∀s∈RectangleBorder z w,ContinuousAt f s) : RectangleBorderIntegrable f z w := by
 have hb (x : ℝ) (hx:x∈Set.uIcc z.re w.re) : (x:ℂ)+(z.im:ℂ)*I∈RectangleBorder z w := by
  simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
  exact Or.inl (Or.inl (Or.inl ⟨by simpa using hx,by simp⟩))
 have ht (x : ℝ) (hx:x∈Set.uIcc z.re w.re) : (x:ℂ)+(w.im:ℂ)*I∈RectangleBorder z w := by
  simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
  exact Or.inl (Or.inr ⟨by simpa using hx,by simp⟩)
 have hr (y : ℝ) (hy:y∈Set.uIcc z.im w.im) : (w.re:ℂ)+(y:ℂ)*I∈RectangleBorder z w := by
  simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
  exact Or.inr ⟨by simp,by simpa using hy⟩
 have hl (y : ℝ) (hy:y∈Set.uIcc z.im w.im) : (z.re:ℂ)+(y:ℂ)*I∈RectangleBorder z w := by
  simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
  exact Or.inl (Or.inl (Or.inr ⟨by simp,by simpa using hy⟩))
 constructor
 · apply ContinuousOn.intervalIntegrable
   intro x hx
   exact ((hf _ (hb x hx)).comp (f:=fun u:ℝ=>(u:ℂ)+(z.im:ℂ)*I) (by fun_prop)).continuousWithinAt
 constructor
 · apply ContinuousOn.intervalIntegrable
   intro x hx
   exact ((hf _ (ht x hx)).comp (f:=fun u:ℝ=>(u:ℂ)+(w.im:ℂ)*I) (by fun_prop)).continuousWithinAt
 constructor
 · apply ContinuousOn.intervalIntegrable
   intro y hy
   exact ((hf _ (hr y hy)).comp (f:=fun u:ℝ=>(w.re:ℂ)+(u:ℂ)*I) (by fun_prop)).continuousWithinAt
 · apply ContinuousOn.intervalIntegrable
   intro y hy
   exact ((hf _ (hl y hy)).comp (f:=fun u:ℝ=>(z.re:ℂ)+(u:ℂ)*I) (by fun_prop)).continuousWithinAt
lemma logDeriv_border_integrable (f : ℂ→ℂ) (z w : ℂ)
 (hf:∀s∈RectangleBorder z w,AnalyticAt ℂ f s)
 (hn:∀s∈RectangleBorder z w,f s≠0) : RectangleBorderIntegrable (logDeriv f) z w := by
 apply border_continuous_integrable
 intro s hs
 have h:AnalyticAt ℂ (fun x=>deriv f x/f x) s := (hf s hs).deriv.div (hf s hs) (hn s hs)
 exact h.continuousAt
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set
namespace RHHighContourGeometry
lemma cells_pos (e : Nat) : 0< cells e := by
 unfold cells RHHighContourGridV2.cells RHHighContourGrid.cells
 split_ifs <;> norm_num
lemma step_bound (e : Nat) : ‖step e‖≤1/32 := by
 unfold step
 split_ifs <;> norm_num [norm_div]
lemma line_add (e j : Nat) (s : ℝ) :
 line e ((j:ℝ)+s)=point e j+(s:ℂ)*step e := by
 simp only[line,point,Complex.ofReal_add]
 ring
lemma line_components (e : Nat) (he:e<4) (t : ℝ) :
 (line e t).re=(if e=0 ∨ e=2 then -64+t/32 else if e=1 then 64 else -64) ∧
 (line e t).im=(if e=0 then -1/2 else if e=2 then 1/2 else -1/2+t/128) := by
 interval_cases e <;> norm_num [line,start,step,mul_re,mul_im] <;> ring
lemma line_box (e : Nat) (he:e<4) (t : ℝ) (ht:t∈Icc 0 (cells e:ℝ)) :
 -64≤(line e t).re ∧ (line e t).re≤64 ∧ -1/2≤(line e t).im ∧ (line e t).im≤1/2 := by
 rcases line_components e he t with ⟨hr,hi⟩
 interval_cases e <;> norm_num [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells] at ht hr hi <;>
  rw[hr,hi] <;> constructor <;> (try constructor) <;> (try constructor) <;> linarith [ht.1,ht.2]
lemma line_border (e : Nat) (he:e<4) (t : ℝ) (ht:t∈Icc 0 (cells e:ℝ)) :
 line e t∈RectangleBorder lo hi := by
 have hb:=line_box e he t ht
 rcases line_components e he t with ⟨hr,him⟩
 simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
 have hx:(line e t).re∈uIcc lo.re hi.re := by
  norm_num [lo,hi,uIcc_of_le] at *
  exact ⟨hb.1,hb.2.1⟩
 have hy:(line e t).im∈uIcc lo.im hi.im := by
  norm_num [lo,hi,uIcc_of_le] at *
  exact ⟨hb.2.2.1,hb.2.2.2⟩
 interval_cases e
 · exact Or.inl (Or.inl (Or.inl ⟨hx,by norm_num [lo] at *;linarith [him]⟩))
 · exact Or.inr ⟨by norm_num [hi] at *;linarith [hr],hy⟩
 · exact Or.inl (Or.inr ⟨hx,by norm_num [hi] at *;linarith [him]⟩)
 · exact Or.inl (Or.inl (Or.inr ⟨by norm_num [lo] at *;linarith [hr],hy⟩))
lemma border_cover (z : ℂ) (hz:z∈RectangleBorder lo hi) :
 ∃e:Nat,e<4 ∧ ∃t:ℝ,t∈Icc 0 (cells e:ℝ) ∧ z=line e t := by
 simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff] at hz
 have hreal : lo.re=-64 ∧ hi.re=64 ∧ lo.im=-1/2 ∧ hi.im=1/2 := by norm_num [lo,hi]
 simp only[hreal.1,hreal.2.1,hreal.2.2.1,hreal.2.2.2,uIcc_of_le (by norm_num : (-64:ℝ)≤64),
  uIcc_of_le (by norm_num : (-1/2:ℝ)≤1/2),mem_Icc] at hz
 rcases hz with ((⟨hx,hy⟩|⟨hx,hy⟩)|⟨hx,hy⟩)|⟨hx,hy⟩
 · refine ⟨0,by omega,32*(z.re+64),?_,?_⟩
   · norm_num [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells];constructor <;> linarith [hx.1,hx.2]
   · apply Complex.ext <;> norm_num [line,start,step,mul_re,mul_im] <;> linarith
 · refine ⟨3,by omega,128*(z.im+1/2),?_,?_⟩
   · norm_num [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells];constructor <;> linarith [hy.1,hy.2]
   · apply Complex.ext <;> norm_num [line,start,step,mul_re,mul_im] <;> linarith
 · refine ⟨2,by omega,32*(z.re+64),?_,?_⟩
   · norm_num [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells];constructor <;> linarith [hx.1,hx.2]
   · apply Complex.ext <;> norm_num [line,start,step,mul_re,mul_im] <;> linarith
 · refine ⟨1,by omega,128*(z.im+1/2),?_,?_⟩
   · norm_num [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells];constructor <;> linarith [hy.1,hy.2]
   · apply Complex.ext <;> norm_num [line,start,step,mul_re,mul_im] <;> linarith
lemma mesh_cover (N : Nat) (hN:0< N) (t : ℝ) (ht:t∈Icc 0 (N:ℝ)) :
 ∃j:Nat,j< N ∧ ∃s:ℝ,0≤ s ∧ s≤1 ∧ t=(j:ℝ)+s := by
 by_cases he:t=(N:ℝ)
 · refine ⟨N-1,by omega,1,by norm_num,by norm_num,?_⟩
   rw[he,Nat.cast_sub (by omega : 1≤ N)]
   norm_num
 · have htN:t<(N:ℝ):=lt_of_le_of_ne ht.2 he
   refine ⟨⌊t⌋₊,?_,t-(⌊t⌋₊:ℝ),?_,?_,by ring⟩
   · exact (Nat.floor_lt ht.1).mpr htN
   · exact sub_nonneg.mpr (Nat.floor_le ht.1)
   · have h:=Nat.lt_floor_add_one t
     linarith
end RHHighContourGeometry
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
open scoped ComplexConjugate
namespace RHHighGridAssembly
open RHHighContourGeometry
lemma all_jets
 (hu:∀j k:Nat,j≤4096 → k<8 →
  ‖RHHighPolynomialJet.jet (-64+(j:ℂ)/32+I/2) (1/32) k-
   RHHighContourVector.value (RHHighContourGrid.horizontal j k)‖≤1/10^12)
 (hl:∀j k:Nat,j≤128 → k<8 →
  ‖RHHighPolynomialJet.jet (-64+(-1/2+(j:ℂ)/128)*I) (I/128) k-
   RHHighContourVector.value (RHHighContourGridV2.vertical false j k)‖≤1/10^12)
 (hr:∀j k:Nat,j≤128 → k<8 →
  ‖RHHighPolynomialJet.jet (64+(-1/2+(j:ℂ)/128)*I) (I/128) k-
   RHHighContourVector.value (RHHighContourGridV2.vertical true j k)‖≤1/10^12)
 (e j k : Nat) (he:e<4) (hj:j≤ cells e) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (point e j) (step e) k-
 RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12 := by
 interval_cases e
 · have hj':j≤4096:=by simpa [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells] using hj
   have hz:point 0 j=conj (-64+(j:ℂ)/32+I/2) := by
    norm_num [point,line,start,step,map_add,map_div₀,map_neg,map_natCast,map_ofNat]
    ring
   have hh:step 0=conj (1/32:ℂ) := by norm_num [step,map_div₀,map_natCast,map_ofNat]
   rw[hz,hh]
   change ‖RHHighPolynomialJet.jet (conj (-64+(j:ℂ)/32+I/2)) (conj (1/32:ℂ)) k-
    RHHighContourVector.value ((RHHighContourGrid.horizontal j k).1,-(RHHighContourGrid.horizontal j k).2)‖≤ _
   rw[RHHighPolynomialSymmetry.error_conj]
   exact hu j k hj' hk
 · have hj':j≤128:=by simpa only[cells,RHHighContourGridV2.cells,RHHighContourGrid.cells,if_neg (by decide : ¬(1=0 ∨ 1=2))] using hj
   have hz:point 1 j=64+(-1/2+(j:ℂ)/128)*I := by norm_num [point,line,start,step];ring
   have hh:step 1=I/128:=by norm_num [step]
   rw[hz,hh]
   exact hr j k hj' hk
 · have hj':j≤4096:=by simpa [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells] using hj
   have hz:point 2 j= -64+(j:ℂ)/32+I/2 := by norm_num [point,line,start,step];ring
   have hh:step 2=1/32:=by norm_num [step]
   rw[hz,hh]
   exact hu j k hj' hk
 · have hj':j≤128:=by simpa only[cells,RHHighContourGridV2.cells,RHHighContourGrid.cells,if_neg (by decide : ¬(3=0 ∨ 3=2))] using hj
   have hz:point 3 j= -64+(-1/2+(j:ℂ)/128)*I := by norm_num [point,line,start,step];ring
   have hh:step 3=I/128:=by norm_num [step]
   rw[hz,hh]
   exact hl j k hj' hk
end RHHighGridAssembly
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighHorizontalAssembly
noncomputable def rows (t k : Nat) : List (List Nat) :=
 (((RHHighContourGrid.horizontalRows[t]?).getD [])[k]?).getD []
lemma lookup (j k : Nat) (rs : List (List Nat))
 (hrs:rs=rows (if j<2048 then 0 else if j<4096 then 1 else 2) k)
 (hr:rs.all (fun row=> decide (row.length=512))=true)
 (hi:j%2048< rs.flatten.length) :
 RHHighContourVector.decode (((rs.flatten)[j%2048]?).getD 0)=RHHighContourGrid.horizontal j k := by
 have h:=RHHighFFTListInterface.uniform_lookup rs (j%2048) hr hi
 simp only[RHHighFFTListInterface.entry] at h
 rw[h]
 dsimp only[RHHighContourGrid.horizontal]
 dsimp only[rows] at hrs
 rw[←hrs]
 have hm:(j%2048)%512=j%512:=Nat.mod_mod_of_dvd j (by decide : 512∣2048)
 rw[hm]
lemma all_upper
 (ha:∀t k:Nat,t<3 → k<8 → ∀i:Nat,i<2048 →
  ‖RHHighPolynomialJet.jet ((64:ℂ)*t-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) k-
   RHHighContourVector.value (RHHighContourVector.decode ((((rows t k).flatten)[i]?).getD 0))‖≤1/10^12)
 (hr:∀t k:Nat,t<3 → k<8 → (rows t k).all (fun row=> decide (row.length=512))=true)
 (hlen:∀t k:Nat,t<3 → k<8 → (rows t k).flatten.length=2048)
 (j k : Nat) (hj:j≤4096) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (-64+(j:ℂ)/32+Complex.I/2) (1/32) k-
   RHHighContourVector.value (RHHighContourGrid.horizontal j k)‖≤1/10^12 := by
 let t:=if j<2048 then 0 else if j<4096 then 1 else 2
 have ht:t<3:=by dsimp[t];split_ifs <;> omega
 have hi:j%2048<2048:=Nat.mod_lt _ (by decide)
 have h:=ha t k ht hk (j%2048) hi
 have hw:=lookup j k (rows t k) rfl (hr t k ht hk) (by rw[hlen t k ht hk];exact hi)
 rw[hw] at h
 have hx:(64:ℂ)*t-64+(1/2:ℂ)*Complex.I+((j%2048:Nat):ℂ)/32=
  -64+(j:ℂ)/32+Complex.I/2 := by
  have he:2048*t+j%2048=j := by dsimp[t];split_ifs <;> omega
  have hc:((2048*t+j%2048:Nat):ℂ)=(j:ℂ):=by exact_mod_cast he
  push_cast at hc
  linear_combination (norm:=ring_nf) hc/32
 rw[hx] at h
 exact h
end RHHighHorizontalAssembly
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighHorizontalAssembly
lemma all_upper_two
 (ha:∀t k:Nat,t<2 → k<8 → ∀i:Nat,i<2048 →
  ‖RHHighPolynomialJet.jet ((64:ℂ)*t-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) k-
   RHHighContourVector.value (RHHighContourVector.decode ((((rows t k).flatten)[i]?).getD 0))‖≤1/10^12)
 (hr:∀t k:Nat,t<2 → k<8 → (rows t k).all (fun row=>decide (row.length=512))=true)
 (hlen:∀t k:Nat,t<2 → k<8 → (rows t k).flatten.length=2048)
 (hend:∀k:Nat,k<8 →
  ‖RHHighPolynomialJet.jet (64+Complex.I/2) (1/32) k-
   RHHighContourVector.value (RHHighContourGrid.horizontal 4096 k)‖≤1/10^12)
 (j k : Nat) (hj:j≤4096) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (-64+(j:ℂ)/32+Complex.I/2) (1/32) k-
   RHHighContourVector.value (RHHighContourGrid.horizontal j k)‖≤1/10^12 := by
 by_cases hlast:j=4096
 · subst j
   convert hend k hk using 1 <;> norm_num
 · have hj':j<4096:=by omega
   let t:=if j<2048 then 0 else 1
   have ht:t<2:=by dsimp[t];split_ifs <;> omega
   have hi:j%2048<2048:=Nat.mod_lt _ (by decide)
   have h:=ha t k ht hk (j%2048) hi
   have hrs:rows t k=rows (if j<2048 then 0 else if j<4096 then 1 else 2) k := by
    simp only[if_pos hj',t]
   have hw:=lookup j k (rows t k) hrs (hr t k ht hk) (by rw[hlen t k ht hk];exact hi)
   rw[hw] at h
   have hx:(64:ℂ)*t-64+(1/2:ℂ)*Complex.I+((j%2048:Nat):ℂ)/32=
    -64+(j:ℂ)/32+Complex.I/2 := by
    have he:2048*t+j%2048=j := by dsimp[t];split_ifs <;> omega
    have hc:((2048*t+j%2048:Nat):ℂ)=(j:ℂ):=by exact_mod_cast he
    push_cast at hc
    linear_combination (norm:=ring_nf) hc/32
   rw[hx] at h
   exact h
end RHHighHorizontalAssembly
end
end RHHighAllContourJetsProof

namespace RHHighContourJetUpperZeroK00
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK00
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k00 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 0-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK00.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK00.rows
 let J:=RHHighContourInputIUpperZeroK00.rows
 let v:=RHHighContourSpectrumUpperZeroK00.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK00.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK00.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK00.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK00.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK00.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK00.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 0=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=RHHighFourierPolynomial.word 0:=by decide +kernel
  change _=RHHighFourierPolynomial.coefficient 0
  simp only[h0,RHHighContourVector.value,RHHighContourVector.decode,
   RHHighFourierPolynomial.coefficient,RHHighFourierPolynomial.realInteger,RHHighFourierPolynomial.imagInteger]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK00.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK00.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK00.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK00.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK00.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK00.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k00
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 0 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK00.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK00.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k00 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK00.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK00.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK01
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK01
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k01 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 1-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK01.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK01.rows
 let J:=RHHighContourInputIUpperZeroK01.rows
 let v:=RHHighContourSpectrumUpperZeroK01.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK01.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK01.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK01.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK01.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k01 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK01.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK01.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 1=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK01.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK01.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK01.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK01.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK01.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK01.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k01
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 1 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK01.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK01.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k01 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK01.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK01.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK02
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK02
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k02 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 2-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK02.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK02.rows
 let J:=RHHighContourInputIUpperZeroK02.rows
 let v:=RHHighContourSpectrumUpperZeroK02.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK02.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK02.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK02.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK02.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k02 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK02.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK02.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 2=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK02.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK02.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK02.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK02.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK02.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK02.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k02
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 2 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK02.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK02.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k02 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK02.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK02.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK03
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK03
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k03 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 3-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK03.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK03.rows
 let J:=RHHighContourInputIUpperZeroK03.rows
 let v:=RHHighContourSpectrumUpperZeroK03.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK03.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK03.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK03.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK03.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k03 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK03.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK03.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 3=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK03.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK03.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK03.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK03.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK03.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK03.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k03
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 3 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK03.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK03.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k03 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK03.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK03.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK04
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK04
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k04 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 4-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK04.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK04.rows
 let J:=RHHighContourInputIUpperZeroK04.rows
 let v:=RHHighContourSpectrumUpperZeroK04.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK04.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK04.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK04.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK04.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k04 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK04.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK04.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 4=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK04.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK04.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK04.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK04.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK04.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK04.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k04
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 4 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK04.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK04.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k04 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK04.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK04.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK05
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK05
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k05 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 5-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK05.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK05.rows
 let J:=RHHighContourInputIUpperZeroK05.rows
 let v:=RHHighContourSpectrumUpperZeroK05.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK05.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK05.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK05.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK05.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k05 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK05.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK05.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 5=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK05.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK05.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK05.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK05.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK05.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK05.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k05
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 5 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK05.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK05.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k05 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK05.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK05.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK06
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK06
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k06 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 6-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK06.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK06.rows
 let J:=RHHighContourInputIUpperZeroK06.rows
 let v:=RHHighContourSpectrumUpperZeroK06.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK06.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK06.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK06.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK06.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k06 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK06.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK06.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 6=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK06.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK06.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK06.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK06.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK06.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK06.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k06
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 6 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK06.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK06.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k06 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK06.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK06.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
namespace RHHighContourJetUpperZeroK07
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
lemma ofFn_add {N : Nat} (xs ys zs : List Nat) (hx:xs.length=N) (hy:ys.length=N) (hz:zs.length=N)
    (hs:∀j:Nat,j<N → entry zs j=entry xs j+entry ys j) :
    List.ofFn (fun j:Fin N=>entry xs j.val+entry ys j.val)=zs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hz.symm
  · intro j hj hj'
    have hN:j<N:=by simpa only [List.length_ofFn] using hj
    have h:=hs j hN
    simpa only [entry,List.getElem?_eq_getElem (show j<xs.length by omega),
      List.getElem?_eq_getElem (show j<ys.length by omega),List.getElem?_eq_getElem hj',
      Option.getD_some,List.getElem_ofFn] using h.symm
end RHHighFFTListInterface
end
section
set_option autoImplicit false
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
end RHHighContourJetUpperZeroK07
theorem TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k07 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (0+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 7-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK07.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHHighContourInputRUpperZeroK07.rows
 let J:=RHHighContourInputIUpperZeroK07.rows
 let v:=RHHighContourSpectrumUpperZeroK07.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK07.RHHighFFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHHighContourJetUpperZeroK07.RHHighFFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK07.RHHighFFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHHighContourJetUpperZeroK07.RHHighFFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
   RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧
   ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k07 i.val i.isLt
  have hhR:=RHHighContourJetUpperZeroK07.RHHighFFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hhJ:=RHHighContourJetUpperZeroK07.RHHighFFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only [ar,ai]
  rw[hhR,hhJ]
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) :((br i:Int)-2^81,(bi i:Int)-2^81)=
   RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hmag (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
   let b:=RHHighContourCoefficientData.proposed v positive m
   |b.1|+|b.2|≤(2:Int)^80 := by
  have h:=TaoFivePrimes.rh_high_height_contour_spectrum_bounds v
    (by simp only[v,List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
  have hlen:v.length=2049:=by decide +kernel
  have hidx:(if positive then 1024+m else m)<v.length := by rw[hlen];split_ifs <;> omega
  have hh:=(List.all_eq_true.mp h) (v[if positive then 1024+m else m]) (List.getElem_mem hidx)
  simpa only[RHHighContourCoefficientData.proposed,List.getElem?_eq_getElem hidx,Option.getD_some,decide_eq_true_eq] using hh
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
   if 7=0 then RHHighFourierPolynomial.coefficient 0 else 0 := by
  have h0:((v[0]?).getD 0)=3138550867693340381917894711643447289308309891028789231616:=by decide +kernel
  norm_num[h0,RHHighContourVector.value,RHHighContourVector.decode]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
   (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK07.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHHighContourJetUpperZeroK07.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw [hs,RHHighContourJetUpperZeroK07.RHHighFFTListInterface.ofFn_at R.flatten hR,
   RHHighContourJetUpperZeroK07.RHHighFFTListInterface.ofFn_at J.flatten hJ,
   RHHighContourJetUpperZeroK07.RHHighFFTListInterface.ofFn_at brs hKR,RHHighContourJetUpperZeroK07.RHHighFFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k07
 have h:=TaoFivePrimes.rh_high_height_contour_fft_semantic ⟨1,by decide⟩ 7 (by decide) v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHHighContourJetUpperZeroK07.RHHighFFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHHighContourJetUpperZeroK07.RHHighFFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun p m hm=>TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k07 m hm p)
  hmag (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHHighContourOutputUpperZeroK07.rows.flatten.length=2048:=by decide +kernel
 rw[RHHighContourJetUpperZeroK07.RHHighFFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Nat.cast_ofNat,Fin.val_mk,RHHighContourVector.value,show (64:ℂ)*1-64=0 by norm_num] at h ⊢
 exact h
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution (e j k : Nat) (he:e<4) (hj:j≤RHHighContourGeometry.cells e) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
 RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12 := by
 apply RHHighAllContourJetsProof.RHHighGridAssembly.all_jets ?_
  (fun j k hj hk=>TaoFivePrimes.rh_high_height_vertical_jet_left_enclosure j k hj hk)
  (fun j k hj hk=>TaoFivePrimes.rh_high_height_vertical_jet_right_enclosure j k hj hk) e j k he hj hk
 intro j k hj hk
 apply RHHighAllContourJetsProof.RHHighHorizontalAssembly.all_upper_two ?_ ?_ ?_ (fun k hk=>TaoFivePrimes.rh_high_height_upper_right_endpoint k hk) j k hj hk
 · intro t k ht hk i hi
   interval_cases t <;> interval_cases k
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 0-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutput00.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k00 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 1-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K01.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k01 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 2-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K02.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k02 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 3-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K03.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k03 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 4-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K04.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k04 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 5-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K05.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k05 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 6-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K06.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k06 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*0-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 7-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K07.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k07 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 0-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK00.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k00 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 1-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK01.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k01 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 2-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK02.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k02 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 3-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK03.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k03 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 4-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK04.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k04 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 5-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK05.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k05 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 6-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK06.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k06 i hi using 1 <;> norm_num
   · simp only[Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
     change ‖RHHighPolynomialJet.jet ((64:ℂ)*1-64+(1/2:ℂ)*Complex.I+(i:ℂ)/32) (1/32) 7-
       RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperZeroK07.rows.flatten)[i]?).getD 0))‖≤_
     convert TaoFivePrimes.rh_high_height_contour_jet_upper_zero_k07 i hi using 1 <;> norm_num
 · intro t k ht hk
   interval_cases t <;> interval_cases k <;> decide +kernel
 · intro t k ht hk
   interval_cases t <;> interval_cases k <;> decide +kernel
#print axioms solution
