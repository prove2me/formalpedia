-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_fourier_polynomial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:12:51.713386+00:00
-- url     : https://prove2.me/submissions/7ae54f24-8098-4ff8-a1c6-b0898fff91ff

import Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
namespace RHBatch01CertifiedPolynomialBounds
namespace RHBatch01FourierPolynomial
export _root_.RHBatch01FourierPolynomial (coefficient imagInteger phase polynomial realInteger word)
end RHBatch01FourierPolynomial
namespace RHBatch01ZetaFourierData
export _root_.RHBatch01ZetaFourierData (row00 row01 row02 rows)
end RHBatch01ZetaFourierData
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
open scoped ComplexConjugate
namespace RHBatch01FourierPolynomial
noncomputable def integerMass (m : Nat) : Nat := (realInteger m).natAbs+(imagInteger m).natAbs
noncomputable def mass : Nat := integerMass 0+2*∑ m∈Finset.range 1024,integerMass (m+1)
noncomputable def mass8 : Nat := 2*∑ m∈Finset.range 1024,integerMass (m+1)*(m+1)^8
theorem integer_bounds : 5*mass≤3*2^80 ∧ 100*mass8≤2^80*1024^8 ∧ imagInteger 0=0 := by decide +kernel
lemma coefficient_norm (m : Nat) : ‖coefficient m‖≤(integerMass m:ℝ)/(2:ℝ)^80 := by
  unfold coefficient integerMass
  rw [norm_div,norm_pow,norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h:=norm_add_le (realInteger m:ℂ) ((imagInteger m:ℂ)*I)
  simp only [norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one,Int.cast_natCast] at h
  simpa only [Nat.cast_add,Nat.cast_natAbs,Int.cast_abs] using h
lemma coefficient_mass : ‖coefficient 0‖+2*∑ m∈Finset.range 1024,‖coefficient (m+1)‖≤3/5 := by
  have h:=integer_bounds.1
  have hr:(5:ℝ)*mass≤3*(2:ℝ)^80 := by exact_mod_cast h
  have hs:(∑ m∈Finset.range 1024,‖coefficient (m+1)‖)≤
      (∑ m∈Finset.range 1024,(integerMass (m+1):ℝ))/(2:ℝ)^80 := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun m hm=>coefficient_norm (m+1))
  have he:((integerMass 0:ℝ)/(2:ℝ)^80)+
      2*((∑ m∈Finset.range 1024,(integerMass (m+1):ℝ))/(2:ℝ)^80)=(mass:ℝ)/(2:ℝ)^80 := by
    unfold mass
    push_cast
    ring
  have hb:(mass:ℝ)/(2:ℝ)^80≤3/5 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  exact ((add_le_add (coefficient_norm 0) (mul_le_mul_of_nonneg_left hs (by norm_num))).trans_eq he).trans hb
lemma coefficient_mass8 :
    2*∑ m∈Finset.range 1024,‖coefficient (m+1)‖*((m+1:ℝ)/1024)^8≤1/100 := by
  have h:=integer_bounds.2.1
  have hr:(100:ℝ)*mass8≤(2:ℝ)^80*1024^8 := by exact_mod_cast h
  have hs:(2:ℝ)*∑ m∈Finset.range 1024,‖coefficient (m+1)‖*((m+1:ℝ)/1024)^8≤
      2*∑ m∈Finset.range 1024,((integerMass (m+1):ℝ)/(2:ℝ)^80)*((m+1:ℝ)/1024)^8 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum (fun m hm=>mul_le_mul_of_nonneg_right (coefficient_norm (m+1)) (by positivity))
  have he:(2:ℝ)*∑ m∈Finset.range 1024,((integerMass (m+1):ℝ)/(2:ℝ)^80)*((m+1:ℝ)/1024)^8=
      (mass8:ℝ)/((2:ℝ)^80*1024^8) := by
    unfold mass8
    push_cast
    rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    push_cast
    ring
  exact hs.trans (he.le.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith)))
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
end RHBatch01FourierPolynomial
end
end RHBatch01CertifiedPolynomialBounds
theorem solution :
 (‖RHBatch01FourierPolynomial.coefficient 0‖+2*∑m∈Finset.range 1024,‖RHBatch01FourierPolynomial.coefficient (m+1)‖≤3/5) ∧
 (2*∑m∈Finset.range 1024,‖RHBatch01FourierPolynomial.coefficient (m+1)‖*((m+1:ℝ)/1024)^8≤1/100) ∧
 RHBatch01FourierPolynomial.imagInteger 0=0 := by
 exact ⟨RHBatch01CertifiedPolynomialBounds.RHBatch01FourierPolynomial.coefficient_mass,
 RHBatch01CertifiedPolynomialBounds.RHBatch01FourierPolynomial.coefficient_mass8,RHBatch01CertifiedPolynomialBounds.RHBatch01FourierPolynomial.integer_bounds.2.2⟩
#print axioms solution
