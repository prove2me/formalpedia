-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_count_from_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:14:37.260259+00:00
-- url     : https://prove2.me/submissions/08b4bf04-958a-44e3-9e92-d165a8eec6a9

import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighContourArithmetic
import Definitions.Def_TaoFivePrimes_RHHighContourArithmeticV2
import Definitions.Def_TaoFivePrimes_RHHighContourGeometry
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Theorems.Thm_SWPort_Zeta0EqZeta
import Theorems.Thm_TaoFivePrimes_rh_high_height_fourier_polynomial_bounds
import Theorems.Thm_TaoFivePrimes_rh_high_height_full_window_reconstruction
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
import Theorems.Thm_Zeta23_Analytic_rectangleIntegralPrime_mul_logDeriv_of_poles
import Theorems.Thm_Zeta23_RvM_completedRiemannZeta_eq_zero_iff
namespace RHHighCountFromCertificateProof
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHHighContourArithmetic
export _root_.RHHighContourArithmetic (Record check difference log16 logAux mul normSq ratio)
end RHHighContourArithmetic
namespace RHHighContourArithmeticV2
export _root_.RHHighContourArithmeticV2 (Record check difference log16 logAux mul normSq ratio)
end RHHighContourArithmeticV2
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
namespace RHHighDirichletArithmetic
export _root_.RHHighDirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHHighDirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHHighFourierPolynomial
export _root_.RHHighFourierPolynomial (coefficient imagInteger phase polynomial realInteger word)
end RHHighFourierPolynomial
namespace RHHighFullCoefficient
export _root_.RHHighFullCoefficient (F L W delta group weight)
end RHHighFullCoefficient
namespace RHHighGammaArithmetic
export _root_.RHHighGammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHHighGammaArithmetic
namespace RHHighGammaGuards
export _root_.RHHighGammaGuards (guard)
end RHHighGammaGuards
namespace RHHighGenericExpHorner
export _root_.RHHighGenericExpHorner (cn cp horner sn sp)
end RHHighGenericExpHorner
namespace RHHighGlobalBinTree
export _root_.RHHighGlobalBinTree (flatten get get_sound length_flatten size valid zeroWord)
end RHHighGlobalBinTree
namespace RHHighGlobalDirichletBins
export _root_.RHHighGlobalDirichletBins (coefficient coefficient_bound coefficients_checked flatten_checked groups tree valid_checked values word word_eq)
end RHHighGlobalDirichletBins
namespace RHHighGlobalDirichletBins00
export _root_.RHHighGlobalDirichletBins00 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins00
namespace RHHighGlobalDirichletBins01
export _root_.RHHighGlobalDirichletBins01 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins01
namespace RHHighGlobalDirichletBins02
export _root_.RHHighGlobalDirichletBins02 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins02
namespace RHHighGlobalDirichletBins03
export _root_.RHHighGlobalDirichletBins03 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 rows)
end RHHighGlobalDirichletBins03
namespace RHHighHeight
export _root_.RHHighHeight (critical normalized normalizedComplex windowZeros)
end RHHighHeight
namespace RHHighHomogeneousHorner
export _root_.RHHighHomogeneousHorner (hom)
end RHHighHomogeneousHorner
namespace RHHighLogData
export _root_.RHHighLogData (D F coefficients denominator log2 log2pi numerator rounded)
end RHHighLogData
namespace RHHighNegativeExp
export _root_.RHHighNegativeExp (denominator en ep numerator seed)
end RHHighNegativeExp
namespace RHHighPolynomialJet
export _root_.RHHighPolynomialJet (generator jet)
end RHHighPolynomialJet
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
namespace RHHighVerticalJetsLeft
export _root_.RHHighVerticalJetsLeft (row00 row01 row02 rows)
end RHHighVerticalJetsLeft
namespace RHHighVerticalJetsRight
export _root_.RHHighVerticalJetsRight (row00 row01 row02 rows)
end RHHighVerticalJetsRight
namespace RHHighZetaFourierData
export _root_.RHHighZetaFourierData (row00 row01 row02 rows)
end RHHighZetaFourierData
namespace SWPort
export _root_.SWPort (Zeta0EqZeta)
end SWPort
namespace TaoFivePrimes
export _root_.TaoFivePrimes (rh_high_height_fourier_polynomial_bounds rh_high_height_full_window_reconstruction)
end TaoFivePrimes
namespace Zeta23.Analytic
export _root_.Zeta23.Analytic (rectangleIntegralPrime_mul_logDeriv_of_poles)
end Zeta23.Analytic
namespace Zeta23
export _root_.Zeta23 (ChebyshevMertens D0 ExplicitFormulaPaper Ffun GammaFacts Hfun IsNontrivialZero Iwin MVHilbert N0 N0simple N0star Ncount Ndist Nsimple PX PaperInputs Params PiX RiemannVonMangoldt TaperProfile ZeroConfig ZetaSeam analyticOrderAt_conj_conj analyticOrderAt_riemannZeta_ne_top analyticOrderAt_zeta_conj analyticOrderAt_zeta_one_sub ell1 gammaOf isConnected_compl_one l mu nuX paperFT reflect riemannZeta_analyticOnNhd_compl_one riemannZeta_conj riemannZeta_zeros_locallyFinite zeroMult zerosIn zetaSeam zetaZeroConfig zetaZeros zeta_mult_reflect zeta_reflect_zero)
end Zeta23
namespace Zeta23.Params
export _root_.Zeta23.Params (Aphi Gentry Gp L Phi PhiR X a autocorr b calE crho d fk g hat hgrid lam1 phi phiHat phiHatR psi tau tilde trGtilde trGtildeSq)
end Zeta23.Params
namespace Zeta23.RvM
export _root_.Zeta23.RvM (completedRiemannZeta_eq_zero_iff)
end Zeta23.RvM
namespace Zeta23.ZeroConfig
export _root_.Zeta23.ZeroConfig (Az Ez Gsummand Gz N N0 N0s N0star NIprime Nd NonIprime Ns S1 S2 W Wsummand ZIprime offLine onLine p s1 s2 simple window)
end Zeta23.ZeroConfig
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourPair
noncomputable def value (D : Nat) (p : Int×Int) : ℂ := ((p.1:ℂ)+(p.2:ℂ)*I)/(D:ℂ)
lemma normSq_cast (p : Int×Int) : (RHHighContourArithmetic.normSq p:ℝ)=(p.1:ℝ)^2+(p.2:ℝ)^2 := by
 simp only [RHHighContourArithmetic.normSq,Nat.cast_add,Nat.cast_pow,Nat.cast_natAbs,Int.cast_abs,sq_abs]
lemma norm_square (D : Nat) (p : Int×Int) :
 ‖value D p‖^2=(RHHighContourArithmetic.normSq p:ℝ)/(D:ℝ)^2 := by
 rw[value,norm_div,div_pow,Complex.norm_natCast,Complex.sq_norm]
 congr 1
 rw[normSq_cast]
 simp [Complex.normSq_apply,pow_two]
lemma lower (D L : Nat) (p : Int×Int) (hD:0<D)
    (h:L^2≤RHHighContourArithmetic.normSq p) : (L:ℝ)/D≤‖value D p‖ := by
 have hR:(L:ℝ)^2≤(RHHighContourArithmetic.normSq p:ℝ):=by exact_mod_cast h
 have he:((L:ℝ)/D)^2≤‖value D p‖^2:=by
  rw[norm_square,div_pow]
  exact div_le_div_of_nonneg_right hR (by positivity)
 nlinarith only [he,norm_nonneg (value D p),show (0:ℝ)≤(L:ℝ)/D by positivity]
lemma upper (D U : Nat) (p : Int×Int) (hD:0<D)
    (h:RHHighContourArithmetic.normSq p≤U^2) : ‖value D p‖≤(U:ℝ)/D := by
 have hR:(RHHighContourArithmetic.normSq p:ℝ)≤(U:ℝ)^2:=by exact_mod_cast h
 have he:‖value D p‖^2≤((U:ℝ)/D)^2:=by
  rw[norm_square,div_pow]
  exact div_le_div_of_nonneg_right hR (by positivity)
 nlinarith only [he,norm_nonneg (value D p),show (0:ℝ)≤(U:ℝ)/D by positivity]
end RHHighContourPair
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourGuard
open RHHighContourArithmetic RHHighContourPair
lemma center_margin (c : Int×Int) (L S : Nat)
 (hl:L^2≤ normSq c) (hSL:S≤ L)
 (hm:101000008*2^80≤(L-S)*10^12) :
 (1/10000:ℝ)+8/10^12+1/10^6 ≤ ‖value (2^80) c‖-(S:ℝ)/(2:ℝ)^80 := by
 have hM:((101000008*2^80:Nat):ℝ)≤(((L-S)*10^12:Nat):ℝ):=by exact_mod_cast hm
 simp only[Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub hSL] at hM
 have hratio:(101000008:ℝ)/10^12≤((L:ℝ)-(S:ℝ))/(2:ℝ)^80 := by
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^80)).mpr
  nlinarith only[hM]
 have hlo:=lower (2^80) L c (by positivity) hl
 simp only[Nat.cast_pow,Nat.cast_ofNat] at hlo
 calc
  _ = (101000008:ℝ)/10^12 := by norm_num
  _ ≤ ((L:ℝ)-(S:ℝ))/(2:ℝ)^80 := hratio
  _ = (L:ℝ)/(2:ℝ)^80-(S:ℝ)/(2:ℝ)^80 := by ring
  _ ≤ _ := sub_le_sub_right hlo _
lemma ratio_small (c v : Int×Int) (hc:0< normSq c)
 (h:4*normSq (difference v c)≤ normSq c) :
 ‖value (2^80) v/value (2^80) c-1‖≤1/2 := by
 have hR:(4:ℝ)*(normSq (difference v c):ℝ)≤(normSq c:ℝ):=by exact_mod_cast h
 have hs:4*‖value (2^80) (difference v c)‖^2≤‖value (2^80) c‖^2 := by
  rw[norm_square,norm_square]
  have he:4*((normSq (difference v c):ℝ)/((2^80:Nat):ℝ)^2)=
    (4*(normSq (difference v c):ℝ))/((2^80:Nat):ℝ)^2 := by ring
  rw[he]
  exact div_le_div_of_nonneg_right hR (by positivity)
 have hpos:0<‖value (2^80) c‖^2 := by rw[norm_square];positivity
 have hcpos:0<‖value (2^80) c‖:=by nlinarith [norm_nonneg (value (2^80) c)]
 have hcn:value (2^80) c≠0:=norm_pos_iff.mp hcpos
 have hd:value (2^80) (difference v c)=value (2^80) v-value (2^80) c := by
  simp only[value,difference,Int.cast_sub]
  ring
 rw[show value (2^80) v/value (2^80) c-1=(value (2^80) v-value (2^80) c)/value (2^80) c by field_simp,
  ←hd,norm_div]
 apply (div_le_iff₀ hcpos).mpr
 have hs':(2*‖value (2^80) (difference v c)‖)^2≤‖value (2^80) c‖^2:=by nlinarith only[hs]
 have hle:=le_of_pow_le_pow_left₀ (by decide : (2:Nat)≠0) (norm_nonneg (value (2^80) c)) hs'
 calc
  _ ≤ ‖value (2^80) c‖/2 := (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by simpa only[mul_comm] using hle)
  _ =_ :=by ring
end RHHighContourGuard
end
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighContourRecord
open RHHighContourArithmeticV2
lemma guards (r : Record) :
 r.edge<4 ∧ r.index< RHHighContourGridV2.cells r.edge ∧ r.upper.length=7 ∧
 0< normSq (RHHighContourGridV2.jet r.edge r.index 0) ∧
 (∀(k:Nat)(hk:k< r.upper.length), normSq (RHHighContourGridV2.jet r.edge r.index (k+1))≤ (r.upper[k]'hk)^2) ∧
 r.lower^2≤ normSq (RHHighContourGridV2.jet r.edge r.index 0) ∧ r.upper.sum≤ r.lower ∧
 101000008*2^80≤(r.lower-r.upper.sum)*10^12 ∧
 4*normSq (difference (RHHighContourGridV2.jet r.edge (r.index+1) 0) (RHHighContourGridV2.jet r.edge r.index 0))≤ normSq (RHHighContourGridV2.jet r.edge r.index 0) ∧
 r.ratio128=ratio (RHHighContourGridV2.jet r.edge r.index 0) (RHHighContourGridV2.jet r.edge (r.index+1) 0) ∧
 r.log128=log16 r.ratio128 := by
 have h:=r.valid
 simp only[check,Bool.and_eq_true,decide_eq_true_eq] at h
 rcases h with ⟨⟨⟨he,hj,hlen,hp⟩,hu⟩,hl,hSL,hm,hr,hra,hlo⟩
 refine ⟨he,hj,hlen,hp,?_,hl,hSL,hm,hr,hra,hlo⟩
 have hz:=List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hu)
 intro k hk
 simpa only[decide_eq_true_eq] using hz k hk
lemma value_agree (p : Int×Int) :
 RHHighContourPair.value (2^80) p=RHHighContourVector.value p := by
 simp only[RHHighContourPair.value,RHHighContourVector.value,Nat.cast_pow,Nat.cast_ofNat]
lemma upper_radius (r : Record) :
 (∑k∈range 7,‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index (k+1))‖)≤
 (r.upper.sum:ℝ)/(2:ℝ)^80 := by
 have hg:=guards r
 have hlist:r.upper=List.ofFn (fun i:Fin 7=> r.upper[i.val]'(by rw[hg.2.2.1];exact i.isLt)) := by
  apply List.ext_getElem
  · simp only[List.length_ofFn,hg.2.2.1]
  · intro i h1 h2
    simp only[List.getElem_ofFn]
 have he:(∑k∈range 7,‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index (k+1))‖)≤
  ∑k:Fin 7,(r.upper[k.val]'(by rw[hg.2.2.1];exact k.isLt):ℝ)/(2:ℝ)^80 := by
  rw[←Fin.sum_univ_eq_sum_range (fun k:Nat=>‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index (k+1))‖) 7]
  apply Finset.sum_le_sum
  intro k hk
  have hk7:=k.isLt
  have hklen:k.val< r.upper.length:=by rw[hg.2.2.1];exact hk7
  rw[←value_agree]
  convert RHHighContourPair.upper (2^80) r.upper[k.val] (RHHighContourGridV2.jet r.edge r.index (k.val+1)) (by positivity) (hg.2.2.2.2.1 k.val hklen) using 1 <;> norm_num <;> rfl
 apply he.trans_eq
 rw[←Finset.sum_div]
 congr 1
 have hsum:=congrArg (fun xs:List Nat=>(xs.sum:ℝ)) hlist
 simp only[List.sum_ofFn,Nat.cast_sum] at hsum
 exact hsum.symm

lemma center_margin (r : Record) :
 (1/10000:ℝ)+8/10^12+1/10^6≤
 ‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0)‖-(r.upper.sum:ℝ)/(2:ℝ)^80 := by
 rcases guards r with ⟨_,_,_,_,_,hl,hSL,hm,_⟩
 simpa only[value_agree] using RHHighContourGuard.center_margin _ r.lower r.upper.sum hl hSL hm
lemma polynomial_disc (r : Record) (z h : ℂ) (s : ℝ)
 (hz:|z.im|≤1/2) (hh:‖h‖≤1/32) (hs:0≤ s ∧ s≤1)
 (ha:∀k:Nat,k<8 → ‖RHHighPolynomialJet.jet z h k-
 RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index k)‖≤1/10^12) :
 ‖RHHighFourierPolynomial.polynomial (z+(s:ℂ)*h)-RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0)‖≤
 (r.upper.sum:ℝ)/(2:ℝ)^80+8/10^12+1/10^6 := by
 have hb:=RHHighFourierPolynomial.boundary_disc z h
  (fun k=> RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index k)) (1/10^12) s hz hh hs (by positivity) ha
 calc
  _ ≤ (∑k∈range 7,‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index (k+1))‖)+8*(1/10^12)+1/10^6 := hb
  _ ≤ _ := by linarith only[upper_radius r]
lemma polynomial_lower (r : Record) (z h : ℂ) (s : ℝ)
 (hz:|z.im|≤1/2) (hh:‖h‖≤1/32) (hs:0≤ s ∧ s≤1)
 (ha:∀k:Nat,k<8 → ‖RHHighPolynomialJet.jet z h k-
 RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index k)‖≤1/10^12) :
 (1/10000:ℝ)≤‖RHHighFourierPolynomial.polynomial (z+(s:ℂ)*h)‖ := by
 have hd:=polynomial_disc r z h s hz hh hs ha
 have hm:=center_margin r
 have hn:=norm_sub_le_norm_sub_add_norm_sub (RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0))
  (RHHighFourierPolynomial.polynomial (z+(s:ℂ)*h)) 0
 simp only[sub_zero] at hn
 rw[norm_sub_rev (RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0))] at hn
 linarith only[hd,hm,hn]
lemma polynomial_start_disc (r : Record) (z h : ℂ) (s : ℝ)
 (hz:|z.im|≤1/2) (hh:‖h‖≤1/32) (hs:0≤ s ∧ s≤1)
 (ha:∀k:Nat,k<8 → ‖RHHighPolynomialJet.jet z h k-
 RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index k)‖≤1/10^12) :
 ‖RHHighFourierPolynomial.polynomial (z+(s:ℂ)*h)-RHHighFourierPolynomial.polynomial z‖<
 ‖RHHighFourierPolynomial.polynomial z‖ := by
 have hd:=polynomial_disc r z h s hz hh hs ha
 have hm:=center_margin r
 have h0:=ha 0 (by omega)
 change ‖RHHighFourierPolynomial.jet z h 0-_‖≤ _ at h0
 rw[RHHighFourierPolynomial.jet_zero] at h0
 have hn:=norm_sub_le_norm_sub_add_norm_sub (RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0))
  (RHHighFourierPolynomial.polynomial z) 0
 simp only[sub_zero] at hn
 rw[norm_sub_rev (RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0))] at hn
 have ht:=norm_sub_le_norm_sub_add_norm_sub (RHHighFourierPolynomial.polynomial (z+(s:ℂ)*h))
  (RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0)) (RHHighFourierPolynomial.polynomial z)
 have hrev:‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0)-RHHighFourierPolynomial.polynomial z‖≤1/10^12:=by rw[norm_sub_rev];exact h0
 linarith only[hd,hm,h0,hn,ht,hrev]
end RHHighContourRecord
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
open Complex Set MeasureTheory Finset
namespace RHHighContourLog
noncomputable def onLine (f : ℂ→ℂ) (z v : ℂ) (t : ℝ) : ℂ := f (z+(t:ℂ)*v)
lemma cell_subset (N j : Nat) (hj:j< N) : Set.uIcc (j:ℝ) ((j+1:Nat):ℝ)⊆Set.uIcc (0:ℝ) (N:ℝ) := by
 rw[Set.uIcc_of_le (by exact_mod_cast Nat.le_succ j),Set.uIcc_of_le (Nat.cast_nonneg N)]
 exact Set.Icc_subset_Icc (Nat.cast_nonneg j) (by exact_mod_cast (show j+1≤ N by omega))
lemma mesh_integral (f : ℂ→ℂ) (z v : ℂ) (N : Nat)
 (hf:∀t∈Set.uIcc (0:ℝ) (N:ℝ),DifferentiableAt ℂ f (z+(t:ℂ)*v))
 (hn:∀t∈Set.uIcc (0:ℝ) (N:ℝ),onLine f z v t≠0)
 (hd:∀j:Nat,j< N → ∀t∈Set.uIcc (j:ℝ) ((j+1:Nat):ℝ),
  ‖onLine f z v t-onLine f z v (j:ℝ)‖<‖onLine f z v (j:ℝ)‖)
 (hi:IntervalIntegrable (fun t:ℝ=> logDeriv f (z+(t:ℂ)*v)*v) volume 0 (N:ℝ)) :
 (∫t:ℝ in (0:ℝ)..(N:ℝ),logDeriv f (z+(t:ℂ)*v)*v)=
 ∑j∈Finset.range N,Complex.log (onLine f z v ((j+1:Nat):ℝ)/onLine f z v (j:ℝ)) := by
 have hicell (j : Nat) (hj:j< N) : IntervalIntegrable (fun t:ℝ=> logDeriv f (z+(t:ℂ)*v)*v) volume (j:ℝ) ((j+1:Nat):ℝ) :=
  hi.mono_set (cell_subset N j hj)
 have hp:=intervalIntegral.sum_integral_adjacent_intervals (a:=fun j:Nat=>(j:ℝ)) hicell
 simp only[Nat.cast_zero] at hp
 rw[←hp]
 apply Finset.sum_congr rfl
 intro j hj
 have hjN:=Finset.mem_range.mp hj
 have hc:onLine f z v (j:ℝ)≠0 := by
  apply hn
  rw[Set.uIcc_of_le (Nat.cast_nonneg N)]
  exact ⟨Nat.cast_nonneg j,by exact_mod_cast hjN.le⟩
 have h:=segment_integral f (onLine f z v (j:ℝ)) z v hc (j:ℝ) ((j+1:Nat):ℝ)
  (fun t ht=> hf t (cell_subset N j hjN ht))
  (fun t ht=> disk_half_plane _ _ hc (hd j hjN t ht)) (hicell j hjN)
 change _=Complex.log (onLine f z v ((j+1:Nat):ℝ)/onLine f z v (j:ℝ))-
  Complex.log (onLine f z v (j:ℝ)/onLine f z v (j:ℝ)) at h
 simpa only[div_self hc,Complex.log_one,sub_zero] using h
lemma mesh_error (f : ℂ→ℂ) (z v : ℂ) (N : Nat) (w : Nat→ℂ)
 (hmesh:(∫t:ℝ in (0:ℝ)..(N:ℝ),logDeriv f (z+(t:ℂ)*v)*v)=
  ∑j∈Finset.range N,Complex.log (onLine f z v ((j+1:Nat):ℝ)/onLine f z v (j:ℝ)))
 (he:∀j:Nat,j< N → ‖Complex.log (onLine f z v ((j+1:Nat):ℝ)/onLine f z v (j:ℝ))-w j‖≤1/10000) :
 ‖(∫t:ℝ in (0:ℝ)..(N:ℝ),logDeriv f (z+(t:ℂ)*v)*v)-∑j∈Finset.range N,w j‖≤(N:ℝ)/10000 := by
 rw[hmesh,←Finset.sum_sub_distrib]
 apply (norm_sum_le _ _).trans
 calc
  _ ≤ ∑j∈Finset.range N,(1/10000:ℝ) := Finset.sum_le_sum (fun j hj=> he j (Finset.mem_range.mp hj))
  _ =_ :=by simp [div_eq_mul_inv]
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighDyadicRounding
lemma nat_division_error (a b : Nat) (hb : 0 < b) :
    |(a:ℝ)/b-((a/b:Nat):ℝ)|≤1 := by
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hr : (0:ℝ)≤(a%b:Nat) := Nat.cast_nonneg _
  have hl : ((a%b:Nat):ℝ)<b := by exact_mod_cast Nat.mod_lt a hb
  have he : ((a/b:Nat):ℝ)*(b:ℝ)+((a%b:Nat):ℝ)=(a:ℝ) := by
    exact_mod_cast Nat.div_add_mod' a b
  have hq : (a:ℝ)/b-((a/b:Nat):ℝ)=((a%b:Nat):ℝ)/b := by
    apply (eq_div_iff hbr.ne').mpr
    field_simp
    linarith
  rw [hq,abs_of_nonneg (div_nonneg hr hbr.le)]
  exact (div_le_one hbr).mpr hl.le
lemma scaled_rounding_error (a b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    |(a:ℝ)/b-((a*D/b:Nat):ℝ)/D|≤1/(D:ℝ) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he := nat_division_error (a*D) b hb
  have hq : (a:ℝ)/b-((a*D/b:Nat):ℝ)/D=
      (((a*D:Nat):ℝ)/b-((a*D/b:Nat):ℝ))/D := by
    push_cast
    field_simp
  rw [hq,abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right he hd.le
lemma complex_rounding_error (a c b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    ‖((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*D/b:Nat):ℂ)+((c*D/b:Nat):ℂ)*I)/(D:ℂ)‖≤2/(D:ℝ) := by
  have hr := scaled_rounding_error a b D hb hD
  have hi := scaled_rounding_error c b D hb hD
  have he : ((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*D/b:Nat):ℂ)+((c*D/b:Nat):ℂ)*I)/(D:ℂ)=
      (((a:ℝ)/b-((a*D/b:Nat):ℝ)/D:ℝ):ℂ)+
        (((c:ℝ)/b-((c*D/b:Nat):ℝ)/D:ℝ):ℂ)*I := by push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact (add_le_add hr hi).trans_eq (by ring)
end RHHighDyadicRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighDyadicRounding
lemma int_division_error (a : Int) (b : Nat) (hb : 0 < b) :
    |(a:ℝ)/b-((a/(b:Int):Int):ℝ)|≤1 := by
  have hbi : (0:Int)<b := by exact_mod_cast hb
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hr : (0:ℝ)≤((a%(b:Int):Int):ℝ) := by exact_mod_cast Int.emod_nonneg a hbi.ne'
  have hl : ((a%(b:Int):Int):ℝ)<b := by exact_mod_cast Int.emod_lt_of_pos a hbi
  have he : ((a/(b:Int):Int):ℝ)*(b:ℝ)+((a%(b:Int):Int):ℝ)=(a:ℝ) := by
    exact_mod_cast Int.ediv_mul_add_emod a (b:Int)
  have hq : (a:ℝ)/b-((a/(b:Int):Int):ℝ)=((a%(b:Int):Int):ℝ)/b := by
    apply (eq_div_iff hbr.ne').mpr
    field_simp
    linarith
  rw [hq,abs_of_nonneg (div_nonneg hr hbr.le)]
  exact (div_le_one hbr).mpr hl.le
lemma int_scaled_rounding_error (a : Int) (b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    |(a:ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ)/D|≤1/(D:ℝ) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he := int_division_error (a*(D:Int)) b hb
  have hq : (a:ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ)/D=
      (((a*(D:Int):Int):ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ))/D := by push_cast;field_simp
  rw [hq,abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right he hd.le
lemma int_complex_rounding_error (a c : Int) (b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    ‖((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*(D:Int)/(b:Int):Int):ℂ)+((c*(D:Int)/(b:Int):Int):ℂ)*I)/(D:ℂ)‖≤2/(D:ℝ) := by
  have hr := int_scaled_rounding_error a b D hb hD
  have hi := int_scaled_rounding_error c b D hb hD
  have he : ((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*(D:Int)/(b:Int):Int):ℂ)+((c*(D:Int)/(b:Int):Int):ℂ)*I)/(D:ℂ)=
      (((a:ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ)/D:ℝ):ℂ)+
        (((c:ℝ)/b-((c*(D:Int)/(b:Int):Int):ℝ)/D:ℝ):ℂ)*I := by push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact (add_le_add hr hi).trans_eq (by ring)
end RHHighDyadicRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighDyadicComplex
noncomputable def value (D : Nat) (a : Int×Int) : ℂ := ((a.1:ℂ)+(a.2:ℂ)*I)/(D:ℂ)
noncomputable def mul (D : Nat) (a b : Int×Int) : Int×Int :=
  ((a.1*b.1-a.2*b.2)/(D:Int),(a.1*b.2+a.2*b.1)/(D:Int))
noncomputable def divide (a : Int×Int) (n : Nat) : Int×Int :=
  (a.1/(n:Int),a.2/(n:Int))
lemma component (a : Int) (D : Nat) (hD:0<D) :
    |(a:ℝ)/(D:ℝ)^2-((a/(D:Int):Int):ℝ)/(D:ℝ)|≤1/(D:ℝ) := by
  have h:=RHHighDyadicRounding.int_division_error a D hD
  have hd:(0:ℝ)<D:=by exact_mod_cast hD
  rw [show (a:ℝ)/(D:ℝ)^2-((a/(D:Int):Int):ℝ)/(D:ℝ)=
    ((a:ℝ)/D-((a/(D:Int):Int):ℝ))/(D:ℝ) by ring,
    abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right h hd.le
lemma mul_error (D : Nat) (hD:0<D) (a b : Int×Int) :
    ‖value D (mul D a b)-value D a*value D b‖≤2/(D:ℝ) := by
  rw [norm_sub_rev]
  have hr:=component (a.1*b.1-a.2*b.2) D hD
  have hi:=component (a.1*b.2+a.2*b.1) D hD
  have he:value D a*value D b-value D (mul D a b)=
      ((((a.1*b.1-a.2*b.2:Int):ℝ)/(D:ℝ)^2-(((a.1*b.1-a.2*b.2)/(D:Int):Int):ℝ)/(D:ℝ):ℝ):ℂ)+
      ((((a.1*b.2+a.2*b.1:Int):ℝ)/(D:ℝ)^2-(((a.1*b.2+a.2*b.1)/(D:Int):Int):ℝ)/(D:ℝ):ℝ):ℂ)*I := by
    unfold value mul
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact (add_le_add hr hi).trans_eq (by ring)
lemma divide_error (D n : Nat) (hD:0<D) (hn:0<n) (a : Int×Int) :
    ‖value D (divide a n)-value D a/(n:ℂ)‖≤2/(D:ℝ) := by
  rw [norm_sub_rev]
  have hr:=RHHighDyadicRounding.int_division_error a.1 n hn
  have hi:=RHHighDyadicRounding.int_division_error a.2 n hn
  have hd:(0:ℝ)<D:=by exact_mod_cast hD
  have he:value D a/(n:ℂ)-value D (divide a n)=
    ((((a.1:ℝ)/(n:ℝ)-((a.1/(n:Int):Int):ℝ))/(D:ℝ):ℝ):ℂ)+
    ((((a.2:ℝ)/(n:ℝ)-((a.2/(n:Int):Int):ℝ))/(D:ℝ):ℝ):ℂ)*I := by
    unfold value divide
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
    abs_div,abs_of_pos hd]
  exact (add_le_add (div_le_div_of_nonneg_right hr hd.le)
    (div_le_div_of_nonneg_right hi hd.le)).trans_eq (by ring)
end RHHighDyadicComplex
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighRoundedLog
open RHHighContourArithmetic
noncomputable def V (p : Int×Int) : ℂ := RHHighDyadicComplex.value (2^128) p
noncomputable def power (r : Int×Int) : Nat→Int×Int
 | 0 => ((2:Int)^128,0)
 | n+1 => mul (power r n) r
noncomputable def sg (n : Nat) : Int := if n%2=1 then 1 else -1
lemma V_unit : V ((2:Int)^128,0)=1 := by norm_num [V,RHHighDyadicComplex.value]
lemma V_add (a b : Int×Int) : V (a.1+b.1,a.2+b.2)=V a+V b := by
 simp only[V,RHHighDyadicComplex.value,Int.cast_add]
 ring
lemma V_signed (a : Int×Int) (j : Nat) :
 V (sg j*(a.1/(j:Int)),sg j*(a.2/(j:Int)))=(sg j:ℂ)*RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide a j) := by
 simp only[V,RHHighDyadicComplex.value,RHHighDyadicComplex.divide,Int.cast_mul]
 ring
lemma sg_norm (j : Nat) : ‖(sg j:ℂ)‖=1 := by unfold sg;split_ifs <;> norm_num
lemma power_error (r : Int×Int) (hr:‖V r‖≤1) (n : Nat) :
 ‖V (power r n)-(V r)^n‖≤2*(n:ℝ)/(2:ℝ)^128 := by
 induction n with
 | zero => rw[power,V_unit,pow_zero,sub_self,norm_zero];norm_num
 | succ n ih =>
  have h:=RHHighDyadicComplex.mul_error (2^128) (by norm_num) (power r n) r
  change ‖V (mul (power r n) r)-V (power r n)*V r‖≤ _ at h
  have hp:‖V (power r n)*V r-(V r)^n*V r‖≤2*(n:ℝ)/(2:ℝ)^128 := by
   rw[←sub_mul,norm_mul]
   exact (mul_le_mul ih hr (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw[power,pow_succ]
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h hp)).trans_eq (by push_cast;norm_num;ring)
lemma term_error (r : Int×Int) (hr:‖V r‖≤1) (j : Nat) (hj:1 ≤ j ∧ j≤16) :
 ‖(sg j:ℂ)*RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide (power r j) j)-
  (sg j:ℂ)*(V r)^j/(j:ℂ)‖≤34/(2:ℝ)^128 := by
 have hd:=RHHighDyadicComplex.divide_error (2^128) j (by norm_num) (by omega) (power r j)
 have hp:‖V (power r j)/(j:ℂ)-(V r)^j/(j:ℂ)‖≤2*(j:ℝ)/(2:ℝ)^128 := by
  rw[←sub_div,norm_div,Complex.norm_natCast]
  have hjR:(1:ℝ)≤ j:=by exact_mod_cast hj.1
  exact (div_le_div_of_nonneg_right (power_error r hr j) (Nat.cast_nonneg j)).trans (div_le_self (by positivity) hjR)
 have he:(sg j:ℂ)*RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide (power r j) j)-
  (sg j:ℂ)*(V r)^j/(j:ℂ)=
  (sg j:ℂ)*(RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide (power r j) j)-(V r)^j/(j:ℂ)):=by ring
 rw[he,norm_mul,sg_norm,one_mul]
 have hjR:(j:ℝ)≤16:=by exact_mod_cast hj.2
 exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hd hp)).trans (by norm_num; nlinarith only[hjR])
lemma power_next (r : Int×Int) (j : Nat) (hj:0< j) :
 mul (power r (j-1)) r=power r j := by
 conv_rhs => rw[←Nat.sub_add_cancel (show 1≤ j by omega)]
 rfl
lemma aux_sum (r : Int×Int) (n next : Nat) (hn:0< next) (acc : Int×Int) :
 V (logAux r n next (power r (next-1)) acc)=V acc+
  ∑j∈Finset.range n,(sg (next+j):ℂ)*RHHighDyadicComplex.value (2^128)
   (RHHighDyadicComplex.divide (power r (next+j)) (next+j)) := by
 induction n generalizing next acc with
 | zero => simp only[logAux,Finset.range_zero,Finset.sum_empty,add_zero]
 | succ n ih =>
  rw[logAux,power_next r next hn]
  have hh:=ih (next+1) (by omega)
   (acc.1+sg next*((power r next).1/(next:Int)),acc.2+sg next*((power r next).2/(next:Int)))
  simp only[Nat.add_sub_cancel] at hh
  change V (logAux r n (next+1) (power r next)
   (acc.1+sg next*((power r next).1/(next:Int)),acc.2+sg next*((power r next).2/(next:Int))))=_
  rw[hh,Finset.sum_range_succ']
  rw[V_add acc (sg next*((power r next).1/(next:Int)),sg next*((power r next).2/(next:Int))),V_signed]
  simp only[Nat.add_zero,show ∀j:Nat,next+1+j=next+(j+1) by intro j;omega]
  ring
lemma sg_power (j : Nat) : (sg j:ℂ)=(-1:ℂ)^(j+1) := by
 rw[neg_one_pow_eq_pow_mod_two]
 unfold sg
 have hj:j%2<2:=Nat.mod_lt j (by decide)
 have he:(j+1)%2=(j%2+1)%2:=by omega
 rw[he]
 generalize hq:j%2=q at hj ⊢
 interval_cases q <;> norm_num
lemma logTaylor17_eq (z : ℂ) :
 Complex.logTaylor 17 z=∑j∈Finset.range 16,(sg (1+j):ℂ)*z^(1+j)/((1+j:Nat):ℂ) := by
 rw[Complex.logTaylor,Finset.sum_range_succ']
 simp only[Nat.zero_add,pow_zero,Nat.cast_zero,div_zero,add_zero]
 apply Finset.sum_congr rfl
 intro j hj
 rw[sg_power]
 simpa only [Nat.add_comm]
lemma log16_error (r : Int×Int) (hr:‖V r‖≤1) :
 ‖V (log16 r)-Complex.logTaylor 17 (V r)‖≤1/10^30 := by
 have h:=aux_sum r 16 1 (by decide) (0,0)
 change V (log16 r)=_ at h
 have hz:V (0,0)=0:=by simp[V,RHHighDyadicComplex.value]
 rw[hz,zero_add] at h
 rw[h,logTaylor17_eq,←Finset.sum_sub_distrib]
 apply (norm_sum_le _ _).trans
 calc
  _ ≤ ∑j∈Finset.range 16,(34/(2:ℝ)^128) := by
   exact Finset.sum_le_sum (fun j hj=> term_error r hr (1+j) ⟨by omega,by have hh:=Finset.mem_range.mp hj;omega⟩)
  _ ≤ _ :=by norm_num
end RHHighRoundedLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
open scoped ComplexConjugate
namespace RHHighContourRatioProgram
open RHHighContourArithmetic
noncomputable def pair (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
lemma normSq_pair (p : Int×Int) : (normSq p:ℂ)=pair p*conj (pair p) := by
 have hR:=RHHighContourPair.normSq_cast p
 have hC:(normSq p:ℂ)=(p.1:ℂ)^2+(p.2:ℂ)^2:=by exact_mod_cast hR
 rw[hC]
 simp only[pair,map_add,map_mul,map_intCast,Complex.conj_I]
 ring_nf
 simp only[I_sq]
 ring
lemma ratio_identity (c v : Int×Int) (hc:0< normSq c) :
 ((difference v c).1*c.1+(difference v c).2*c.2:ℂ)/ (normSq c:ℂ)+
  (((difference v c).2*c.1-(difference v c).1*c.2:ℂ)/(normSq c:ℂ))*I=
 RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1 := by
 have hM:(normSq c:ℂ)≠0:=by exact_mod_cast (Nat.ne_of_gt hc)
 have hcn:pair c≠0:=by intro h;rw[normSq_pair,h,zero_mul] at hM;exact hM rfl
 have hconj:conj (pair c)≠0 := by
  intro h
  apply hcn
  have he:=congrArg (fun z:ℂ=>conj z) h
  simpa only[starRingEnd_self_apply,map_zero] using he
 have hnum:(((difference v c).1*c.1+(difference v c).2*c.2:Int):ℂ)+
   ((((difference v c).2*c.1-(difference v c).1*c.2:Int):ℂ))*I=(pair v-pair c)*conj (pair c) := by
  simp only[difference,pair,Int.cast_add,Int.cast_sub,Int.cast_mul,map_add,map_mul,map_intCast,Complex.conj_I]
  ring_nf
  simp only[I_sq]
  ring
 have hscale (p : Int×Int) : RHHighContourPair.value (2^80) p=pair p/(2:ℂ)^80 := by
  simp only[RHHighContourPair.value,pair,Nat.cast_pow,Nat.cast_ofNat]
 have he:((normSq c:ℂ))=pair c*conj (pair c):=normSq_pair c
 calc
  _ = (((((difference v c).1*c.1+(difference v c).2*c.2:Int):ℂ)+
    ((((difference v c).2*c.1-(difference v c).1*c.2:Int):ℂ))*I)/(normSq c:ℂ)) := by push_cast;ring
  _ = (pair v-pair c)/pair c := by rw[hnum,he];field_simp [hcn,hconj] <;> ring
  _ = _ := by rw[hscale,hscale];field_simp <;> ring
lemma ratio_error (c v : Int×Int) (hc:0< normSq c) :
 ‖(RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1)-
 RHHighRoundedLog.V (ratio c v)‖≤2/(2:ℝ)^128 := by
 let a:Int:=(difference v c).1*c.1+(difference v c).2*c.2
 let b:Int:=(difference v c).2*c.1-(difference v c).1*c.2
 have h:=RHHighDyadicRounding.int_complex_rounding_error a b (normSq c) (2^128) hc (by norm_num)
 have he:((a:ℂ)+(b:ℂ)*I)/(normSq c:ℂ)=RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1 := by
  calc
   _ = (a:ℂ)/(normSq c:ℂ)+((b:ℂ)/(normSq c:ℂ))*I := by ring
   _ = _ := by simpa only[a,b,Int.cast_add,Int.cast_sub,Int.cast_mul] using ratio_identity c v hc
 rw[he] at h
 simpa only[RHHighRoundedLog.V,RHHighDyadicComplex.value,ratio,a,b,Nat.cast_pow,Nat.cast_ofNat,Int.natCast_pow] using h
end RHHighContourRatioProgram
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourLog
lemma ratio_perturbation (A B c v : ℂ)
    (hc:(1/10000:ℝ)≤‖c‖) (hA:‖A-c‖≤1/10^12) (hB:‖B-v‖≤1/10^12)
    (hr:‖v/c-1‖≤1/2) :
 ‖(B/A-1)-(v/c-1)‖≤1/10^7 ∧ ‖B/A-1‖≤3/5 := by
 have hcn:c≠0:=by intro h;rw[h,norm_zero] at hc;norm_num at hc
 have hAnorm:(1/20000:ℝ)≤‖A‖ := by
  have ht:=norm_sub_le_norm_sub_add_norm_sub c A 0
  simp only[sub_zero] at ht
  rw[norm_sub_rev] at ht
  have hs:‖A-c‖≤1/20000:=hA.trans (by norm_num)
  linarith only [ht,hc,hs]
 have hAn:A≠0:=by intro h;rw[h,norm_zero] at hAnorm;norm_num at hAnorm
 have hi:(1:ℝ)/‖A‖≤20000 := by
  have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/20000) hAnorm
  norm_num at hh
  simpa only [one_div] using hh
 have hq:‖v/c‖≤3/2 := by
  have h:=norm_sub_le_norm_sub_add_norm_sub (v/c) 1 0
  simp only[sub_zero,norm_one] at h
  linarith only[h,hr]
 have he:B/A-v/c=(B-v)/A-(v/c)*((A-c)/A) := by field_simp;ring
 have h1:‖(B-v)/A‖≤20000/10^12 := by
  rw[norm_div,div_eq_mul_inv]
  have hi':‖A‖⁻¹≤20000:=by simpa only[one_div] using hi
  exact (mul_le_mul hB hi' (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)).trans_eq (by ring)
 have h2:‖(v/c)*((A-c)/A)‖≤30000/10^12 := by
  have hi':‖A‖⁻¹≤20000:=by simpa only[one_div] using hi
  have he0:=mul_le_mul hA hi' (inv_nonneg.mpr (norm_nonneg _)) (by norm_num : (0:ℝ)≤1/10^12)
  have ht : ‖v/c‖*(‖A-c‖*‖A‖⁻¹)≤(3/2:ℝ)*((1/10^12)*20000) :=
   mul_le_mul hq he0 (by positivity) (by norm_num)
  calc
   _ = ‖v/c‖*(‖A-c‖*‖A‖⁻¹) := by simp only [norm_mul,norm_div,div_eq_mul_inv,norm_inv]
   _ ≤ (3/2:ℝ)*((1/10^12)*20000) := ht
   _ = 30000/10^12 := by norm_num
 have herr:‖(B/A-1)-(v/c-1)‖≤1/10^7 := by
  rw[show (B/A-1)-(v/c-1)=B/A-v/c by ring,he]
  exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (by norm_num))
 refine ⟨herr,?_⟩
 have h:=norm_sub_le_norm_sub_add_norm_sub (B/A-1) (v/c-1) 0
 simp only[sub_zero] at h
 exact h.trans ((add_le_add herr hr).trans (by norm_num))
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighContourLog
lemma log_taylor16 (z : ℂ) (hz:‖z-1‖≤1/2) :
    ‖Complex.log z-Complex.logTaylor 16 (z-1)‖≤1/500000 := by
  have h := Complex.norm_log_sub_logTaylor_le 15 (lt_of_le_of_lt hz (by norm_num : (1/2:ℝ)<1))
  simp only [add_sub_cancel,Nat.reduceAdd] at h
  norm_num only [Nat.cast_ofNat] at h
  have hp : ‖z-1‖^16≤(1/2:ℝ)^16 := pow_le_pow_left₀ (norm_nonneg _) hz _
  have hi : (1-‖z-1‖)⁻¹≤2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) (by linarith : (1/2:ℝ)≤1-‖z-1‖)
    norm_num [one_div] at hh
    exact hh
  have hinv:0≤(1-‖z-1‖)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ ≤ ‖z-1‖^16*(1-‖z-1‖)⁻¹/16 := h
    _ ≤ (1/2:ℝ)^16*2/16 := by gcongr
    _ ≤ _ := by norm_num
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourLog
lemma log_taylor16_three_fifths (z : ℂ) (hz:‖z-1‖≤3/5) :
 ‖Complex.log z-Complex.logTaylor 16 (z-1)‖≤1/20000 := by
 have h:=Complex.norm_log_sub_logTaylor_le 15 (lt_of_le_of_lt hz (by norm_num : (3/5:ℝ)<1))
 simp only [add_sub_cancel,Nat.reduceAdd] at h
 norm_num only [Nat.cast_ofNat] at h
 have hp:‖z-1‖^16≤(3/5:ℝ)^16:=pow_le_pow_left₀ (norm_nonneg _) hz _
 have hi:(1-‖z-1‖)⁻¹≤5/2 := by
  have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2/5) (by linarith : (2/5:ℝ)≤1-‖z-1‖)
  norm_num [one_div] at hh ⊢
  exact hh
 have hinv:0≤(1-‖z-1‖)⁻¹:=inv_nonneg.mpr (by linarith)
 calc
  _ ≤‖z-1‖^16*(1-‖z-1‖)⁻¹/16:=h
  _ ≤(3/5:ℝ)^16*(5/2)/16 := by gcongr
  _ ≤_ :=by norm_num
lemma log_taylor17_three_fifths (z : ℂ) (hz:‖z-1‖≤3/5) :
 ‖Complex.log z-Complex.logTaylor 17 (z-1)‖≤1/20000 := by
 have h:=Complex.norm_log_sub_logTaylor_le 16 (lt_of_le_of_lt hz (by norm_num : (3/5:ℝ)<1))
 simp only [add_sub_cancel,Nat.reduceAdd] at h
 norm_num only [Nat.cast_ofNat] at h
 have hp:‖z-1‖^17≤(3/5:ℝ)^17:=pow_le_pow_left₀ (norm_nonneg _) hz _
 have hi:(1-‖z-1‖)⁻¹≤5/2 := by
  have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2/5) (by linarith : (2/5:ℝ)≤1-‖z-1‖)
  norm_num [one_div] at hh ⊢
  exact hh
 have hinv:0≤(1-‖z-1‖)⁻¹:=inv_nonneg.mpr (by linarith)
 calc
  _ ≤‖z-1‖^17*(1-‖z-1‖)⁻¹/17:=h
  _ ≤(3/5:ℝ)^17*(5/2)/17 := by gcongr
  _ ≤_ :=by norm_num
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHHighContourLog
lemma power_lipschitz (z w : ℂ) (ε : ℝ) (hε:0≤ε) (hz:‖z‖≤1) (hw:‖w‖≤1)
    (he:‖z-w‖≤ε) (n : Nat) : ‖z^n-w^n‖≤(n:ℝ)*ε := by
 induction n with
 | zero => simp
 | succ n ih =>
  have hid:z^(n+1)-w^(n+1)=(z^n-w^n)*z+w^n*(z-w):=by rw[pow_succ,pow_succ];ring
  rw[hid]
  have hp:‖w^n‖≤1:=by rw[norm_pow];exact pow_le_one₀ (norm_nonneg _) hw
  have h1:‖(z^n-w^n)*z‖≤(n:ℝ)*ε:=by
   rw[norm_mul]
   exact (mul_le_mul ih hz (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h2:‖w^n*(z-w)‖≤ε:=by
   rw[norm_mul]
   exact (mul_le_mul hp he (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by push_cast;ring))
lemma polynomial_lipschitz (z w : ℂ) (ε : ℝ) (hε:0≤ε) (hz:‖z‖≤1) (hw:‖w‖≤1)
    (he:‖z-w‖≤ε) (n : Nat) :
 ‖Complex.logTaylor n z-Complex.logTaylor n w‖≤(n:ℝ)*ε := by
 unfold Complex.logTaylor
 rw [←Finset.sum_sub_distrib]
 apply (norm_sum_le _ _).trans
 calc
  _ ≤∑j∈Finset.range n,ε := by
   apply Finset.sum_le_sum
   intro j hj
   by_cases hj0:j=0
   · subst j;simp;exact hε
   · rw [←sub_div,←mul_sub,norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Complex.norm_natCast]
     have hp:=power_lipschitz z w ε hε hz hw he j
     exact (div_le_div_of_nonneg_right hp (Nat.cast_nonneg j)).trans_eq (by
      have hne:(j:ℝ)≠0:=by exact_mod_cast hj0
      field_simp)
  _ =_ :=by simp
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHHighContourLog
lemma endpoint_log_error (c v : Int×Int) (A B : ℂ)
 (hM:0< RHHighContourArithmetic.normSq c)
 (hc:(1/10000:ℝ)≤‖RHHighContourPair.value (2^80) c‖)
 (hA:‖A-RHHighContourPair.value (2^80) c‖≤1/10^12)
 (hB:‖B-RHHighContourPair.value (2^80) v‖≤1/10^12)
 (hr:‖RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1‖≤1/2) :
 ‖Complex.log (B/A)-RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v))‖≤1/10000 := by
 let q:=RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1
 let z:=B/A-1
 let w:=RHHighRoundedLog.V (RHHighContourArithmetic.ratio c v)
 have hpert:=ratio_perturbation A B _ _ hc hA hB hr
 have hround:=RHHighContourRatioProgram.ratio_error c v hM
 have hw:‖w‖≤1 := by
  have h:=norm_sub_le_norm_sub_add_norm_sub w q 0
  simp only[sub_zero] at h
  have hrev:‖w-q‖≤2/(2:ℝ)^128:=by rw[norm_sub_rev];exact hround
  exact h.trans ((add_le_add hrev hr).trans (by norm_num))
 have he:‖z-w‖≤1/10^7+2/(2:ℝ)^128 :=
  (norm_sub_le_norm_sub_add_norm_sub z q w).trans (add_le_add hpert.1 hround)
 have hz:‖z‖≤1:=hpert.2.trans (by norm_num)
 have hp:=polynomial_lipschitz z w (1/10^7+2/(2:ℝ)^128) (by positivity) hz hw he 17
 have ht:=log_taylor17_three_fifths (B/A) hpert.2
 have hn:=RHHighRoundedLog.log16_error (RHHighContourArithmetic.ratio c v) hw
 rw[norm_sub_rev] at hn
 have h1:=norm_sub_le_norm_sub_add_norm_sub (Complex.log (B/A)) (Complex.logTaylor 17 z)
  (RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v)))
 have h2:=norm_sub_le_norm_sub_add_norm_sub (Complex.logTaylor 17 z) (Complex.logTaylor 17 w)
  (RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v)))
 have hh:‖Complex.log (B/A)-RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v))‖≤
  1/20000+17*(1/10^7+2/(2:ℝ)^128)+1/10^30 := by linarith only[h1,h2,ht,hp,hn]
 exact hh.trans (by norm_num)
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourGlobal
open RHHighContourGeometry RHHighContourRecord RHHighContourLog RHHighContourArithmeticV2
lemma cell_data (R : Nat→Nat→Record)
 (hR:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (e j : Nat) (he:e<4) (hj:j< cells e) :
 (∀k:Nat,k<8 → ‖RHHighPolynomialJet.jet (point e j) (step e) k-
 RHHighContourVector.value (RHHighContourGridV2.jet (R e j).edge (R e j).index k)‖≤1/10^12) ∧
 |(point e j).im|≤1/2 := by
 refine ⟨?_,?_⟩
 · intro k hk
   rw[(hR e j he hj).1,(hR e j he hj).2]
   exact hjet e j k he hj.le hk
 · have hb:=line_box e he (j:ℝ) ⟨Nat.cast_nonneg j,by exact_mod_cast hj.le⟩
   change |(line e (j:ℝ)).im|≤1/2
   exact abs_le.mpr ⟨by linarith [hb.2.2.1],hb.2.2.2⟩
lemma boundary_lower (R : Nat→Nat→Record)
 (hR:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (z : ℂ) (hz:z∈RectangleBorder lo hi) :
 (1/10000:ℝ)≤‖RHHighFourierPolynomial.polynomial z‖ := by
 obtain ⟨e,he,t,ht,rfl⟩:=border_cover z hz
 obtain ⟨j,hj,s,hs0,hs1,hts⟩:=mesh_cover (cells e) (cells_pos e) t ht
 rw[hts,line_add]
 exact polynomial_lower (R e j) (point e j) (step e) s
  (cell_data R hR hjet e j he hj).2 (step_bound e) ⟨hs0,hs1⟩ (cell_data R hR hjet e j he hj).1
lemma cell_start_disc (R : Nat→Nat→Record)
 (hR:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (e j : Nat) (he:e<4) (hj:j< cells e) (t : ℝ) (ht:t∈uIcc (j:ℝ) ((j+1:Nat):ℝ)) :
 ‖RHHighFourierPolynomial.polynomial (line e t)-RHHighFourierPolynomial.polynomial (point e j)‖<
 ‖RHHighFourierPolynomial.polynomial (point e j)‖ := by
 rw[uIcc_of_le (by exact_mod_cast Nat.le_succ j)] at ht
 have hs:0≤ t-(j:ℝ) ∧ t-(j:ℝ)≤1:=by push_cast at ht;constructor <;> linarith [ht.1,ht.2]
 have hb:=polynomial_start_disc (R e j) (point e j) (step e) (t-(j:ℝ))
  (cell_data R hR hjet e j he hj).2 (step_bound e) hs (cell_data R hR hjet e j he hj).1
 rw[←line_add,show (j:ℝ)+(t-(j:ℝ))=t by ring] at hb
 exact hb
lemma endpoint_error (R : Nat→Nat→Record)
 (hR:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (e j : Nat) (he:e<4) (hj:j< cells e) :
 ‖Complex.log (RHHighFourierPolynomial.polynomial (point e (j+1))/RHHighFourierPolynomial.polynomial (point e j))-
 RHHighRoundedLog.V (R e j).log128‖≤1/10000 := by
 let r:=R e j
 rcases guards r with ⟨_,_,_,hM,_,_,_,_,hr,hra,hlo⟩
 have hm:=center_margin r
 have hs:(0:ℝ)≤(r.upper.sum:ℝ)/(2:ℝ)^80:=by positivity
 have hc:(1/10000:ℝ)≤‖RHHighContourVector.value (RHHighContourGridV2.jet r.edge r.index 0)‖:=by linarith
 have ha (i : Nat) (hi:i≤ cells e):
  ‖RHHighFourierPolynomial.polynomial (point e i)-RHHighContourPair.value (2^80) (RHHighContourGridV2.jet e i 0)‖≤1/10^12 := by
  have h:=hjet e i 0 he hi (by omega)
  change ‖RHHighFourierPolynomial.jet (point e i) (step e) 0-_‖≤ _ at h
  rw[RHHighFourierPolynomial.jet_zero,←value_agree] at h
  exact h
 have h:=endpoint_log_error (RHHighContourGridV2.jet r.edge r.index 0)
  (RHHighContourGridV2.jet r.edge (r.index+1) 0)
  (RHHighFourierPolynomial.polynomial (point e j)) (RHHighFourierPolynomial.polynomial (point e (j+1))) hM
  (by simpa only[value_agree] using hc)
  (by rw[(hR e j he hj).1,(hR e j he hj).2];exact ha j hj.le)
  (by rw[(hR e j he hj).1,(hR e j he hj).2];exact ha (j+1) (by omega))
  (RHHighContourGuard.ratio_small _ _ hM hr)
 rw[←hra,←hlo] at h
 exact h
end RHHighContourGlobal
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourGeometry
noncomputable def edgeIntegral (f : ℂ→ℂ) (e : Nat) : ℂ :=
 ∫t:ℝ in (0:ℝ)..(cells e:ℝ),f (line e t)*step e
lemma scale_parameter (f : ℝ→ℂ) (a c N : ℝ) (hc:c≠0) :
 (∫t:ℝ in (0:ℝ)..N,f (a+t/c)*(c:ℂ)⁻¹)=∫x:ℝ in a..(a+N/c),f x := by
 rw[intervalIntegral.integral_mul_const,intervalIntegral.integral_comp_add_div f hc]
 simp only[zero_div,add_zero,Complex.real_smul]
 have hc':(c:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hc
 field_simp
lemma horizontal_edge (f : ℂ→ℂ) (e : Nat) (he:e=0 ∨ e=2) :
 edgeIntegral f e=HIntegral f (-64) 64 (if e=0 then -1/2 else 1/2) := by
 have hdata:(∀t:ℝ,line e t=(-64+t/32:ℝ)+((if e=0 then -1/2 else 1/2):ℝ)*I) ∧
  step e=1/32 ∧ cells e=4096 := by
  rcases he with rfl|rfl <;> (constructor; intro t; norm_num [line,start,step]; ring) <;>
   norm_num [step,cells,RHHighContourGridV2.cells,RHHighContourGrid.cells]
 unfold edgeIntegral
 rw[hdata.2.1,hdata.2.2]
 have hfun:∀t:ℝ, f (line e t)*(1/32)=
  (fun x:ℝ=>f ((x:ℂ)+((if e=0 then -1/2 else 1/2):ℝ)*I)) (-64+t/32)*(32:ℂ)⁻¹ := by
  intro t
  rw[hdata.1 t]
  simp only[one_div]
 rw[intervalIntegral.integral_congr (fun t _=>hfun t)]
 have hp:=scale_parameter (fun x:ℝ=>f ((x:ℂ)+((if e=0 then -1/2 else 1/2):ℝ)*I)) (-64) 32 4096 (by norm_num)
 norm_num at hp
 simpa only[intervalIntegral.integral_mul_const,HIntegral,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat,Nat.cast_ofNat,Complex.ofReal_inv,neg_div,one_div] using hp

lemma vertical_edge (f : ℂ→ℂ) (e : Nat) (he:e=1 ∨ e=3) :
 edgeIntegral f e=VIntegral f (if e=1 then 64 else -64) (-1/2) (1/2) := by
 have hdata:(∀t:ℝ,line e t=((if e=1 then 64 else -64):ℝ)+((-1/2+t/128:ℝ):ℂ)*I) ∧
  step e=I/128 ∧ cells e=128 := by
  rcases he with rfl|rfl <;> (constructor; intro t; norm_num [line,start,step]; ring) <;>
   norm_num [step,cells,RHHighContourGridV2.cells,RHHighContourGrid.cells]
 unfold edgeIntegral
 rw[hdata.2.1,hdata.2.2]
 have hfun:∀t:ℝ,f (line e t)*(I/128)=
  I*((fun y:ℝ=>f (((if e=1 then 64 else -64):ℝ)+(y:ℂ)*I)) (-1/2+t/128)*(128:ℂ)⁻¹) := by
  intro t
  rw[hdata.1 t]
  ring
 rw[intervalIntegral.integral_congr (fun t _=>hfun t),intervalIntegral.integral_const_mul]
 have hp:=scale_parameter (fun y:ℝ=>f (((if e=1 then 64 else -64):ℝ)+(y:ℂ)*I)) (-1/2) 128 128 (by norm_num)
 norm_num at hp
 simpa only[intervalIntegral.integral_mul_const,VIntegral,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat,Nat.cast_ofNat,Complex.ofReal_inv,neg_div,one_div] using congrArg (fun u:ℂ=>I*u) hp

lemma rectangle_edges (f : ℂ→ℂ) :
 RectangleIntegral f lo hi=edgeIntegral f 0+edgeIntegral f 1-edgeIntegral f 2-edgeIntegral f 3 := by
 rw[horizontal_edge f 0 (Or.inl rfl),horizontal_edge f 2 (Or.inr rfl),
  vertical_edge f 1 (Or.inl rfl),vertical_edge f 3 (Or.inr rfl)]
 unfold RectangleIntegral
 norm_num [lo,hi]
 ring
end RHHighContourGeometry
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory Finset
namespace RHHighContourGlobal
open RHHighContourGeometry RHHighContourLog RHHighContourArithmeticV2
noncomputable def logSum (R : Nat→Nat→Record) (e : Nat) : ℂ :=
 ∑j∈range (cells e),RHHighRoundedLog.V (R e j).log128
lemma mesh_bound (R : Nat→Nat→Record)
 (hR:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (e : Nat) (he:e<4) :
 ‖edgeIntegral (logDeriv RHHighFourierPolynomial.polynomial) e-logSum R e‖≤(cells e:ℝ)/10000 := by
 let P:=RHHighFourierPolynomial.polynomial
 have hn (t : ℝ) (ht:t∈uIcc (0:ℝ) (cells e:ℝ)):P (line e t)≠0:=by
  rw[Set.uIcc_of_le (Nat.cast_nonneg _)] at ht
  have hp:=boundary_lower R hR hjet (line e t) (line_border e he t ht)
  intro hh
  change (1/10000:ℝ)≤‖P (line e t)‖ at hp
  rw[hh,norm_zero] at hp
  norm_num at hp
 have ha (t : ℝ) (ht:t∈uIcc (0:ℝ) (cells e:ℝ)):AnalyticAt ℂ (logDeriv P) (line e t):=by
  exact (RHHighFourierPolynomial.polynomial_entire.analyticAt (line e t)).deriv.div
   (RHHighFourierPolynomial.polynomial_entire.analyticAt (line e t)) (hn t ht)
 have hi:IntervalIntegrable (fun t:ℝ=> logDeriv P (line e t)*step e) volume 0 (cells e:ℝ):=by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact (((ha t ht).continuousAt.comp (f:=line e) (by unfold line;fun_prop)).mul_const (step e)).continuousWithinAt
 have hm:=mesh_integral P (start e) (step e) (cells e)
  (fun t _=> RHHighFourierPolynomial.polynomial_entire _)
  hn (fun j hj t ht=> cell_start_disc R hR hjet e j he hj t ht) hi
 exact mesh_error P (start e) (step e) (cells e) (fun j=> RHHighRoundedLog.V (R e j).log128) hm
  (fun j hj=> endpoint_error R hR hjet e j he hj)
lemma rectangle_bound (R : Nat→Nat→Record)
 (hR:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12) :
 ‖RectangleIntegral (logDeriv RHHighFourierPolynomial.polynomial) lo hi-
 (logSum R 0+logSum R 1-logSum R 2-logSum R 3)‖≤(8448:ℝ)/10000 := by
 let A:=fun e=> edgeIntegral (logDeriv RHHighFourierPolynomial.polynomial) e-logSum R e
 have h0:=mesh_bound R hR hjet 0 (by omega)
 have h1:=mesh_bound R hR hjet 1 (by omega)
 have h2:=mesh_bound R hR hjet 2 (by omega)
 have h3:=mesh_bound R hR hjet 3 (by omega)
 change ‖A 0‖≤ _ at h0
 change ‖A 1‖≤ _ at h1
 change ‖A 2‖≤ _ at h2
 change ‖A 3‖≤ _ at h3
 norm_num [cells,RHHighContourGridV2.cells,RHHighContourGrid.cells] at h0 h1 h2 h3
 have hn1:=norm_add_le (A 0) (A 1)
 have hn2:=norm_sub_le (A 0+A 1) (A 2)
 have hn3:=norm_sub_le (A 0+A 1-A 2) (A 3)
 rw[rectangle_edges]
 have hh:(edgeIntegral (logDeriv RHHighFourierPolynomial.polynomial) 0+
  edgeIntegral (logDeriv RHHighFourierPolynomial.polynomial) 1-
  edgeIntegral (logDeriv RHHighFourierPolynomial.polynomial) 2-
  edgeIntegral (logDeriv RHHighFourierPolynomial.polynomial) 3)-
  (logSum R 0+logSum R 1-logSum R 2-logSum R 3)=A 0+A 1-A 2-A 3:=by dsimp[A];ring
 rw[hh]
 linarith
end RHHighContourGlobal
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Finset
namespace RHHighContourEnumeration
open RHHighContourArithmeticV2
noncomputable def edgeOf (i : Nat) : Nat := if i<4096 then 0 else if i<4224 then 1 else if i<8320 then 2 else 3
noncomputable def offsetOf (i : Nat) : Nat := if i<4096 then i else if i<4224 then i-4096 else if i<8320 then i-4224 else i-8320
noncomputable def index (e j : Nat) : Nat := if e=0 then j else if e=1 then 4096+j else if e=2 then 4224+j else 8320+j
lemma index_bounds (e j : Nat) (he:e<4) (hj:j< RHHighContourGridV2.cells e) :
 index e j<8448 ∧ edgeOf (index e j)=e ∧ offsetOf (index e j)=j := by
 interval_cases e <;> norm_num [index,edgeOf,offsetOf,RHHighContourGridV2.cells,RHHighContourGrid.cells] at hj ⊢ <;>
  split_ifs <;> omega
lemma coordinates (rs : List Record) (d : Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=> decide (p.1.edge=edgeOf p.2 ∧ p.1.index=offsetOf p.2))=true)
 (e j : Nat) (he:e<4) (hj:j< RHHighContourGridV2.cells e) :
 let r:=(rs[index e j]?).getD d
 r.edge=e ∧ r.index=j := by
 have hb:=index_bounds e j he hj
 have hi:index e j< rs.length:=by rw[hlen];exact hb.1
 have h:=List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hc) (index e j) hi
 simp only[decide_eq_true_eq] at h
 rw[List.getElem?_eq_getElem hi,Option.getD_some]
 exact ⟨h.1.trans hb.2.1,h.2.trans hb.2.2⟩
lemma list_sum {α β : Type} [AddCommMonoid β] (rs : List α) (d : α) (N : Nat) (hlen:rs.length=N) (f : α→β) :
 (rs.map f).sum=∑i∈range N,f ((rs[i]?).getD d) := by
 have h:rs.map f=List.ofFn (fun i:Fin N=> f ((rs[i.val]?).getD d)):=by
  apply List.ext_getElem
  · simp only[List.length_map,List.length_ofFn,hlen]
  · intro i hi hi'
    have hi0:i< rs.length:=by simpa only[List.length_map] using hi
    simp only[List.getElem_map,List.getElem_ofFn,List.getElem?_eq_getElem hi0,Option.getD_some]
 rw[h,List.sum_ofFn]
 exact Fin.sum_univ_eq_sum_range (fun i:Nat=>f ((rs[i]?).getD d)) N
lemma oriented_sum (rs : List Record) (d : Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=> decide (p.1.edge=edgeOf p.2 ∧ p.1.index=offsetOf p.2))=true) :
 (rs.map (fun r=> if r.edge<2 then r.log128.2 else -r.log128.2)).sum=
 (∑j∈range 4096,((rs[index 0 j]?).getD d).log128.2)+
 (∑j∈range 128,((rs[index 1 j]?).getD d).log128.2)-
 (∑j∈range 4096,((rs[index 2 j]?).getD d).log128.2)-
 (∑j∈range 128,((rs[index 3 j]?).getD d).log128.2) := by
 let f:=fun i:Nat=> if ((rs[i]?).getD d).edge<2 then ((rs[i]?).getD d).log128.2 else -((rs[i]?).getD d).log128.2
 have hsign (e j : Nat) (he:e<4) (hj:j< RHHighContourGridV2.cells e) :
 f (index e j)=if e<2 then ((rs[index e j]?).getD d).log128.2 else -((rs[index e j]?).getD d).log128.2 := by
  dsimp[f]
  rw[(coordinates rs d hlen hc e j he hj).1]
 rw[list_sum rs d 8448 hlen]
 change (∑i∈range 8448,f i)=_
 change (∑i∈range ((4096+128)+4096+128),f i)=_
 rw[Finset.sum_range_add,Finset.sum_range_add,Finset.sum_range_add]
 have h0:(∑j∈range 4096,f j)=∑j∈range 4096,((rs[index 0 j]?).getD d).log128.2:=by
  apply Finset.sum_congr rfl
  intro j hj
  exact hsign 0 j (by omega) (by simpa [RHHighContourGridV2.cells,RHHighContourGrid.cells] using mem_range.mp hj)
 have h1:(∑j∈range 128,f (4096+j))=∑j∈range 128,((rs[index 1 j]?).getD d).log128.2:=by
  apply Finset.sum_congr rfl
  intro j hj
  exact hsign 1 j (by omega) (by simpa [RHHighContourGridV2.cells,RHHighContourGrid.cells] using mem_range.mp hj)
 have h2:(∑j∈range 4096,f (4096+128+j))= -(∑j∈range 4096,((rs[index 2 j]?).getD d).log128.2):=by
  rw[←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact hsign 2 j (by omega) (by simpa [RHHighContourGridV2.cells,RHHighContourGrid.cells] using mem_range.mp hj)
 have h3:(∑j∈range 128,f (4096+128+4096+j))= -(∑j∈range 128,((rs[index 3 j]?).getD d).log128.2):=by
  rw[←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact hsign 3 j (by omega) (by simpa [RHHighContourGridV2.cells,RHHighContourGrid.cells] using mem_range.mp hj)
 rw[h0,h1,h2,h3]
 ring
end RHHighContourEnumeration
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighContourNative
open RHHighContourGlobal RHHighContourGeometry RHHighContourEnumeration RHHighContourArithmeticV2
lemma value_im (p : Int×Int) : (RHHighRoundedLog.V p).im=(p.2:ℝ)/(2:ℝ)^128 := by
 unfold RHHighRoundedLog.V RHHighDyadicComplex.value
 have hd:((2^128:Nat):ℂ)=(((2:ℝ)^128:ℝ):ℂ):=by norm_num
 rw[hd,Complex.div_ofReal_im]
 simp only[Complex.add_im,Complex.mul_im,Complex.intCast_im,Complex.intCast_re,
  Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero]

lemma sum_im (rs : List Record) (d : Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=> decide (p.1.edge=edgeOf p.2 ∧ p.1.index=offsetOf p.2))=true) :
 let R:=fun e j:Nat=>(rs[index e j]?).getD d
 (logSum R 0+logSum R 1-logSum R 2-logSum R 3).im=
 (((rs.map (fun r=> if r.edge<2 then r.log128.2 else -r.log128.2)).sum:Int):ℝ)/(2:ℝ)^128 := by
 let R:=fun e j:Nat=>(rs[index e j]?).getD d
 have h:=congrArg (fun n:Int=>(n:ℝ)/(2:ℝ)^128) (oriented_sum rs d hlen hc)
 push_cast at h
 simp only[add_div,sub_div,Finset.sum_div] at h
 simp only[logSum,Complex.add_im,Complex.sub_im,Complex.im_sum,value_im]
 have hc0:cells 0=4096:=by decide +kernel
 have hc1:cells 1=128:=by decide +kernel
 have hc2:cells 2=4096:=by decide +kernel
 have hc3:cells 3=128:=by decide +kernel
 simp only[hc0,hc1,hc2,hc3]
 simpa only[Int.cast_list_sum] using h.symm
lemma integral_bound (rs : List Record) (d : Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=> decide (p.1.edge=edgeOf p.2 ∧ p.1.index=offsetOf p.2))=true)
 (hs:(rs.map (fun r=> if r.edge<2 then r.log128.2 else -r.log128.2)).sum≤2571*(2:Int)^128)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12) :
 (RectangleIntegral (logDeriv RHHighFourierPolynomial.polynomial) lo hi).im≤2571+(8448:ℝ)/10000 := by
 let R:=fun e j:Nat=>(rs[index e j]?).getD d
 have hr:∀e j:Nat,e<4 → j< cells e → (R e j).edge=e ∧ (R e j).index=j:=by
  intro e j he hj
  exact coordinates rs d hlen hc e j he hj
 have he:=rectangle_bound R hr hjet
 have him:=Complex.im_le_norm (RectangleIntegral (logDeriv RHHighFourierPolynomial.polynomial) lo hi-
  (logSum R 0+logSum R 1-logSum R 2-logSum R 3))
 have hsum:=sum_im rs d hlen hc
 have hSr:(((rs.map (fun r=> if r.edge<2 then r.log128.2 else -r.log128.2)).sum:Int):ℝ)≤2571*(2:ℝ)^128:=by exact_mod_cast hs
 have hdiv:(((rs.map (fun r=> if r.edge<2 then r.log128.2 else -r.log128.2)).sum:Int):ℝ)/(2:ℝ)^128≤2571:=by
  exact (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).mpr hSr
 change (logSum R 0+logSum R 1-logSum R 2-logSum R 3).im=_ at hsum
 rw[Complex.sub_im] at him
 rw[hsum] at him
 linarith
end RHHighContourNative
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma segment_primitive (H f : ℂ→ℂ) (z v : ℂ) (a b : ℝ)
 (hf:∀t∈Set.uIcc a b,HasDerivAt H (f (z+(t:ℂ)*v)) (z+(t:ℂ)*v))
 (hi:IntervalIntegrable (fun t:ℝ=>f (z+(t:ℂ)*v)*v) volume a b) :
 (∫t:ℝ in a..b,f (z+(t:ℂ)*v)*v)=H (z+(b:ℂ)*v)-H (z+(a:ℂ)*v) := by
 apply intervalIntegral.integral_eq_sub_of_hasDerivAt
 · intro t ht
   have ha:HasDerivAt (fun u:ℝ=>z+(u:ℂ)*v) v t := by
    simpa only[Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
     ((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const v).const_add z
   exact (hf t ht).comp t ha
 · exact hi
lemma primitive_rectangle (H f : ℂ→ℂ) (z w : ℂ)
 (hF:∀s∈RectangleBorder z w,HasDerivAt H (f s) s)
 (hi:RectangleBorderIntegrable f z w) : RectangleIntegral f z w=0 := by
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
  have hbottom := segment_primitive H f ((z.im:ℂ)*I) 1 z.re w.re
    (fun x hx => by simpa only[mul_one,add_comm] using hF _ (hb x hx))
    (by simpa only[mul_one,add_comm] using hi.1)
  have htop := segment_primitive H f ((w.im:ℂ)*I) 1 z.re w.re
    (fun x hx => by simpa only[mul_one,add_comm] using hF _ (ht x hx))
    (by simpa only[mul_one,add_comm] using hi.2.1)
  have hright := segment_primitive H f (w.re:ℂ) I z.im w.im
    (fun y hy => hF _ (hr y hy)) (hi.2.2.1.mul_const I)
  have hleft := segment_primitive H f (z.re:ℂ) I z.im w.im
    (fun y hy => hF _ (hl y hy)) (hi.2.2.2.mul_const I)
  simp only[mul_one] at hbottom htop hright hleft
  unfold RectangleIntegral HIntegral VIntegral
  simp only [smul_eq_mul]
  rw [show I*(∫ y:ℝ in z.im..w.im,f ((w.re:ℂ)+(y:ℂ)*I))=
    ∫ y:ℝ in z.im..w.im,f ((w.re:ℂ)+(y:ℂ)*I)*I by
      rw [intervalIntegral.integral_mul_const];ring,
    show I*(∫ y:ℝ in z.im..w.im,f ((z.re:ℂ)+(y:ℂ)*I))=
    ∫ y:ℝ in z.im..w.im,f ((z.re:ℂ)+(y:ℂ)*I)*I by
      rw [intervalIntegral.integral_mul_const];ring]
  rw [show (fun x:ℝ => f ((x:ℂ)+(z.im:ℂ)*I))=
      (fun x:ℝ => f ((z.im:ℂ)*I+(x:ℂ))) by funext x;rw [add_comm],hbottom,
    show (fun x:ℝ => f ((x:ℂ)+(w.im:ℂ)*I))=
      (fun x:ℝ => f ((w.im:ℂ)*I+(x:ℂ))) by funext x;rw [add_comm],htop,hright,hleft]
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
lemma rectangle_sub (f g : ℂ→ℂ) (z w : ℂ)
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (fun s => f s-g s) z w=RectangleIntegral f z w-RectangleIntegral g z w := by
  unfold RectangleIntegral HIntegral VIntegral
  rw [intervalIntegral.integral_sub hf.1 hg.1,
    intervalIntegral.integral_sub hf.2.1 hg.2.1,
    intervalIntegral.integral_sub hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_sub hf.2.2.2 hg.2.2.2]
  simp only [smul_eq_mul]
  ring
lemma rectangle_congr (f g : ℂ→ℂ) (z w : ℂ)
    (h:∀ s∈RectangleBorder z w,f s=g s) : RectangleIntegral f z w=RectangleIntegral g z w := by
  have hh (x y : ℝ) (hx:x∈Set.uIcc z.re w.re) (hy:y=z.im ∨ y=w.im) : f ((x:ℂ)+(y:ℂ)*I)=g ((x:ℂ)+(y:ℂ)*I) := by
    apply h
    simp only [RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
    rcases hy with rfl|rfl
    · exact Or.inl (Or.inl (Or.inl ⟨by simpa using hx,by simp⟩))
    · exact Or.inl (Or.inr ⟨by simpa using hx,by simp⟩)
  have hv (x y : ℝ) (hx:x=z.re ∨ x=w.re) (hy:y∈Set.uIcc z.im w.im) : f ((x:ℂ)+(y:ℂ)*I)=g ((x:ℂ)+(y:ℂ)*I) := by
    apply h
    simp only [RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
    rcases hx with rfl|rfl
    · exact Or.inl (Or.inl (Or.inr ⟨by simp,by simpa using hy⟩))
    · exact Or.inr ⟨by simp,by simpa using hy⟩
  unfold RectangleIntegral HIntegral VIntegral
  rw [intervalIntegral.integral_congr (fun x hx => hh x z.im hx (Or.inl rfl)),
    intervalIntegral.integral_congr (fun x hx => hh x w.im hx (Or.inr rfl)),
    intervalIntegral.integral_congr (fun y hy => hv w.re y (Or.inr rfl) hy),
    intervalIntegral.integral_congr (fun y hy => hv z.re y (Or.inl rfl) hy)]
lemma rectangle_ratio_compare (F G : ℂ→ℂ) (z w : ℂ)
    (hF : ∀ s∈RectangleBorder z w,DifferentiableAt ℂ F s)
    (hG : ∀ s∈RectangleBorder z w,DifferentiableAt ℂ G s)
    (hn : ∀ s∈RectangleBorder z w,G s≠0)
    (he : ∀ s∈RectangleBorder z w,‖F s-G s‖<‖G s‖)
    (hiF : RectangleBorderIntegrable (logDeriv F) z w)
    (hiG : RectangleBorderIntegrable (logDeriv G) z w)
    (hiR : RectangleBorderIntegrable (logDeriv (fun s => F s/G s)) z w) :
    RectangleIntegral (logDeriv F) z w=RectangleIntegral (logDeriv G) z w := by
  have hz := halfplane_rectangle (fun s => F s/G s) z w
    (fun s hs => (hF s hs).div (hG s hs) (hn s hs))
    (fun s hs => disk_half_plane _ _ (hn s hs) (he s hs)) hiR
  rw [rectangle_congr _ (fun s => logDeriv F s-logDeriv G s) z w
    (fun s hs => logDeriv_ratio F G s (hF s hs) (hG s hs) (hn s hs) (he s hs)),
    rectangle_sub _ _ z w hiF hiG] at hz
  exact sub_eq_zero.mp hz
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma rectangle_add (f g : ℂ→ℂ) (z w : ℂ)
 (hf:RectangleBorderIntegrable f z w) (hg:RectangleBorderIntegrable g z w) :
 RectangleIntegral (fun s=>f s+g s) z w=RectangleIntegral f z w+RectangleIntegral g z w := by
 unfold RectangleIntegral HIntegral VIntegral
 rw[intervalIntegral.integral_add hf.1 hg.1,
  intervalIntegral.integral_add hf.2.1 hg.2.1,
  intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
  intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
 simp only[smul_eq_mul]
 ring
lemma product_integral (F G : ℂ→ℂ) (z w : ℂ)
 (hF:∀s∈RectangleBorder z w,DifferentiableAt ℂ F s)
 (hG:∀s∈RectangleBorder z w,DifferentiableAt ℂ G s)
 (hFn:∀s∈RectangleBorder z w,F s≠0) (hGn:∀s∈RectangleBorder z w,G s≠0)
 (hiF:RectangleBorderIntegrable (logDeriv F) z w) (hiG:RectangleBorderIntegrable (logDeriv G) z w) :
 RectangleIntegral (logDeriv (fun s=>F s*G s)) z w=
  RectangleIntegral (logDeriv F) z w+RectangleIntegral (logDeriv G) z w := by
 rw[rectangle_congr _ (fun s=>logDeriv F s+logDeriv G s) z w
  (by intro s hs;exact logDeriv_mul s (hFn s hs) (hGn s hs) (hF s hs) (hG s hs))]
 exact rectangle_add _ _ z w hiF hiG
lemma logDeriv_exp (H : ℂ→ℂ) (g : ℂ) (s : ℂ) (h:HasDerivAt H g s) :
 logDeriv (fun x=>Complex.exp (H x)) s=g := by
 have hd:=(Complex.hasDerivAt_exp (H s)).comp s h
 change HasDerivAt (fun x=>Complex.exp (H x)) (Complex.exp (H s)*g) s at hd
 rw[logDeriv_apply,hd.deriv]
 field_simp[Complex.exp_ne_zero]
lemma exponential_rectangle (H g : ℂ→ℂ) (z w : ℂ)
 (hH:∀s∈RectangleBorder z w,HasDerivAt H (g s) s)
 (hi:RectangleBorderIntegrable g z w) :
 RectangleIntegral (logDeriv (fun s=>Complex.exp (H s))) z w=0 := by
 rw[rectangle_congr _ g z w (by intro s hs;exact logDeriv_exp H (g s) s (hH s hs))]
 exact primitive_rectangle H g z w hH hi
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Set
namespace RHHighEntireCorrection
noncomputable def sline (T : ℝ) (z : ℂ) : ℂ := 1/2+I*(z+(T:ℂ))
noncomputable def window (T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi:ℂ)*(z+(T:ℂ))/4-z^2/800)
noncomputable def damping (T : ℝ) (z : ℂ) : ℂ := Complex.exp (-(z+(T:ℂ))^2/2)
noncomputable def pole0 (T : ℝ) : ℂ := -(T:ℂ)+I/2
noncomputable def pole1 (T : ℝ) : ℂ := -(T:ℂ)-I/2
noncomputable def residue (T : ℝ) (p : ℂ) : ℂ := window T p/damping T p
noncomputable def numerator (T : ℝ) (p z : ℂ) : ℂ :=
  window T z-residue T p*damping T z
noncomputable def corrected (T : ℝ) (z : ℂ) : ℂ :=
  completedRiemannZeta₀ (sline T z)*window T z+
    I*dslope (numerator T (pole0 T)) (pole0 T) z-
      I*dslope (numerator T (pole1 T)) (pole1 T) z
lemma numerator_at_pole (T : ℝ) (p : ℂ) : numerator T p p=0 := by
  unfold numerator residue
  field_simp [damping,Complex.exp_ne_zero]
  ring
lemma numerator_differentiable (T : ℝ) (p : ℂ) : Differentiable ℂ (numerator T p) := by
  unfold numerator window damping
  fun_prop
lemma corrected_entire (T : ℝ) : Differentiable ℂ (corrected T) := by
  have hd (p : ℂ) : Differentiable ℂ (dslope (numerator T p) p) := by
    rw [←differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
      (numerator_differentiable T p).differentiableOn
  unfold corrected
  apply Differentiable.sub
  · apply Differentiable.add
    · exact (differentiable_completedZeta₀.comp (by unfold sline;fun_prop)).mul
        (by unfold window;fun_prop)
    · exact (hd (pole0 T)).const_mul I
  · exact (hd (pole1 T)).const_mul I
lemma sline_poles (T : ℝ) (z : ℂ) :
    sline T z=I*(z-pole0 T) ∧ 1-sline T z= -I*(z-pole1 T) := by
  unfold sline pole0 pole1
  constructor <;> calc
    _ = _ := by ring_nf;simp only [I_sq];ring
lemma corrected_eq (T : ℝ) (z : ℂ) (hz0 : z≠pole0 T) (hz1 : z≠pole1 T) :
    corrected T z=completedRiemannZeta (sline T z)*window T z+
      damping T z*(residue T (pole0 T)/sline T z+residue T (pole1 T)/(1-sline T z)) := by
  have hs0 : sline T z≠0 := by rw [(sline_poles T z).1];exact mul_ne_zero I_ne_zero (sub_ne_zero.mpr hz0)
  have hs1 : 1-sline T z≠0 := by rw [(sline_poles T z).2];exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (sub_ne_zero.mpr hz1)
  unfold corrected
  rw [dslope_of_ne _ hz0,dslope_of_ne _ hz1]
  simp only [slope,numerator_at_pole,vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [completedRiemannZeta_eq]
  unfold numerator
  rw [(sline_poles T z).2,(sline_poles T z).1]
  field_simp [sub_ne_zero.mpr hz0,sub_ne_zero.mpr hz1]
  ring_nf
  simp [I_sq]
  ring
lemma residue_norm (T : ℝ) (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    ‖residue T (-(T:ℂ)+(ε:ℂ)*I/2)‖=
      Real.exp (-T^2/800+1/3200-1/8) := by
  rw [residue,norm_div]
  unfold window damping
  rw [Complex.norm_exp,Complex.norm_exp,←Real.exp_sub]
  rcases hε with rfl|rfl
  all_goals congr 1
  all_goals simp [pow_two,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,
    Complex.normSq]
  all_goals ring
end RHHighEntireCorrection
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighXiWindow
open RHHighEntireCorrection
noncomputable def xi (s : ℂ) : ℂ := s*(s-1)*completedRiemannZeta₀ s+1
noncomputable def normalized (T : ℝ) (z : ℂ) : ℂ :=
  -(xi (sline T z)*window T z)/(T:ℂ)^2
lemma xi_entire : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1)
lemma normalized_entire (T : ℝ) : Differentiable ℂ (normalized T) := by
  unfold normalized
  exact (((xi_entire.comp (by unfold sline;fun_prop)).mul
    (by unfold window;fun_prop)).neg).div_const _
lemma xi_eq (s : ℂ) (hs0 : s≠0) (hs1 : s≠1) :
    xi s=s*(s-1)*completedRiemannZeta s := by
  have hh : 1-s≠0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [completedRiemannZeta_eq]
  unfold xi
  field_simp [hs0,hh]
  ring
lemma normalized_eq (T : ℝ) (z : ℂ) (hs0 : sline T z≠0) (hs1 : sline T z≠1) :
    normalized T z=(-sline T z*(sline T z-1)/(T:ℂ)^2)*
      (completedRiemannZeta (sline T z)*window T z) := by
  unfold normalized
  rw [xi_eq _ hs0 hs1]
  ring
lemma real_factor (T t : ℝ) :
    -sline T (t:ℂ)*(sline T (t:ℂ)-1)/(T:ℂ)^2=
      (((T+t)^2+1/4)/T^2:ℝ) := by
  unfold sline
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring
lemma real_normalized (T t : ℝ) :
    normalized T (t:ℂ)=((((T+t)^2+1/4)/T^2:ℝ):ℂ)*
      (completedRiemannZeta (sline T (t:ℂ))*window T (t:ℂ)) := by
  have hr : (sline T (t:ℂ)).re=1/2 := by simp [sline]
  have hs0 : sline T (t:ℂ)≠0 := by intro h;rw [h] at hr;norm_num at hr
  have hs1 : sline T (t:ℂ)≠1 := by intro h;rw [h] at hr;norm_num at hr
  rw [normalized_eq T (t:ℂ) hs0 hs1,real_factor]
lemma normalized_zero_iff (T : ℝ) (z : ℂ) (hT : T≠0)
    (hs0 : sline T z≠0) (hs1 : sline T z≠1) :
    normalized T z=0 ↔ completedRiemannZeta (sline T z)=0 := by
  rw [normalized_eq T z hs0 hs1,mul_eq_zero]
  have hT' : (T:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hf : -sline T z*(sline T z-1)/(T:ℂ)^2≠0 :=
    div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs0) (sub_ne_zero.mpr hs1)) (pow_ne_zero _ hT')
  have hw : window T z≠0 := Complex.exp_ne_zero _
  simp only [hf,false_or,mul_eq_zero,hw,or_false]
end RHHighXiWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighXiWindow
noncomputable def q (T : ℝ) (z : ℂ) : ℂ := ((T+z)^2+1/4)/(T:ℂ)^2
lemma q_entire (T : ℝ) : Differentiable ℂ (q T) := by unfold q;fun_prop
lemma q_real (T t : ℝ) : q T (t:ℂ)=((((T+t)^2+1/4)/T^2:ℝ):ℂ) := by unfold q;push_cast;rfl
lemma q_positive (T : ℝ) (z : ℂ) (hT:65≤T) (hx:|z.re|≤64) (hy:|z.im|≤1/2) : 0 < (q T z).re := by
  have ht:0<T := by linarith
  have htr:0<T+z.re := by have h:=abs_le.mp hx;linarith
  have hys:z.im^2≤1/4 := by
    have h:=pow_le_pow_left₀ (abs_nonneg z.im) hy 2
    norm_num only [sq_abs] at h
    exact h
  have he:(q T z).re=((T+z.re)^2-z.im^2+1/4)/T^2 := by
    unfold q
    simp [Complex.div_re,Complex.normSq,pow_two]
    field_simp
  rw [he]
  exact div_pos (by nlinarith [sq_pos_of_pos htr]) (sq_pos_of_pos ht)
lemma q_nonzero (T : ℝ) (z : ℂ) (hT:65≤T) (hx:|z.re|≤64) (hy:|z.im|≤1/2) : q T z≠0 := by
  intro h
  have hp:=q_positive T z hT hx hy
  simpa only [h,zero_re,lt_self_iff_false] using hp
lemma q_factor (T : ℝ) (z : ℂ) :
    -RHHighEntireCorrection.sline T z*(RHHighEntireCorrection.sline T z-1)/(T:ℂ)^2=q T z := by
  unfold RHHighEntireCorrection.sline q
  congr 1
  ring_nf
  simp only [I_sq]
  ring
end RHHighXiWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighXiWindow
lemma q_norm_lower (T : ℝ) (z : ℂ) (hT:256≤T) (hx:|z.re|≤64) (hy:|z.im|≤1/2) :
 (1/2:ℝ)≤‖q T z‖ := by
 have ht:0<T:=by linarith
 have he:(q T z).re=((T+z.re)^2-z.im^2+1/4)/T^2 := by
  unfold q
  simp [Complex.div_re,Complex.normSq,pow_two]
  field_simp
 have hx':3*T/4≤T+z.re:=by have hh:=abs_le.mp hx;linarith
 have hsq: (3*T/4)^2≤(T+z.re)^2 := pow_le_pow_left₀ (by positivity) hx' 2
 have hys:z.im^2≤1/4 := by
  have h:=pow_le_pow_left₀ (abs_nonneg z.im) hy 2
  norm_num only [sq_abs] at h
  linarith only [h]
 have hr:(1/2:ℝ)≤(q T z).re := by
  rw[he]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith only [hsq,hys,sq_nonneg T]
 exact hr.trans (Complex.re_le_norm _)
end RHHighXiWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighXiContour
open RHHighContourGeometry RHHighContourLog RHHighXiWindow
lemma border_box (z : ℂ) (hz:z∈RectangleBorder lo hi) : |z.re|≤64 ∧ |z.im|≤1/2 := by
 obtain ⟨e,he,t,ht,rfl⟩:=border_cover z hz
 have h:=line_box e he t ht
 exact ⟨abs_le.mpr ⟨h.1,h.2.1⟩,abs_le.mpr ⟨by linarith [h.2.2.1],h.2.2.2⟩⟩
lemma compare (T : ℝ) (hT:256≤ T)
 (hP:∀z∈RectangleBorder lo hi,(1/10000:ℝ)≤‖RHHighFourierPolynomial.polynomial z‖)
 (he:∀z∈RectangleBorder lo hi,‖normalized T z-q T z*RHHighFourierPolynomial.polynomial z‖≤1/100000) :
 (∀z∈RectangleBorder lo hi,normalized T z≠0) ∧
 RectangleIntegral (logDeriv (normalized T)) lo hi=
 RectangleIntegral (logDeriv RHHighFourierPolynomial.polynomial) lo hi := by
 let P:=RHHighFourierPolynomial.polynomial
 let F:=normalized T
 let Q:=q T
 let G:=fun z=> Q z*P z
 have hQa (z : ℂ):AnalyticAt ℂ Q z:=(q_entire T).analyticAt z
 have hPa (z : ℂ):AnalyticAt ℂ P z:=RHHighFourierPolynomial.polynomial_entire.analyticAt z
 have hFa (z : ℂ):AnalyticAt ℂ F z:=(normalized_entire T).analyticAt z
 have hGa (z : ℂ):AnalyticAt ℂ G z:=(hQa z).mul (hPa z)
 have hQn (z : ℂ) (hz:z∈RectangleBorder lo hi):Q z≠0:=by
  have hb:=border_box z hz
  exact q_nonzero T z (by linarith) hb.1 hb.2
 have hPn (z : ℂ) (hz:z∈RectangleBorder lo hi):P z≠0:=by
  have hp:=hP z hz
  intro hh
  change (1/10000:ℝ)≤‖P z‖ at hp
  rw[hh,norm_zero] at hp
  norm_num at hp
 have hGn (z : ℂ) (hz:z∈RectangleBorder lo hi):G z≠0:=mul_ne_zero (hQn z hz) (hPn z hz)
 have hstrict (z : ℂ) (hz:z∈RectangleBorder lo hi):‖F z-G z‖<‖G z‖:=by
  have hb:=border_box z hz
  have hq:=q_norm_lower T z hT hb.1 hb.2
  have hp:=hP z hz
  calc
   _ ≤ 1/100000 := he z hz
   _ < (1/2:ℝ)*(1/10000) := by norm_num
   _ ≤ _ := by
    change _≤‖Q z*P z‖
    rw[norm_mul]
    exact mul_le_mul hq hp (by positivity) (norm_nonneg _)
 have hFn (z : ℂ) (hz:z∈RectangleBorder lo hi):F z≠0:=by
  intro hh
  have hs:=hstrict z hz
  rw[hh,zero_sub,norm_neg] at hs
  exact (lt_irrefl _) hs
 refine ⟨hFn,?_⟩
 have hraw:=rectangle_ratio_compare F G lo hi
  (fun z _=>(hFa z).differentiableAt) (fun z _=>(hGa z).differentiableAt) hGn hstrict
  (logDeriv_border_integrable F lo hi (fun z _=> hFa z) hFn)
  (logDeriv_border_integrable G lo hi (fun z _=> hGa z) hGn)
  (logDeriv_border_integrable (fun z=> F z/G z) lo hi
   (fun z hz=>(hFa z).div (hGa z) (hGn z hz))
   (fun z hz=> div_ne_zero (hFn z hz) (hGn z hz)))
 have hprod:=product_integral Q P lo hi
  (fun z _=>(hQa z).differentiableAt) (fun z _=>(hPa z).differentiableAt) hQn hPn
  (logDeriv_border_integrable Q lo hi (fun z _=> hQa z) hQn)
  (logDeriv_border_integrable P lo hi (fun z _=> hPa z) hPn)
 have hqzero:=halfplane_rectangle Q lo hi (fun z _=>(hQa z).differentiableAt)
  (fun z hz=> q_positive T z (by linarith) (border_box z hz).1 (border_box z hz).2)
  (logDeriv_border_integrable Q lo hi (fun z _=> hQa z) hQn)
 exact hraw.trans (hprod.trans (by rw[hqzero,zero_add]))
end RHHighXiContour
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourRotation
open RHHighEntireCorrection
lemma horizontal (g : ℂ→ℂ) (T y : ℝ) :
 HIntegral (fun z=> g (sline T z)*I) (-64) 64 y=
 VIntegral g (1/2-y) (T-64) (T+64) := by
 have hz (x : ℝ):sline T ((x:ℂ)+(y:ℂ)*I)=(1/2-y:ℝ)+(T+x:ℝ)*I := by
  unfold sline
  push_cast
  ring_nf
  simp only[I_sq]
  ring
 unfold HIntegral VIntegral
 simp_rw[hz]
 rw[intervalIntegral.integral_mul_const,intervalIntegral.integral_comp_add_left (fun v:ℝ=>g ((1/2-y:ℝ)+(v:ℂ)*I)) T]
 norm_num only[Complex.real_smul,smul_eq_mul]
 rw[show T+(-64)=T-64 by ring]
 ring
lemma vertical (g : ℂ→ℂ) (T x : ℝ) :
 VIntegral (fun z=> g (sline T z)*I) x (-1/2) (1/2)=
 -HIntegral g 0 1 (T+x) := by
 have hz (y : ℝ):sline T ((x:ℂ)+(y:ℂ)*I)=(1/2-y:ℝ)+(T+x:ℝ)*I := by
  unfold sline
  push_cast
  ring_nf
  simp only[I_sq]
  ring
 unfold HIntegral VIntegral
 simp_rw[hz]
 rw[intervalIntegral.integral_mul_const,intervalIntegral.integral_comp_sub_left (fun v:ℝ=>g ((v:ℂ)+(T+x:ℝ)*I)) (1/2)]
 norm_num only[show (1/2:ℝ)-1/2=0 by ring,show (1/2:ℝ)-(-1/2)=1 by ring,smul_eq_mul]
 calc
  _ = (I*I)*(∫y:ℝ in (0:ℝ)..1,g ((y:ℂ)+(T+x:ℝ)*I)) := by ring
  _ = _ := by rw[I_mul_I,neg_one_mul]
lemma rectangle (g : ℂ→ℂ) (T : ℝ) :
 RectangleIntegral (fun z=> g (sline T z)*I) RHHighContourGeometry.lo RHHighContourGeometry.hi=
 RectangleIntegral g ((T-64:ℝ)*I) (1+(T+64:ℝ)*I) := by
 unfold RectangleIntegral
 norm_num [RHHighContourGeometry.lo,RHHighContourGeometry.hi]
 have hv1:=vertical g T 64
 have hv0:=vertical g T (-64)
 norm_num at hv1 hv0
 rw[horizontal,horizontal,hv1,hv0]
 norm_num
 ring
end RHHighContourRotation
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Complex Set Filter MeasureTheory Topology
namespace RHHighXiContour
open RHHighContourGeometry RHHighContourLog RHHighXiWindow RHHighEntireCorrection
lemma analyticAt_completedRiemannZeta {s : ℂ} (h0:s≠0) (h1:s≠1) : AnalyticAt ℂ completedRiemannZeta s := by
 have hopen:IsOpen (({0,1}:Set ℂ)ᶜ):=(Set.toFinite _).isClosed.isOpen_compl
 have hdiff:DifferentiableOn ℂ completedRiemannZeta (({0,1}:Set ℂ)ᶜ):=by
  intro z hz
  simp only[mem_compl_iff,mem_insert_iff,mem_singleton_iff,not_or] at hz
  exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
 exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0,h1]))
lemma sline_im (T : ℝ) (z : ℂ) : (sline T z).im=T+z.re := by simp [sline];ring
lemma sline_regular (T : ℝ) (hT:256≤ T) (z : ℂ) (hz:z∈RectangleBorder lo hi) :
 sline T z≠0 ∧ sline T z≠1 := by
 have hp:0<(sline T z).im:=by rw[sline_im];have hb:=abs_le.mp (border_box z hz).1;linarith
 constructor <;> intro h <;> simp [h] at hp
lemma factor_near (T : ℝ) (z : ℂ) (h0:sline T z≠0) (h1:sline T z≠1) :
 normalized T =ᶠ[𝓝 z] (fun u=> q T u*(completedRiemannZeta (sline T u)*window T u)) := by
 have hs:ContinuousAt (sline T) z:=by unfold sline;fun_prop
 filter_upwards[hs.eventually_ne h0,hs.eventually_ne h1] with u hu0 hu1
 rw[normalized_eq T u hu0 hu1,q_factor]
lemma window_derivative (T : ℝ) (z : ℂ) :
 HasDerivAt (fun u:ℂ=>(Real.pi:ℂ)*(u+(T:ℂ))/4-u^2/800) ((Real.pi:ℂ)/4-z/400) z := by
 have h1:=(((hasDerivAt_id z).add_const (T:ℂ)).const_mul (Real.pi:ℂ)).div_const 4
 have h2:=(hasDerivAt_pow 2 z).div_const 800
 have hd:=h1.sub h2
 have he:(Real.pi:ℂ)/4-z/400=(Real.pi:ℂ)*1/4-(2:ℂ)*z^(2-1)/800:=by norm_num;ring
 rw[he]
 exact hd
lemma window_integral (T : ℝ) : RectangleIntegral (logDeriv (window T)) lo hi=0 := by
 apply exponential_rectangle (fun u:ℂ=>(Real.pi:ℂ)*(u+(T:ℂ))/4-u^2/800)
  (fun u:ℂ=>(Real.pi:ℂ)/4-u/400) lo hi
 · intro z _;exact window_derivative T z
 · apply border_continuous_integrable
   intro z _
   fun_prop
lemma completed_integral (T : ℝ) (hT:256≤ T)
 (hn:∀z∈RectangleBorder lo hi,normalized T z≠0) :
 RectangleIntegral (logDeriv completedRiemannZeta) ((T-64:ℝ)*I) (1+(T+64:ℝ)*I)=
 RectangleIntegral (logDeriv (normalized T)) lo hi := by
 let Q:=q T
 let A:=fun z=> completedRiemannZeta (sline T z)
 let W:=window T
 have hQa (z : ℂ):AnalyticAt ℂ Q z:=(q_entire T).analyticAt z
 have hAa (z : ℂ) (hz:z∈RectangleBorder lo hi):AnalyticAt ℂ A z:=by
  exact (analyticAt_completedRiemannZeta (sline_regular T hT z hz).1 (sline_regular T hT z hz).2).comp
   (by unfold sline;fun_prop)
 have hWa (z : ℂ):AnalyticAt ℂ W z:=by
  apply Differentiable.analyticAt (z:=z)
  unfold W window
  fun_prop
 have hQn (z : ℂ) (hz:z∈RectangleBorder lo hi):Q z≠0:=by
  exact q_nonzero T z (by linarith) (border_box z hz).1 (border_box z hz).2
 have hAn (z : ℂ) (hz:z∈RectangleBorder lo hi):A z≠0:=by
  intro h
  have hp:=hn z hz
  apply hp
  exact (normalized_zero_iff T z (by linarith) (sline_regular T hT z hz).1 (sline_regular T hT z hz).2).mpr h
 have hWn (z : ℂ):W z≠0:=Complex.exp_ne_zero _
 have hqi:=logDeriv_border_integrable Q lo hi (fun z _=> hQa z) hQn
 have hai:=logDeriv_border_integrable A lo hi hAa hAn
 have hwi:=logDeriv_border_integrable W lo hi (fun z _=> hWa z) (fun z _=> hWn z)
 have hawi:=logDeriv_border_integrable (fun z=> A z*W z) lo hi
  (fun z hz=>(hAa z hz).mul (hWa z)) (fun z hz=> mul_ne_zero (hAn z hz) (hWn z))
 have hprod1:=product_integral Q (fun z=> A z*W z) lo hi
  (fun z _=>(hQa z).differentiableAt) (fun z hz=>((hAa z hz).mul (hWa z)).differentiableAt)
  hQn (fun z hz=> mul_ne_zero (hAn z hz) (hWn z)) hqi hawi
 have hprod2:=product_integral A W lo hi (fun z hz=>(hAa z hz).differentiableAt)
  (fun z _=>(hWa z).differentiableAt) hAn (fun z _=> hWn z) hai hwi
 have hqzero:=halfplane_rectangle Q lo hi (fun z _=>(hQa z).differentiableAt)
  (fun z hz=> q_positive T z (by linarith) (border_box z hz).1 (border_box z hz).2) hqi
 have heq:RectangleIntegral (logDeriv (normalized T)) lo hi=RectangleIntegral (logDeriv A) lo hi := by
  rw[rectangle_congr _ (logDeriv (fun z=> Q z*(A z*W z))) lo hi
   (by intro z hz;exact (logDeriv_congr_nhds (factor_near T z (sline_regular T hT z hz).1 (sline_regular T hT z hz).2)).self_of_nhds)]
  rw[hprod1,hprod2,hqzero,window_integral,zero_add,add_zero]
 rw[heq]
 have hc:RectangleIntegral (logDeriv A) lo hi=
  RectangleIntegral (fun z=> logDeriv completedRiemannZeta (sline T z)*I) lo hi:=by
  apply rectangle_congr
  intro z hz
  have hsd:HasDerivAt (sline T) I z:=by
   have hh:=(((hasDerivAt_id z).add_const (T:ℂ)).const_mul I).const_add (1/2)
   change HasDerivAt (sline T) (I*1) z at hh
   simpa only[mul_one] using hh
  change logDeriv (completedRiemannZeta ∘ sline T) z=_
  rw[logDeriv_comp (analyticAt_completedRiemannZeta (sline_regular T hT z hz).1 (sline_regular T hT z hz).2).differentiableAt hsd.differentiableAt,hsd.deriv]
 exact (hc.trans (RHHighContourRotation.rectangle _ T)).symm
lemma good_heights (T : ℝ) (hT:256≤ T)
 (hn:∀z∈RectangleBorder lo hi,normalized T z≠0)
 (ρ : ℂ) (hρ:Zeta23.IsNontrivialZero ρ) : ρ.im≠T-64 ∧ ρ.im≠T+64 := by
 let z:ℂ:=(ρ.im-T:ℝ)+(1/2-ρ.re:ℝ)*I
 have hsz:sline T z=ρ:=by
  apply Complex.ext <;> simp [sline,z,mul_re,mul_im] <;> ring
 have hzbox:-(1/2:ℝ)≤ z.im ∧ z.im≤1/2:=by
  simp only[z,add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,zero_add,sub_im]
  constructor <;> linarith [hρ.2.1,hρ.2.2]
 have hzero:normalized T z=0:=by
  rw[normalized_zero_iff T z (by linarith)]
  · rw[hsz];exact Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr hρ
  · rw[hsz];intro h;have hh:=hρ.2.1;simpa [h] using hh
  · rw[hsz];intro h;have hh:=hρ.2.2;simpa [h] using hh
 constructor <;> intro he
 · apply hn z ?_ hzero
   simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
   apply Or.inl;apply Or.inl;apply Or.inr
   norm_num [lo,hi,uIcc_of_le,z] at *
   constructor
   · linarith
   · constructor <;> linarith [hzbox.1,hzbox.2]
 · apply hn z ?_ hzero
   simp only[RectangleBorder,mem_union,mem_reProdIm,mem_singleton_iff]
   apply Or.inr
   norm_num [lo,hi,uIcc_of_le,z] at *
   constructor
   · linarith
   · constructor <;> linarith [hzbox.1,hzbox.2]
end RHHighXiContour
end
section
set_option autoImplicit false
open Complex
namespace RHHighContourCount
lemma bound (N : Nat) (Q : ℂ)
 (hid:(1/((2*Real.pi:ℝ):ℂ)/I)*Q=(N:ℂ))
 (hQ:Q.im≤2571+(8448:ℝ)/10000) : N≤409 := by
 have hpi:((Real.pi:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
 have hq:Q=((2*Real.pi:ℝ):ℂ)*I*(N:ℂ):=by
  apply mul_left_cancel₀ (a:=(1/((2*Real.pi:ℝ):ℂ)/I)) (by simp [hpi,I_ne_zero])
  rw[hid]
  field_simp
 have him:=congrArg Complex.im hq
 simp only[Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,
  Complex.natCast_re,Complex.natCast_im,mul_zero,zero_mul,mul_one,add_zero,zero_add] at him
 have hN:(N:ℝ)<410:=by
  by_contra hh
  have hge:(410:ℝ)≤N:=le_of_not_gt hh
  have hp:3.14<Real.pi:=by linarith [Real.pi_gt_d2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hge) Real.pi_pos.le]
 have hN':N<410:=by exact_mod_cast hN
 omega
end RHHighContourCount
end
section

-- from Zeta23.FromPNTPlus.Rectangle
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem rhHighNarrow_preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.rhHighNarrow_coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl














lemma rhHighNarrow_rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩






















end

-- from Zeta23.Analytic.RectangleLogDeriv
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Residue calculus on rectangles beyond one simple pole.
Used for the weighted contour integral ∮ H·Λ'/Λ and for the Riemann–von Mangoldt count
N(T₁,T₂) = (1/2πi)∮ Λ'/Λ.

* `residueTheorem_finset`: f holomorphic on Rectangle z w minus a finite set S of interior points, with
  f − A p/(s − p) bounded near each p ∈ S  ⟹  RectangleIntegral' f z w = Σ_{p∈S} A p.
  (Induction on S: subtract one principal part, remove the singularity, recurse.)
* `rectangleIntegral'_mul_logDeriv` (the "argument principle with weight"): f, g analytic on a
  neighbourhood of each point of Rectangle z w, f ≠ 0 on the border, Z = the (finite) zero set of
  f in the rectangle  ⟹  RectangleIntegral' (g · f'/f) z w = Σ_{ρ∈Z} ord_ρ(f) · g(ρ).
* `finite_zeros_rectangle`, `rectangleIntegral'_mul_logDeriv'`: the zero set is finite; self-contained form.
-/

open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace Zeta23
namespace Analytic



/-! ## Meromorphic version: finitely many zeros AND poles inside the rectangle

Intended for f = completedRiemannZeta (simple poles at 0 and 1, residues ∓1):
(1/2πi) ∮ g·(f'/f) = Σ_{zeros ρ} ord_ρ(f)·g(ρ) − Σ_{poles p} m_p·g(p).
A pole of order m at p is witnessed elementarily by  (s − p)^m · f(s) → c ≠ 0  (s → p, s ≠ p),
which is the shape of Mathlib's `completedRiemannZeta_residue_one` (m = 1). -/


/-- **Weighted argument principle on a rectangle.** For f, g analytic on a neighbourhood of every
point of the closed rectangle, f nonvanishing on its border, and Z the zero set of f in the
rectangle (as a Finset):  (1/2πi) ∮ g·(f'/f) = Σ_{ρ ∈ Z} ord_ρ(f)·g(ρ). -/
theorem rectangleIntegral'_mul_logDeriv {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  have h := rectangleIntegralPrime_mul_logDeriv_of_poles hre him Z ∅ (Finset.disjoint_empty_right _)
    (by simp) (by simpa using hf) hg hborder (by simpa using hZ) hZsub (fun _ => 0) (by simp)
  simpa using h



end Analytic
end Zeta23
end
end

-- from Zeta23.RvM.CountByIntegral
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/CountByIntegral.lean — the zero count as a contour integral, specialised to Λ.
Used by Zeta23/RvM/Statement.lean and MainTerm.lean (the symmetry fold and the Γ-side).

MAIN RESULT `rectangleIntegral'_logDeriv_completedZeta_eq_Ncount`: for 0 < T₁ ≤ T₂, neither the
ordinate of a nontrivial zero,
    (1/2πi) ∮_{∂([−1,2]×[T₁,T₂])} Λ'/Λ(s) ds = N(T₁,T₂)        (Λ = completedRiemannZeta),
where N = Zeta23.Ncount counts nontrivial zeros of Mathlib's riemannZeta with T₁ < γ ≤ T₂ with
multiplicity zeroMult = analyticOrderAt ζ. Ingredients (all proved here from Mathlib):
 • Λ is analytic off {0,1}; Λ = Gammaℝ·ζ with Gammaℝ ≠ 0 on Re s > 0, so on the strip the zeros
   and their analytic orders agree with ζ's; Λ ≠ 0 for Re s ≥ 1 (Mathlib's non-vanishing of ζ)
   and, by Λ(1−s) = Λ(s), for Re s ≤ 0; hence {Λ = 0} = nontrivial zeros of ζ exactly.
 • Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (weighted argument principle, g ≡ 1).
-/

open Complex Set Topology Filter Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Λ = completedRiemannZeta: analyticity, relation to ζ, zeros -/

lemma analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ completedRiemannZeta (({0, 1} : Set ℂ)ᶜ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0, h1]))






/-- On the open right half-plane (away from 1) the analytic order of Λ equals zeroMult = the
analytic order of ζ. -/
lemma analyticOrderNatAt_completedRiemannZeta {ρ : ℂ} (h : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderNatAt completedRiemannZeta ρ = zeroMult ρ := by
  have h0 : ρ ≠ 0 := fun h' => by simp [h'] at h
  have hev : riemannZeta =ᶠ[𝓝 ρ] (completedRiemannZeta * fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  have hΛ := analyticAt_completedRiemannZeta h0 h1
  have hGinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  have hG0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 :=
    hGinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h))
  unfold zeroMult analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hΛ hGinv, hG0, add_zero]

/-! ## The count -/


end RvM
end Zeta23
end
open Complex Set Topology Filter Real
open Zeta23
open RvM

theorem RHHighNarrowContourCount {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv completedRiemannZeta) (T₁ * I) (1 + T₂ * I)
      = (Ncount T₁ T₂ : ℂ) := by
  classical
  set z : ℂ := T₁ * I with hzdef
  set w : ℂ := 1 + T₂ * I with hwdef
  have hzre : z.re = 0 := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = 1 := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (0 ≤ s.re ∧ s.re ≤ 1) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num), uIcc_of_le hT, mem_Icc]
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w) := by
    intro s hs
    have hi : 0 < s.im := by linarith [((hmem s).mp hs).2.1]
    exact analyticAt_completedRiemannZeta (fun h => by simp [h] at hi) (fun h => by simp [h] at hi)
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Rectangle z w) := fun _ _ => analyticAt_const
  have hfin := zetaSeam.finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w, completedRiemannZeta s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hs
    rw [completedRiemannZeta_eq_zero_iff]
    constructor
    · intro hnz
      exact ⟨hnz, lt_of_le_of_ne hi1 (fun h' => hgood₁ s hnz h'.symm), hi2⟩
    · rintro ⟨hnz, _⟩
      exact hnz
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨_, h1, h2⟩, hi1, hi2⟩ := hs
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp (rhHighNarrow_rectangleBorder_subset_rectangle z w hs)
    have hnz := completedRiemannZeta_eq_zero_iff.mp h0
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, hzre, hzim, hwre,
      hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood₁ s hnz h'
    · linarith [hnz.2.1]
    · exact hgood₂ s hnz h'
    · linarith [hnz.2.2]
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder
    hfin.toFinset hZ hZsub
  simp only [one_mul, mul_one] at key
  rw [show (fun s => logDeriv completedRiemannZeta s) = logDeriv completedRiemannZeta from rfl]
    at key
  rw [key]
  unfold Ncount
  have hset : zerosIn T₁ T₂ = {ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
    ext ρ; simp [zerosIn]
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨⟨_, h1, h2⟩, _⟩ := hρ
  rw [analyticOrderNatAt_completedRiemannZeta h1 (fun h' => by simp [h'] at h2)]

end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex Set
namespace RHHighCountMultiplicity
open Zeta23
lemma closed_eq (a b : ℝ) (ha : ∀ ρ, IsNontrivialZero ρ → ρ.im≠a) :
    RHHighHeight.windowZeros a b=zerosIn a b := by
  ext ρ
  simp only [RHHighHeight.windowZeros,zerosIn,IsNontrivialZero,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz,hr0,hr1,hi0,hi1⟩
    exact ⟨⟨hz,hr0,hr1⟩,lt_of_le_of_ne hi0 (Ne.symm (ha ρ ⟨hz,hr0,hr1⟩)),hi1⟩
  · rintro ⟨⟨hz,hr0,hr1⟩,hi0,hi1⟩
    exact ⟨hz,hr0,hr1,hi0.le,hi1⟩
lemma cardinality_le (a b : ℝ) (ha : ∀ ρ, IsNontrivialZero ρ → ρ.im≠a) :
    (RHHighHeight.windowZeros a b).ncard≤Ncount a b := by
  classical
  have hf : (zerosIn a b).Finite := zetaSeam.finite_window a b
  rw [closed_eq a b ha,Set.ncard_eq_toFinset_card _ hf]
  unfold Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  calc
    _ = ∑ _ρ ∈ hf.toFinset, (1:Nat) := by simp
    _ ≤ ∑ ρ ∈ hf.toFinset, zeroMult ρ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have h : ρ∈zerosIn a b := by simpa only [Set.Finite.mem_toFinset] using hρ
      exact zetaSeam.one_le_mult ρ h.1
end RHHighCountMultiplicity
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourCount
open RHHighContourGeometry RHHighXiContour RHHighXiWindow
lemma from_contour
 (hP:∀z∈RectangleBorder lo hi,(1/10000:ℝ)≤‖RHHighFourierPolynomial.polynomial z‖)
 (he:∀z∈RectangleBorder lo hi,‖normalized 3289999936 z-q 3289999936 z*RHHighFourierPolynomial.polynomial z‖≤1/100000)
 (hQ:(RectangleIntegral (logDeriv RHHighFourierPolynomial.polynomial) lo hi).im≤2571+(8448:ℝ)/10000) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by
 have hcomp:=compare 3289999936 (by norm_num) hP he
 have hg:=good_heights 3289999936 (by norm_num) hcomp.1
 have hga:∀ρ,Zeta23.IsNontrivialZero ρ → ρ.im≠3289999872:=by
  intro ρ hρ
  norm_num only[show (3289999936:ℝ)-64=3289999872 by norm_num] at hg
  exact (hg ρ hρ).1
 have hgb:∀ρ,Zeta23.IsNontrivialZero ρ → ρ.im≠3290000000:=by
  intro ρ hρ
  norm_num only[show (3289999936:ℝ)+64=3290000000 by norm_num] at hg
  exact (hg ρ hρ).2
 have hn:=RHHighNarrowContourCount (by norm_num : (0:ℝ)<3289999872)
  (by norm_num : (3289999872:ℝ)≤3290000000) hga hgb
 have hraw:=completed_integral 3289999936 (by norm_num) hcomp.1
 norm_num only[show (3289999936:ℝ)-64=3289999872 by norm_num,
  show (3289999936:ℝ)+64=3290000000 by norm_num] at hraw
 rw[hcomp.2] at hraw
 have hid:(1/((2*Real.pi:ℝ):ℂ)/I)*RectangleIntegral (logDeriv RHHighFourierPolynomial.polynomial) lo hi=
  (Zeta23.Ncount 3289999872 3290000000:ℂ):=by
  change (1/(2*(Real.pi:ℂ)*I))*RectangleIntegral (logDeriv completedRiemannZeta)
   ((3289999872:ℝ)*I) (1+(3290000000:ℝ)*I)=_ at hn
  rw[hraw] at hn
  convert hn using 1 <;> push_cast <;> ring
 exact (RHHighCountMultiplicity.cardinality_le 3289999872 3290000000 hga).trans
  (bound _ _ hid hQ)
end RHHighContourCount
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex Set
namespace RHHighThreeLines
lemma horizontal (f : ℂ→ℂ) (R ε M : ℝ) (hR : 0 < R) (hf : Differentiable ℂ f)
    (hzero : ∀ x : ℝ, ‖f (x:ℂ)‖≤ε)
    (hbound : ∀ z : ℂ, 0≤z.im ∧ z.im≤R → ‖f z‖≤M)
    (w : ℂ) (hw : 0≤w.im ∧ w.im≤R) :
    ‖f w‖≤ε^(1-w.im/R)*M^(w.im/R) := by
  let g : ℂ→ℂ := fun z => f (I*z)
  have hg : Differentiable ℂ g := hf.comp (by fun_prop)
  have hd : DiffContOnCl ℂ g (HadamardThreeLines.verticalStrip 0 R) :=
    ⟨hg.differentiableOn,hg.continuous.continuousOn⟩
  have hb : BddAbove ((norm ∘ g) '' HadamardThreeLines.verticalClosedStrip 0 R) := by
    refine ⟨M,?_⟩
    rintro v ⟨z,hz,rfl⟩
    change 0≤z.re ∧ z.re≤R at hz
    exact hbound (I*z) (by simpa only [mul_im,I_re,I_im,zero_mul,one_mul,zero_add] using hz)
  have h0 : ∀ z ∈ Complex.re ⁻¹' {(0:ℝ)}, ‖g z‖≤ε := by
    intro z hz
    have hz' : z.re=0 := hz
    have he : I*z=((-z.im:ℝ):ℂ) := by
      apply Complex.ext <;> simp [mul_re,mul_im,hz']
    simpa only [g,he] using hzero (-z.im)
  have h1 : ∀ z ∈ Complex.re ⁻¹' {R}, ‖g z‖≤M := by
    intro z hz
    have hz' : z.re=R := hz
    exact hbound (I*z) (by simpa only [mul_im,I_re,I_im,zero_mul,one_mul,zero_add,hz'] using And.intro hR.le le_rfl)
  have hz : -I*w∈HadamardThreeLines.verticalClosedStrip 0 R := by
    change 0≤(-I*w).re ∧ (-I*w).re≤R
    simpa using hw
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hR hz hd hb h0 h1
  have he : g (-I*w)=f w := by
    dsimp [g]
    congr 1
    ring_nf
    simp [I_sq]
  rw [he] at h
  simpa only [mul_re,neg_re,neg_im,I_re,I_im,neg_zero,zero_mul,
    neg_one_mul,neg_neg,one_mul,sub_zero,zero_sub] using h
end RHHighThreeLines
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighDampedWindow
noncomputable def damp (z : ℂ) : ℂ := Complex.exp (-z^2/2048)
noncomputable def error (T : ℝ) (P : ℂ→ℂ) (z : ℂ) : ℂ :=
  damp z*(RHHighXiWindow.normalized T z-RHHighXiWindow.q T z*P z)
lemma error_entire (T : ℝ) (P : ℂ→ℂ) (hP:Differentiable ℂ P) : Differentiable ℂ (error T P) := by
  have hd:Differentiable ℂ damp := by unfold damp;fun_prop
  unfold error
  exact hd.mul ((RHHighXiWindow.normalized_entire T).sub ((RHHighXiWindow.q_entire T).mul hP))
lemma damp_norm (z : ℂ) : ‖damp z‖=Real.exp (-z.re^2/2048+z.im^2/2048) := by
  unfold damp
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two,Complex.mul_re,Complex.div_re,Complex.normSq]
  ring
lemma undamp_error (T : ℝ) (P : ℂ→ℂ) (z : ℂ) (ε:ℝ) (he:‖error T P z‖≤ε) :
    ‖RHHighXiWindow.normalized T z-RHHighXiWindow.q T z*P z‖≤
      ε*Real.exp (z.re^2/2048-z.im^2/2048) := by
  have hd:0<Real.exp (-z.re^2/2048+z.im^2/2048) := Real.exp_pos _
  unfold error at he
  rw [norm_mul,damp_norm] at he
  have h:‖RHHighXiWindow.normalized T z-RHHighXiWindow.q T z*P z‖≤
      ε/Real.exp (-z.re^2/2048+z.im^2/2048) := (le_div_iff₀ hd).mpr (by nlinarith)
  apply h.trans_eq
  rw [div_eq_mul_inv,←Real.exp_neg]
  congr 2
  ring
end RHHighDampedWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighZetaGrowth
noncomputable def saw (x : ℝ) : ℂ := (((Int.floor x:ℝ)+1/2-x:ℝ):ℂ)
lemma saw_norm (x : ℝ) : ‖saw x‖≤1/2 := by
  rw [saw,Complex.norm_real,Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one x],by linarith [Int.floor_le x]⟩
lemma saw_integral_norm (s : ℂ) (hs : s.re=1/2) :
    ‖∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)‖≤1 := by
  have hi : IntegrableOn (fun x : ℝ => (1/2)*x^(-(3/2:ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) (by norm_num : (0:ℝ)<1)).const_mul _
  have hb : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1), ‖saw x/(x:ℂ)^(s+1)‖≤(1/2)*x^(-(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := by linarith [mem_Ioi.mp hx]
    rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [add_re,one_re,hs]
    norm_num
    have he : (1/2:ℝ)/x^(3/2:ℝ)=(1/2)*x^(-(3/2:ℝ)) := by
      rw [Real.rpow_neg hx0.le]
      ring
    exact (div_le_div_of_nonneg_right (saw_norm x) (Real.rpow_pos_of_pos hx0 _).le).trans_eq he
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, (1/2)*x^(-(3/2:ℝ)) := norm_integral_le_of_norm_le hi hb
    _ = 1 := by rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0:ℝ)<1)];norm_num
lemma critical_growth (t : ℝ) : ‖riemannZeta (1/2+(t:ℂ)*I)‖≤3+|t| := by
  let s : ℂ := 1/2+(t:ℂ)*I
  have hs : s.re=1/2 := by simp [s]
  have hs0 : s≠0 := by intro he;have hr:=congrArg Complex.re he;rw [hs] at hr;norm_num at hr
  have hs1 : s≠1 := by intro he;have hr:=congrArg Complex.re he;rw [hs] at hr;norm_num at hr
  have hz := SWPort.Zeta0EqZeta (N:=1) (by norm_num) (s:=s) (by rw [hs];norm_num) hs1
  have he : riemannZeta s=(1/2:ℂ)-1/(1-s)+s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)) := by
    rw [←hz]
    unfold SWPort.riemannZeta0
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,Nat.cast_zero,
      Nat.cast_one,Complex.zero_cpow hs0,Complex.one_cpow,div_zero,zero_div,div_one]
    have hf : (fun x : ℝ => ((⌊x⌋:ℂ)+1/2-(x:ℂ))/(x:ℂ)^(s+1))=
        (fun x : ℝ => saw x/(x:ℂ)^(s+1)) := by ext x;unfold saw;push_cast;rfl
    rw [hf]
    ring
  have hd : 1/2≤‖1-s‖ := by
    have hr := Complex.re_le_norm (1-s)
    simpa only [sub_re,one_re,hs,show (1-1/2:ℝ)=1/2 by norm_num] using hr
  have hrec : ‖1/(1-s)‖≤2 := by
    rw [norm_div,norm_one]
    apply (div_le_iff₀ (by linarith : 0<‖1-s‖)).mpr
    linarith
  have hsn : ‖s‖≤1/2+|t| := by
    have h := norm_add_le (1/2:ℂ) ((t:ℂ)*I)
    simpa only [s,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      norm_div,norm_one,norm_ofNat,show |t|=|t| by rfl] using h
  change ‖riemannZeta s‖≤_
  rw [he]
  calc
    _ ≤ ‖(1/2:ℂ)-1/(1-s)‖+‖s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1))‖ := norm_add_le _ _
    _ ≤ (1/2+2)+‖s‖*1 := by
      apply add_le_add
      · exact (norm_sub_le _ _).trans (add_le_add (by norm_num) hrec)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (saw_integral_norm s hs) (norm_nonneg _)
    _ ≤ _ := by nlinarith
end RHHighZetaGrowth
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex MeasureTheory Set
namespace RHHighZetaGrowth
lemma saw_integral_strip (s : ℂ) (hs : 1/2≤ s.re) :
    ‖∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)‖≤1 := by
  have hi : IntegrableOn (fun x : ℝ => (1/2)*x^(-(3/2:ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) (by norm_num : (0:ℝ)<1)).const_mul _
  have hb : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1), ‖saw x/(x:ℂ)^(s+1)‖≤(1/2)*x^(-(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    have hx1 : 1≤x := (mem_Ioi.mp hx).le
    rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [add_re,one_re]
    have hden : x^(3/2:ℝ)≤x^(s.re+1) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc
      _ ≤ (1/2:ℝ)/x^(s.re+1) := div_le_div_of_nonneg_right (saw_norm x) (by positivity)
      _ ≤ (1/2:ℝ)/x^(3/2:ℝ) := div_le_div_of_nonneg_left (by norm_num)
        (Real.rpow_pos_of_pos hx0 _) hden
      _ = _ := by rw [Real.rpow_neg hx0.le];ring
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, (1/2)*x^(-(3/2:ℝ)) := norm_integral_le_of_norm_le hi hb
    _ = 1 := by rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0:ℝ)<1)];norm_num
lemma right_strip_growth (s : ℂ) (hs : 1/2≤ s.re ∧ s.re≤33/2) (ht : 1≤|s.im|) :
    ‖riemannZeta s‖≤20+|s.im| := by
  have hs0 : s≠0 := by intro h;rw [h] at hs;norm_num at hs
  have hs1 : s≠1 := by intro h;rw [h] at ht;norm_num at ht
  have hz := SWPort.Zeta0EqZeta (N:=1) (by norm_num) (s:=s) (by linarith [hs.1]) hs1
  have he : riemannZeta s=(1/2:ℂ)-1/(1-s)+s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)) := by
    rw [←hz]
    unfold SWPort.riemannZeta0
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,Nat.cast_zero,
      Nat.cast_one,Complex.zero_cpow hs0,Complex.one_cpow,div_zero,zero_div,div_one]
    have hf : (fun x : ℝ => ((⌊x⌋:ℂ)+1/2-(x:ℂ))/(x:ℂ)^(s+1))=
        (fun x : ℝ => saw x/(x:ℂ)^(s+1)) := by ext x;unfold saw;push_cast;rfl
    rw [hf]
    ring
  have hd : 1≤‖1-s‖ := by
    have h := Complex.abs_im_le_norm (1-s)
    simp only [sub_im,one_im,zero_sub,abs_neg] at h
    exact ht.trans h
  have hrec : ‖1/(1-s)‖≤1 := by
    rw [norm_div,norm_one]
    exact (div_le_one (by linarith)).mpr hd
  have hsn : ‖s‖≤33/2+|s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0≤ s.re)] at h
    linarith [hs.2]
  rw [he]
  calc
    _ ≤ ‖(1/2:ℂ)-1/(1-s)‖+‖s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1))‖ := norm_add_le _ _
    _ ≤ (1/2+1)+‖s‖*1 := by
      apply add_le_add
      · exact (norm_sub_le _ _).trans (add_le_add (by norm_num) hrec)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (saw_integral_strip s hs.1) (norm_nonneg _)
    _ ≤ _ := by linarith
end RHHighZetaGrowth
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped ComplexConjugate
namespace RHHighGamma
lemma quarter_le_four : Real.Gamma (1/4)≤4 := by
  have h := Real.convexOn_Gamma.2
    (by norm_num : (1:ℝ) ∈ Set.Ioi 0) (by norm_num : (2:ℝ) ∈ Set.Ioi 0)
    (by norm_num : 0≤(3/4:ℝ)) (by norm_num : 0≤(1/4:ℝ))
    (by norm_num : (3/4:ℝ)+1/4=1)
  norm_num [smul_eq_mul,Real.Gamma_one,Real.Gamma_two] at h
  have hs := Real.Gamma_add_one (s:=(1/4:ℝ)) (by norm_num)
  norm_num at hs
  nlinarith
lemma norm_beta_le (u v : ℂ) (hu : 0<u.re) (hv : 0<v.re) :
    ‖betaIntegral u v‖ ≤ (betaIntegral (u.re:ℂ) (v.re:ℂ)).re := by
  have h := intervalIntegral.norm_integral_le_integral_norm
    (μ:=volume) (f:=fun x : ℝ => (x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)) (by norm_num : (0:ℝ)≤1)
  unfold betaIntegral
  refine h.trans_eq ?_
  have hi := Complex.reCLM.intervalIntegral_comp_comm
    (Complex.betaIntegral_convergent (u:=(u.re:ℂ)) (v:=(v.re:ℂ))
      (by simpa using hu) (by simpa using hv))
  change (∫ x : ℝ in 0..1, ‖(x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)‖)=_
  change (∫ x : ℝ in 0..1,
    ((x:ℂ)^((u.re:ℂ)-1)*(1-(x:ℂ))^((v.re:ℂ)-1)).re)=
    (∫ x : ℝ in 0..1,
    (x:ℂ)^((u.re:ℂ)-1)*(1-(x:ℂ))^((v.re:ℂ)-1)).re at hi
  rw [←hi]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  have hx0 : 0<x := hx.1
  have hx1 : 0<1-x := by linarith [hx.2]
  have he : 1-(x:ℂ)=((1-x:ℝ):ℂ) := by push_cast; rfl
  dsimp only
  rw [norm_mul,he,Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    Complex.norm_cpow_eq_rpow_re_of_pos hx1]
  have heu : (u.re:ℂ)-1=((u.re-1:ℝ):ℂ) := by push_cast; rfl
  have hev : (v.re:ℂ)-1=((v.re-1:ℝ):ℂ) := by push_cast; rfl
  rw [heu,hev,←Complex.ofReal_cpow hx0.le,←Complex.ofReal_cpow hx1.le,
    ←Complex.ofReal_mul,Complex.ofReal_re]
  simp only [sub_re,one_re]
lemma half_norm_sq (x : ℝ) :
    ‖Complex.Gamma (1/2+(x:ℂ)*I)‖^2=Real.pi/Real.cosh (Real.pi*x) := by
  let z : ℂ := 1/2+(x:ℂ)*I
  have hc : 1-z=conj z := by
    apply Complex.ext <;> simp [z] <;> ring
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hc,Complex.Gamma_conj] at h
  have he : (Real.pi:ℂ)*z=(Real.pi:ℂ)/2+((Real.pi*x:ℝ):ℂ)*I := by
    dsimp [z]; push_cast; ring
  rw [he,Complex.sin_add,Complex.sin_pi_div_two,Complex.cos_pi_div_two,
    one_mul,zero_mul,add_zero,Complex.cos_mul_I,←Complex.ofReal_cosh] at h
  have hn := congrArg norm h
  simp only [norm_mul,Complex.norm_conj,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos (Real.cosh_pos (Real.pi*x))] at hn
  simpa only [z,pow_two] using hn
lemma gamma_real_norm {r : ℝ} (hr : 0<r) : ‖Complex.Gamma (r:ℂ)‖=Real.Gamma r := by
  rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos hr)]
lemma quarter_half_ratio (x : ℝ) :
    ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*Real.Gamma (1/2) ≤
      4*‖Complex.Gamma (1/2+(x:ℂ)*I)‖ := by
  let q := Real.Gamma (1/4)
  let h := Real.Gamma (1/2)
  have hq : 0<q := Real.Gamma_pos_of_pos (by norm_num)
  have hh : 0<h := Real.Gamma_pos_of_pos (by norm_num)
  have hB := norm_beta_le (1/4+(x:ℂ)*I) (1/4) (by norm_num) (by norm_num)
  norm_num at hB
  have hr : (betaIntegral (1/4) (1/4)).re=q^2/h := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    have hq' : Complex.Gamma (1/4:ℂ)=(q:ℂ) := by
      rw [show (1/4:ℂ)=((1/4:ℝ):ℂ) by norm_num,Complex.Gamma_ofReal]
    have hh' : Complex.Gamma (1/2:ℂ)=(h:ℂ) := by
      rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,Complex.Gamma_ofReal]
    rw [show (1/4+1/4:ℂ)=1/2 by ring,hq',hh']
    simp only [←Complex.ofReal_mul,←Complex.ofReal_div,Complex.ofReal_re,pow_two]
  rw [hr] at hB
  have hp := congrArg norm
    (Complex.Gamma_mul_Gamma_eq_betaIntegral (s:=1/4+(x:ℂ)*I) (t:=1/4)
      (by norm_num) (by norm_num))
  have he : (1/4+(x:ℂ)*I)+(1/4)=1/2+(x:ℂ)*I := by ring
  have hn : ‖Complex.Gamma (1/4:ℂ)‖=q := by
    convert gamma_real_norm (by norm_num : (0:ℝ)<1/4) using 1 <;> norm_num
  rw [norm_mul,he,norm_mul,hn] at hp
  have hm : ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*q ≤
      ‖Complex.Gamma (1/2+(x:ℂ)*I)‖*(q^2/h) :=
    hp.trans_le (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
  have hm' := mul_le_mul_of_nonneg_right hm hh.le
  rw [mul_assoc ‖Complex.Gamma (1/2+(x:ℂ)*I)‖,div_mul_cancel₀ _ hh.ne'] at hm'
  have hc : (‖Complex.Gamma (1/4+(x:ℂ)*I)‖*h)*q ≤
      (‖Complex.Gamma (1/2+(x:ℂ)*I)‖*q)*q := by nlinarith [hm']
  have hc' := (mul_le_mul_iff_left₀ hq).mp hc
  exact hc'.trans (by simpa [q,mul_comm] using
    mul_le_mul_of_nonneg_left quarter_le_four (norm_nonneg (Complex.Gamma (1/2+(x:ℂ)*I))))
lemma half_scaled_sq (x : ℝ) :
    (‖Complex.Gamma (1/2+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2))^2≤2*Real.pi := by
  have hc : 0<Real.cosh (Real.pi*x) := Real.cosh_pos _
  have hn : ‖Complex.Gamma (1/2+(x:ℂ)*I)‖^2*Real.cosh (Real.pi*x)=Real.pi :=
    (eq_div_iff hc.ne').mp (half_norm_sq x)
  have he : Real.exp (Real.pi*x)≤2*Real.cosh (Real.pi*x) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(Real.pi*x))]
  have hs : (Real.exp (Real.pi*x/2))^2=Real.exp (Real.pi*x) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow,hs]
  calc
    _ ≤ ‖Complex.Gamma (1/2+(x:ℂ)*I)‖^2*(2*Real.cosh (Real.pi*x)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = 2*Real.pi := by nlinarith [hn]
lemma scaled_quarter_le_six (x : ℝ) :
    ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2)≤6 := by
  let U := ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2)
  let V := ‖Complex.Gamma (1/2+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2)
  let H := Real.Gamma (1/2)
  have hU : 0≤U := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hV : 0≤V := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hH : 0<H := Real.Gamma_pos_of_pos (by norm_num)
  have hH2 : H^2=Real.pi := by
    dsimp [H]
    rw [Real.Gamma_one_half_eq,Real.sq_sqrt Real.pi_pos.le]
  have hratio := mul_le_mul_of_nonneg_right (quarter_half_ratio x) (Real.exp_pos (Real.pi*x/2)).le
  have hr : U*H≤4*V := by dsimp [U,H,V]; nlinarith [hratio]
  have hr2 : (U*H)^2≤(4*V)^2 := by gcongr
  have hv2 : V^2≤2*Real.pi := half_scaled_sq x
  have hu2 : U^2*Real.pi≤32*Real.pi := by
    calc
      U^2*Real.pi=(U*H)^2 := by simp only [mul_pow,hH2]
      _ ≤ (4*V)^2 := hr2
      _ ≤ 32*Real.pi := by nlinarith [hv2]
  have hu : U^2≤32 := (mul_le_mul_iff_left₀ Real.pi_pos).mp hu2
  nlinarith [hu]
lemma gaussian_kernel_le (T t h : ℝ) (k : Nat) :
    ‖Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*
      (Real.exp (Real.pi*(t+T)/4-t^2/(2*h^2)):ℂ)*
      (-2*(Real.pi:ℂ)*I*(t:ℂ))^k‖ ≤
      6*(2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2)) := by
  have hg := scaled_quarter_le_six ((t+T)/2)
  rw [show Real.pi*((t+T)/2)/2=Real.pi*(t+T)/4 by ring] at hg
  have hn : ‖-2*(Real.pi:ℂ)*I*(t:ℂ)‖=2*Real.pi*|t| := by
    rw [norm_mul,norm_mul,norm_mul,norm_neg]
    norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have he : Real.exp (Real.pi*(t+T)/4-t^2/(2*h^2))=
      Real.exp (Real.pi*(t+T)/4)*Real.exp (-t^2/(2*h^2)) := by
    simp only [sub_eq_add_neg,Real.exp_add,neg_div]
  calc
    _ = (‖Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)‖*Real.exp (Real.pi*(t+T)/4))*
        ((2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2))) := by
      rw [norm_mul,norm_mul,norm_pow,hn,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _),he]
      ring
    _ ≤ 6*((2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2))) :=
      mul_le_mul_of_nonneg_right hg (by positivity)
    _ = _ := by ring
end RHHighGamma
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex MeasureTheory Set
namespace RHHighGammaStrip
lemma half_scaled (b : ℝ) :
    ‖Complex.Gamma (1/2+(b:ℂ)*I)‖*Real.exp (Real.pi*b/2)≤3 := by
  have h := RHHighGamma.half_scaled_sq b
  have hp : 0≤‖Complex.Gamma (1/2+(b:ℂ)*I)‖*Real.exp (Real.pi*b/2) := by positivity
  nlinarith [Real.pi_lt_four]
lemma real_gamma_lower_exp (τ : ℝ) (hτ : 1≤τ) :
    Real.exp (-2)≤Real.Gamma τ := by
  have hp : 0 < τ := by linarith
  have hi := Real.GammaIntegral_convergent hp
  have hsub : Icc (1:ℝ) 2⊆Set.Ioi 0 := by intro x hx;change 0 < x;linarith [hx.1]
  have hi' := hi.mono_set hsub
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (-2)) (Icc (1:ℝ) 2) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hlocal : (∫ x : ℝ in Icc 1 2, Real.exp (-2))≤
      ∫ x : ℝ in Icc 1 2, Real.exp (-x)*x^(τ-1) := by
    apply setIntegral_mono_on hc hi' measurableSet_Icc
    intro x hx
    have hx0 : 0≤x := by linarith [hx.1]
    have hpow : 1≤x^(τ-1) := Real.one_le_rpow hx.1 (by linarith)
    have he : Real.exp (-2)≤Real.exp (-x) := Real.exp_le_exp.mpr (by linarith [hx.2])
    simpa only [mul_one] using mul_le_mul he hpow (by norm_num : (0:ℝ)≤1) (Real.exp_pos (-x)).le
  have hpos : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x : ℝ => Real.exp (-x)*x^(τ-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)
  have hglobal := setIntegral_mono_set hi hpos
    (Filter.Eventually.of_forall (fun x hx => hsub hx))
  rw [Real.Gamma_eq_integral hp]
  have hloc : Real.exp (-2)≤∫ x : ℝ in Icc 1 2, Real.exp (-x)*x^(τ-1) := by
    simpa using (by norm_num at hlocal ⊢;exact hlocal)
  exact hloc.trans hglobal
lemma real_gamma_lower (τ : ℝ) (hτ : 1≤τ) : (1/9:ℝ)≤Real.Gamma τ := by
  have he : Real.exp (2:ℝ)≤9 := by
    rw [show Real.exp (2:ℝ)=(Real.exp 1)^2 by simpa using Real.exp_nat_mul (1:ℝ) (2:Nat)]
    nlinarith [Real.exp_one_lt_three,Real.exp_pos 1]
  have hi : (1/9:ℝ)≤Real.exp (-2) := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos 2) he
  exact hi.trans (real_gamma_lower_exp τ hτ)
end RHHighGammaStrip
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex MeasureTheory Set
namespace RHHighGammaStrip
lemma beta_bound (u v : ℂ) (hu : 1/4≤u.re) (hv : 1≤v.re) :
    ‖betaIntegral u v‖≤4 := by
  have hu0 : 0 < u.re := by linarith
  have hv0 : 0 < v.re := by linarith
  have hi := (Complex.betaIntegral_convergent hu0 hv0).norm
  have hg : IntervalIntegrable (fun x : ℝ => x^(-(3:ℝ)/4)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hm : (∫ x : ℝ in 0..1, ‖(x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)‖)≤
      ∫ x : ℝ in 0..1, x^(-(3:ℝ)/4) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi hg
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : 0 < 1-x := by linarith [hx.2]
    rw [norm_mul,show 1-(x:ℂ)=((1-x:ℝ):ℂ) by push_cast;rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.norm_cpow_eq_rpow_re_of_pos hx1]
    simp only [sub_re,one_re]
    have h1 : x^(u.re-1)≤x^(-(3:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx.2.le (by linarith)
    have h2 : (1-x)^(v.re-1)≤1 := Real.rpow_le_one
      hx1.le (by linarith [hx.1]) (by linarith)
    exact (mul_le_mul h1 h2 (Real.rpow_nonneg hx1.le _) (Real.rpow_nonneg hx0.le _)).trans_eq (mul_one _)
  have he : (∫ x : ℝ in 0..1, x^(-(3:ℝ)/4))=4 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(3:ℝ)/4))]
    norm_num
  exact (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ)≤1)).trans
    (hm.trans_eq he)
lemma gamma_compare (a b : ℝ) (ha : 1/4≤a ∧ a≤17/2) :
    ‖Complex.Gamma ((a:ℂ)+(b:ℂ)*I)‖≤36*‖Complex.Gamma (19/2+(b:ℂ)*I)‖ := by
  let τ : ℝ := 19/2-a
  have ht : 1≤τ := by dsimp [τ];linarith [ha.2]
  have hu : 0 < ((a:ℂ)+(b:ℂ)*I).re := by simp;linarith [ha.1]
  have hv : 0 < (τ:ℂ).re := by simp;linarith
  have hh := congrArg norm (Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv)
  have he : ((a:ℂ)+(b:ℂ)*I)+(τ:ℂ)=19/2+(b:ℂ)*I := by dsimp [τ];push_cast;ring
  have ht' : ‖Complex.Gamma (τ:ℂ)‖=Real.Gamma τ := RHHighGamma.gamma_real_norm (by linarith)
  rw [norm_mul,norm_mul,he,ht'] at hh
  have hbet : ‖betaIntegral ((a:ℂ)+(b:ℂ)*I) (τ:ℂ)‖≤4 :=
    beta_bound _ _ (by simpa using ha.1) (by simpa using ht)
  have hgam := real_gamma_lower τ ht
  have h1 := mul_le_mul_of_nonneg_left hbet (norm_nonneg (Complex.Gamma (19/2+(b:ℂ)*I)))
  have h2 := mul_le_mul_of_nonneg_left hgam (norm_nonneg (Complex.Gamma ((a:ℂ)+(b:ℂ)*I)))
  rw [←hh] at h1
  nlinarith
end RHHighGammaStrip
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighGammaStrip
lemma half_shift_bound (b : ℝ) (n : Nat) (hn : n≤9) :
    ‖Complex.Gamma (1/2+(b:ℂ)*I+(n:ℂ))‖*Real.exp (Real.pi*b/2)≤
      3*(|b|+10)^n := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,pow_zero,mul_one] using half_scaled b
  | succ n ih =>
    have hn' : n≤9 := by omega
    have hz : (1/2+(b:ℂ)*I+(n:ℂ):ℂ)≠0 := by
      intro he
      have h := congrArg Complex.re he
      simp at h
      have hnon : (0:ℝ)≤n := Nat.cast_nonneg _
      linarith
    have he : 1/2+(b:ℂ)*I+((n+1:Nat):ℂ)=
        (1/2+(b:ℂ)*I+(n:ℂ))+1 := by push_cast;ring
    rw [he,Complex.Gamma_add_one _ hz,norm_mul]
    have hnorm : ‖1/2+(b:ℂ)*I+(n:ℂ)‖≤|b|+10 := by
      have hh := norm_add_le (1/2+(b:ℂ)*I) (n:ℂ)
      have h1 := norm_add_le (1/2:ℂ) ((b:ℂ)*I)
      norm_num only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
        Real.norm_eq_abs,Complex.norm_natCast,norm_div,norm_one,Complex.norm_ofNat] at hh h1
      have hnreal : (n:ℝ)≤8 := by exact_mod_cast (show n≤8 by omega)
      linarith
    calc
      _ = ‖1/2+(b:ℂ)*I+(n:ℂ)‖*
          (‖Complex.Gamma (1/2+(b:ℂ)*I+(n:ℂ))‖*Real.exp (Real.pi*b/2)) := by ring
      _ ≤ (|b|+10)*(3*(|b|+10)^n) := mul_le_mul hnorm (ih hn')
        (by positivity) (by positivity)
      _ = _ := by rw [pow_succ];ring
lemma strip_scaled (a b : ℝ) (ha : 1/4≤a ∧ a≤17/2) :
    ‖Complex.Gamma ((a:ℂ)+(b:ℂ)*I)‖*Real.exp (Real.pi*b/2)≤
      108*(|b|+10)^9 := by
  have h1 := mul_le_mul_of_nonneg_right (gamma_compare a b ha) (Real.exp_pos (Real.pi*b/2)).le
  have h2 := half_shift_bound b 9 (by decide)
  have he : (1/2+(b:ℂ)*I+(9:ℂ))=19/2+(b:ℂ)*I := by ring
  norm_num only [Nat.cast_ofNat] at h2
  rw [he] at h2
  nlinarith
end RHHighGammaStrip
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex MeasureTheory Set
namespace RHHighGammaStrip
lemma norm_gamma_le_real (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖≤Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs,Real.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  apply norm_integral_le_of_norm_le (Real.GammaIntegral_convergent hs)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.norm_of_nonneg (Real.exp_pos (-x)).le]
  simp only [sub_re,one_re,neg_re,Complex.ofReal_re]
  rfl
lemma real_gamma_coarse (a : ℝ) (ha : 1/4≤a ∧ a≤9) : Real.Gamma a≤40320 := by
  have h := Real.convexOn_Gamma.2
    (by norm_num : (1/4:ℝ)∈Set.Ioi 0) (by norm_num : (9:ℝ)∈Set.Ioi 0)
    (show 0≤(9-a)/(9-1/4) by apply div_nonneg <;> linarith [ha.2])
    (show 0≤(a-1/4)/(9-1/4) by apply div_nonneg <;> linarith [ha.1])
    (show (9-a)/(9-1/4)+(a-1/4)/(9-1/4)=(1:ℝ) by ring)
  have he : ((9-a)/(9-1/4))*((1/4:ℝ))+((a-1/4)/(9-1/4))*9=a := by ring
  simp only [smul_eq_mul,he] at h
  have h9 : Real.Gamma (9:ℝ)=40320 := by
    norm_num [Real.Gamma_nat_eq_factorial]
  rw [h9] at h
  have hq := RHHighGamma.quarter_le_four
  have hm := mul_le_mul_of_nonneg_left hq (show 0≤(9-a)/(9-1/4) by
    apply div_nonneg <;> linarith [ha.2])
  norm_num at h hm
  nlinarith
end RHHighGammaStrip
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex MeasureTheory Set Metric
namespace RHHighCompletedCompact
open RHHighZetaGrowth RHHighGammaStrip
lemma right_growth_of_pole_distance (s : ℂ) (hs : 1/2≤ s.re) (hd : 1/2≤‖1-s‖) :
    ‖riemannZeta s‖≤5/2+‖s‖ := by
  have hs0 : s≠0 := by intro h;rw [h] at hs;norm_num at hs
  have hs1 : s≠1 := by intro h;rw [h] at hd;norm_num at hd
  have hz := SWPort.Zeta0EqZeta (N:=1) (by norm_num) (s:=s) (by linarith) hs1
  have he : riemannZeta s=(1/2:ℂ)-1/(1-s)+s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)) := by
    rw [←hz]
    unfold SWPort.riemannZeta0
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,Nat.cast_zero,
      Nat.cast_one,Complex.zero_cpow hs0,Complex.one_cpow,div_zero,zero_div,div_one]
    have hf : (fun x : ℝ => ((⌊x⌋:ℂ)+1/2-(x:ℂ))/(x:ℂ)^(s+1))=
        (fun x : ℝ => saw x/(x:ℂ)^(s+1)) := by ext x;unfold saw;push_cast;rfl
    rw [hf]
    ring
  have hrec : ‖1/(1-s)‖≤2 := by
    rw [norm_div,norm_one]
    apply (div_le_iff₀ (by linarith : 0 < ‖1-s‖)).mpr
    linarith
  rw [he]
  calc
    _ ≤ ‖(1/2:ℂ)-1/(1-s)‖+‖s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1))‖ := norm_add_le _ _
    _ ≤ (1/2+2)+‖s‖*1 := by
      apply add_le_add
      · exact (norm_sub_le _ _).trans (add_le_add (by norm_num) hrec)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (saw_integral_strip s hs) (norm_nonneg _)
    _ = _ := by ring
lemma completed_factor (s : ℂ) (hs : 0 < s.re) :
    completedRiemannZeta s=(Real.pi:ℂ)^(-s/2)*Complex.Gamma (s/2)*riemannZeta s := by
  have hs0 : s≠0 := by intro h;rw [h] at hs;norm_num at hs
  have hg : Gammaℝ s≠0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [riemannZeta_def_of_ne_zero hs0]
  rw [Gammaℝ_def] at hg
  rw [Gammaℝ_def]
  field_simp [hg,Complex.Gamma_ne_zero_of_re_pos (by simp;linarith : 0 < (s/2).re)]
lemma right_circle (s : ℂ) (hs : 1/2≤ s.re) (hc : ‖s-1/2‖=17) :
    ‖completedRiemannZeta₀ s‖≤1000000 := by
  have hsn : ‖s‖≤35/2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub s (1/2:ℂ) 0
    norm_num only [sub_zero,norm_div,norm_one,norm_ofNat] at h
    linarith
  have hd0 : 33/2≤‖s‖ := by
    have h := norm_sub_le s (1/2:ℂ)
    norm_num only [norm_div,norm_one,norm_ofNat] at h
    linarith
  have hd1 : 33/2≤‖1-s‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub s (1:ℂ) (1/2:ℂ)
    rw [norm_sub_rev s 1] at h
    norm_num at h
    linarith
  have hre := (Complex.re_le_norm s).trans hsn
  have hG : ‖Complex.Gamma (s/2)‖≤40320 := by
    apply (norm_gamma_le_real _ (by simp;linarith)).trans
    apply real_gamma_coarse
    simp only [Complex.div_ofNat_re]
    constructor <;> linarith
  have hpi : ‖(Real.pi:ℂ)^(-s/2)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [Complex.div_ofNat_re,neg_re]
    linarith
  have hz : ‖riemannZeta s‖≤20 := by
    have h := right_growth_of_pole_distance s hs (by linarith)
    linarith
  have hM : ‖completedRiemannZeta s‖≤806400 := by
    rw [completed_factor s (by linarith),norm_mul,norm_mul]
    exact (mul_le_mul (mul_le_mul hpi hG (norm_nonneg _) (by norm_num)) hz
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h0 : ‖1/s‖≤1 := by rw [norm_div,norm_one];exact (div_le_one (by linarith)).mpr (by linarith)
  have h1 : ‖1/(1-s)‖≤1 := by rw [norm_div,norm_one];exact (div_le_one (by linarith)).mpr (by linarith)
  have he : completedRiemannZeta₀ s=completedRiemannZeta s+1/s+1/(1-s) := by rw [completedRiemannZeta_eq];ring
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hM h0)) h1)).trans (by norm_num)
lemma circle (s : ℂ) (hc : ‖s-1/2‖=17) : ‖completedRiemannZeta₀ s‖≤1000000 := by
  rcases le_total (1/2:ℝ) s.re with hs|hs
  · exact right_circle s hs hc
  · have he : ‖(1-s)-1/2‖=17 := by
      have hi : (1-s)-1/2= -(s-1/2) := by ring
      rw [hi,norm_neg,hc]
    rw [←completedRiemannZeta₀_one_sub s]
    exact right_circle (1-s) (by simp;linarith) he
lemma compact_bound (s : ℂ) (hs : -(31/2:ℝ)≤ s.re ∧ s.re≤33/2) (hi : |s.im|≤1) :
    ‖completedRiemannZeta₀ s‖≤1000000 := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball (x:=(1/2:ℂ)) (r:=17))
    differentiable_completedZeta₀.diffContOnCl
  · intro z hz
    rw [frontier_ball (1/2:ℂ) (by norm_num : (17:ℝ)≠0),Metric.mem_sphere,dist_eq_norm] at hz
    exact circle z hz
  · rw [closure_ball (1/2:ℂ) (by norm_num : (17:ℝ)≠0),Metric.mem_closedBall,dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (s-1/2)
    norm_num only [sub_re,sub_im,Complex.div_ofNat_re,Complex.one_re,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] at h
    have hr : |s.re-1/2|≤16 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    linarith
end RHHighCompletedCompact
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
open scoped ComplexConjugate
namespace RHHighGammaStrip
lemma strip_scaled_abs (a b : ℝ) (ha : 1/4≤a ∧ a≤17/2) :
    ‖Complex.Gamma ((a:ℂ)+(b:ℂ)*I)‖*Real.exp (Real.pi*|b|/2)≤
      108*(|b|+10)^9 := by
  by_cases hb : 0≤b
  · simpa only [abs_of_nonneg hb] using strip_scaled a b ha
  · have hb' : 0≤-b := by linarith
    have h := strip_scaled a (-b) ha
    have he : (a:ℂ)+((-b:ℝ):ℂ)*I=conj ((a:ℂ)+(b:ℂ)*I) := by
      simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
      ring
    rw [he,Complex.Gamma_conj,Complex.norm_conj,abs_neg] at h
    simpa only [abs_of_neg (lt_of_not_ge hb)] using h
end RHHighGammaStrip
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighCompletedStrip
open RHHighGammaStrip RHHighCompletedCompact RHHighZetaGrowth
lemma right_scaled (s : ℂ) (hs : 1/2≤ s.re ∧ s.re≤33/2) (hi : 1≤|s.im|) :
    ‖completedRiemannZeta s‖*Real.exp (Real.pi*|s.im|/4)≤108*(|s.im|+20)^10 := by
  have hz : ((s.re/2:ℝ):ℂ)+((s.im/2:ℝ):ℂ)*I=s/2 := by
    apply Complex.ext <;> simp
  have hG := strip_scaled_abs (s.re/2) (s.im/2) (by constructor <;> linarith [hs.1,hs.2])
  rw [hz,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hG
  have hG' : ‖Complex.Gamma (s/2)‖*Real.exp (Real.pi*|s.im|/4)≤108*(|s.im|+20)^9 := by
    have he : Real.pi*(|s.im|/2)/2=Real.pi*|s.im|/4 := by ring
    rw [he] at hG
    exact hG.trans (by gcongr <;> linarith [abs_nonneg s.im])
  have hp : ‖(Real.pi:ℂ)^(-s/2)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [Complex.div_ofNat_re,neg_re]
    linarith [hs.1]
  rw [completed_factor s (by linarith [hs.1]),norm_mul,norm_mul]
  calc
    _ = ‖(Real.pi:ℂ)^(-s/2)‖*(‖Complex.Gamma (s/2)‖*Real.exp (Real.pi*|s.im|/4))*‖riemannZeta s‖ := by ring
    _ ≤ (1*(108*(|s.im|+20)^9))*(20+|s.im|) :=
      mul_le_mul (mul_le_mul hp hG' (by positivity) (by norm_num))
        (right_strip_growth s hs hi) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ];ring
lemma strip_scaled (s : ℂ) (hs : -(31/2:ℝ)≤ s.re ∧ s.re≤33/2) (hi : 1≤|s.im|) :
    ‖completedRiemannZeta s‖*Real.exp (Real.pi*|s.im|/4)≤108*(|s.im|+20)^10 := by
  by_cases hr : 1/2≤ s.re
  · exact right_scaled s ⟨hr,hs.2⟩ hi
  · have h := right_scaled (1-s) (by simp;constructor <;> linarith [hs.1])
      (by simpa only [sub_im,one_im,zero_sub,abs_neg] using hi)
    simpa only [completedRiemannZeta_one_sub,sub_im,one_im,zero_sub,abs_neg] using h
end RHHighCompletedStrip
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighXiEnvelope
open RHHighXiWindow RHHighEntireCorrection RHHighCompletedStrip
lemma window_norm (T : ℝ) (z : ℂ) :
    ‖window T z‖=Real.exp (Real.pi*(z.re+T)/4-z.re^2/800+z.im^2/800) := by
  unfold window
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq]
  ring
lemma sline_coordinates (T : ℝ) (z : ℂ) :
    (sline T z).re=1/2-z.im ∧ (sline T z).im=z.re+T := by
  simp [sline,sub_eq_add_neg]
lemma sline_norm (T : ℝ) (z : ℂ) (hz : |z.im|≤16) :
    ‖sline T z‖≤17+|z.re+T| ∧ ‖sline T z-1‖≤17+|z.re+T| := by
  have hr := (sline_coordinates T z).1
  have hi := (sline_coordinates T z).2
  have hy := abs_le.mp hz
  constructor
  · have h := Complex.norm_le_abs_re_add_abs_im (sline T z)
    rw [hr,hi] at h
    have ha : |1/2-z.im|≤17 := abs_le.mpr ⟨by linarith,by linarith⟩
    linarith
  · have h := Complex.norm_le_abs_re_add_abs_im (sline T z-1)
    simp only [sub_re,sub_im,one_re,one_im,sub_zero,hr,hi] at h
    have ha : |1/2-z.im-1|≤17 := abs_le.mpr ⟨by linarith,by linarith⟩
    linarith
lemma window_norm_le (T : ℝ) (z : ℂ) :
    ‖window T z‖≤Real.exp (Real.pi*|z.re+T|/4)*
      Real.exp (-z.re^2/800+z.im^2/800) := by
  rw [window_norm,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos,le_abs_self (z.re+T)]
lemma away_envelope (T : ℝ) (z : ℂ) (hT : 0 < T) (hz : |z.im|≤16)
    (hu : 1≤|z.re+T|) :
    ‖normalized T z‖≤108*(|z.re+T|+20)^12/T^2*
      Real.exp (-z.re^2/800+z.im^2/800) := by
  let s := sline T z
  have hc := sline_coordinates T z
  have hs : -(31/2:ℝ)≤ s.re ∧ s.re ≤33/2 := by
    dsimp [s]
    rw [hc.1]
    have h := abs_le.mp hz
    constructor <;> linarith
  have hi : 1 ≤ |s.im| := by simpa only [s,hc.2] using hu
  have h0 : s≠0 := by intro h;rw [h] at hi;norm_num at hi
  have h1 : s≠1 := by intro h;rw [h] at hi;norm_num at hi
  have hM := strip_scaled s hs hi
  have hn := sline_norm T z hz
  have hN : ‖s‖*‖s-1‖≤(|z.re+T|+20)^2 := by
    calc
      _ ≤ (17+|z.re+T|)*(17+|z.re+T|) :=
        mul_le_mul hn.1 hn.2 (norm_nonneg _) (by positivity)
      _ ≤ (|z.re+T|+20)^2 := by nlinarith [abs_nonneg (z.re+T)]
  rw [normalized_eq T z h0 h1,norm_mul,norm_div,norm_mul,norm_neg,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT,norm_mul]
  calc
    _ ≤ ((|z.re+T|+20)^2/T^2)*
        (‖completedRiemannZeta s‖*(Real.exp (Real.pi*|z.re+T|/4)*
          Real.exp (-z.re^2/800+z.im^2/800))) :=
      mul_le_mul (div_le_div_of_nonneg_right hN (sq_nonneg T))
        (mul_le_mul_of_nonneg_left (window_norm_le T z) (norm_nonneg _))
        (by positivity) (by positivity)
    _ = ((|z.re+T|+20)^2/T^2)*
        ((‖completedRiemannZeta s‖*Real.exp (Real.pi*|s.im|/4))*
          Real.exp (-z.re^2/800+z.im^2/800)) := by rw [hc.2];ring
    _ ≤ ((|z.re+T|+20)^2/T^2)*
        ((108*(|z.re+T|+20)^10)*Real.exp (-z.re^2/800+z.im^2/800)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by simpa only [s,hc.2] using hM) (Real.exp_pos _).le)
        (div_nonneg (sq_nonneg _) (sq_nonneg T))
    _ = _ := by ring
lemma compact_envelope (T : ℝ) (z : ℂ) (hT : 0 < T) (hz : |z.im|≤16)
    (hu : |z.re+T|≤1) :
    ‖normalized T z‖≤1000000000/T^2*
      Real.exp (-z.re^2/800+z.im^2/800) := by
  let s := sline T z
  have hc := sline_coordinates T z
  have hs : -(31/2:ℝ) ≤ s.re ∧ s.re ≤ 33/2 := by
    dsimp [s]
    rw [hc.1]
    have h := abs_le.mp hz
    constructor <;> linarith
  have hi : |s.im|≤1 := by simpa only [s,hc.2] using hu
  have hM := RHHighCompletedCompact.compact_bound s hs hi
  have hn := sline_norm T z hz
  have hN : ‖s‖≤18 ∧ ‖s-1‖≤18 := ⟨by linarith [hn.1],by linarith [hn.2]⟩
  have hxi : ‖xi s‖≤325000000 := by
    unfold xi
    calc
      _ ≤ ‖s‖*‖s-1‖*‖completedRiemannZeta₀ s‖+1 := by
        simpa only [norm_mul,norm_one] using norm_add_le (s*(s-1)*completedRiemannZeta₀ s) 1
      _ ≤ 18*18*1000000+1 := by
        exact add_le_add (mul_le_mul (mul_le_mul hN.1 hN.2 (norm_nonneg _) (by norm_num))
          hM (norm_nonneg _) (by norm_num)) le_rfl
      _ ≤ _ := by norm_num
  have hp : Real.exp (Real.pi*|z.re+T|/4)≤3 := by
    apply (Real.exp_le_exp.mpr (show Real.pi*|z.re+T|/4≤1 by
      nlinarith [abs_nonneg (z.re+T),Real.pi_pos,Real.pi_lt_four])).trans
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hw := (window_norm_le T z).trans
    (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
  rw [normalized,norm_div,norm_neg,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hT]
  calc
    _ ≤ (325000000*(3*Real.exp (-z.re^2/800+z.im^2/800)))/T^2 :=
      div_le_div_of_nonneg_right (mul_le_mul hxi hw (norm_nonneg _) (by norm_num)) (sq_nonneg T)
    _ ≤ _ := by
      have he := (Real.exp_pos (-z.re^2/800+z.im^2/800)).le
      have ht := (sq_pos_of_pos hT).le
      field_simp
      nlinarith
lemma envelope (T : ℝ) (z : ℂ) (hT : 0 < T) (hz : |z.im|≤16) :
    ‖normalized T z‖≤1000000000*(|z.re+T|+20)^12/T^2*
      Real.exp (-z.re^2/800+z.im^2/800) := by
  by_cases hu : 1≤|z.re+T|
  · exact (away_envelope T z hT hz hu).trans (by gcongr <;> norm_num)
  · apply (compact_envelope T z hT hz (by linarith)).trans
    have hp : (1:ℝ)≤(|z.re+T|+20)^12 := one_le_pow₀ (by linarith [abs_nonneg (z.re+T)])
    gcongr
    nlinarith
end RHHighXiEnvelope
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighXiEnvelope
lemma polynomial_envelope (T x : ℝ) (hT : 0≤T) :
    (|x+T|+20)^12≤(T+4821)^12*Real.exp (x^2/1600) := by
  have ha : |x+T|≤|x|+T := by simpa only [abs_of_nonneg hT] using abs_add_le x T
  have hx : |x|≤4800+x^2/19200 := by nlinarith [sq_abs x,sq_nonneg (|x|-9600)]
  have he := Real.add_one_le_exp (x^2/19200)
  have hc : 1≤T+4821 := by linarith
  have hn : 0≤x^2/19200 := by positivity
  have hh : |x+T|+20≤(T+4821)*Real.exp (x^2/19200) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hn]
  calc
    _ ≤ ((T+4821)*Real.exp (x^2/19200))^12 := pow_le_pow_left₀ (by positivity) hh _
    _ = (T+4821)^12*Real.exp (x^2/1600) := by
      rw [mul_pow,←Real.exp_nat_mul]
      congr 2
      ring
lemma gaussian_envelope (T : ℝ) (z : ℂ)
    (hT : 3000000000≤T ∧ T≤4000000000) (hz : |z.im|≤16) :
    ‖RHHighXiWindow.normalized T z‖≤(10:ℝ)^110*Real.exp (-z.re^2/1600) := by
  have ht : 0 < T := by linarith
  have h := envelope T z ht hz
  have hp := polynomial_envelope T z.re ht.le
  have hy : z.im^2≤256 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg z.im) hz 2
    simpa only [sq_abs,show (16:ℝ)^2=256 by norm_num] using hsq
  have he : Real.exp (z.im^2/800)≤3 :=
    (Real.exp_le_exp.mpr (show z.im^2/800≤1 by linarith)).trans Real.exp_one_lt_three.le
  have hC : 1000000000*(T+4821)^12/T^2*3≤(10:ℝ)^110 := by
    calc
      _ ≤ 1000000000*(5000000000:ℝ)^12/(3000000000:ℝ)^2*3 := by
        gcongr <;> linarith [hT.1,hT.2]
      _ ≤ _ := by norm_num
  calc
    _ ≤ 1000000000*((T+4821)^12*Real.exp (z.re^2/1600))/T^2*
        Real.exp (-z.re^2/800+z.im^2/800) :=
      h.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (sq_nonneg T)) (Real.exp_pos _).le)
    _ = (1000000000*(T+4821)^12/T^2)*Real.exp (z.im^2/800)*Real.exp (-z.re^2/1600) := by
      rw [Real.exp_add]
      have hh : Real.exp (z.re^2/1600)*Real.exp (-z.re^2/800)=Real.exp (-z.re^2/1600) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        _ = (1000000000*(T+4821)^12/T^2)*Real.exp (z.im^2/800)*
          (Real.exp (z.re^2/1600)*Real.exp (-z.re^2/800)) := by ring
        _ = _ := by rw [hh]
    _ ≤ (1000000000*(T+4821)^12/T^2)*3*Real.exp (-z.re^2/1600) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
end RHHighXiEnvelope
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 10000
open Complex
namespace RHHighDampedWindow
lemma q_bound (T : ℝ) (z : ℂ) (hT:3000000000≤T) (hy:|z.im|≤16) :
    ‖RHHighXiWindow.q T z‖≤3+2*z.re^2/T^2 := by
  have ht:0<T:=by linarith
  have hy2:z.im^2≤256 := by
    have h:=pow_le_pow_left₀ (abs_nonneg _) hy 2
    norm_num only [sq_abs] at h
    exact h
  have hn:‖(T:ℂ)+z‖^2=(T+z.re)^2+z.im^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply,Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,zero_add]
    ring
  unfold RHHighXiWindow.q
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  have h:‖((T:ℂ)+z)^2+1/4‖≤‖(T:ℂ)+z‖^2+1/4 := by
    have hh:=norm_add_le (((T:ℂ)+z)^2) (1/4)
    rw [Complex.norm_pow,norm_div,norm_one,norm_ofNat] at hh
    exact hh
  apply (div_le_div_of_nonneg_right h (sq_nonneg T)).trans
  apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
  rw [hn]
  field_simp
  nlinarith [sq_nonneg (T-z.re),sq_nonneg (T-3000000000)]
lemma damp_bound (z : ℂ) (hy:|z.im|≤16) :
    ‖damp z‖≤3*Real.exp (-z.re^2/2048) := by
  have hy2:z.im^2≤256 := by
    have h:=pow_le_pow_left₀ (abs_nonneg _) hy 2
    norm_num only [sq_abs] at h
    exact h
  rw [damp_norm,Real.exp_add]
  apply (mul_le_mul_of_nonneg_left
    ((Real.exp_le_exp.mpr (show z.im^2/2048≤1 by linarith)).trans Real.exp_one_lt_three.le)
    (Real.exp_pos _).le).trans_eq
  ring
lemma quadratic_damped (x : ℝ) : x^2*Real.exp (-x^2/2048)≤2048 := by
  have h:=Real.add_one_le_exp (x^2/2048)
  have hp:0<Real.exp (x^2/2048):=Real.exp_pos _
  have he:Real.exp (-x^2/2048)=(Real.exp (x^2/2048))⁻¹ := by rw [←Real.exp_neg];congr 1;ring
  rw [he]
  apply (mul_inv_le_iff₀ hp).mpr
  linarith
lemma damp_q_bound (T : ℝ) (z : ℂ) (hT:3000000000≤T) (hy:|z.im|≤16) :
    ‖damp z‖*‖RHHighXiWindow.q T z‖≤10 := by
  have he:Real.exp (-z.re^2/2048)≤1:=Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z.re])
  have hq:=quadratic_damped z.re
  have ht:0<T:=by linarith
  have h:=mul_le_mul (damp_bound z hy) (q_bound T z hT hy) (norm_nonneg _) (by positivity)
  have heq:(3*Real.exp (-z.re^2/2048))*(3+2*z.re^2/T^2)=
      9*Real.exp (-z.re^2/2048)+6*(z.re^2*Real.exp (-z.re^2/2048))/T^2 := by ring
  rw [heq] at h
  have hd:6*(z.re^2*Real.exp (-z.re^2/2048))/T^2≤1 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    nlinarith [sq_nonneg (T-3000000000)]
  linarith
lemma strip_bound (T : ℝ) (hT:3000000000≤T ∧ T≤4000000000) (z : ℂ) (hy:|z.im|≤16) :
    ‖error T RHHighFourierPolynomial.polynomial z‖≤(10:ℝ)^115 := by
  have hd:‖damp z‖≤3 :=
    (damp_bound z hy).trans (by have h:=Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z.re] : -z.re^2/2048≤0);nlinarith)
  have hF:‖RHHighXiWindow.normalized T z‖≤(10:ℝ)^110 :=
    (RHHighXiEnvelope.gaussian_envelope T z hT hy).trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z.re])))
  have hP:‖RHHighFourierPolynomial.polynomial z‖≤(11/4:ℝ)^256 := by
    apply RHHighFourierPolynomial.polynomial_norm z |>.trans
    calc
      _ ≤ Real.exp 256 := Real.exp_le_exp.mpr (by
        have hp:=Real.pi_lt_four
        nlinarith [Real.pi_pos,abs_nonneg z.im])
      _ = (Real.exp 1)^256 := by simpa using (Real.exp_nat_mul (1:ℝ) (256:Nat)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  unfold error
  rw [norm_mul]
  have hs:=norm_sub_le (RHHighXiWindow.normalized T z)
    (RHHighXiWindow.q T z*RHHighFourierPolynomial.polynomial z)
  rw [norm_mul] at hs
  calc
    _ ≤ ‖damp z‖*(‖RHHighXiWindow.normalized T z‖+
        ‖RHHighXiWindow.q T z‖*‖RHHighFourierPolynomial.polynomial z‖) := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = ‖damp z‖*‖RHHighXiWindow.normalized T z‖+
        (‖damp z‖*‖RHHighXiWindow.q T z‖)*‖RHHighFourierPolynomial.polynomial z‖ := by ring
    _ ≤ 3*(10:ℝ)^110+10*(11/4:ℝ)^256 := add_le_add
      (mul_le_mul hd hF (norm_nonneg _) (by norm_num))
      (mul_le_mul (damp_q_bound T z hT.1 hy) hP (norm_nonneg _) (by norm_num))
    _ ≤ _ := by norm_num
end RHHighDampedWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaFourier
noncomputable def logKernel (s : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-(Real.exp y:ℂ)+s*(y:ℂ))
lemma gamma_log_integral (s : ℂ) (hs : 0<s.re) :
    Complex.Gamma s=∫ y : ℝ, logKernel s y := by
  rw [Complex.Gamma_eq_integral hs,Complex.GammaIntegral]
  have hi := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ: Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (Real.exp (-u):ℂ)*(u:ℂ)^(s-1))
  have him : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by
    simpa using Real.range_exp
  rw [him] at hi
  rw [hi]
  simp only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  unfold logKernel
  congr 1
  push_cast
  ring
lemma gaussian_factor (h : ℝ) (hh : 0<h) :
    ((Real.pi:ℂ)/(1/(2*(h:ℂ)^2)))^(1/2:ℂ)=(Real.sqrt (2*Real.pi):ℂ)*(h:ℂ) := by
  have he : (Real.pi:ℂ)/(1/(2*(h:ℂ)^2))=((2*Real.pi*h^2:ℝ):ℂ) := by push_cast;field_simp <;> ring
  rw [he]
  have hx : (0:ℝ)≤2*Real.pi*h^2 := by positivity
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hx,←Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh,Complex.ofReal_mul]
lemma exponential_gaussian_fourier (h : ℝ) (hh : 0<h) (a x : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (-(t:ℂ)^2/(2*(h:ℂ)^2)+(a:ℂ)*t)) x=
      (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
        Complex.exp ((h:ℂ)^2/2*((a:ℂ)-2*(Real.pi:ℂ)*I*x)^2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,←Complex.exp_add]
  have he (t : ℝ) : ((-2*Real.pi*t*x:ℝ):ℂ)*I+
      (-(t:ℂ)^2/(2*(h:ℂ)^2)+(a:ℂ)*t)=
      (-1/(2*(h:ℂ)^2))*(t:ℂ)^2+((a:ℂ)-2*(Real.pi:ℂ)*I*x)*t+0 := by push_cast;ring
  simp_rw [he]
  have hb : (-1/(2*(h:ℂ)^2)).re<0 := by
    have he : (-1/(2*(h:ℂ)^2))=((-1/(2*h^2):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  rw [integral_cexp_quadratic hb]
  have hf : -( -1/(2*(h:ℂ)^2))=1/(2*(h:ℂ)^2) := by ring
  rw [hf,gaussian_factor h hh]
  congr 1
  congr 1
  field_simp
  ring
lemma log_kernel_exp_rewrite (s : ℂ) (y : ℝ) :
    (Real.exp y) • ((Real.exp (-Real.exp y):ℂ)*(Real.exp y:ℂ)^(s-1))=logKernel s y := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  unfold logKernel
  congr 1
  push_cast
  ring
lemma log_kernel_integrable (s : ℂ) (hs : 0<s.re) : Integrable (logKernel s) := by
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (Real.exp (-u):ℂ)*(u:ℂ)^(s-1))).mp
      (he.symm ▸ Complex.GammaIntegral_convergent hs)
  simpa only [IntegrableOn,Measure.restrict_univ,abs_of_pos (Real.exp_pos _),
    log_kernel_exp_rewrite] using hi
noncomputable def window (T h t : ℝ) : ℂ :=
  Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
noncomputable def gammaWindow (T h t : ℝ) : ℂ :=
  Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t
noncomputable def Q (T h x y : ℝ) : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
    Complex.exp ((Real.pi*T/4:ℝ)+((h:ℂ)^2/2)*
      ((Real.pi/4:ℝ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2)
noncomputable def joint (T h x t y : ℝ) : ℂ :=
  logKernel (1/4+(((t+T)/2:ℝ):ℂ)*I) y*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma window_integrable (T h : ℝ) (hh : 0<h) : Integrable (window T h) := by
  have hb : (-(1/(2*(h:ℂ)^2))).re<0 := by
    have he : (-(1/(2*(h:ℂ)^2)))=((-1/(2*h^2):ℝ):ℂ) := by push_cast;ring
    rw [he,ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have he (t : ℝ) : window T h t=Complex.exp (
    (-(1/(2*(h:ℂ)^2)))*(t:ℂ)^2+(Real.pi/4:ℝ)*t+(Real.pi*T/4:ℝ)) := by
    unfold window
    congr 1
    push_cast
    ring
  change Integrable (fun t : ℝ => window T h t)
  simp_rw [he]
  exact integrable_cexp_quadratic' hb _ _
lemma log_kernel_norm (s : ℂ) (y : ℝ) :
    ‖logKernel s y‖=Real.exp (-Real.exp y+s.re*y) := by
  rw [logKernel,Complex.norm_exp]
  congr 1
  simp only [add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma joint_norm (T h x t y : ℝ) :
    ‖joint T h x t y‖=‖window T h t‖*‖logKernel (1/4) y‖ := by
  unfold joint
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one,log_kernel_norm,log_kernel_norm]
  have hr : (1/4+(((t+T)/2:ℝ):ℂ)*I:ℂ).re=(1/4:ℂ).re := by simp
  rw [hr]
  ring
lemma joint_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => joint T h x p.1 p.2) := by
  have hm := (window_integrable T h hh).norm.mul_prod
    (log_kernel_integrable (1/4) (by norm_num)).norm
  apply hm.mono'
  · have hc : Continuous (fun p : ℝ×ℝ => joint T h x p.1 p.2) := by
      unfold joint logKernel window
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    exact (joint_norm T h x p.1 p.2).le
lemma inner_joint (T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, joint T h x t y)=
      Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  let b : ℂ := -1/(2*(h:ℂ)^2)
  let c : ℂ := (Real.pi/4:ℝ)+I*((y/2-2*Real.pi*x:ℝ):ℂ)
  let d : ℂ := (-Real.exp y+y/4+Real.pi*T/4:ℝ)+I*(T:ℂ)*y/2
  have hb : b.re<0 := by
    have he : b=((-1/(2*h^2):ℝ):ℂ) := by dsimp [b];push_cast;ring
    rw [he,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have he (t : ℝ) : joint T h x t y=Complex.exp (b*(t:ℂ)^2+c*t+d) := by
    unfold joint logKernel window
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    dsimp [b,c,d]
    push_cast
    ring
  simp_rw [he]
  rw [integral_cexp_quadratic hb]
  have hn : -b=1/(2*(h:ℂ)^2) := by dsimp [b];ring
  rw [hn,gaussian_factor h hh]
  have hr : d-c^2/(4*b)=((-Real.exp y+y/4:ℝ):ℂ)+
      ((Real.pi*T/4:ℝ)+((h:ℂ)^2/2)*c^2+I*(T:ℂ)*y/2) := by
    dsimp [b,d]
    push_cast
    field_simp
    ring
  rw [hr,Complex.exp_add]
  dsimp [Q,c]
  ring
lemma gamma_window_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (gammaWindow T h) x=
      ∫ y : ℝ, Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  have hi (t : ℝ) : (∫ y : ℝ, joint T h x t y)=
      Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t*
        Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [joint,integral_mul_const]
    rw [←gamma_log_integral _ (by norm_num)]
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, ∫ y : ℝ, joint T h x t y := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      dsimp [gammaWindow]
      ring
    _ = ∫ y : ℝ, ∫ t : ℝ, joint T h x t y :=
      integral_integral_swap (joint_integrable T h x hh)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact inner_joint T h x y hh
end RHHighGammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set HurwitzZeta Filter Asymptotics
open scoped FourierTransform Topology
namespace RHHighThetaFourier
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0
lemma modif_convergent (s : ℂ) : MellinConvergent P.f_modif s := by
  exact mellinConvergent_of_isBigO_rpow P.hf_modif_int
    (P.isStrongFEPair_toStrongFEPair.hf_top (-(s.re+1))) (by linarith)
    (P.isStrongFEPair_toStrongFEPair.hf_zero (-(s.re-1))) (by linarith)
lemma modif_one_lt (t : ℝ) (ht : 1<t) :
    P.f_modif t=(evenKernel 0 t:ℂ)-1 := by
  simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,not_lt.2 ht.le,Set.indicator_of_notMem]
lemma modif_lt_one (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    P.f_modif t=(evenKernel 0 t:ℂ)-(t^(-(1:ℝ)/2):ℝ) := by
  simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,ht1,not_lt.2 ht1.le]
  norm_num
noncomputable def logMellin (s : ℂ) (y : ℝ) : ℂ :=
  P.f_modif (Real.exp y)*Complex.exp (s*(y:ℂ))
lemma modif_log_rewrite (s : ℂ) (y : ℝ) :
    (Real.exp y) • ((Real.exp y:ℂ)^(s-1)*P.f_modif (Real.exp y))=logMellin s y := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp]
  unfold logMellin
  have he : Complex.exp (y:ℂ)*Complex.exp ((y:ℂ)*(s-1))=Complex.exp (s*(y:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (y:ℂ)*Complex.exp ((y:ℂ)*(s-1)))*P.f_modif (Real.exp y) := by ring
    _ = _ := by rw [he];ring
lemma modif_log_integrable (s : ℂ) : Integrable (logMellin s) := by
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (u:ℂ)^(s-1)*P.f_modif u)).mp (he.symm ▸ modif_convergent s)
  simpa only [IntegrableOn,Measure.restrict_univ,abs_of_pos (Real.exp_pos _),modif_log_rewrite] using hi
lemma completed_log_mellin (s : ℂ) :
    completedRiemannZeta₀ s=(∫ y : ℝ, logMellin (s/2) y)/2 := by
  have hi := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (u:ℂ)^(s/2-1)*P.f_modif u)
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
  rw [he] at hi
  have hd : completedRiemannZeta₀ s=mellin P.f_modif (s/2)/2 := rfl
  rw [hd,mellin]
  simp only [smul_eq_mul]
  rw [hi]
  simp only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _),modif_log_rewrite]
open RHHighGammaFourier
noncomputable def thetaJoint (T h x t y : ℝ) : ℂ :=
  (logMellin ((1/2+((t+T:ℝ):ℂ)*I)/2) y/2)*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma log_mellin_norm (s : ℂ) (y : ℝ) :
    ‖logMellin s y‖=‖P.f_modif (Real.exp y)‖*Real.exp (s.re*y) := by
  rw [logMellin,norm_mul,Complex.norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma theta_joint_norm (T h x t y : ℝ) :
    ‖thetaJoint T h x t y‖=‖window T h t‖*(‖logMellin (1/4) y‖/2) := by
  unfold thetaJoint
  rw [norm_mul,norm_mul,norm_div,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one,log_mellin_norm,log_mellin_norm]
  norm_num
  ring
lemma theta_joint_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => thetaJoint T h x p.1 p.2) := by
  have hm := (window_integrable T h hh).norm.mul_prod
    ((modif_log_integrable (1/4)).norm.div_const 2)
  apply hm.mono'
  · have hf := P.hf_modif_int.aestronglyMeasurable
    have hm : AEStronglyMeasurable (fun y : ℝ => P.f_modif (Real.exp y)) volume := by
      have hi := modif_log_integrable (0:ℂ)
      convert! hi.aestronglyMeasurable using 1
      ext y
      simp [logMellin]
    have he : Continuous (fun p : ℝ×ℝ =>
      Complex.exp (((1/2+((p.1+T:ℝ):ℂ)*I)/2)*(p.2:ℂ))/2*window T h p.1*
        Complex.exp (((-2*Real.pi*p.1*x:ℝ):ℂ)*I)) := by unfold window;fun_prop
    have hmeas : AEStronglyMeasurable (fun p : ℝ×ℝ =>
      P.f_modif (Real.exp p.2)*(Complex.exp (((1/2+((p.1+T:ℝ):ℂ)*I)/2)*(p.2:ℂ))/2*window T h p.1*
        Complex.exp (((-2*Real.pi*p.1*x:ℝ):ℂ)*I))) (volume.prod volume) :=
      hm.comp_snd.mul he.aestronglyMeasurable
    convert! hmeas using 1
    ext p
    dsimp [thetaJoint,logMellin]
    ring
  · filter_upwards [] with p
    exact (theta_joint_norm T h x p.1 p.2).le
lemma theta_joint_factor (T h x t y : ℝ) :
    thetaJoint T h x t y=
      (P.f_modif (Real.exp y)*Complex.exp (Real.exp y:ℂ)/2)*joint T h x t y := by
  unfold thetaJoint logMellin joint logKernel
  have he : ((1/2+((t+T:ℝ):ℂ)*I)/2)*(y:ℂ)=
      (Real.exp y:ℂ)+(-(Real.exp y:ℂ)+(1/4+(((t+T)/2:ℝ):ℂ)*I)*(y:ℂ)) := by
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring
lemma theta_joint_inner (T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, thetaJoint T h x t y)=
      (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y := by
  simp_rw [theta_joint_factor]
  rw [integral_const_mul,inner_joint T h x y hh]
  have he : Complex.exp (Real.exp y:ℂ)*Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)=
      Complex.exp ((y/4:ℝ):ℂ) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (P.f_modif (Real.exp y)*(Complex.exp (Real.exp y:ℂ)*
      Complex.exp ((-Real.exp y+y/4:ℝ):ℂ))/2)*Q T h x y := by ring
    _ = _ := by rw [he]
noncomputable def entireWindow (T h t : ℝ) : ℂ :=
  completedRiemannZeta₀ (1/2+((t+T:ℝ):ℂ)*I)*window T h t
lemma entire_window_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (entireWindow T h) x=
      ∫ y : ℝ, (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y := by
  have hi (t : ℝ) : (∫ y : ℝ, thetaJoint T h x t y)=
      entireWindow T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [thetaJoint,integral_mul_const,integral_div]
    rw [←completed_log_mellin]
    rfl
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, ∫ y : ℝ, thetaJoint T h x t y := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = ∫ y : ℝ, ∫ t : ℝ, thetaJoint T h x t y :=
      integral_integral_swap (theta_joint_integrable T h x hh)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact theta_joint_inner T h x y hh
end RHHighThetaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighPoleFourier
open RHHighGammaFourier
noncomputable def sline (ε T t : ℝ) : ℂ := 1/2+(ε:ℂ)*I*(t+T:ℝ)
lemma sline_re (ε T t : ℝ) : (sline ε T t).re=1/2 := by simp [sline]
noncomputable def poleJoint (ε T h x t y : ℝ) : ℂ :=
  Complex.exp (-(sline ε T t/2)*(y:ℂ))*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma laplace_half (s : ℂ) (hs : 0<s.re) :
    (∫ y : ℝ in Set.Ioi 0, Complex.exp (-(s/2)*(y:ℂ)))=2/s := by
  have h := integral_exp_mul_complex_Ioi (a:=-(s/2)) (by simp;linarith) 0
  simpa using h
lemma pole_joint_norm (ε T h x t y : ℝ) :
    ‖poleJoint ε T h x t y‖=‖window T h t‖*Real.exp (-y/4) := by
  rw [poleJoint,norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]
  have hr : (-(sline ε T t/2)*(y:ℂ)).re= -y/4 := by simp [sline];ring
  rw [hr]
  ring
lemma pole_joint_integrable (ε T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => poleJoint ε T h x p.1 p.2)
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
  have hy : IntegrableOn (fun y : ℝ => Real.exp (-y/4)) (Set.Ioi 0) := by
    convert! integrableOn_exp_mul_Ioi (a:=(-1/4:ℝ)) (by norm_num) 0 using 1
    ext y
    congr 1
    ring
  have hm := (window_integrable T h hh).norm.mul_prod hy
  apply hm.mono'
  · have hc : Continuous (fun p : ℝ×ℝ => poleJoint ε T h x p.1 p.2) := by
      unfold poleJoint sline window
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    exact (pole_joint_norm ε T h x p.1 p.2).le
lemma pole_joint_factor (ε T h x t y : ℝ) :
    poleJoint ε T h x t y=
      Complex.exp ((Real.exp (-ε*y)-(-ε*y)/4-y/4:ℝ):ℂ)*joint T h x t (-ε*y) := by
  unfold poleJoint sline joint logKernel
  conv_rhs => rw [←mul_assoc,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
lemma pole_joint_inner (ε T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, poleJoint ε T h x t y)=
      Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  simp_rw [pole_joint_factor]
  rw [integral_const_mul,inner_joint T h x (-ε*y) hh]
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
noncomputable def poleWindow (ε T h t : ℝ) : ℂ := window T h t/sline ε T t
lemma pole_window_fourier (ε T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow ε T h) x=
      (1/2:ℂ)*∫ y : ℝ in Set.Ioi 0, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  have hi (t : ℝ) : (1/2:ℂ)*(∫ y : ℝ in Set.Ioi 0, poleJoint ε T h x t y)=
      poleWindow ε T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [poleJoint,integral_mul_const]
    rw [laplace_half _ (by rw [sline_re];norm_num)]
    unfold poleWindow
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (1/2:ℂ)*∫ t : ℝ, ∫ y : ℝ in Set.Ioi 0, poleJoint ε T h x t y := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = (1/2:ℂ)*∫ y : ℝ in Set.Ioi 0, ∫ t : ℝ, poleJoint ε T h x t y := by
      rw [integral_integral_swap (pole_joint_integrable ε T h x hh)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      exact pole_joint_inner ε T h x y hh
end RHHighPoleFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaFourier
lemma Q_norm (T h x y : ℝ) (hh : 0<h) :
    ‖Q T h x y‖=Real.sqrt (2*Real.pi)*h*
      Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2) := by
  rw [Q,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hh,
    Complex.norm_exp]
  congr 1
  simp only [add_re,mul_re,div_re,ofReal_re,ofReal_im,I_re,I_im,pow_two]
  norm_num
  ring
lemma real_quadratic_integrable (b c d : ℝ) (hb : b<0) :
    Integrable (fun y : ℝ => Real.exp (b*y^2+c*y+d)) := by
  have h := (integrable_cexp_quadratic' (b:= (b:ℂ)) (by simpa using hb) (c:ℂ) (d:ℂ)).norm
  convert! h using 1
  ext y
  rw [Complex.norm_exp]
  congr 1
  simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_add,Complex.ofReal_re]
noncomputable def Qmajorant (T h x y : ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi)*h/Real.pi)*
    Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2-3*y/4)
lemma Qmajorant_integrable (T h x : ℝ) (hh : 0<h) : Integrable (Qmajorant T h x) := by
  have he (y : ℝ) : Qmajorant T h x y=(Real.sqrt (2*Real.pi)*h/Real.pi)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x-3/4)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    unfold Qmajorant
    congr 1
    congr 1
    ring
  change Integrable (fun y : ℝ => Qmajorant T h x y)
  simp_rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
lemma Qweighted_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun y : ℝ => Real.exp (y/4)*‖Q T h x y‖) := by
  have he (y : ℝ) : Real.exp (y/4)*‖Q T h x y‖=
      (Real.sqrt (2*Real.pi)*h)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    rw [Q_norm T h x y hh]
    have hp : (y/4)+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
        (-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y+
          (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2) := by ring
    calc
      _ = (Real.sqrt (2*Real.pi)*h)*
        (Real.exp (y/4)*Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
      _ = _ := by rw [←Real.exp_add,hp]
  simp_rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
end RHHighGammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaFourier
noncomputable def dirichletWeight (T a : ℝ) : ℂ :=
  Complex.exp (-(1/2+I*(T:ℂ))*(Real.log a:ℂ))
lemma Q_translation (T h x y a : ℝ) (ha : 0<a) :
    Q T h (x+Real.log a/(2*Real.pi)) (y+2*Real.log a)=
      Q T h x y*Complex.exp (I*(T:ℂ)*(Real.log a:ℂ)) := by
  unfold Q
  have he : ((y+2*Real.log a)/2-2*Real.pi*(x+Real.log a/(2*Real.pi)):ℝ)=
      y/2-2*Real.pi*x := by field_simp;ring
  rw [he]
  conv_rhs => rw [mul_assoc,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma gamma_fourier_dirichlet_shift (T h x a : ℝ) (hh : 0<h) (ha : 0<a) :
    dirichletWeight T a*𝓕 (gammaWindow T h) (x+Real.log a/(2*Real.pi))=
      ∫ y : ℝ, Complex.exp ((-a^2*Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  rw [gamma_window_fourier T h _ hh]
  rw [←integral_const_mul]
  have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ =>
    dirichletWeight T a*(Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*
      Q T h (x+Real.log a/(2*Real.pi)) y)) (2*Real.log a)
  rw [←ht]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Q_translation T h x y a ha]
  have hexp : Real.exp (y+2*Real.log a)=a^2*Real.exp y := by
    rw [Real.exp_add,show 2*Real.log a=Real.log a+Real.log a by ring,Real.exp_add,Real.exp_log ha]
    ring
  rw [hexp]
  unfold dirichletWeight
  have he : -(1/2+I*(T:ℂ))*(Real.log a:ℂ)+
      ((-a^2*Real.exp y+(y+2*Real.log a)/4:ℝ):ℂ)+
      I*(T:ℂ)*(Real.log a:ℂ)=((-a^2*Real.exp y+y/4:ℝ):ℂ) := by push_cast;ring
  calc
    _ = (Complex.exp (-(1/2+I*(T:ℂ))*(Real.log a:ℂ))*
      Complex.exp ((-a^2*Real.exp y+(y+2*Real.log a)/4:ℝ):ℂ)*
      Complex.exp (I*(T:ℂ)*(Real.log a:ℂ)))*Q T h x y := by ring
    _ = _ := by rw [←Complex.exp_add,←Complex.exp_add,he]
end RHHighGammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Real MeasureTheory Set HurwitzZeta Filter
open scoped Topology
namespace RHHighThetaSeries
noncomputable def psi (u : ℝ) : ℝ := (evenKernel 0 u-1)/2
lemma hasSum_psi (u : ℝ) (hu : 0<u) :
    HasSum (fun n : Nat => Real.exp (-Real.pi*(n+1:ℝ)^2*u)) (psi u) := by
  have h := (hasSum_nat_cosKernel₀ 0 hu).div_const 2
  convert! h using 1
  · ext n
    simp
  · simp only [QuotientAddGroup.mk_zero]
    rw [←evenKernel_eq_cosKernel_of_zero]
    rfl
lemma psi_nonneg (u : ℝ) (hu : 0<u) : 0≤psi u := by
  rw [←(hasSum_psi u hu).tsum_eq]
  exact tsum_nonneg (fun n => (Real.exp_pos _).le)
lemma psi_le (u : ℝ) (hu : 0<u) : psi u≤1/(Real.pi*u) := by
  let q := Real.exp (-Real.pi*u)
  have hp : 0<Real.pi*u := mul_pos Real.pi_pos hu
  have hqp : 0<q := Real.exp_pos _
  have hq1 : q<1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hqn : ‖q‖<1 := by simpa only [Real.norm_eq_abs,abs_of_pos hqp] using hq1
  have hg : HasSum (fun n : Nat => q^(n+1)) (q/(1-q)) := by
    convert! (hasSum_geometric_of_norm_lt_one hqn).mul_left q using 1
    · ext n
      rw [pow_succ]
      ring
  have hb (n : Nat) : Real.exp (-Real.pi*(n+1:ℝ)^2*u)≤q^(n+1) := by
    have hn : 1≤(n+1:ℝ) := by have h := Nat.cast_nonneg (α:=ℝ) n; linarith
    have hpow : (n+1:ℝ)≤(n+1:ℝ)^2 := by nlinarith
    have he : q^(n+1)=Real.exp (-Real.pi*(n+1:ℝ)*u) := by
      dsimp [q]
      rw [←Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hpow hp.le]
  have hs : psi u≤q/(1-q) := by
    rw [←(hasSum_psi u hu).tsum_eq,←hg.tsum_eq]
    exact (hasSum_psi u hu).summable.tsum_le_tsum hb hg.summable
  have hexp : q*Real.exp (Real.pi*u)=1 := by
    dsimp [q]
    rw [←Real.exp_add]
    simp
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.pi*u)) hqp.le
  rw [hexp] at he
  apply hs.trans
  apply (div_le_div_iff₀ (by linarith : 0<1-q) hp).mpr
  nlinarith
lemma finite_psi_sum_le (u : ℝ) (hu : 0<u) (N : Nat) :
    (∑ n ∈ Finset.range N, Real.exp (-Real.pi*(n+1:ℝ)^2*u))≤1/(Real.pi*u) := by
  apply le_trans _ (psi_le u hu)
  rw [←(hasSum_psi u hu).tsum_eq]
  exact (hasSum_psi u hu).summable.sum_le_tsum (Finset.range N) (fun n _ => (Real.exp_pos _).le)
end RHHighThetaSeries
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighThetaGamma
open RHHighGammaFourier RHHighThetaSeries
noncomputable def seriesKernel (n : Nat) (T h x y : ℝ) : ℂ :=
  Complex.exp ((-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4:ℝ):ℂ)*Q T h x y
lemma series_kernel_norm (n : Nat) (T h x y : ℝ) :
    ‖seriesKernel n T h x y‖=
      Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4)*‖Q T h x y‖ := by
  rw [seriesKernel,norm_mul,Complex.norm_exp,Complex.ofReal_re]
lemma series_kernel_integrable (n : Nat) (T h x : ℝ) (hh : 0<h) :
    Integrable (seriesKernel n T h x) := by
  have hc : Continuous (seriesKernel n T h x) := by unfold seriesKernel Q;fun_prop
  apply (Qweighted_integrable T h x hh).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [series_kernel_norm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hp : 0≤Real.pi*(n+1:ℝ)^2*Real.exp y := by positivity
  linarith
lemma Qmajorant_eq (T h x y : ℝ) (hh : 0<h) :
    Qmajorant T h x y=
      (1/(Real.pi*Real.exp y))*(Real.exp (y/4)*‖Q T h x y‖) := by
  rw [Q_norm T h x y hh]
  have he : 1/(Real.pi*Real.exp y)=(1/Real.pi)*Real.exp (-y) := by
    rw [Real.exp_neg]
    ring
  rw [he]
  have hp : (-y)+(y/4)+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
      Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2-3*y/4 := by ring
  unfold Qmajorant
  calc
    _ = (1/Real.pi)*(Real.sqrt (2*Real.pi)*h)*
      (Real.exp (-y)*Real.exp (y/4)*Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by
      rw [←Real.exp_add,←Real.exp_add,hp]
      ring
    _ = _ := by ring
lemma finite_kernel_norm_le (T h x y : ℝ) (hh : 0<h) (N : Nat) :
    (∑ n ∈ Finset.range N, ‖seriesKernel n T h x y‖)≤Qmajorant T h x y := by
  simp_rw [series_kernel_norm]
  have he (n : Nat) : Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4)*‖Q T h x y‖=
      Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y)*(Real.exp (y/4)*‖Q T h x y‖) := by
    rw [Real.exp_add]
    ring
  simp_rw [he]
  rw [←Finset.sum_mul,Qmajorant_eq T h x y hh]
  exact mul_le_mul_of_nonneg_right (finite_psi_sum_le (Real.exp y) (Real.exp_pos _) N) (by positivity)
lemma kernel_integral_norm_summable (T h x : ℝ) (hh : 0<h) :
    Summable (fun n : Nat => ∫ y : ℝ, ‖seriesKernel n T h x y‖) := by
  apply summable_of_sum_range_le (fun n => integral_nonneg (fun y => norm_nonneg _))
  intro N
  rw [←integral_finset_sum (Finset.range N) (fun n _ => (series_kernel_integrable n T h x hh).norm)]
  exact integral_mono (integrable_finsetSum _ (fun n _ => (series_kernel_integrable n T h x hh).norm))
    (Qmajorant_integrable T h x hh) (fun y => finite_kernel_norm_le T h x y hh N)
lemma hasSum_kernel_point (T h x y : ℝ) :
    HasSum (fun n : Nat => seriesKernel n T h x y)
      ((psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y) := by
  have hbase : HasSum (fun n : Nat => (Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y):ℂ))
      (psi (Real.exp y):ℂ) := hasSum_ofReal.mpr (hasSum_psi (Real.exp y) (Real.exp_pos _))
  have hsum := (hbase.mul_right (Complex.exp ((y/4:ℝ):ℂ))).mul_right (Q T h x y)
  convert! hsum using 1
  ext n
  unfold seriesKernel
  rw [Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma sum_kernel_integral (T h x : ℝ) (hh : 0<h) :
    (∑' n : Nat, ∫ y : ℝ, seriesKernel n T h x y)=
      ∫ y : ℝ, (psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y := by
  have hsum := hasSum_integral_of_summable_integral_norm
    (fun n => series_kernel_integrable n T h x hh) (kernel_integral_norm_summable T h x hh)
  rw [hsum.tsum_eq]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (hasSum_kernel_point T h x y).tsum_eq
end RHHighThetaGamma
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaFourier
lemma weighted_Q_integrable (c T h x : ℝ) (hh : 0<h) :
    Integrable (fun y : ℝ => Complex.exp ((c*y:ℝ):ℂ)*Q T h x y) := by
  have he (y : ℝ) : ‖Complex.exp ((c*y:ℝ):ℂ)*Q T h x y‖=
      (Real.sqrt (2*Real.pi)*h)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+c)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,Q_norm T h x y hh]
    have hp : c*y+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
        (-h^2/8)*y^2+(h^2*Real.pi*x+c)*y+
          (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2) := by ring
    calc
      _ = (Real.sqrt (2*Real.pi)*h)*(Real.exp (c*y)*
        Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
      _ = _ := by rw [←Real.exp_add,hp]
  have hi : Integrable (fun y : ℝ => ‖Complex.exp ((c*y:ℝ):ℂ)*Q T h x y‖) := by
    simp_rw [he]
    exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
  have hc : Continuous (fun y : ℝ => Complex.exp ((c*y:ℝ):ℂ)*Q T h x y) := by unfold Q;fun_prop
  exact (integrable_norm_iff hc.aestronglyMeasurable).mp hi
end RHHighGammaFourier
namespace RHHighThetaGamma
open RHHighGammaFourier RHHighThetaSeries
noncomputable def psiKernel (T h x y : ℝ) : ℂ :=
  (psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y
lemma psi_kernel_integrable (T h x : ℝ) (hh : 0<h) : Integrable (psiKernel T h x) := by
  have ht : Continuous (fun y : ℝ => HurwitzZeta.evenKernel 0 (Real.exp y)) :=
    (HurwitzZeta.continuousOn_evenKernel 0).comp_continuous Real.continuous_exp (fun y => Real.exp_pos y)
  have hc : Continuous (psiKernel T h x) := by
    have hp : Continuous (fun y : ℝ => psi (Real.exp y)) := by
      unfold psi
      exact (ht.sub continuous_const).div_const _
    unfold psiKernel Q
    fun_prop
  apply (Qmajorant_integrable T h x hh).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [psiKernel,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (psi_nonneg (Real.exp y) (Real.exp_pos _)),Complex.norm_exp,Complex.ofReal_re]
  rw [Qmajorant_eq T h x y hh]
  have he : psi (Real.exp y)*Real.exp (y/4)*‖Q T h x y‖=
      psi (Real.exp y)*(Real.exp (y/4)*‖Q T h x y‖) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (psi_le (Real.exp y) (Real.exp_pos _)) (by positivity)
end RHHighThetaGamma
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaFourier
lemma croot_of_pos (a : ℝ) (ha : 0<a) : (a:ℂ)^(1/2:ℂ)=(Real.sqrt a:ℂ) := by
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow ha.le,←Real.sqrt_eq_rpow]
lemma mass_prefactor (h : ℝ) (hh : 0<h) :
    (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*((Real.pi:ℂ)/(h^2/8))^(1/2:ℂ)/2=2*(Real.pi:ℂ) := by
  have he : (Real.pi:ℂ)/(h^2/8)=((8*Real.pi/h^2:ℝ):ℂ) := by push_cast;ring
  rw [he,croot_of_pos _ (by positivity)]
  have hs : Real.sqrt (8*Real.pi/h^2)=2*Real.sqrt (2*Real.pi)/h := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh]
    rw [show (8*Real.pi:ℝ)=4*(2*Real.pi) by ring,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs]
  have hn : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
  have hs2 : (Real.sqrt (2*Real.pi):ℂ)^2=2*(Real.pi:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  push_cast
  calc
    _ = (Real.sqrt (2*Real.pi):ℂ)^2 := by field_simp [hn] <;> ring
    _ = _ := hs2
lemma gaussian_pole_mass (T h x : ℝ) (hh : 0<h) :
    (1/2:ℂ)*(∫ y : ℝ, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y)=
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  let b : ℂ := -(h:ℂ)^2/8
  let c : ℂ := ((h^2*Real.pi*x-1/4:ℝ):ℂ)+I*((h^2*Real.pi/8+T/2:ℝ):ℂ)
  let d : ℂ := ((Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2:ℝ):ℂ)-I*((h^2*Real.pi^2*x/2:ℝ):ℂ)
  have hb : b.re<0 := by
    have he : b=((-h^2/8:ℝ):ℂ) := by dsimp [b];push_cast;rfl
    rw [he,ofReal_re]
    nlinarith [sq_pos_of_pos hh]
  have he (y : ℝ) : Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y=
      (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*Complex.exp (b*(y:ℂ)^2+c*y+d) := by
    unfold Q
    have hp : ((-y/4:ℝ):ℂ)+((Real.pi*T/4:ℝ):ℂ)+((h:ℂ)^2/2)*
        (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2=
        b*(y:ℂ)^2+c*y+d := by dsimp [b,c,d];push_cast;ring_nf <;> simp only [Complex.I_sq] <;> ring
    calc
      _ = (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
        (Complex.exp ((-y/4:ℝ):ℂ)*Complex.exp (
          ((Real.pi*T/4:ℝ):ℂ)+((h:ℂ)^2/2)*
          (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2)) := by ring
      _ = _ := by rw [←Complex.exp_add];congr 2;simpa only [add_assoc] using hp
  simp_rw [he]
  rw [integral_const_mul,integral_cexp_quadratic hb]
  have hn : -b=(h:ℂ)^2/8 := by dsimp [b];ring
  rw [hn]
  have he : d-c^2/(4*b)=
      ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
      I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ) := by
    dsimp [b,c,d]
    push_cast
    have hne : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
    field_simp [hne]
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  rw [he]
  have hp := mass_prefactor h hh
  calc
    _ = ((Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*((Real.pi:ℂ)/(h^2/8))^(1/2:ℂ)/2)*
      Complex.exp (((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by ring
    _ = _ := by rw [hp]
end RHHighGammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighPlattFourier
open RHHighGammaFourier RHHighThetaFourier RHHighThetaGamma RHHighThetaSeries
open RHHighPoleFourier
noncomputable def dirichletTerm (T h x : ℝ) (n : Nat) : ℂ :=
  dirichletWeight T ((n+1:ℝ)*Real.sqrt Real.pi)*
    𝓕 (gammaWindow T h) (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi))
lemma dirichlet_term_eq (T h x : ℝ) (hh : 0<h) (n : Nat) :
    dirichletTerm T h x n=∫ y : ℝ, seriesKernel n T h x y := by
  unfold dirichletTerm
  rw [gamma_fourier_dirichlet_shift T h x _ hh (by positivity)]
  have he : ((n+1:ℝ)*Real.sqrt Real.pi)^2=Real.pi*(n+1:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt Real.pi_pos.le]
    ring
  simp only [he,seriesKernel,neg_mul]
lemma dirichlet_series_fourier (T h x : ℝ) (hh : 0<h) :
    (∑' n : Nat, dirichletTerm T h x n)=∫ y : ℝ, psiKernel T h x y := by
  simp_rw [dirichlet_term_eq T h x hh]
  exact sum_kernel_integral T h x hh
noncomputable def positiveKernel (T h x y : ℝ) : ℂ :=
  Complex.exp ((y/4:ℝ):ℂ)*Q T h x y
noncomputable def negativeKernel (T h x y : ℝ) : ℂ :=
  Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y
lemma positive_kernel_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (positiveKernel T h x) := by
  convert weighted_Q_integrable (1/4) T h x hh using 1
  ext y
  simp only [positiveKernel,one_div_mul_eq_div]
lemma negative_kernel_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (negativeKernel T h x) := by
  convert weighted_Q_integrable (-1/4) T h x hh using 1
  ext y
  unfold negativeKernel
  congr 2
  congr 1
  ring
lemma theta_kernel_eq (T h x : ℝ) :
    (fun y : ℝ => (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y)
      =ᵐ[volume] (fun y : ℝ => psiKernel T h x y+
        (Iio (0:ℝ)).indicator (fun y => (positiveKernel T h x y-negativeKernel T h x y)/2) y) := by
  have hae : ∀ᵐ y : ℝ ∂volume, y≠0 := by
    rw [ae_iff]
    simp
  filter_upwards [hae] with y hy
  rcases lt_or_gt_of_ne hy with hn|hp
  · rw [Set.indicator_of_mem (show y∈Iio (0:ℝ) from hn),modif_lt_one _ (Real.exp_pos _) (by simpa using hn)]
    have he : Real.exp y^(-(1:ℝ)/2)=Real.exp (-y/2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      ring
    rw [he]
    unfold psiKernel positiveKernel negativeKernel psi
    push_cast
    have hm : (Real.exp (-y/2):ℂ)*Complex.exp ((y/4:ℝ):ℂ)=
        Complex.exp ((-y/4:ℝ):ℂ) := by
      rw [Complex.ofReal_exp,←Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (((HurwitzZeta.evenKernel 0 (Real.exp y):ℂ)-1)/2)*
          Complex.exp ((y/4:ℝ):ℂ)*Q T h x y+
          (Complex.exp ((y/4:ℝ):ℂ)*Q T h x y-
            ((Real.exp (-y/2):ℂ)*Complex.exp ((y/4:ℝ):ℂ))*Q T h x y)/2 := by
        simp only [Complex.ofReal_exp]
        push_cast
        ring
      _ = _ := by rw [hm];push_cast;rfl
  · rw [Set.indicator_of_notMem (by simpa using hp.le),modif_one_lt _ (by simpa using hp)]
    simp only [add_zero]
    unfold psiKernel psi
    push_cast
    ring
lemma entire_fourier_correction (T h x : ℝ) (hh : 0<h) :
    𝓕 (entireWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)+
      ((∫ y : ℝ in Iio 0, positiveKernel T h x y)-
        (∫ y : ℝ in Iio 0, negativeKernel T h x y))/2 := by
  rw [entire_window_fourier T h x hh,integral_congr_ae (theta_kernel_eq T h x)]
  have hi : Integrable (fun y : ℝ => (positiveKernel T h x y-negativeKernel T h x y)/2) :=
    ((positive_kernel_integrable T h x hh).sub (negative_kernel_integrable T h x hh)).div_const (2:ℂ)
  rw [integral_add (psi_kernel_integrable T h x hh) (hi.indicator measurableSet_Iio),
    integral_indicator measurableSet_Iio,integral_div,
    integral_sub (positive_kernel_integrable T h x hh).integrableOn
      (negative_kernel_integrable T h x hh).integrableOn,
    ←dirichlet_series_fourier T h x hh]
noncomputable def fullWindow (T h t : ℝ) : ℂ :=
  completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*I)*window T h t
lemma full_window_eq (T h t : ℝ) :
    fullWindow T h t=entireWindow T h t-poleWindow 1 T h t-poleWindow (-1) T h t := by
  unfold fullWindow entireWindow poleWindow sline
  rw [completedRiemannZeta_eq]
  have hs : 1-(1/2+((t+T:ℝ):ℂ)*I)=1/2+(-1:ℂ)*I*((t+T:ℝ):ℂ) := by ring
  rw [hs]
  push_cast
  ring
end RHHighPlattFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighPlattFourier
open RHHighGammaFourier RHHighThetaFourier RHHighThetaGamma RHHighPoleFourier
noncomputable def modulate (f : ℝ→ℂ) (x t : ℝ) : ℂ :=
  f t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma entire_modulate_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (modulate (entireWindow T h) x) := by
  convert (theta_joint_integrable T h x hh).integral_prod_left using 1
  ext t
  simp only [thetaJoint,integral_mul_const,integral_div]
  rw [←completed_log_mellin]
  rfl
lemma pole_modulate_integrable (ε T h x : ℝ) (hh : 0<h) :
    Integrable (modulate (poleWindow ε T h) x) := by
  convert ((pole_joint_integrable ε T h x hh).integral_prod_left).const_mul (1/2:ℂ) using 1
  ext t
  simp only [poleJoint,integral_mul_const]
  rw [laplace_half _ (by rw [sline_re];norm_num)]
  unfold poleWindow modulate
  ring
lemma full_fourier_decomposition (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=𝓕 (entireWindow T h) x-
      𝓕 (poleWindow 1 T h) x-𝓕 (poleWindow (-1) T h) x := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  have he (t : ℝ) : Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*fullWindow T h t=
      modulate (entireWindow T h) x t-modulate (poleWindow 1 T h) x t-
        modulate (poleWindow (-1) T h) x t := by
    rw [full_window_eq]
    unfold modulate
    ring
  simp_rw [he]
  have hisub : Integrable (fun t : ℝ => modulate (entireWindow T h) x t-modulate (poleWindow 1 T h) x t) :=
    (entire_modulate_integrable T h x hh).sub (pole_modulate_integrable 1 T h x hh)
  rw [integral_sub hisub
    (pole_modulate_integrable (-1) T h x hh),
    integral_sub (entire_modulate_integrable T h x hh) (pole_modulate_integrable 1 T h x hh)]
  simp only [modulate,mul_comm]
lemma pole_plus_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow 1 T h) x=(∫ y : ℝ in Iio 0, positiveKernel T h x y)/2 := by
  rw [pole_window_fourier 1 T h x hh]
  have he : (fun y : ℝ => Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-1*y))=
      (fun y : ℝ => positiveKernel T h x (-y)) := by
    ext y
    simp [positiveKernel]
  rw [he,integral_comp_neg_Ioi,neg_zero,integral_Iic_eq_integral_Iio]
  ring
lemma pole_minus_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow (-1) T h) x=(∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)/2 := by
  rw [pole_window_fourier (-1) T h x hh]
  simp only [neg_neg,one_mul]
  change (1/2:ℂ)*(∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)=_
  ring
lemma full_fourier_series (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)-
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  rw [full_fourier_decomposition T h x hh,entire_fourier_correction T h x hh,
    pole_plus_fourier T h x hh,pole_minus_fourier T h x hh]
  have hi : (∫ y : ℝ in Iio 0, negativeKernel T h x y)+
      (∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)=∫ y : ℝ, negativeKernel T h x y := by
    rw [←integral_Iic_eq_integral_Iio]
    exact intervalIntegral.integral_Iic_add_Ioi (negative_kernel_integrable T h x hh).integrableOn
      (negative_kernel_integrable T h x hh).integrableOn
  have hm := gaussian_pole_mass T h x hh
  change (1/2:ℂ)*(∫ y : ℝ, negativeKernel T h x y)=_ at hm
  rw [←hm,←hi]
  ring
lemma full_fourier_remainder_norm (T h x : ℝ) (hh : 0<h) :
    ‖𝓕 (fullWindow T h) x-(∑' n : Nat, dirichletTerm T h x n)‖=
      2*Real.pi*Real.exp (1/(8*h^2)-T^2/(2*h^2)-Real.pi*x) := by
  rw [full_fourier_series T h x hh]
  simp only [sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_exp,
    Complex.add_re,Complex.ofReal_re]
  simp
  rw [abs_of_pos Real.pi_pos]
  have he : ((T:ℂ)/(2*(h:ℂ)^2)).im=0 := by
    rw [show (T:ℂ)/(2*(h:ℂ)^2)=((T/(2*h^2):ℝ):ℂ) by push_cast;rfl]
    rfl
  rw [he,add_zero]
end RHHighPlattFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGaussianTaylor
open RHHighGammaFourier RHHighTaylor
lemma gamma_window_norm (T h t : ℝ) : ‖gammaWindow T h t‖≤6*Real.exp (-t^2/(2*h^2)) := by
  have h := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t h 0
  simpa only [pow_zero,mul_one,one_mul,gammaWindow,window,Complex.ofReal_exp] using h
lemma pow_exp_factorial (v : ℝ) (hv : 0≤v) (n : Nat) :
    v^n*Real.exp (-v)≤(n.factorial:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp v hv n
  rw [div_le_iff₀ (show (0:ℝ)<n.factorial by positivity)] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-v)).le
  have he : Real.exp v*(n.factorial:ℝ)*Real.exp (-v)=(n.factorial:ℝ) := by
    calc
      _ = n.factorial*(Real.exp v*Real.exp (-v)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  simpa only [he] using hm
lemma young_gaussian (t : ℝ) :
    Real.exp (-t^2/800+|t|/128)≤3*Real.exp (-t^2/1600) := by
  have hy : -t^2/800+|t|/128≤1-t^2/1600 := by
    nlinarith [sq_abs t,sq_nonneg (|t|-25/4)]
  calc
    _ ≤ Real.exp (1-t^2/1600) := Real.exp_le_exp.mpr hy
    _ = Real.exp 1*Real.exp (-t^2/1600) := by rw [sub_eq_add_neg,Real.exp_add,neg_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
lemma polynomial_gaussian (t : ℝ) :
    |t|^20*Real.exp (-t^2/1600)≤
      (3200:ℝ)^10*((10).factorial:ℝ)*Real.exp (-t^2/3200) := by
  have hp := pow_exp_factorial (t^2/3200) (by positivity) 10
  have he : |t|^20=(3200:ℝ)^10*(t^2/3200)^10 := by
    rw [show (20:Nat)=2*10 by norm_num,pow_mul,sq_abs]
    ring
  have he' : -t^2/1600= -t^2/3200+(-t^2/3200) := by ring
  rw [he,he',Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-t^2/3200)).le)
    (show 0≤(3200:ℝ)^10 by positivity)
  convert hm using 1 <;> first | rfl | ring
noncomputable def remainder (T δ t : ℝ) : ℂ :=
  gammaWindow T 20 t*(Complex.exp (-2*(Real.pi:ℂ)*I*(δ:ℂ)*t)-
    ∑ k ∈ Finset.range 20, (-2*(Real.pi:ℂ)*I*(δ:ℂ)*t)^k/(k.factorial:ℂ))
noncomputable def constant : ℝ :=
  18*(1/128:ℝ)^20*(3200:ℝ)^10*((10).factorial:ℝ)/((20).factorial:ℝ)
lemma remainder_norm (T δ t : ℝ) (hδ : |δ|≤1/1024) :
    ‖remainder T δ t‖ ≤ constant*Real.exp (-t^2/3200) := by
  let z : ℂ := -2*(Real.pi:ℂ)*I*(δ:ℂ)*t
  have hn : ‖z‖≤|t|/128 := by
    dsimp [z]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,norm_neg,
      norm_ofNat,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_lt_four,Real.pi_pos,abs_nonneg δ,abs_nonneg t,
      mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hδ),
      mul_nonneg (abs_nonneg δ) (sub_nonneg.mpr Real.pi_lt_four.le)]
  have hg := gamma_window_norm T 20 t
  norm_num at hg
  have hr := exp_factorial_remainder z 20
  have hz : ‖remainder T δ t‖=‖gammaWindow T 20 t‖*
      ‖Complex.exp z-∑ k ∈ Finset.range 20, z^k/(k.factorial:ℂ)‖ := by rw [remainder,norm_mul]
  rw [hz]
  calc
    _ ≤ (6*Real.exp (-t^2/800))*((|t|/128)^20/((20).factorial:ℝ)*Real.exp (|t|/128)) := by
      apply mul_le_mul hg _ (norm_nonneg _) (by positivity)
      apply hr.trans
      gcongr
    _ = (6*(1/128:ℝ)^20/((20).factorial:ℝ))*|t|^20*
        Real.exp (-t^2/800+|t|/128) := by rw [Real.exp_add];ring
    _ ≤ (18*(1/128:ℝ)^20/((20).factorial:ℝ))*(|t|^20*Real.exp (-t^2/1600)) := by
      have hm := mul_le_mul_of_nonneg_left (young_gaussian t)
        (show 0≤(6*(1/128:ℝ)^20/((20).factorial:ℝ))*|t|^20 by positivity)
      convert hm using 1 <;> first | rfl | ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left (polynomial_gaussian t)
        (show 0≤18*(1/128:ℝ)^20/((20).factorial:ℝ) by positivity)
      convert hm using 1 <;> first | rfl | (simp only [constant];ring)
end RHHighGaussianTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighZetaWindowGrowth
open RHHighGammaFourier RHHighPlattFourier RHHighGaussianTaylor RHHighZetaGrowth
lemma completed_gamma_zeta (t : ℝ) :
    completedRiemannZeta (1/2+(t:ℂ)*I)=
      ((Real.pi:ℂ)^(-(1/2+(t:ℂ)*I)/2))*
        Complex.Gamma (1/4+((t/2:ℝ):ℂ)*I)*riemannZeta (1/2+(t:ℂ)*I) := by
  let s : ℂ := 1/2+(t:ℂ)*I
  have hs : 0<s.re := by simp [s]
  have hs0 : s≠0 := by intro h;rw [h] at hs;norm_num at hs
  have he : s/2=1/4+((t/2:ℝ):ℂ)*I := by dsimp [s];push_cast;ring
  have hg : Gammaℝ s≠0 := Gammaℝ_ne_zero_of_re_pos hs
  have hm : completedRiemannZeta s=Gammaℝ s*riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp [hg]
  rw [Gammaℝ_def,he] at hm
  exact hm
lemma full_window_factor (T h t : ℝ) :
    fullWindow T h t=(Real.pi:ℂ)^(-(1/2+((t+T:ℝ):ℂ)*I)/2)*
      gammaWindow T h t*riemannZeta (1/2+((t+T:ℝ):ℂ)*I) := by
  unfold fullWindow gammaWindow
  rw [completed_gamma_zeta]
  ring
lemma pi_factor_le (t : ℝ) : ‖(Real.pi:ℂ)^(-(1/2+(t:ℂ)*I)/2)‖≤1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have he : (-(1/2+(t:ℂ)*I)/2).re= -(1/4:ℝ) := by simp <;> norm_num
  rw [he]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
lemma full_window_norm (T h t : ℝ) :
    ‖fullWindow T h t‖≤6*(3+|t+T|)*Real.exp (-t^2/(2*h^2)) := by
  rw [full_window_factor,norm_mul,norm_mul]
  calc
    _ ≤ (1*(6*Real.exp (-t^2/(2*h^2))))*(3+|t+T|) := by
      apply mul_le_mul
      · exact mul_le_mul (pi_factor_le (t+T)) (gamma_window_norm T h t)
          (norm_nonneg _) (by norm_num)
      · exact critical_growth (t+T)
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring
end RHHighZetaWindowGrowth
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighZetaWindowGrowth
open RHHighPlattFourier
lemma full_window_gaussian (T t : ℝ) :
    ‖fullWindow T 20 t‖≤6*(|T|+404)*Real.exp (-t^2/1600) := by
  have h := full_window_norm T 20 t
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num] at h
  have ha : |t+T|≤|t|+|T| := abs_add_le t T
  have ht : |t|≤400+t^2/1600 := by nlinarith [sq_abs t,sq_nonneg (|t|-800)]
  have he := Real.add_one_le_exp (t^2/1600)
  have hh : 3+|t+T|≤(|T|+404)*Real.exp (t^2/1600) := by
    have hc : 1≤|T|+404 := by linarith [abs_nonneg T]
    have hn : 0≤t^2/1600 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hn]
  calc
    _ ≤ 6*((|T|+404)*Real.exp (t^2/1600))*Real.exp (-t^2/800) :=
      h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) (Real.exp_pos _).le)
    _ = (6*(|T|+404))*(Real.exp (t^2/1600)*Real.exp (-t^2/800)) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring
end RHHighZetaWindowGrowth
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 10000
open Complex
namespace RHHighDampedWindow
lemma real_factor (T x : ℝ) :
    RHHighXiWindow.normalized T (x:ℂ)=
      RHHighXiWindow.q T (x:ℂ)*RHHighPlattFourier.fullWindow T 20 x := by
  rw [RHHighXiWindow.real_normalized,RHHighXiWindow.q_real]
  congr 1
  unfold RHHighPlattFourier.fullWindow RHHighEntireCorrection.sline
    RHHighEntireCorrection.window RHHighGammaFourier.window
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring
lemma q_real_small (T x : ℝ) (hT:3000000000≤T) (hx:|x|≤256) : ‖RHHighXiWindow.q T (x:ℂ)‖≤2 := by
  have ht:0<T:=by linarith
  rw [RHHighXiWindow.q_real,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
  have hh:=abs_le.mp hx
  have hx2:x^2≤256^2 := by
    have h:=pow_le_pow_left₀ (abs_nonneg _) hx 2
    simpa only [sq_abs] using h
  nlinarith [sq_nonneg (T-3000000000)]
lemma exp_neg_nat_bound (b : ℝ) (n : Nat) (hb:1≤b) (he:b≤Real.exp 1) : Real.exp (-(n:ℝ))≤1/b^n := by
  rw [Real.exp_neg]
  have h:=pow_le_pow_left₀ (by linarith : (0:ℝ)≤b) he n
  rw [←Real.exp_nat_mul] at h
  norm_num only [mul_one] at h
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ)<b^n) h
lemma full_outside (T x : ℝ) (hT:0≤T ∧ T≤4000000000) (hx:256≤|x|) :
    ‖RHHighPlattFourier.fullWindow T 20 x‖≤1 := by
  have hx2:256^2≤x^2 := by
    have h:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤256) hx 2
    simpa only [sq_abs] using h
  have h:=RHHighZetaWindowGrowth.full_window_gaussian T x
  rw [abs_of_nonneg hT.1] at h
  have he:Real.exp (-x^2/1600)≤1/(2:ℝ)^40 :=
    (Real.exp_le_exp.mpr (by nlinarith : -x^2/1600≤-(40:ℝ))).trans
      (by simpa using exp_neg_nat_bound 2 40 (by norm_num) Real.exp_one_gt_two.le)
  calc
    _ ≤ 6*(T+404)*(1/(2:ℝ)^40) := h.trans (mul_le_mul_of_nonneg_left he (by linarith [hT.1]))
    _ ≤ 6*(4000000000+404)*(1/(2:ℝ)^40) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ _ := by norm_num
lemma damp_q_real_outside (T x : ℝ) (hT:3000000000≤T) (hx:256≤|x|) :
    ‖damp (x:ℂ)‖*‖RHHighXiWindow.q T (x:ℂ)‖≤1/10^12 := by
  have hx2:256^2≤x^2 := by
    have h:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤256) hx 2
    simpa only [sq_abs] using h
  have he:Real.exp (-x^2/2048)≤1/(27/10:ℝ)^32 :=
    (Real.exp_le_exp.mpr (by nlinarith : -x^2/2048≤-(32:ℝ))).trans
      (by simpa using exp_neg_nat_bound (27/10) 32 (by norm_num) (by linarith [Real.exp_one_gt_d9]))
  have hd:‖damp (x:ℂ)‖=Real.exp (-x^2/2048) := by simp only [damp_norm,Complex.ofReal_re,Complex.ofReal_im,zero_pow (by decide : (2:Nat)≠0),zero_div,add_zero]
  have hq:=q_bound T (x:ℂ) hT (by simp)
  simp only [Complex.ofReal_re] at hq
  rw [hd]
  have ht:0<T:=by linarith
  have hh:=quadratic_damped x
  have hpoly:2*(x^2*Real.exp (-x^2/2048))/T^2≤4096/(3000000000:ℝ)^2 := by
    exact div_le_div₀ (by positivity) (by linarith) (by norm_num) (by nlinarith [sq_nonneg (T-3000000000)])
  calc
    _ ≤ Real.exp (-x^2/2048)*(3+2*x^2/T^2) := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ = 3*Real.exp (-x^2/2048)+2*(x^2*Real.exp (-x^2/2048))/T^2 := by ring
    _ ≤ 3/(27/10:ℝ)^32+4096/(3000000000:ℝ)^2 := by nlinarith only [he,hpoly]
    _ ≤ _ := by norm_num
lemma real_bound (T : ℝ) (hT:3000000000≤T ∧ T≤4000000000)
    (happrox:∀ x:ℝ,|x|≤256 → ‖RHHighPlattFourier.fullWindow T 20 x-RHHighFourierPolynomial.polynomial (x:ℂ)‖≤4/10^11)
    (x : ℝ) : ‖error T RHHighFourierPolynomial.polynomial (x:ℂ)‖≤1/10^10 := by
  have hf:error T RHHighFourierPolynomial.polynomial (x:ℂ)=
      damp (x:ℂ)*RHHighXiWindow.q T (x:ℂ)*
        (RHHighPlattFourier.fullWindow T 20 x-RHHighFourierPolynomial.polynomial (x:ℂ)) := by
    unfold error
    rw [real_factor]
    ring
  rw [hf,norm_mul,norm_mul]
  by_cases hx:|x|≤256
  · have hd:‖damp (x:ℂ)‖≤1 := by
      rw [damp_norm]
      simp only [Complex.ofReal_re,Complex.ofReal_im,zero_pow (by decide : (2:Nat)≠0),zero_div,add_zero]
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hq:=q_real_small T x hT.1 hx
    have h:=mul_le_mul (mul_le_mul hd hq (norm_nonneg _) (by norm_num)) (happrox x hx) (norm_nonneg _) (by norm_num : (0:ℝ)≤1*2)
    exact h.trans (by norm_num)
  · have hx':256≤|x|:=by linarith
    have hg:=full_outside T x ⟨by linarith,hT.2⟩ hx'
    have hp:‖RHHighFourierPolynomial.polynomial (x:ℂ)‖≤1 := by simpa using RHHighFourierPolynomial.polynomial_norm (x:ℂ)
    have hs:‖RHHighPlattFourier.fullWindow T 20 x-RHHighFourierPolynomial.polynomial (x:ℂ)‖≤2 := (norm_sub_le _ _).trans (by linarith)
    exact (mul_le_mul (damp_q_real_outside T x hT.1 hx') hs (norm_nonneg _) (by norm_num : (0:ℝ)≤1/10^12)).trans (by norm_num)
end RHHighDampedWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighThreeLines
lemma horizontal_abs (f : ℂ→ℂ) (R ε M : ℝ) (hR:0<R) (hf:Differentiable ℂ f)
    (hzero:∀ x:ℝ,‖f (x:ℂ)‖≤ε)
    (hbound:∀ z:ℂ,|z.im|≤R → ‖f z‖≤M)
    (w : ℂ) (hw:|w.im|≤R) :
    ‖f w‖≤ε^(1-|w.im|/R)*M^(|w.im|/R) := by
  by_cases hy:0≤w.im
  · simpa only [abs_of_nonneg hy] using horizontal f R ε M hR hf hzero
      (fun z hz => hbound z (by rw [abs_of_nonneg hz.1];exact hz.2)) w
      ⟨hy,by rwa [abs_of_nonneg hy] at hw⟩
  · have hy':0≤(-w).im := by simp only [neg_im];linarith
    have hn:Differentiable ℂ (fun z:ℂ => f (-z)) := hf.comp (by fun_prop)
    have h:=horizontal (fun z:ℂ => f (-z)) R ε M hR hn
      (fun x => by simpa only [←Complex.ofReal_neg] using hzero (-x))
      (fun z hz => hbound (-z) (by simp only [neg_im,abs_neg,abs_of_nonneg hz.1];exact hz.2)) (-w)
      ⟨hy',by simpa only [neg_im,neg_nonneg,abs_of_nonpos (le_of_lt (lt_of_not_ge hy))] using hw⟩
    simpa only [neg_neg,neg_im,abs_of_nonpos (le_of_lt (lt_of_not_ge hy))] using h
end RHHighThreeLines
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighDampedWindow
lemma interpolation_fixed (u : ℝ) (hu:0≤u ∧ u≤1/32) :
    (1/10^10:ℝ)^(1-u)*((10:ℝ)^111)^u≤1/10^6 := by
  have he:(1/10^10:ℝ)=(10:ℝ)^(-(10:ℝ)) := by norm_num [Real.rpow_neg]
  have hM:((10:ℝ)^111)=(10:ℝ)^(111:ℝ) := by norm_num
  rw [he,hM,←Real.rpow_mul (by norm_num),←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
  calc
    _ ≤ (10:ℝ)^(-(6:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by norm_num [Real.rpow_neg]
lemma fixed_transfer (T : ℝ) (P : ℂ→ℂ) (hP:Differentiable ℂ P)
    (hreal:∀ x:ℝ,‖error T P (x:ℂ)‖≤1/10^10)
    (hstrip:∀ z:ℂ,|z.im|≤16 → ‖error T P z‖≤(10:ℝ)^111)
    (z : ℂ) (hx:|z.re|≤64) (hy:|z.im|≤1/2) :
    ‖RHHighXiWindow.normalized T z-RHHighXiWindow.q T z*P z‖≤1/100000 := by
  have hz:|z.im|≤16 := by linarith
  have h:=RHHighThreeLines.horizontal_abs (error T P) 16 (1/10^10) ((10:ℝ)^111)
    (by norm_num) (error_entire T P hP) hreal hstrip z hz
  have he:‖error T P z‖≤1/10^6 := h.trans
    (interpolation_fixed (|z.im|/16) ⟨by positivity,by linarith⟩)
  have hund:=undamp_error T P z (1/10^6) he
  have hx2:z.re^2≤4096 := by
    have hh:=pow_le_pow_left₀ (abs_nonneg z.re) hx 2
    norm_num only [sq_abs] at hh
    exact hh
  have hex:Real.exp (z.re^2/2048-z.im^2/2048)≤9 := by
    calc
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.im])
      _ = (Real.exp 1)^2 := by simpa using (Real.exp_nat_mul (1:ℝ) (2:Nat)).symm
      _ ≤ _ := by nlinarith [Real.exp_pos 1,Real.exp_one_lt_three]
  exact hund.trans (by nlinarith)
lemma interpolation_fixed115 (u : ℝ) (hu:0≤u ∧ u≤1/32) :
    (1/10^10:ℝ)^(1-u)*((10:ℝ)^115)^u≤1/10^6 := by
  have he:(1/10^10:ℝ)=(10:ℝ)^(-(10:ℝ)) := by norm_num [Real.rpow_neg]
  have hM:((10:ℝ)^115)=(10:ℝ)^(115:ℝ) := by norm_num
  rw [he,hM,←Real.rpow_mul (by norm_num),←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
  calc
    _ ≤ (10:ℝ)^(-(6:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by norm_num [Real.rpow_neg]
lemma fixed_transfer115 (T : ℝ) (P : ℂ→ℂ) (hP:Differentiable ℂ P)
    (hreal:∀ x:ℝ,‖error T P (x:ℂ)‖≤1/10^10)
    (hstrip:∀ z:ℂ,|z.im|≤16 → ‖error T P z‖≤(10:ℝ)^115)
    (z : ℂ) (hx:|z.re|≤64) (hy:|z.im|≤1/2) :
    ‖RHHighXiWindow.normalized T z-RHHighXiWindow.q T z*P z‖≤1/100000 := by
  have hz:|z.im|≤16 := by linarith
  have h:=RHHighThreeLines.horizontal_abs (error T P) 16 (1/10^10) ((10:ℝ)^115)
    (by norm_num) (error_entire T P hP) hreal hstrip z hz
  have he:‖error T P z‖≤1/10^6 := h.trans
    (interpolation_fixed115 (|z.im|/16) ⟨by positivity,by linarith⟩)
  have hund:=undamp_error T P z (1/10^6) he
  have hx2:z.re^2≤4096 := by
    have hh:=pow_le_pow_left₀ (abs_nonneg z.re) hx 2
    norm_num only [sq_abs] at hh
    exact hh
  have hex:Real.exp (z.re^2/2048-z.im^2/2048)≤9 := by
    calc
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.im])
      _ = (Real.exp 1)^2 := by simpa using (Real.exp_nat_mul (1:ℝ) (2:Nat)).symm
      _ ≤ _ := by nlinarith [Real.exp_pos 1,Real.exp_one_lt_three]
  exact hund.trans (by nlinarith)
end RHHighDampedWindow
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
open scoped FourierTransform
namespace RHHighWindowTransfer
lemma from_coefficients
 (hc:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 (z : ℂ) (hx:|z.re|≤64) (hy:|z.im|≤1/2) :
 ‖RHHighXiWindow.normalized 3289999936 z-RHHighXiWindow.q 3289999936 z*RHHighFourierPolynomial.polynomial z‖≤1/100000 := by
 have hW:RHHighPlattFourier.fullWindow 3289999936 20=RHHighFullCoefficient.W:=by
  funext t
  unfold RHHighPlattFourier.fullWindow RHHighGammaFourier.window RHHighFullCoefficient.W
  norm_num only[show (2*(20:ℝ)^2)=800 by norm_num]
 have ha (x : ℝ) (hx:|x|≤256) :
  ‖RHHighPlattFourier.fullWindow 3289999936 20 x-RHHighFourierPolynomial.polynomial (x:ℂ)‖≤4/10^11:=by
  rw[hW]
  exact TaoFivePrimes.rh_high_height_full_window_reconstruction 3289999936 x ⟨by norm_num,by norm_num⟩ hx hc
 apply RHHighDampedWindow.fixed_transfer115 3289999936 RHHighFourierPolynomial.polynomial
  RHHighFourierPolynomial.polynomial_entire ?_ ?_ z hx hy
 · intro x
   exact RHHighDampedWindow.real_bound 3289999936 ⟨by norm_num,by norm_num⟩ ha x
 · intro w hw
   exact RHHighDampedWindow.strip_bound 3289999936 ⟨by norm_num,by norm_num⟩ w hw
end RHHighWindowTransfer
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
open scoped FourierTransform
namespace RHHighFinalCount
open RHHighContourArithmeticV2 RHHighContourEnumeration RHHighContourGeometry
lemma from_data (rs : List Record) (d : Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=> decide (p.1.edge=edgeOf p.2 ∧ p.1.index=offsetOf p.2))=true)
 (hs:(rs.map (fun r=> if r.edge<2 then r.log128.2 else -r.log128.2)).sum≤2571*(2:Int)^128)
 (hjet:∀e j k:Nat,e<4 → j≤ cells e → k<8 →
  ‖RHHighPolynomialJet.jet (point e j) (step e) k-RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by
 have hR:∀e j:Nat,e<4 → j< cells e →
  ((rs[index e j]?).getD d).edge=e ∧ ((rs[index e j]?).getD d).index=j:=by
  intro e j he hj
  exact coordinates rs d hlen hc e j he hj
 apply RHHighContourCount.from_contour
 · exact RHHighContourGlobal.boundary_lower (fun e j=>(rs[index e j]?).getD d) hR hjet
 · intro z hz
   exact RHHighWindowTransfer.from_coefficients hcoeff z (RHHighXiContour.border_box z hz).1 (RHHighXiContour.border_box z hz).2
 · exact RHHighContourNative.integral_bound rs d hlen hc hs hjet
end RHHighFinalCount
end
end RHHighCountFromCertificateProof
open scoped FourierTransform
theorem solution
 (rs : List RHHighContourArithmeticV2.Record) (d : RHHighContourArithmeticV2.Record) (hlen:rs.length=8448)
 (hc:rs.zipIdx.all (fun p=>decide
  (p.1.edge=(if p.2<4096 then 0 else if p.2<4224 then 1 else if p.2<8320 then 2 else 3) ∧
   p.1.index=(if p.2<4096 then p.2 else if p.2<4224 then p.2-4096 else if p.2<8320 then p.2-4224 else p.2-8320)))=true)
 (hs:(rs.map (fun r=>if r.edge<2 then r.log128.2 else -r.log128.2)).sum≤2571*(2:Int)^128)
 (hjet:∀e j k:Nat,e<4 → j≤RHHighContourGeometry.cells e → k<8 →
  ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
   RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12)
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by
 exact RHHighCountFromCertificateProof.RHHighFinalCount.from_data rs d hlen hc hs hjet hcoeff
#print axioms solution
