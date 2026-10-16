-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_full_coefficient_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T13:11:56.247348+00:00
-- url     : https://prove2.me/submissions/ee175843-57b6-4952-b334-9ee35c2dc3e4

import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
import Definitions.Def_TaoFivePrimes_RHHighZetaCoefficientAssembly
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_all_gamma_fourier_enclosures
import Theorems.Thm_TaoFivePrimes_rh_high_height_all_zeta_correlations
import Theorems.Thm_TaoFivePrimes_rh_high_height_full_coefficient_analytic
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_coefficient_assembly
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation_semantic
namespace RHHighFullCoefficientEnclosureProof
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHHighContourVector
export _root_.RHHighContourVector (coefficient decode raw value vector)
end RHHighContourVector
namespace RHHighDirichletArithmetic
export _root_.RHHighDirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHHighDirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHHighFFTPositive00
export _root_.RHHighFFTPositive00 (row00 row01 row02 row03 rows)
end RHHighFFTPositive00
namespace RHHighFFTPositive01
export _root_.RHHighFFTPositive01 (row00 row01 row02 row03 rows)
end RHHighFFTPositive01
namespace RHHighFFTPositive02
export _root_.RHHighFFTPositive02 (row00 row01 row02 row03 rows)
end RHHighFFTPositive02
namespace RHHighFFTPositive03
export _root_.RHHighFFTPositive03 (row00 row01 row02 row03 rows)
end RHHighFFTPositive03
namespace RHHighFFTPositive04
export _root_.RHHighFFTPositive04 (row00 row01 row02 row03 rows)
end RHHighFFTPositive04
namespace RHHighFFTPositive05
export _root_.RHHighFFTPositive05 (row00 row01 row02 row03 rows)
end RHHighFFTPositive05
namespace RHHighFFTPositive06
export _root_.RHHighFFTPositive06 (row00 row01 row02 row03 rows)
end RHHighFFTPositive06
namespace RHHighFFTPositive07
export _root_.RHHighFFTPositive07 (row00 row01 row02 row03 rows)
end RHHighFFTPositive07
namespace RHHighFFTPositive08
export _root_.RHHighFFTPositive08 (row00 row01 row02 row03 rows)
end RHHighFFTPositive08
namespace RHHighFFTPositive09
export _root_.RHHighFFTPositive09 (row00 row01 row02 row03 rows)
end RHHighFFTPositive09
namespace RHHighFFTPositive10
export _root_.RHHighFFTPositive10 (row00 row01 row02 row03 rows)
end RHHighFFTPositive10
namespace RHHighFFTPositive11
export _root_.RHHighFFTPositive11 (row00 row01 row02 row03 rows)
end RHHighFFTPositive11
namespace RHHighFFTPositive12
export _root_.RHHighFFTPositive12 (row00 row01 row02 row03 rows)
end RHHighFFTPositive12
namespace RHHighFFTPositive13
export _root_.RHHighFFTPositive13 (row00 row01 row02 row03 rows)
end RHHighFFTPositive13
namespace RHHighFFTPositive14
export _root_.RHHighFFTPositive14 (row00 row01 row02 row03 rows)
end RHHighFFTPositive14
namespace RHHighFFTPositive15
export _root_.RHHighFFTPositive15 (row00 row01 row02 row03 rows)
end RHHighFFTPositive15
namespace RHHighFFTPositive16
export _root_.RHHighFFTPositive16 (row00 row01 row02 row03 rows)
end RHHighFFTPositive16
namespace RHHighFFTPositive17
export _root_.RHHighFFTPositive17 (row00 row01 row02 row03 rows)
end RHHighFFTPositive17
namespace RHHighFFTPositive18
export _root_.RHHighFFTPositive18 (row00 row01 row02 row03 rows)
end RHHighFFTPositive18
namespace RHHighFFTPositive19
export _root_.RHHighFFTPositive19 (row00 row01 row02 row03 rows)
end RHHighFFTPositive19
namespace RHHighFFTPositive20
export _root_.RHHighFFTPositive20 (row00 row01 row02 row03 rows)
end RHHighFFTPositive20
namespace RHHighFFTPositive21
export _root_.RHHighFFTPositive21 (row00 row01 row02 row03 rows)
end RHHighFFTPositive21
namespace RHHighFFTPositive22
export _root_.RHHighFFTPositive22 (row00 row01 row02 row03 rows)
end RHHighFFTPositive22
namespace RHHighFFTPositive23
export _root_.RHHighFFTPositive23 (row00 row01 row02 row03 rows)
end RHHighFFTPositive23
namespace RHHighFourierPolynomial
export _root_.RHHighFourierPolynomial (coefficient imagInteger phase polynomial realInteger word)
end RHHighFourierPolynomial
namespace RHHighFullCoefficient
export _root_.RHHighFullCoefficient (F L W delta group weight)
end RHHighFullCoefficient
namespace RHHighGammaArithmetic
export _root_.RHHighGammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHHighGammaArithmetic
namespace RHHighGammaFourierTable
export _root_.RHHighGammaFourierTable (packets value values)
end RHHighGammaFourierTable
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
namespace RHHighHomogeneousHorner
export _root_.RHHighHomogeneousHorner (hom)
end RHHighHomogeneousHorner
namespace RHHighLogData
export _root_.RHHighLogData (D F coefficients denominator log2 log2pi numerator rounded)
end RHHighLogData
namespace RHHighNegativeExp
export _root_.RHHighNegativeExp (denominator en ep numerator seed)
end RHHighNegativeExp
namespace RHHighPackedFFT
export _root_.RHHighPackedFFT (combine convolution decode digits output pack pair unbias windows)
end RHHighPackedFFT
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
namespace RHHighZetaCoefficientAssembly
export _root_.RHHighZetaCoefficientAssembly (add expected packets rounded total)
end RHHighZetaCoefficientAssembly
namespace RHHighZetaCorrelation
export _root_.RHHighZetaCorrelation (aImag aReal bImag bReal combine convolution decode output sample signed)
end RHHighZetaCorrelation
namespace RHHighZetaCorrelationOutput00
export _root_.RHHighZetaCorrelationOutput00 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput00
namespace RHHighZetaCorrelationOutput01
export _root_.RHHighZetaCorrelationOutput01 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput01
namespace RHHighZetaCorrelationOutput02
export _root_.RHHighZetaCorrelationOutput02 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput02
namespace RHHighZetaCorrelationOutput03
export _root_.RHHighZetaCorrelationOutput03 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput03
namespace RHHighZetaCorrelationOutput04
export _root_.RHHighZetaCorrelationOutput04 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput04
namespace RHHighZetaCorrelationOutput05
export _root_.RHHighZetaCorrelationOutput05 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput05
namespace RHHighZetaCorrelationOutput06
export _root_.RHHighZetaCorrelationOutput06 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput06
namespace RHHighZetaCorrelationOutput07
export _root_.RHHighZetaCorrelationOutput07 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput07
namespace RHHighZetaCorrelationOutput08
export _root_.RHHighZetaCorrelationOutput08 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput08
namespace RHHighZetaCorrelationOutput09
export _root_.RHHighZetaCorrelationOutput09 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput09
namespace RHHighZetaCorrelationOutput10
export _root_.RHHighZetaCorrelationOutput10 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput10
namespace RHHighZetaCorrelationOutput11
export _root_.RHHighZetaCorrelationOutput11 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput11
namespace RHHighZetaCorrelationOutput12
export _root_.RHHighZetaCorrelationOutput12 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput12
namespace RHHighZetaCorrelationOutput13
export _root_.RHHighZetaCorrelationOutput13 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput13
namespace RHHighZetaCorrelationOutput14
export _root_.RHHighZetaCorrelationOutput14 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput14
namespace RHHighZetaCorrelationOutput15
export _root_.RHHighZetaCorrelationOutput15 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput15
namespace RHHighZetaCorrelationOutput16
export _root_.RHHighZetaCorrelationOutput16 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput16
namespace RHHighZetaCorrelationOutput17
export _root_.RHHighZetaCorrelationOutput17 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput17
namespace RHHighZetaCorrelationOutput18
export _root_.RHHighZetaCorrelationOutput18 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput18
namespace RHHighZetaCorrelationOutput19
export _root_.RHHighZetaCorrelationOutput19 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput19
namespace RHHighZetaCorrelationOutput20
export _root_.RHHighZetaCorrelationOutput20 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput20
namespace RHHighZetaCorrelationOutput21
export _root_.RHHighZetaCorrelationOutput21 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput21
namespace RHHighZetaCorrelationOutput22
export _root_.RHHighZetaCorrelationOutput22 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput22
namespace RHHighZetaCorrelationOutput23
export _root_.RHHighZetaCorrelationOutput23 (row00 row01 row02 rows)
end RHHighZetaCorrelationOutput23
namespace RHHighZetaFourierData
export _root_.RHHighZetaFourierData (row00 row01 row02 rows)
end RHHighZetaFourierData
namespace TaoFivePrimes
export _root_.TaoFivePrimes (rh_high_height_all_gamma_fourier_enclosures rh_high_height_all_zeta_correlations rh_high_height_full_coefficient_analytic rh_high_height_zeta_coefficient_assembly rh_high_height_zeta_correlation_semantic)
end TaoFivePrimes
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighCoefficientListSum
noncomputable def value (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
open RHHighZetaCoefficientAssembly
lemma add_length (xs ys : List (Int×Int)) (N : Nat) (hx:xs.length=N) (hy:ys.length=N) :
 (add xs ys).length=N := by simp only[add,List.length_zipWith,hx,hy,min_self]
lemma add_at (xs ys : List (Int×Int)) (N : Nat) (hx:xs.length=N) (hy:ys.length=N)
 (j : Nat) (hj:j<N) :
 value (((add xs ys)[j]?).getD (0,0))=value ((xs[j]?).getD (0,0))+value ((ys[j]?).getD (0,0)) := by
 have hz:j<(add xs ys).length:=by rw[add_length xs ys N hx hy];exact hj
 rw[List.getElem?_eq_getElem hz,Option.getD_some,
  List.getElem?_eq_getElem (by omega : j<xs.length),Option.getD_some,
  List.getElem?_eq_getElem (by omega : j<ys.length),Option.getD_some]
 simp only[add,List.getElem_zipWith,value,Int.cast_add]
 ring
lemma fold_length (packets : List (List Nat)) (N : Nat)
 (h:∀xs∈packets,(RHHighZetaCorrelation.decode xs).length=N) (acc : List (Int×Int)) (ha:acc.length=N) :
 (packets.foldl (fun a xs=>add a (RHHighZetaCorrelation.decode xs)) acc).length=N := by
 induction packets generalizing acc with
 | nil => exact ha
 | cons xs xss ih =>
  rw[List.foldl_cons]
  apply ih
  · intro ys hy;exact h ys (List.mem_cons_of_mem _ hy)
  · exact add_length _ _ N ha (h xs (by simp))
lemma fold_at (packets : List (List Nat)) (N : Nat)
 (h:∀xs∈packets,(RHHighZetaCorrelation.decode xs).length=N) (acc : List (Int×Int)) (ha:acc.length=N)
 (j : Nat) (hj:j<N) :
 value (((packets.foldl (fun a xs=>add a (RHHighZetaCorrelation.decode xs)) acc)[j]?).getD (0,0))=
 value ((acc[j]?).getD (0,0))+(packets.map (fun xs=>value (((RHHighZetaCorrelation.decode xs)[j]?).getD (0,0)))).sum := by
 induction packets generalizing acc with
 | nil => simp only[List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
 | cons xs xss ih =>
  rw[List.foldl_cons,ih (by intro ys hy;exact h ys (List.mem_cons_of_mem _ hy)) _ (add_length _ _ N ha (h xs (by simp))),add_at _ _ N ha (h xs (by simp)) j hj]
  simp only[List.map_cons,List.sum_cons]
  ring
end RHHighCoefficientListSum
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighCoefficientGroupTotal
open RHHighZetaCoefficientAssembly RHHighCoefficientListSum
lemma packet_shapes : packets.all (fun xs=> decide (xs.length=1025))=true := by decide +kernel
lemma packets_length : packets.length=24 := by decide +kernel
lemma total_value (m : Nat) (hm:m≤1024) :
 value ((total[m]?).getD (0,0))=
 ∑k:Fin 24,value (((RHHighZetaCorrelation.decode ((packets[k.val]?).getD []))[m]?).getD (0,0)) := by
 have hlens (xs : List Nat) (hx:xs∈packets) : (RHHighZetaCorrelation.decode xs).length=1025 := by
  simp only[RHHighZetaCorrelation.decode,List.length_map]
  exact decide_eq_true_eq.mp ((List.all_eq_true.mp packet_shapes) xs hx)
 have h:=fold_at packets 1025 hlens (List.replicate 1025 (0,0)) (by simp) m (by omega)
 have ha:value (((List.replicate 1025 ((0,0):Int×Int))[m]?).getD (0,0))=0 := by
  rw[List.getElem?_replicate_of_lt (by omega),Option.getD_some]
  simp only[value,Int.cast_zero,zero_mul,add_zero]
 rw[ha,zero_add] at h
 have he:(packets.map (fun xs=> value (((RHHighZetaCorrelation.decode xs)[m]?).getD (0,0))))=
  List.ofFn (fun k:Fin 24=> value (((RHHighZetaCorrelation.decode ((packets[k.val]?).getD []))[m]?).getD (0,0))) := by
  apply List.ext_getElem
  · simp only[List.length_map,packets_length,List.length_ofFn]
  · intro k hk hk'
    have hkp:k< packets.length:=by simpa only[List.length_map] using hk
    simp only[List.getElem_map,List.getElem_ofFn,List.getElem?_eq_getElem hkp,Option.getD_some]
 rw[he,List.sum_ofFn] at h
 exact h
lemma group_total (m : Nat) (hm:m≤1024)
 (hc:∀k:Nat,k<24 → RHHighZetaCorrelation.output k (RHHighGammaFourierTable.values k)=
   RHHighZetaCorrelation.decode ((packets[k]?).getD []))
 (hs:∀k:Nat,k<24 →
  RHHighBinningSemantic.pairValue (((RHHighZetaCorrelation.output k (RHHighGammaFourierTable.values k))[m]?).getD (0,0))/(2:ℂ)^213=
  ∑b:Fin 929,(RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient b.val k)/(2:ℂ)^128)*
   RHHighGammaFourierTable.value k (m+b.val)) :
 RHHighFullCoefficient.group (fun b k=> RHHighGammaFourierTable.value k (m+b))=
 value ((total[m]?).getD (0,0))/(2:ℂ)^213 := by
 unfold RHHighFullCoefficient.group
 rw[Finset.sum_comm,total_value m hm,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro k hk
 have h:=hs k.val k.isLt
 rw[hc k.val k.isLt] at h
 exact h.symm
lemma group_scaled (m : Nat) (hm:m≤1024)
 (hg:RHHighFullCoefficient.group (fun b k=> RHHighGammaFourierTable.value k (m+b))=
  value ((total[m]?).getD (0,0))/(2:ℂ)^213) :
 (1/512:ℂ)*RHHighFullCoefficient.group (fun b k=> RHHighGammaFourierTable.value k (m+b))=
 value ((total[m]?).getD (0,0))/(2:ℂ)^222 := by
 rw[hg,show (2:ℂ)^222=(2:ℂ)^213*512 by norm_num]
 ring
end RHHighCoefficientGroupTotal
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
open Complex
namespace RHHighDyadicRescale
open RHHighDyadicComplex
lemma rescale (B S : Nat) (hB:0<B) (hS:0<S) (p : Int×Int) :
 ‖value (B*S) p-value S (p.1/(B:Int),p.2/(B:Int))‖≤2/(S:ℝ) := by
 have h:=divide_error S B hS hB p
 have he:value S p/(B:ℂ)=value (B*S) p:=by simp only[value,Nat.cast_mul];ring
 rw[he,norm_sub_rev] at h
 exact h
end RHHighDyadicRescale
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighCoefficientAssemblySound
noncomputable def value (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
lemma rescale_error (p : Int×Int) :
 ‖value p/(2:ℂ)^222-value (p.1/(2:Int)^142,p.2/(2:Int)^142)/(2:ℂ)^80‖≤2/(2:ℝ)^80 := by
 have h:=RHHighDyadicRescale.rescale (2^142) (2^80) (by norm_num) (by norm_num) p
 simpa only [RHHighDyadicComplex.value,value,show (2:Nat)^142*2^80=2^222 by norm_num,
  Nat.cast_pow,Nat.cast_ofNat,Int.natCast_pow] using h
end RHHighCoefficientAssemblySound
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
namespace RHHighFFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHHighFFTOutputSample
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHHighCoefficientAssemblySound
open RHHighZetaCoefficientAssembly
lemma word_at (j : Nat) (hj:j≤1024) :
 (RHHighZetaFourierData.rows.flatten[j]?).getD 0=RHHighFourierPolynomial.word j := by
 have hlen:RHHighZetaFourierData.rows.flatten.length=1025:=by decide +kernel
 have hs:RHHighZetaFourierData.rows.all (fun row=> decide (row.length≤512))=true:=by decide +kernel
 have hf:RHHighZetaFourierData.rows.dropLast.all (fun row=> decide (row.length=512))=true:=by decide +kernel
 apply RHHighFlatRows.lookup 512 (by decide) 0 RHHighZetaFourierData.rows
 · intro row hr;exact decide_eq_true_eq.mp ((List.all_eq_true.mp hs) row hr)
 · intro row hr;exact decide_eq_true_eq.mp ((List.all_eq_true.mp hf) row hr)
 · rw[hlen];omega
lemma expected_value (j : Nat) (hj:j≤1024) :
 value ((expected[j]?).getD (0,0))/(2:ℂ)^80=RHHighFourierPolynomial.coefficient j := by
 have hlen:RHHighZetaFourierData.rows.flatten.length=1025:=by decide +kernel
 have h:=RHHighFFTOutputSample.at_index RHHighZetaFourierData.rows.flatten j (by rw[hlen];omega)
 change value (((RHHighPackedFFT.decode RHHighZetaFourierData.rows.flatten)[j]?).getD (0,0))/(2:ℂ)^80=_
 rw[h]
 simp only[word_at j hj,value,RHHighContourVector.decode,RHHighFourierPolynomial.coefficient,
  RHHighFourierPolynomial.realInteger,RHHighFourierPolynomial.imagInteger]
lemma rounded_at (j : Nat) (hj:j≤1024) :
 let p:=(total[j]?).getD (0,0)
 (p.1/(2:Int)^142,if j=0 then 0 else p.2/(2:Int)^142)=(expected[j]?).getD (0,0) := by
 have hlen:=TaoFivePrimes.rh_high_height_zeta_coefficient_assembly.1
 have hj':j< total.length:=by omega
 have h:=congrArg (fun xs:List (Int×Int)=>(xs[j]?).getD (0,0)) TaoFivePrimes.rh_high_height_zeta_coefficient_assembly.2.1
 have he:((rounded[j]?).getD (0,0))=
  (((total[j]?).getD (0,0)).1/(2:Int)^142,
    if j=0 then 0 else ((total[j]?).getD (0,0)).2/(2:Int)^142) := by
  unfold rounded
  rw[List.getElem?_eq_getElem (by simp only[List.length_map,List.length_zipIdx];exact hj'),Option.getD_some,
   List.getElem_map,List.getElem_zipIdx,List.getElem?_eq_getElem hj',Option.getD_some]
  simp only[Nat.zero_add,Prod.fst,Prod.snd]
 rw[he] at h
 exact h
lemma rounding (j : Nat) (hj:j≤1024) :
 ‖value ((total[j]?).getD (0,0))/(2:ℂ)^222-RHHighFourierPolynomial.coefficient j‖≤3/(2:ℝ)^80 := by
 let p:=(total[j]?).getD (0,0)
 let a:Int×Int:=(p.1/(2:Int)^142,p.2/(2:Int)^142)
 let b:Int×Int:=(p.1/(2:Int)^142,if j=0 then 0 else p.2/(2:Int)^142)
 have hb:value b/(2:ℂ)^80=RHHighFourierPolynomial.coefficient j := by
  have he:=rounded_at j hj
  rw[show b=(expected[j]?).getD (0,0) from he]
  exact expected_value j hj
 have hc:‖value a/(2:ℂ)^80-value b/(2:ℂ)^80‖≤1/(2:ℝ)^80 := by
  by_cases hj0:j=0
  · subst j
    have hi:=TaoFivePrimes.rh_high_height_zeta_coefficient_assembly.2.2
    have he:value a/(2:ℂ)^80-value b/(2:ℂ)^80=(-I)/(2:ℂ)^80 := by
     dsimp only[a,b,p]
     simp only[if_true,value,Prod.fst,Prod.snd,Int.cast_zero,zero_mul,add_zero]
     rw[show (((total[0]?).getD (0,0)).2/(2:Int)^142)= -1 from hi]
     push_cast
     ring
    rw[he,norm_div,norm_neg,norm_I,norm_pow,norm_ofNat]
  · simp only[a,b,hj0,if_false,sub_self,norm_zero]
    positivity
 have hr:=rescale_error p
 change ‖value p/(2:ℂ)^222-_‖≤ _
 rw[←hb]
 exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hr hc)).trans_eq (by ring)
end RHHighCoefficientAssemblySound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
open scoped FourierTransform
namespace RHHighCoefficientFinal
lemma group_identity (m : Nat) (hm:m≤1024) :
 (1/512:ℂ)*RHHighFullCoefficient.group (fun b k=> RHHighGammaFourierTable.value k (m+b))=
 RHHighCoefficientListSum.value ((RHHighZetaCoefficientAssembly.total[m]?).getD (0,0))/(2:ℂ)^222 := by
 apply RHHighCoefficientGroupTotal.group_scaled m hm
 apply RHHighCoefficientGroupTotal.group_total m hm
 · intro k hk;exact (TaoFivePrimes.rh_high_height_all_zeta_correlations k hk).1
 · intro k hk
   have h:=TaoFivePrimes.rh_high_height_zeta_correlation_semantic k hk (RHHighGammaFourierTable.values k)
    (TaoFivePrimes.rh_high_height_all_zeta_correlations k hk).2 ⟨m,by omega⟩
   exact h
lemma enclosure
 (hgamma:∀k j:Nat,k<24 → j<1954 →
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537)
 (m : Nat) (hm:m≤1024) :
 ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14 := by
 let G:Nat→Nat→ℂ:=fun b k=> RHHighGammaFourierTable.value k (m+b)
 have hF (b : Nat) (hb:b<929) (k : Nat) (hk:k<24) : ‖RHHighFullCoefficient.F m b k‖≤65537 := by
  exact (hgamma k (m+b) hk (by omega)).2
 have heF (b : Nat) (hb:b<929) (k : Nat) (hk:k<24) : ‖RHHighFullCoefficient.F m b k-G b k‖≤1/10^15 := by
  exact (hgamma k (m+b) hk (by omega)).1
 have h:=TaoFivePrimes.rh_high_height_full_coefficient_analytic m hm G hF heF
 rw[group_identity m hm] at h
 have hr:=RHHighCoefficientAssemblySound.rounding m hm
 have ht:‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤3/10^15+3/(2:ℝ)^80 :=
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h hr)
 exact ht.trans (by norm_num)
end RHHighCoefficientFinal
end
end RHHighFullCoefficientEnclosureProof
open scoped FourierTransform
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem solution (m : Nat) (hm:m≤1024) :
 ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14 := by
 exact RHHighFullCoefficientEnclosureProof.RHHighCoefficientFinal.enclosure
  (fun k j hk hj=>TaoFivePrimes.rh_high_height_all_gamma_fourier_enclosures k j hk hj) m hm
#print axioms solution
