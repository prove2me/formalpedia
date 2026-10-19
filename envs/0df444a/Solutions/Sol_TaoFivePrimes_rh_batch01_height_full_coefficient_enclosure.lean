-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_full_coefficient_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T18:08:56.063987+00:00
-- url     : https://prove2.me/submissions/0793bda7-746c-468c-ba6f-e8452457943b

import Definitions.Def_TaoFivePrimes_RHBatch01CoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCoefficientAssembly
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_gamma_fourier_enclosures
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_zeta_correlations
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_full_coefficient_analytic
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_coefficient_assembly
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation_semantic
namespace RHBatch01FullCoefficientEnclosureProof
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHHighContourVector
export _root_.RHHighContourVector (coefficient decode raw value vector)
end RHHighContourVector
namespace RHBatch01DirichletArithmetic
export _root_.RHBatch01DirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHBatch01DirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHBatch01FFTPositive00
export _root_.RHBatch01FFTPositive00 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive00
namespace RHBatch01FFTPositive01
export _root_.RHBatch01FFTPositive01 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive01
namespace RHBatch01FFTPositive02
export _root_.RHBatch01FFTPositive02 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive02
namespace RHBatch01FFTPositive03
export _root_.RHBatch01FFTPositive03 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive03
namespace RHBatch01FFTPositive04
export _root_.RHBatch01FFTPositive04 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive04
namespace RHBatch01FFTPositive05
export _root_.RHBatch01FFTPositive05 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive05
namespace RHBatch01FFTPositive06
export _root_.RHBatch01FFTPositive06 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive06
namespace RHBatch01FFTPositive07
export _root_.RHBatch01FFTPositive07 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive07
namespace RHBatch01FFTPositive08
export _root_.RHBatch01FFTPositive08 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive08
namespace RHBatch01FFTPositive09
export _root_.RHBatch01FFTPositive09 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive09
namespace RHBatch01FFTPositive10
export _root_.RHBatch01FFTPositive10 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive10
namespace RHBatch01FFTPositive11
export _root_.RHBatch01FFTPositive11 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive11
namespace RHBatch01FFTPositive12
export _root_.RHBatch01FFTPositive12 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive12
namespace RHBatch01FFTPositive13
export _root_.RHBatch01FFTPositive13 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive13
namespace RHBatch01FFTPositive14
export _root_.RHBatch01FFTPositive14 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive14
namespace RHBatch01FFTPositive15
export _root_.RHBatch01FFTPositive15 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive15
namespace RHBatch01FFTPositive16
export _root_.RHBatch01FFTPositive16 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive16
namespace RHBatch01FFTPositive17
export _root_.RHBatch01FFTPositive17 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive17
namespace RHBatch01FFTPositive18
export _root_.RHBatch01FFTPositive18 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive18
namespace RHBatch01FFTPositive19
export _root_.RHBatch01FFTPositive19 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive19
namespace RHBatch01FFTPositive20
export _root_.RHBatch01FFTPositive20 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive20
namespace RHBatch01FFTPositive21
export _root_.RHBatch01FFTPositive21 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive21
namespace RHBatch01FFTPositive22
export _root_.RHBatch01FFTPositive22 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive22
namespace RHBatch01FFTPositive23
export _root_.RHBatch01FFTPositive23 (row00 row01 row02 row03 rows)
end RHBatch01FFTPositive23
namespace RHBatch01FourierPolynomial
export _root_.RHBatch01FourierPolynomial (coefficient imagInteger phase polynomial realInteger word)
end RHBatch01FourierPolynomial
namespace RHBatch01FullCoefficient
export _root_.RHBatch01FullCoefficient (F L W delta group weight)
end RHBatch01FullCoefficient
namespace RHBatch01GammaArithmetic
export _root_.RHBatch01GammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHBatch01GammaArithmetic
namespace RHBatch01GammaFourierTable
export _root_.RHBatch01GammaFourierTable (packets value values)
end RHBatch01GammaFourierTable
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
namespace RHHighPackedFFT
export _root_.RHHighPackedFFT (combine convolution decode digits output pack pair unbias windows)
end RHHighPackedFFT
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
namespace RHBatch01ZetaCoefficientAssembly
export _root_.RHBatch01ZetaCoefficientAssembly (add expected packets rounded total)
end RHBatch01ZetaCoefficientAssembly
namespace RHBatch01ZetaCorrelation
export _root_.RHBatch01ZetaCorrelation (aImag aReal bImag bReal combine convolution decode output sample signed)
end RHBatch01ZetaCorrelation
namespace RHBatch01ZetaCorrelationOutput00
export _root_.RHBatch01ZetaCorrelationOutput00 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput00
namespace RHBatch01ZetaCorrelationOutput01
export _root_.RHBatch01ZetaCorrelationOutput01 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput01
namespace RHBatch01ZetaCorrelationOutput02
export _root_.RHBatch01ZetaCorrelationOutput02 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput02
namespace RHBatch01ZetaCorrelationOutput03
export _root_.RHBatch01ZetaCorrelationOutput03 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput03
namespace RHBatch01ZetaCorrelationOutput04
export _root_.RHBatch01ZetaCorrelationOutput04 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput04
namespace RHBatch01ZetaCorrelationOutput05
export _root_.RHBatch01ZetaCorrelationOutput05 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput05
namespace RHBatch01ZetaCorrelationOutput06
export _root_.RHBatch01ZetaCorrelationOutput06 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput06
namespace RHBatch01ZetaCorrelationOutput07
export _root_.RHBatch01ZetaCorrelationOutput07 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput07
namespace RHBatch01ZetaCorrelationOutput08
export _root_.RHBatch01ZetaCorrelationOutput08 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput08
namespace RHBatch01ZetaCorrelationOutput09
export _root_.RHBatch01ZetaCorrelationOutput09 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput09
namespace RHBatch01ZetaCorrelationOutput10
export _root_.RHBatch01ZetaCorrelationOutput10 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput10
namespace RHBatch01ZetaCorrelationOutput11
export _root_.RHBatch01ZetaCorrelationOutput11 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput11
namespace RHBatch01ZetaCorrelationOutput12
export _root_.RHBatch01ZetaCorrelationOutput12 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput12
namespace RHBatch01ZetaCorrelationOutput13
export _root_.RHBatch01ZetaCorrelationOutput13 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput13
namespace RHBatch01ZetaCorrelationOutput14
export _root_.RHBatch01ZetaCorrelationOutput14 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput14
namespace RHBatch01ZetaCorrelationOutput15
export _root_.RHBatch01ZetaCorrelationOutput15 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput15
namespace RHBatch01ZetaCorrelationOutput16
export _root_.RHBatch01ZetaCorrelationOutput16 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput16
namespace RHBatch01ZetaCorrelationOutput17
export _root_.RHBatch01ZetaCorrelationOutput17 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput17
namespace RHBatch01ZetaCorrelationOutput18
export _root_.RHBatch01ZetaCorrelationOutput18 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput18
namespace RHBatch01ZetaCorrelationOutput19
export _root_.RHBatch01ZetaCorrelationOutput19 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput19
namespace RHBatch01ZetaCorrelationOutput20
export _root_.RHBatch01ZetaCorrelationOutput20 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput20
namespace RHBatch01ZetaCorrelationOutput21
export _root_.RHBatch01ZetaCorrelationOutput21 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput21
namespace RHBatch01ZetaCorrelationOutput22
export _root_.RHBatch01ZetaCorrelationOutput22 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput22
namespace RHBatch01ZetaCorrelationOutput23
export _root_.RHBatch01ZetaCorrelationOutput23 (row00 row01 row02 rows)
end RHBatch01ZetaCorrelationOutput23
namespace RHBatch01ZetaFourierData
export _root_.RHBatch01ZetaFourierData (row00 row01 row02 rows)
end RHBatch01ZetaFourierData
namespace TaoFivePrimes
export _root_.TaoFivePrimes (rh_batch01_height_all_gamma_fourier_enclosures rh_batch01_height_all_zeta_correlations rh_batch01_height_full_coefficient_analytic rh_batch01_height_zeta_coefficient_assembly rh_batch01_height_zeta_correlation_semantic)
end TaoFivePrimes
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHBatch01CoefficientListSum
noncomputable def value (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
open RHBatch01ZetaCoefficientAssembly
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
 (h:∀xs∈packets,(RHBatch01ZetaCorrelation.decode xs).length=N) (acc : List (Int×Int)) (ha:acc.length=N) :
 (packets.foldl (fun a xs=>add a (RHBatch01ZetaCorrelation.decode xs)) acc).length=N := by
 induction packets generalizing acc with
 | nil => exact ha
 | cons xs xss ih =>
  rw[List.foldl_cons]
  apply ih
  · intro ys hy;exact h ys (List.mem_cons_of_mem _ hy)
  · exact add_length _ _ N ha (h xs (by simp))
lemma fold_at (packets : List (List Nat)) (N : Nat)
 (h:∀xs∈packets,(RHBatch01ZetaCorrelation.decode xs).length=N) (acc : List (Int×Int)) (ha:acc.length=N)
 (j : Nat) (hj:j<N) :
 value (((packets.foldl (fun a xs=>add a (RHBatch01ZetaCorrelation.decode xs)) acc)[j]?).getD (0,0))=
 value ((acc[j]?).getD (0,0))+(packets.map (fun xs=>value (((RHBatch01ZetaCorrelation.decode xs)[j]?).getD (0,0)))).sum := by
 induction packets generalizing acc with
 | nil => simp only[List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
 | cons xs xss ih =>
  rw[List.foldl_cons,ih (by intro ys hy;exact h ys (List.mem_cons_of_mem _ hy)) _ (add_length _ _ N ha (h xs (by simp))),add_at _ _ N ha (h xs (by simp)) j hj]
  simp only[List.map_cons,List.sum_cons]
  ring
end RHBatch01CoefficientListSum
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHBatch01CoefficientGroupTotal
open RHBatch01ZetaCoefficientAssembly RHBatch01CoefficientListSum
lemma packet_shapes : packets.all (fun xs=> decide (xs.length=1025))=true := by decide +kernel
lemma packets_length : packets.length=24 := by decide +kernel
lemma total_value (m : Nat) (hm:m≤1024) :
 value ((total[m]?).getD (0,0))=
 ∑k:Fin 24,value (((RHBatch01ZetaCorrelation.decode ((packets[k.val]?).getD []))[m]?).getD (0,0)) := by
 have hlens (xs : List Nat) (hx:xs∈packets) : (RHBatch01ZetaCorrelation.decode xs).length=1025 := by
  simp only[RHBatch01ZetaCorrelation.decode,List.length_map]
  exact decide_eq_true_eq.mp ((List.all_eq_true.mp packet_shapes) xs hx)
 have h:=fold_at packets 1025 hlens (List.replicate 1025 (0,0)) (by simp) m (by omega)
 have ha:value (((List.replicate 1025 ((0,0):Int×Int))[m]?).getD (0,0))=0 := by
  rw[List.getElem?_replicate_of_lt (by omega),Option.getD_some]
  simp only[value,Int.cast_zero,zero_mul,add_zero]
 rw[ha,zero_add] at h
 have he:(packets.map (fun xs=> value (((RHBatch01ZetaCorrelation.decode xs)[m]?).getD (0,0))))=
  List.ofFn (fun k:Fin 24=> value (((RHBatch01ZetaCorrelation.decode ((packets[k.val]?).getD []))[m]?).getD (0,0))) := by
  apply List.ext_getElem
  · simp only[List.length_map,packets_length,List.length_ofFn]
  · intro k hk hk'
    have hkp:k< packets.length:=by simpa only[List.length_map] using hk
    simp only[List.getElem_map,List.getElem_ofFn,List.getElem?_eq_getElem hkp,Option.getD_some]
 rw[he,List.sum_ofFn] at h
 exact h
lemma group_total (m : Nat) (hm:m≤1024)
 (hc:∀k:Nat,k<24 → RHBatch01ZetaCorrelation.output k (RHBatch01GammaFourierTable.values k)=
   RHBatch01ZetaCorrelation.decode ((packets[k]?).getD []))
 (hs:∀k:Nat,k<24 →
  RHHighBinningSemantic.pairValue (((RHBatch01ZetaCorrelation.output k (RHBatch01GammaFourierTable.values k))[m]?).getD (0,0))/(2:ℂ)^213=
  ∑b:Fin 929,(RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient b.val k)/(2:ℂ)^128)*
   RHBatch01GammaFourierTable.value k (m+b.val)) :
 RHBatch01FullCoefficient.group (fun b k=> RHBatch01GammaFourierTable.value k (m+b))=
 value ((total[m]?).getD (0,0))/(2:ℂ)^213 := by
 unfold RHBatch01FullCoefficient.group
 rw[Finset.sum_comm,total_value m hm,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro k hk
 have h:=hs k.val k.isLt
 rw[hc k.val k.isLt] at h
 exact h.symm
lemma group_scaled (m : Nat) (hm:m≤1024)
 (hg:RHBatch01FullCoefficient.group (fun b k=> RHBatch01GammaFourierTable.value k (m+b))=
  value ((total[m]?).getD (0,0))/(2:ℂ)^213) :
 (1/512:ℂ)*RHBatch01FullCoefficient.group (fun b k=> RHBatch01GammaFourierTable.value k (m+b))=
 value ((total[m]?).getD (0,0))/(2:ℂ)^222 := by
 rw[hg,show (2:ℂ)^222=(2:ℂ)^213*512 by norm_num]
 ring
end RHBatch01CoefficientGroupTotal
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHBatch01DyadicRounding
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
end RHBatch01DyadicRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHBatch01DyadicRounding
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
end RHBatch01DyadicRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHBatch01DyadicComplex
noncomputable def value (D : Nat) (a : Int×Int) : ℂ := ((a.1:ℂ)+(a.2:ℂ)*I)/(D:ℂ)
noncomputable def mul (D : Nat) (a b : Int×Int) : Int×Int :=
  ((a.1*b.1-a.2*b.2)/(D:Int),(a.1*b.2+a.2*b.1)/(D:Int))
noncomputable def divide (a : Int×Int) (n : Nat) : Int×Int :=
  (a.1/(n:Int),a.2/(n:Int))
lemma component (a : Int) (D : Nat) (hD:0<D) :
    |(a:ℝ)/(D:ℝ)^2-((a/(D:Int):Int):ℝ)/(D:ℝ)|≤1/(D:ℝ) := by
  have h:=RHBatch01DyadicRounding.int_division_error a D hD
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
  have hr:=RHBatch01DyadicRounding.int_division_error a.1 n hn
  have hi:=RHBatch01DyadicRounding.int_division_error a.2 n hn
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
end RHBatch01DyadicComplex
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHBatch01DyadicRescale
open RHBatch01DyadicComplex
lemma rescale (B S : Nat) (hB:0<B) (hS:0<S) (p : Int×Int) :
 ‖value (B*S) p-value S (p.1/(B:Int),p.2/(B:Int))‖≤2/(S:ℝ) := by
 have h:=divide_error S B hS hB p
 have he:value S p/(B:ℂ)=value (B*S) p:=by simp only[value,Nat.cast_mul];ring
 rw[he,norm_sub_rev] at h
 exact h
end RHBatch01DyadicRescale
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHBatch01CoefficientAssemblySound
noncomputable def value (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
lemma rescale_error (p : Int×Int) :
 ‖value p/(2:ℂ)^222-value (p.1/(2:Int)^142,p.2/(2:Int)^142)/(2:ℂ)^80‖≤2/(2:ℝ)^80 := by
 have h:=RHBatch01DyadicRescale.rescale (2^142) (2^80) (by norm_num) (by norm_num) p
 simpa only [RHBatch01DyadicComplex.value,value,show (2:Nat)^142*2^80=2^222 by norm_num,
  Nat.cast_pow,Nat.cast_ofNat,Int.natCast_pow] using h
end RHBatch01CoefficientAssemblySound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHBatch01FlatRows
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
end RHBatch01FlatRows
end
section
set_option autoImplicit false
namespace RHBatch01FFTOutputSample
lemma at_index (v : List Nat) (j : Nat) (hj:j<v.length) :
 ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighContourVector.decode ((v[j]?).getD 0) := by
 unfold RHHighPackedFFT.decode RHHighContourVector.decode
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
   List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
 rfl
end RHBatch01FFTOutputSample
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHBatch01CoefficientAssemblySound
open RHBatch01ZetaCoefficientAssembly
lemma word_at (j : Nat) (hj:j≤1024) :
 (RHBatch01ZetaFourierData.rows.flatten[j]?).getD 0=RHBatch01FourierPolynomial.word j := by
 have hlen:RHBatch01ZetaFourierData.rows.flatten.length=1025:=by decide +kernel
 have hs:RHBatch01ZetaFourierData.rows.all (fun row=> decide (row.length≤512))=true:=by decide +kernel
 have hf:RHBatch01ZetaFourierData.rows.dropLast.all (fun row=> decide (row.length=512))=true:=by decide +kernel
 apply RHBatch01FlatRows.lookup 512 (by decide) 0 RHBatch01ZetaFourierData.rows
 · intro row hr;exact decide_eq_true_eq.mp ((List.all_eq_true.mp hs) row hr)
 · intro row hr;exact decide_eq_true_eq.mp ((List.all_eq_true.mp hf) row hr)
 · rw[hlen];omega
lemma expected_value (j : Nat) (hj:j≤1024) :
 value ((expected[j]?).getD (0,0))/(2:ℂ)^80=RHBatch01FourierPolynomial.coefficient j := by
 have hlen:RHBatch01ZetaFourierData.rows.flatten.length=1025:=by decide +kernel
 have h:=RHBatch01FFTOutputSample.at_index RHBatch01ZetaFourierData.rows.flatten j (by rw[hlen];omega)
 change value (((RHHighPackedFFT.decode RHBatch01ZetaFourierData.rows.flatten)[j]?).getD (0,0))/(2:ℂ)^80=_
 rw[h]
 simp only[word_at j hj,value,RHHighContourVector.decode,RHBatch01FourierPolynomial.coefficient,
  RHBatch01FourierPolynomial.realInteger,RHBatch01FourierPolynomial.imagInteger]
lemma rounded_at (j : Nat) (hj:j≤1024) :
 let p:=(total[j]?).getD (0,0)
 (p.1/(2:Int)^142,if j=0 then 0 else p.2/(2:Int)^142)=(expected[j]?).getD (0,0) := by
 have hlen:=TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly.1
 have hj':j< total.length:=by omega
 have h:=congrArg (fun xs:List (Int×Int)=>(xs[j]?).getD (0,0)) TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly.2.1
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
 ‖value ((total[j]?).getD (0,0))/(2:ℂ)^222-RHBatch01FourierPolynomial.coefficient j‖≤3/(2:ℝ)^80 := by
 let p:=(total[j]?).getD (0,0)
 let a:Int×Int:=(p.1/(2:Int)^142,p.2/(2:Int)^142)
 let b:Int×Int:=(p.1/(2:Int)^142,if j=0 then 0 else p.2/(2:Int)^142)
 have hb:value b/(2:ℂ)^80=RHBatch01FourierPolynomial.coefficient j := by
  have he:=rounded_at j hj
  rw[show b=(expected[j]?).getD (0,0) from he]
  exact expected_value j hj
 have hc:‖value a/(2:ℂ)^80-value b/(2:ℂ)^80‖≤1/(2:ℝ)^80 := by
  by_cases hj0:j=0
  · subst j
    let qi : Int := (((total[0]?).getD (0,0)).2/(2:Int)^142)
    have hi : |qi|≤1 := TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly.2.2
    have he:value a/(2:ℂ)^80-value b/(2:ℂ)^80=(qi:ℂ)*I/(2:ℂ)^80 := by
     dsimp only[a,b,p,qi]
     simp only[if_true,value,Prod.fst,Prod.snd,Int.cast_zero,zero_mul,add_zero]
     ring
    have hcases : qi= -1 ∨ qi=0 ∨ qi=1 := by
     have hh:=abs_le.mp hi
     omega
    rw[he]
    rcases hcases with h|h|h <;> rw[h] <;> norm_num[norm_div,norm_mul,norm_pow]
  · simp only[a,b,hj0,if_false,sub_self,norm_zero]
    positivity
 have hr:=rescale_error p
 change ‖value p/(2:ℂ)^222-_‖≤ _
 rw[←hb]
 exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hr hc)).trans_eq (by ring)
end RHBatch01CoefficientAssemblySound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
open scoped FourierTransform
namespace RHBatch01CoefficientFinal
lemma group_identity (m : Nat) (hm:m≤1024) :
 (1/512:ℂ)*RHBatch01FullCoefficient.group (fun b k=> RHBatch01GammaFourierTable.value k (m+b))=
 RHBatch01CoefficientListSum.value ((RHBatch01ZetaCoefficientAssembly.total[m]?).getD (0,0))/(2:ℂ)^222 := by
 apply RHBatch01CoefficientGroupTotal.group_scaled m hm
 apply RHBatch01CoefficientGroupTotal.group_total m hm
 · intro k hk;exact (TaoFivePrimes.rh_batch01_height_all_zeta_correlations k hk).1
 · intro k hk
   have h:=TaoFivePrimes.rh_batch01_height_zeta_correlation_semantic k hk (RHBatch01GammaFourierTable.values k)
    (TaoFivePrimes.rh_batch01_height_all_zeta_correlations k hk).2 ⟨m,by omega⟩
   exact h
lemma enclosure
 (hgamma:∀k j:Nat,k<24 → j<1954 →
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 ∧
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)‖≤65537)
 (m : Nat) (hm:m≤1024) :
 ‖(1/512:ℂ)*𝓕 RHBatch01FullCoefficient.W ((m:ℝ)/512)-RHBatch01FourierPolynomial.coefficient m‖≤1/10^14 := by
 let G:Nat→Nat→ℂ:=fun b k=> RHBatch01GammaFourierTable.value k (m+b)
 have hF (b : Nat) (hb:b<929) (k : Nat) (hk:k<24) : ‖RHBatch01FullCoefficient.F m b k‖≤65537 := by
  exact (hgamma k (m+b) hk (by omega)).2
 have heF (b : Nat) (hb:b<929) (k : Nat) (hk:k<24) : ‖RHBatch01FullCoefficient.F m b k-G b k‖≤1/10^15 := by
  exact (hgamma k (m+b) hk (by omega)).1
 have h:=TaoFivePrimes.rh_batch01_height_full_coefficient_analytic m hm G hF heF
 rw[group_identity m hm] at h
 have hr:=RHBatch01CoefficientAssemblySound.rounding m hm
 have ht:‖(1/512:ℂ)*𝓕 RHBatch01FullCoefficient.W ((m:ℝ)/512)-RHBatch01FourierPolynomial.coefficient m‖≤3/10^15+3/(2:ℝ)^80 :=
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h hr)
 exact ht.trans (by norm_num)
end RHBatch01CoefficientFinal
end
end RHBatch01FullCoefficientEnclosureProof
open scoped FourierTransform
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem solution (m : Nat) (hm:m≤1024) :
 ‖(1/512:ℂ)*𝓕 RHBatch01FullCoefficient.W ((m:ℝ)/512)-RHBatch01FourierPolynomial.coefficient m‖≤1/10^14 := by
 exact RHBatch01FullCoefficientEnclosureProof.RHBatch01CoefficientFinal.enclosure
  (fun k j hk hj=>TaoFivePrimes.rh_batch01_height_all_gamma_fourier_enclosures k j hk hj) m hm
#print axioms solution
