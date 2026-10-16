-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_all_gamma_fourier_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:50:45.235286+00:00
-- url     : https://prove2.me/submissions/2b5ef429-6148-4e02-8b2d-3b18196bbb17

import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_actual_input21
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_actual_input22
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_actual_input23
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation21
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation22
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation23
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_kernel_interface
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds21
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds22
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds23
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_semantic
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure00
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure01
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure02
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure03
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure04
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure05
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure06
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure07
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure08
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure09
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure10
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure11
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure12
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure13
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure14
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure15
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure16
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure17
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure18
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure19
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure20
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation00
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation01
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation02
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation03
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation04
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation05
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation06
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation07
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation08
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation09
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation10
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation11
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation12
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation13
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation14
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation15
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation16
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation17
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation18
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation19
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation20
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation21
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation22
import Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation23
namespace RHHighAllGammaFourierProof
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
namespace RHHighGammaFourierTable
export _root_.RHHighGammaFourierTable (packets value values)
end RHHighGammaFourierTable
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
namespace RHHighPackedFFT
export _root_.RHHighPackedFFT (combine convolution decode digits output pack pair unbias windows)
end RHHighPackedFFT
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
namespace RHHighZetaCorrelation
export _root_.RHHighZetaCorrelation (aImag aReal bImag bReal combine convolution decode output sample signed)
end RHHighZetaCorrelation
namespace TaoFivePrimes
export _root_.TaoFivePrimes (rh_high_height_fft_actual_input21 rh_high_height_fft_actual_input22 rh_high_height_fft_actual_input23 rh_high_height_fft_computation21 rh_high_height_fft_computation22 rh_high_height_fft_computation23 rh_high_height_fft_kernel_interface rh_high_height_gamma_fft_array_bounds21 rh_high_height_gamma_fft_array_bounds22 rh_high_height_gamma_fft_array_bounds23 rh_high_height_gamma_fft_semantic rh_high_height_gamma_fourier_enclosure00 rh_high_height_gamma_fourier_enclosure01 rh_high_height_gamma_fourier_enclosure02 rh_high_height_gamma_fourier_enclosure03 rh_high_height_gamma_fourier_enclosure04 rh_high_height_gamma_fourier_enclosure05 rh_high_height_gamma_fourier_enclosure06 rh_high_height_gamma_fourier_enclosure07 rh_high_height_gamma_fourier_enclosure08 rh_high_height_gamma_fourier_enclosure09 rh_high_height_gamma_fourier_enclosure10 rh_high_height_gamma_fourier_enclosure11 rh_high_height_gamma_fourier_enclosure12 rh_high_height_gamma_fourier_enclosure13 rh_high_height_gamma_fourier_enclosure14 rh_high_height_gamma_fourier_enclosure15 rh_high_height_gamma_fourier_enclosure16 rh_high_height_gamma_fourier_enclosure17 rh_high_height_gamma_fourier_enclosure18 rh_high_height_gamma_fourier_enclosure19 rh_high_height_gamma_fourier_enclosure20 rh_high_height_zeta_correlation00 rh_high_height_zeta_correlation01 rh_high_height_zeta_correlation02 rh_high_height_zeta_correlation03 rh_high_height_zeta_correlation04 rh_high_height_zeta_correlation05 rh_high_height_zeta_correlation06 rh_high_height_zeta_correlation07 rh_high_height_zeta_correlation08 rh_high_height_zeta_correlation09 rh_high_height_zeta_correlation10 rh_high_height_zeta_correlation11 rh_high_height_zeta_correlation12 rh_high_height_zeta_correlation13 rh_high_height_zeta_correlation14 rh_high_height_zeta_correlation15 rh_high_height_zeta_correlation16 rh_high_height_zeta_correlation17 rh_high_height_zeta_correlation18 rh_high_height_zeta_correlation19 rh_high_height_zeta_correlation20 rh_high_height_zeta_correlation21 rh_high_height_zeta_correlation22 rh_high_height_zeta_correlation23)
end TaoFivePrimes
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighGammaSampleNorm
lemma pair (p : Int×Int) (hp:|p.1|≤(2:Int)^100 ∧ |p.2|≤(2:Int)^100) :
 ‖((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85‖≤65536 := by
 have h1:|(p.1:ℝ)|≤(2:ℝ)^100:=by exact_mod_cast hp.1
 have h2:|(p.2:ℝ)|≤(2:ℝ)^100:=by exact_mod_cast hp.2
 rw[norm_div,norm_pow,norm_ofNat]
 apply (div_le_iff₀ (by positivity : (0:ℝ)<2^85)).mpr
 have h:=norm_add_le (p.1:ℂ) ((p.2:ℂ)*I)
 simp only[norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one] at h
 exact h.trans ((add_le_add h1 h2).trans_eq (by norm_num))
lemma signed (v : List Nat) (m : Nat)
 (h:|(RHHighZetaCorrelation.sample v m).1|≤(2:Int)^100 ∧ |(RHHighZetaCorrelation.sample v m).2|≤(2:Int)^100) :
 let p:=RHHighZetaCorrelation.signed v m
 ‖((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85‖≤65536 := by
 apply pair
 unfold RHHighZetaCorrelation.signed
 split_ifs <;> simpa only[Prod.fst,Prod.snd,abs_neg] using h
lemma true_bound (f z : ℂ) (he:‖f-z‖≤1/10^15) (hz:‖z‖≤65536) : ‖f‖≤65537 := by
 have h:=norm_sub_le_norm_sub_add_norm_sub f z 0
 simp only[sub_zero] at h
 exact h.trans ((add_le_add he hz).trans (by norm_num))
end RHHighGammaSampleNorm
end
end RHHighAllGammaFourierProof

namespace RHHighGammaFourierOrder21
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
set_option maxHeartbeats 1000000
open Complex
namespace RHHighGammaSignedPhase
lemma phase (j : Nat) : Complex.exp (((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)=
    if j%2=0 then (1:ℂ) else -1 := by
  have he:(((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)=(j:ℂ)*((Real.pi:ℂ)*I):=by push_cast;ring
  rw [he,Complex.exp_nat_mul,Complex.exp_pi_mul_I]
  have hj:j=j%2+2*(j/2):=(Nat.mod_add_div j 2).symm
  conv_lhs => rw [hj,pow_add,pow_mul]
  norm_num only [neg_one_sq,one_pow,mul_one]
  split_ifs with hz
  · rw [hz,pow_zero]
  · have hm:j%2=1:=by omega
    rw [hm,pow_one]
lemma value (v : List Nat) (j : Nat) :
    Complex.exp (((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)*((1/32:ℂ)*
      (((RHHighZetaCorrelation.sample v j).1:ℂ)+((RHHighZetaCorrelation.sample v j).2:ℂ)*I)/(2:ℂ)^80)=
    (((RHHighZetaCorrelation.signed v j).1:ℂ)+((RHHighZetaCorrelation.signed v j).2:ℂ)*I)/(2:ℂ)^85 := by
  rw [phase]
  unfold RHHighZetaCorrelation.signed
  split_ifs <;> simp only [Prod.fst,Prod.snd,Int.cast_neg]
  all_goals norm_num <;> ring
lemma sample_decode (v : List Nat) (j : Nat) (hj:j< v.length) :
    ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighZetaCorrelation.sample v j := by
  unfold RHHighPackedFFT.decode RHHighZetaCorrelation.sample
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
    List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
  rfl
end RHHighGammaSignedPhase
end
end RHHighGammaFourierOrder21
open scoped FourierTransform
theorem TaoFivePrimes.rh_high_height_gamma_fourier_enclosure21 (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive21.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 21) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by
  let R:=RHHighFFTInputR21.rows
  let J:=RHHighFFTInputI21.rows
  let brs:=RHHighFFTChirpR.rows.flatten
  let bis:=RHHighFFTChirpI.rows.flatten
  let bss:=RHHighFFTChirpS.rows.flatten
  have hR:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds21 R (by simp only [R,List.mem_cons,true_or])
  have hJ:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds21 J (by simp only [J,List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only [List.mem_cons,true_or])
  have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  let ar:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.entry R.flatten j.val
  let ai:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.entry J.flatten j.val
  let br:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.entry brs j.val
  let bi:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.entry bis j.val
  have hi (j:Fin 16384):
    let p:=RHHighMomentArithmetic.moment j.val (RHHighGammaArithmetic.compute j.val) 21
    let c:=RHHighFFTArithmeticBase.chirp j.val
    (p.1*c.1+p.2*c.2,p.2*c.1-p.1*c.2)=((ar j:Int)-2^166,(ai j:Int)-2^166) := by
    have h:=TaoFivePrimes.rh_high_height_fft_actual_input21 j.val j.isLt
    have hr:=RHHighGammaFourierOrder21.RHHighFFTListInterface.uniform_lookup R j.val
      (RHHighGammaFourierOrder21.RHHighFFTListInterface.lengths_from_bound R (2^167) hR.2) (by rw [hR.1];exact j.isLt)
    have hj:=RHHighGammaFourierOrder21.RHHighFFTListInterface.uniform_lookup J j.val
      (RHHighGammaFourierOrder21.RHHighFFTListInterface.lengths_from_bound J (2^167) hJ.2) (by rw [hJ.1];exact j.isLt)
    change _=(((RHHighGammaFourierOrder21.RHHighFFTListInterface.entry R.flatten j.val:Int)-2^166),
      ((RHHighGammaFourierOrder21.RHHighFFTListInterface.entry J.flatten j.val:Int)-2^166))
    rw [hr,hj]
    exact h
  have hk (j:Fin 32767):((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs :=
    (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j.val j.isLt).1
  have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
      (List.ofFn (fun j=>br j+bi j)) RHHighFFTArithmeticBase.chirp=
      RHHighPackedFFT.decode RHHighFFTPositive21.rows.flatten := by
    have hs:List.ofFn (fun j:Fin 32767=>br j+bi j)=bss := by
      apply RHHighGammaFourierOrder21.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
      intro j hj
      exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j hj).2
    rw [hs,RHHighGammaFourierOrder21.RHHighFFTListInterface.ofFn_at R.flatten hR.1,
      RHHighGammaFourierOrder21.RHHighFFTListInterface.ofFn_at J.flatten hJ.1,
      RHHighGammaFourierOrder21.RHHighFFTListInterface.ofFn_at brs hKR,RHHighGammaFourierOrder21.RHHighFFTListInterface.ofFn_at bis hKI]
    exact TaoFivePrimes.rh_high_height_fft_computation21
  have h:=TaoFivePrimes.rh_high_height_gamma_fft_semantic 21 (by decide) ar ai br bi
    (fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.bounded_at R.flatten (2^167)
      (RHHighGammaFourierOrder21.RHHighFFTListInterface.flatten_bounded R (2^167) hR.2) j.val)
    (fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.bounded_at J.flatten (2^167)
      (RHHighGammaFourierOrder21.RHHighFFTListInterface.flatten_bounded J (2^167) hJ.2) j.val)
    (fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.bounded_at brs (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 j.val)
    (fun j=>RHHighGammaFourierOrder21.RHHighFFTListInterface.bounded_at bis (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 j.val) hi hk ⟨m,by omega⟩ (by change m≤1953;omega)
  rw [hout] at h
  have hv:RHHighFFTPositive21.rows.flatten.length=2048:=by decide +kernel
  rw [RHHighGammaFourierOrder21.RHHighGammaSignedPhase.sample_decode _ m (by rw [hv];omega)] at h
  have he:=RHHighGammaFourierOrder21.RHHighGammaSignedPhase.value RHHighFFTPositive21.rows.flatten m
  simp only [mul_div_assoc] at he
  rw [he] at h
  exact h
namespace RHHighGammaFourierOrder22
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
set_option maxHeartbeats 1000000
open Complex
namespace RHHighGammaSignedPhase
lemma phase (j : Nat) : Complex.exp (((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)=
    if j%2=0 then (1:ℂ) else -1 := by
  have he:(((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)=(j:ℂ)*((Real.pi:ℂ)*I):=by push_cast;ring
  rw [he,Complex.exp_nat_mul,Complex.exp_pi_mul_I]
  have hj:j=j%2+2*(j/2):=(Nat.mod_add_div j 2).symm
  conv_lhs => rw [hj,pow_add,pow_mul]
  norm_num only [neg_one_sq,one_pow,mul_one]
  split_ifs with hz
  · rw [hz,pow_zero]
  · have hm:j%2=1:=by omega
    rw [hm,pow_one]
lemma value (v : List Nat) (j : Nat) :
    Complex.exp (((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)*((1/32:ℂ)*
      (((RHHighZetaCorrelation.sample v j).1:ℂ)+((RHHighZetaCorrelation.sample v j).2:ℂ)*I)/(2:ℂ)^80)=
    (((RHHighZetaCorrelation.signed v j).1:ℂ)+((RHHighZetaCorrelation.signed v j).2:ℂ)*I)/(2:ℂ)^85 := by
  rw [phase]
  unfold RHHighZetaCorrelation.signed
  split_ifs <;> simp only [Prod.fst,Prod.snd,Int.cast_neg]
  all_goals norm_num <;> ring
lemma sample_decode (v : List Nat) (j : Nat) (hj:j< v.length) :
    ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighZetaCorrelation.sample v j := by
  unfold RHHighPackedFFT.decode RHHighZetaCorrelation.sample
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
    List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
  rfl
end RHHighGammaSignedPhase
end
end RHHighGammaFourierOrder22
open scoped FourierTransform
theorem TaoFivePrimes.rh_high_height_gamma_fourier_enclosure22 (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive22.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 22) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by
  let R:=RHHighFFTInputR22.rows
  let J:=RHHighFFTInputI22.rows
  let brs:=RHHighFFTChirpR.rows.flatten
  let bis:=RHHighFFTChirpI.rows.flatten
  let bss:=RHHighFFTChirpS.rows.flatten
  have hR:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds22 R (by simp only [R,List.mem_cons,true_or])
  have hJ:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds22 J (by simp only [J,List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only [List.mem_cons,true_or])
  have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  let ar:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.entry R.flatten j.val
  let ai:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.entry J.flatten j.val
  let br:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.entry brs j.val
  let bi:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.entry bis j.val
  have hi (j:Fin 16384):
    let p:=RHHighMomentArithmetic.moment j.val (RHHighGammaArithmetic.compute j.val) 22
    let c:=RHHighFFTArithmeticBase.chirp j.val
    (p.1*c.1+p.2*c.2,p.2*c.1-p.1*c.2)=((ar j:Int)-2^166,(ai j:Int)-2^166) := by
    have h:=TaoFivePrimes.rh_high_height_fft_actual_input22 j.val j.isLt
    have hr:=RHHighGammaFourierOrder22.RHHighFFTListInterface.uniform_lookup R j.val
      (RHHighGammaFourierOrder22.RHHighFFTListInterface.lengths_from_bound R (2^167) hR.2) (by rw [hR.1];exact j.isLt)
    have hj:=RHHighGammaFourierOrder22.RHHighFFTListInterface.uniform_lookup J j.val
      (RHHighGammaFourierOrder22.RHHighFFTListInterface.lengths_from_bound J (2^167) hJ.2) (by rw [hJ.1];exact j.isLt)
    change _=(((RHHighGammaFourierOrder22.RHHighFFTListInterface.entry R.flatten j.val:Int)-2^166),
      ((RHHighGammaFourierOrder22.RHHighFFTListInterface.entry J.flatten j.val:Int)-2^166))
    rw [hr,hj]
    exact h
  have hk (j:Fin 32767):((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs :=
    (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j.val j.isLt).1
  have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
      (List.ofFn (fun j=>br j+bi j)) RHHighFFTArithmeticBase.chirp=
      RHHighPackedFFT.decode RHHighFFTPositive22.rows.flatten := by
    have hs:List.ofFn (fun j:Fin 32767=>br j+bi j)=bss := by
      apply RHHighGammaFourierOrder22.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
      intro j hj
      exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j hj).2
    rw [hs,RHHighGammaFourierOrder22.RHHighFFTListInterface.ofFn_at R.flatten hR.1,
      RHHighGammaFourierOrder22.RHHighFFTListInterface.ofFn_at J.flatten hJ.1,
      RHHighGammaFourierOrder22.RHHighFFTListInterface.ofFn_at brs hKR,RHHighGammaFourierOrder22.RHHighFFTListInterface.ofFn_at bis hKI]
    exact TaoFivePrimes.rh_high_height_fft_computation22
  have h:=TaoFivePrimes.rh_high_height_gamma_fft_semantic 22 (by decide) ar ai br bi
    (fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.bounded_at R.flatten (2^167)
      (RHHighGammaFourierOrder22.RHHighFFTListInterface.flatten_bounded R (2^167) hR.2) j.val)
    (fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.bounded_at J.flatten (2^167)
      (RHHighGammaFourierOrder22.RHHighFFTListInterface.flatten_bounded J (2^167) hJ.2) j.val)
    (fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.bounded_at brs (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 j.val)
    (fun j=>RHHighGammaFourierOrder22.RHHighFFTListInterface.bounded_at bis (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 j.val) hi hk ⟨m,by omega⟩ (by change m≤1953;omega)
  rw [hout] at h
  have hv:RHHighFFTPositive22.rows.flatten.length=2048:=by decide +kernel
  rw [RHHighGammaFourierOrder22.RHHighGammaSignedPhase.sample_decode _ m (by rw [hv];omega)] at h
  have he:=RHHighGammaFourierOrder22.RHHighGammaSignedPhase.value RHHighFFTPositive22.rows.flatten m
  simp only [mul_div_assoc] at he
  rw [he] at h
  exact h
namespace RHHighGammaFourierOrder23
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
set_option maxHeartbeats 1000000
open Complex
namespace RHHighGammaSignedPhase
lemma phase (j : Nat) : Complex.exp (((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)=
    if j%2=0 then (1:ℂ) else -1 := by
  have he:(((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)=(j:ℂ)*((Real.pi:ℂ)*I):=by push_cast;ring
  rw [he,Complex.exp_nat_mul,Complex.exp_pi_mul_I]
  have hj:j=j%2+2*(j/2):=(Nat.mod_add_div j 2).symm
  conv_lhs => rw [hj,pow_add,pow_mul]
  norm_num only [neg_one_sq,one_pow,mul_one]
  split_ifs with hz
  · rw [hz,pow_zero]
  · have hm:j%2=1:=by omega
    rw [hm,pow_one]
lemma value (v : List Nat) (j : Nat) :
    Complex.exp (((2*Real.pi*((j:ℝ)/2):ℝ):ℂ)*I)*((1/32:ℂ)*
      (((RHHighZetaCorrelation.sample v j).1:ℂ)+((RHHighZetaCorrelation.sample v j).2:ℂ)*I)/(2:ℂ)^80)=
    (((RHHighZetaCorrelation.signed v j).1:ℂ)+((RHHighZetaCorrelation.signed v j).2:ℂ)*I)/(2:ℂ)^85 := by
  rw [phase]
  unfold RHHighZetaCorrelation.signed
  split_ifs <;> simp only [Prod.fst,Prod.snd,Int.cast_neg]
  all_goals norm_num <;> ring
lemma sample_decode (v : List Nat) (j : Nat) (hj:j< v.length) :
    ((RHHighPackedFFT.decode v)[j]?).getD (0,0)=RHHighZetaCorrelation.sample v j := by
  unfold RHHighPackedFFT.decode RHHighZetaCorrelation.sample
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hj),Option.getD_some,
    List.getElem_map,List.getElem?_eq_getElem hj,Option.getD_some]
  rfl
end RHHighGammaSignedPhase
end
end RHHighGammaFourierOrder23
open scoped FourierTransform
theorem TaoFivePrimes.rh_high_height_gamma_fourier_enclosure23 (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive23.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 23) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by
  let R:=RHHighFFTInputR23.rows
  let J:=RHHighFFTInputI23.rows
  let brs:=RHHighFFTChirpR.rows.flatten
  let bis:=RHHighFFTChirpI.rows.flatten
  let bss:=RHHighFFTChirpS.rows.flatten
  have hR:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds23 R (by simp only [R,List.mem_cons,true_or])
  have hJ:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds23 J (by simp only [J,List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only [List.mem_cons,true_or])
  have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  let ar:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.entry R.flatten j.val
  let ai:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.entry J.flatten j.val
  let br:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.entry brs j.val
  let bi:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.entry bis j.val
  have hi (j:Fin 16384):
    let p:=RHHighMomentArithmetic.moment j.val (RHHighGammaArithmetic.compute j.val) 23
    let c:=RHHighFFTArithmeticBase.chirp j.val
    (p.1*c.1+p.2*c.2,p.2*c.1-p.1*c.2)=((ar j:Int)-2^166,(ai j:Int)-2^166) := by
    have h:=TaoFivePrimes.rh_high_height_fft_actual_input23 j.val j.isLt
    have hr:=RHHighGammaFourierOrder23.RHHighFFTListInterface.uniform_lookup R j.val
      (RHHighGammaFourierOrder23.RHHighFFTListInterface.lengths_from_bound R (2^167) hR.2) (by rw [hR.1];exact j.isLt)
    have hj:=RHHighGammaFourierOrder23.RHHighFFTListInterface.uniform_lookup J j.val
      (RHHighGammaFourierOrder23.RHHighFFTListInterface.lengths_from_bound J (2^167) hJ.2) (by rw [hJ.1];exact j.isLt)
    change _=(((RHHighGammaFourierOrder23.RHHighFFTListInterface.entry R.flatten j.val:Int)-2^166),
      ((RHHighGammaFourierOrder23.RHHighFFTListInterface.entry J.flatten j.val:Int)-2^166))
    rw [hr,hj]
    exact h
  have hk (j:Fin 32767):((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs :=
    (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j.val j.isLt).1
  have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
      (List.ofFn (fun j=>br j+bi j)) RHHighFFTArithmeticBase.chirp=
      RHHighPackedFFT.decode RHHighFFTPositive23.rows.flatten := by
    have hs:List.ofFn (fun j:Fin 32767=>br j+bi j)=bss := by
      apply RHHighGammaFourierOrder23.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
      intro j hj
      exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j hj).2
    rw [hs,RHHighGammaFourierOrder23.RHHighFFTListInterface.ofFn_at R.flatten hR.1,
      RHHighGammaFourierOrder23.RHHighFFTListInterface.ofFn_at J.flatten hJ.1,
      RHHighGammaFourierOrder23.RHHighFFTListInterface.ofFn_at brs hKR,RHHighGammaFourierOrder23.RHHighFFTListInterface.ofFn_at bis hKI]
    exact TaoFivePrimes.rh_high_height_fft_computation23
  have h:=TaoFivePrimes.rh_high_height_gamma_fft_semantic 23 (by decide) ar ai br bi
    (fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.bounded_at R.flatten (2^167)
      (RHHighGammaFourierOrder23.RHHighFFTListInterface.flatten_bounded R (2^167) hR.2) j.val)
    (fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.bounded_at J.flatten (2^167)
      (RHHighGammaFourierOrder23.RHHighFFTListInterface.flatten_bounded J (2^167) hJ.2) j.val)
    (fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.bounded_at brs (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 j.val)
    (fun j=>RHHighGammaFourierOrder23.RHHighFFTListInterface.bounded_at bis (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 j.val) hi hk ⟨m,by omega⟩ (by change m≤1953;omega)
  rw [hout] at h
  have hv:RHHighFFTPositive23.rows.flatten.length=2048:=by decide +kernel
  rw [RHHighGammaFourierOrder23.RHHighGammaSignedPhase.sample_decode _ m (by rw [hv];omega)] at h
  have he:=RHHighGammaFourierOrder23.RHHighGammaSignedPhase.value RHHighFFTPositive23.rows.flatten m
  simp only [mul_div_assoc] at he
  rw [he] at h
  exact h
open scoped FourierTransform
theorem solution (k j : Nat) (hk:k<24) (hj:j<1954) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537 := by
 interval_cases k
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure00 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive00.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation00.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure01 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive01.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation01.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure02 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive02.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation02.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure03 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive03.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation03.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure04 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive04.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation04.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure05 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive05.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation05.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure06 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive06.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation06.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure07 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive07.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation07.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure08 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive08.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation08.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure09 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive09.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation09.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure10 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive10.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation10.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure11 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive11.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation11.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure12 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive12.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation12.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure13 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive13.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation13.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure14 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive14.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation14.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure15 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive15.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation15.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure16 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive16.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation16.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure17 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive17.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation17.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure18 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive18.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation18.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure19 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive19.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation19.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure20 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive20.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation20.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure21 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive21.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation21.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure22 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive22.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation22.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
 · have he:=TaoFivePrimes.rh_high_height_gamma_fourier_enclosure23 j hj
   have hz:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.signed RHHighFFTPositive23.rows.flatten j
    (TaoFivePrimes.rh_high_height_zeta_correlation23.2 j hj)
   have hnorm:=RHHighAllGammaFourierProof.RHHighGammaSampleNorm.true_bound _ _ he hz
   simpa only[RHHighGammaFourierTable.value,RHHighGammaFourierTable.values,RHHighGammaFourierTable.packets,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using And.intro he hnorm
#print axioms solution
