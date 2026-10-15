-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_fft_semantic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T07:46:44.444773+00:00
-- url     : https://prove2.me/submissions/117d75ee-f851-4a06-a00c-6276b6e45161

import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourReference
import Definitions.Def_TaoFivePrimes_RHHighContourUnit
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighGammaArithmetic
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_fourier_polynomial_bounds
import Theorems.Thm_TaoFivePrimes_rh_high_height_vector_fft_semantic
import Theorems.Thm_TaoFivePrimes_rh_pi_enclosure_700
namespace RHHighRepairedContourFFT
namespace RHHighContourCoefficientData
export _root_.RHHighContourCoefficientData (D amplitude coefficient comparison decode divide frequency inputCoefficient mul proposed rootIndex seed)
end RHHighContourCoefficientData
namespace RHHighContourReference
export _root_.RHHighContourReference (Record check frequency iterate lookup lookup_checked lookup_m record0001 record0002 record0003 record0004 record0005 record0006 record0007 record0008 record0009 record0010 record0011 record0012 record0013 record0014 record0015 record0016 record0017 record0018 record0019 record0020 record0021 record0022 record0023 record0024 record0025 record0026 record0027 record0028 record0029 record0030 record0031 record0032 record0033 record0034 record0035 record0036 record0037 record0038 record0039 record0040 record0041 record0042 record0043 record0044 record0045 record0046 record0047 record0048 record0049 record0050 record0051 record0052 record0053 record0054 record0055 record0056 record0057 record0058 record0059 record0060 record0061 record0062 record0063 record0064 record0065 record0066 record0067 record0068 record0069 record0070 record0071 record0072 record0073 record0074 record0075 record0076 record0077 record0078 record0079 record0080 record0081 record0082 record0083 record0084 record0085 record0086 record0087 record0088 record0089 record0090 record0091 record0092 record0093 record0094 record0095 record0096 record0097 record0098 record0099 record0100 record0101 record0102 record0103 record0104 record0105 record0106 record0107 record0108 record0109 record0110 record0111 record0112 record0113 record0114 record0115 record0116 record0117 record0118 record0119 record0120 record0121 record0122 record0123 record0124 record0125 record0126 record0127 record0128 record0129 record0130 record0131 record0132 record0133 record0134 record0135 record0136 record0137 record0138 record0139 record0140 record0141 record0142 record0143 record0144 record0145 record0146 record0147 record0148 record0149 record0150 record0151 record0152 record0153 record0154 record0155 record0156 record0157 record0158 record0159 record0160 record0161 record0162 record0163 record0164 record0165 record0166 record0167 record0168 record0169 record0170 record0171 record0172 record0173 record0174 record0175 record0176 record0177 record0178 record0179 record0180 record0181 record0182 record0183 record0184 record0185 record0186 record0187 record0188 record0189 record0190 record0191 record0192 record0193 record0194 record0195 record0196 record0197 record0198 record0199 record0200 record0201 record0202 record0203 record0204 record0205 record0206 record0207 record0208 record0209 record0210 record0211 record0212 record0213 record0214 record0215 record0216 record0217 record0218 record0219 record0220 record0221 record0222 record0223 record0224 record0225 record0226 record0227 record0228 record0229 record0230 record0231 record0232 record0233 record0234 record0235 record0236 record0237 record0238 record0239 record0240 record0241 record0242 record0243 record0244 record0245 record0246 record0247 record0248 record0249 record0250 record0251 record0252 record0253 record0254 record0255 record0256 record0257 record0258 record0259 record0260 record0261 record0262 record0263 record0264 record0265 record0266 record0267 record0268 record0269 record0270 record0271 record0272 record0273 record0274 record0275 record0276 record0277 record0278 record0279 record0280 record0281 record0282 record0283 record0284 record0285 record0286 record0287 record0288 record0289 record0290 record0291 record0292 record0293 record0294 record0295 record0296 record0297 record0298 record0299 record0300 record0301 record0302 record0303 record0304 record0305 record0306 record0307 record0308 record0309 record0310 record0311 record0312 record0313 record0314 record0315 record0316 record0317 record0318 record0319 record0320 record0321 record0322 record0323 record0324 record0325 record0326 record0327 record0328 record0329 record0330 record0331 record0332 record0333 record0334 record0335 record0336 record0337 record0338 record0339 record0340 record0341 record0342 record0343 record0344 record0345 record0346 record0347 record0348 record0349 record0350 record0351 record0352 record0353 record0354 record0355 record0356 record0357 record0358 record0359 record0360 record0361 record0362 record0363 record0364 record0365 record0366 record0367 record0368 record0369 record0370 record0371 record0372 record0373 record0374 record0375 record0376 record0377 record0378 record0379 record0380 record0381 record0382 record0383 record0384 record0385 record0386 record0387 record0388 record0389 record0390 record0391 record0392 record0393 record0394 record0395 record0396 record0397 record0398 record0399 record0400 record0401 record0402 record0403 record0404 record0405 record0406 record0407 record0408 record0409 record0410 record0411 record0412 record0413 record0414 record0415 record0416 record0417 record0418 record0419 record0420 record0421 record0422 record0423 record0424 record0425 record0426 record0427 record0428 record0429 record0430 record0431 record0432 record0433 record0434 record0435 record0436 record0437 record0438 record0439 record0440 record0441 record0442 record0443 record0444 record0445 record0446 record0447 record0448 record0449 record0450 record0451 record0452 record0453 record0454 record0455 record0456 record0457 record0458 record0459 record0460 record0461 record0462 record0463 record0464 record0465 record0466 record0467 record0468 record0469 record0470 record0471 record0472 record0473 record0474 record0475 record0476 record0477 record0478 record0479 record0480 record0481 record0482 record0483 record0484 record0485 record0486 record0487 record0488 record0489 record0490 record0491 record0492 record0493 record0494 record0495 record0496 record0497 record0498 record0499 record0500 record0501 record0502 record0503 record0504 record0505 record0506 record0507 record0508 record0509 record0510 record0511 record0512 record0513 record0514 record0515 record0516 record0517 record0518 record0519 record0520 record0521 record0522 record0523 record0524 record0525 record0526 record0527 record0528 record0529 record0530 record0531 record0532 record0533 record0534 record0535 record0536 record0537 record0538 record0539 record0540 record0541 record0542 record0543 record0544 record0545 record0546 record0547 record0548 record0549 record0550 record0551 record0552 record0553 record0554 record0555 record0556 record0557 record0558 record0559 record0560 record0561 record0562 record0563 record0564 record0565 record0566 record0567 record0568 record0569 record0570 record0571 record0572 record0573 record0574 record0575 record0576 record0577 record0578 record0579 record0580 record0581 record0582 record0583 record0584 record0585 record0586 record0587 record0588 record0589 record0590 record0591 record0592 record0593 record0594 record0595 record0596 record0597 record0598 record0599 record0600 record0601 record0602 record0603 record0604 record0605 record0606 record0607 record0608 record0609 record0610 record0611 record0612 record0613 record0614 record0615 record0616 record0617 record0618 record0619 record0620 record0621 record0622 record0623 record0624 record0625 record0626 record0627 record0628 record0629 record0630 record0631 record0632 record0633 record0634 record0635 record0636 record0637 record0638 record0639 record0640 record0641 record0642 record0643 record0644 record0645 record0646 record0647 record0648 record0649 record0650 record0651 record0652 record0653 record0654 record0655 record0656 record0657 record0658 record0659 record0660 record0661 record0662 record0663 record0664 record0665 record0666 record0667 record0668 record0669 record0670 record0671 record0672 record0673 record0674 record0675 record0676 record0677 record0678 record0679 record0680 record0681 record0682 record0683 record0684 record0685 record0686 record0687 record0688 record0689 record0690 record0691 record0692 record0693 record0694 record0695 record0696 record0697 record0698 record0699 record0700 record0701 record0702 record0703 record0704 record0705 record0706 record0707 record0708 record0709 record0710 record0711 record0712 record0713 record0714 record0715 record0716 record0717 record0718 record0719 record0720 record0721 record0722 record0723 record0724 record0725 record0726 record0727 record0728 record0729 record0730 record0731 record0732 record0733 record0734 record0735 record0736 record0737 record0738 record0739 record0740 record0741 record0742 record0743 record0744 record0745 record0746 record0747 record0748 record0749 record0750 record0751 record0752 record0753 record0754 record0755 record0756 record0757 record0758 record0759 record0760 record0761 record0762 record0763 record0764 record0765 record0766 record0767 record0768 record0769 record0770 record0771 record0772 record0773 record0774 record0775 record0776 record0777 record0778 record0779 record0780 record0781 record0782 record0783 record0784 record0785 record0786 record0787 record0788 record0789 record0790 record0791 record0792 record0793 record0794 record0795 record0796 record0797 record0798 record0799 record0800 record0801 record0802 record0803 record0804 record0805 record0806 record0807 record0808 record0809 record0810 record0811 record0812 record0813 record0814 record0815 record0816 record0817 record0818 record0819 record0820 record0821 record0822 record0823 record0824 record0825 record0826 record0827 record0828 record0829 record0830 record0831 record0832 record0833 record0834 record0835 record0836 record0837 record0838 record0839 record0840 record0841 record0842 record0843 record0844 record0845 record0846 record0847 record0848 record0849 record0850 record0851 record0852 record0853 record0854 record0855 record0856 record0857 record0858 record0859 record0860 record0861 record0862 record0863 record0864 record0865 record0866 record0867 record0868 record0869 record0870 record0871 record0872 record0873 record0874 record0875 record0876 record0877 record0878 record0879 record0880 record0881 record0882 record0883 record0884 record0885 record0886 record0887 record0888 record0889 record0890 record0891 record0892 record0893 record0894 record0895 record0896 record0897 record0898 record0899 record0900 record0901 record0902 record0903 record0904 record0905 record0906 record0907 record0908 record0909 record0910 record0911 record0912 record0913 record0914 record0915 record0916 record0917 record0918 record0919 record0920 record0921 record0922 record0923 record0924 record0925 record0926 record0927 record0928 record0929 record0930 record0931 record0932 record0933 record0934 record0935 record0936 record0937 record0938 record0939 record0940 record0941 record0942 record0943 record0944 record0945 record0946 record0947 record0948 record0949 record0950 record0951 record0952 record0953 record0954 record0955 record0956 record0957 record0958 record0959 record0960 record0961 record0962 record0963 record0964 record0965 record0966 record0967 record0968 record0969 record0970 record0971 record0972 record0973 record0974 record0975 record0976 record0977 record0978 record0979 record0980 record0981 record0982 record0983 record0984 record0985 record0986 record0987 record0988 record0989 record0990 record0991 record0992 record0993 record0994 record0995 record0996 record0997 record0998 record0999 record1000 record1001 record1002 record1003 record1004 record1005 record1006 record1007 record1008 record1009 record1010 record1011 record1012 record1013 record1014 record1015 record1016 record1017 record1018 record1019 record1020 record1021 record1022 record1023 record1024 records rr)
end RHHighContourReference
namespace RHHighContourUnit
export _root_.RHHighContourUnit (D H pair root_checked)
end RHHighContourUnit
namespace RHHighContourVector
export _root_.RHHighContourVector (coefficient decode raw value vector)
end RHHighContourVector
namespace RHHighFourierPolynomial
export _root_.RHHighFourierPolynomial (coefficient imagInteger phase polynomial realInteger word)
end RHHighFourierPolynomial
namespace RHHighGammaArithmetic
export _root_.RHHighGammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHHighGammaArithmetic
namespace RHHighGammaGuards
export _root_.RHHighGammaGuards (guard)
end RHHighGammaGuards
namespace RHHighGenericExpHorner
export _root_.RHHighGenericExpHorner (cn cp horner sn sp)
end RHHighGenericExpHorner
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
namespace RHHighZetaFourierData
export _root_.RHHighZetaFourierData (row00 row01 row02 rows)
end RHHighZetaFourierData
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighChirpDFT
noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((Real.pi*x:ℝ)*I)
lemma phase_norm (x : ℝ) : ‖phase x‖=1 := by rw [phase,Complex.norm_exp];simp
lemma phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma chirp_factorization (N x y : ℝ) :
    phase (-2*x*y/N)=phase (-x^2/N)*phase (-y^2/N)*phase ((x-y)^2/N) := by
  rw [←phase_add,←phase_add]
  congr 1
  ring
noncomputable def dft {N : Nat} (a : Fin N→ℂ) (n : Fin N) : ℂ :=
  ∑ m : Fin N, a m*phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ))
lemma dft_chirp {N : Nat} (a : Fin N→ℂ) (n : Fin N) :
    dft a n=phase (-(n.val:ℝ)^2/(N:ℝ))*
      ∑ m : Fin N, (a m*phase (-(m.val:ℝ)^2/(N:ℝ)))*
        phase (((n.val:ℝ)-(m.val:ℝ))^2/(N:ℝ)) := by
  unfold dft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show -2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ)= -2*(n.val:ℝ)*(m.val:ℝ)/(N:ℝ) by ring,
    chirp_factorization]
  ring
lemma dft_error {N : Nat} (a b : Fin N→ℂ) (ε : ℝ)
    (he : ∀ m, ‖a m-b m‖≤ε) (n : Fin N) :
    ‖dft a n-dft b n‖≤(N:ℝ)*ε := by
  unfold dft
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m : Fin N, ‖a m*phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ))-
        b m*phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ m : Fin N, ε := by
      apply Finset.sum_le_sum
      intro m hm
      rw [←sub_mul,norm_mul,phase_norm,mul_one]
      exact he m
    _ = _ := by simp
lemma product_error (a b a' b' : ℂ) (A B εa εb : ℝ)
    (hA : ‖a'‖≤A) (hB : ‖b‖≤B) (ha : ‖a-a'‖≤εa) (hb : ‖b-b'‖≤εb)
    (hεa : 0≤εa) (hεb : 0≤εb) :
    ‖a*b-a'*b'‖≤εa*B+A*εb := by
  calc
    _ = ‖(a-a')*b+a'*(b-b')‖ := by congr 1;ring
    _ ≤ ‖(a-a')*b‖+‖a'*(b-b')‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul ha hB (norm_nonneg _) hεa)
        (mul_le_mul hA hb (norm_nonneg _) (le_trans (norm_nonneg _) hA))
end RHHighChirpDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighSparseContourDFT
open RHHighChirpDFT
noncomputable def spike {N : Nat} (p : Fin N) (z : ℂ) (j : Fin N) : ℂ := if j=p then z else 0
lemma dft_spike {N : Nat} (p r : Fin N) (z : ℂ) :
    dft (spike p z) r=z*phase (-2*(p.val:ℝ)*(r.val:ℝ)/(N:ℝ)) := by
  simp [dft,spike,ite_mul,Finset.sum_ite_eq']
lemma dft_add {N : Nat} (a b : Fin N→ℂ) (r : Fin N) :
    dft (fun j=>a j+b j) r=dft a r+dft b r := by
  simp only [dft,add_mul,Finset.sum_add_distrib]
lemma dft_sum {N M : Nat} (a : Fin M→Fin N→ℂ) (r : Fin N) :
    dft (fun j=>∑ m:Fin M,a m j) r=∑ m:Fin M,dft (a m) r := by
  simp only [dft,Finset.sum_mul]
  rw [Finset.sum_comm]
lemma phase_period (r : Nat) : phase (-2*(r:ℝ))=1 := by
  have he:((Real.pi*(-2*(r:ℝ)):ℝ):ℂ)*I=-((r:ℂ)*(2*(Real.pi:ℂ)*I)) := by
    push_cast
    ring
  rw [phase,he,Complex.exp_neg,Complex.exp_nat_mul_two_pi_mul_I,inv_one]
lemma positive_phase (m : Fin 1024) (r : Fin 16384) :
    phase (-2*((16383-m.val:Nat):ℝ)*(r.val:ℝ)/16384)=
      phase (2*((m.val:ℝ)+1)*(r.val:ℝ)/16384) := by
  have hm:(16383-m.val:Nat)+m.val=16383:=Nat.sub_add_cancel (by omega)
  have hmR:((16383-m.val:Nat):ℝ)+(m.val:ℝ)=16383:=by exact_mod_cast hm
  have he:-2*((16383-m.val:Nat):ℝ)*(r.val:ℝ)/16384=
      2*((m.val:ℝ)+1)*(r.val:ℝ)/16384+(-2*(r.val:ℝ)) := by nlinarith only [hmR]
  rw [he,phase_add,phase_period,mul_one]
noncomputable def spectrum (a0 : ℂ) (ap an : Fin 1024→ℂ) (j : Fin 16384) : ℂ :=
  spike ⟨0,by decide⟩ a0 j+
    ∑ m:Fin 1024,(spike ⟨16383-m.val,by omega⟩ (ap m) j+spike ⟨m.val+1,by omega⟩ (an m) j)
lemma spectrum_dft (a0 : ℂ) (ap an : Fin 1024→ℂ) (r : Fin 16384) :
    dft (spectrum a0 ap an) r=a0+
      ∑ m:Fin 1024,(ap m*phase (2*((m.val:ℝ)+1)*(r.val:ℝ)/16384)+
        an m*phase (-2*((m.val:ℝ)+1)*(r.val:ℝ)/16384)) := by
  unfold spectrum
  rw [dft_add,dft_spike,dft_sum]
  have h0:phase 0=1:=by simp [phase]
  simp only [Nat.cast_zero,mul_zero,zero_mul,zero_div,h0,mul_one]
  apply congrArg (fun z:ℂ=>a0+z)
  apply Finset.sum_congr rfl
  intro m hm
  rw [dft_add,dft_spike,dft_spike]
  simp only [Fin.val_mk,Nat.cast_ofNat]
  rw [positive_phase]
  push_cast
  rfl
end RHHighSparseContourDFT
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
set_option maxRecDepth 10000
open Complex
namespace RHHighContourCoefficient
open RHHighDyadicComplex
abbrev D : Nat := 2^128
noncomputable def step (a w : Int×Int) (n : Nat) : Int×Int := divide (mul D a w) n
lemma step_error (a w : Int×Int) (z v : ℂ) (n : Nat) (hn:0<n)
    (ε : ℝ) (hε:0≤ε) (hz:‖z‖≤1000) (hw:‖value D w‖≤1)
    (ha:‖value D a-z‖≤ε) (hv:‖value D w-v‖≤1/10^36) :
    ‖value D (step a w n)-z*v/(n:ℂ)‖≤ε+1/10^30 := by
  have hd:(0:ℝ)<D:=by norm_num [D]
  have hnR:(1:ℝ)≤n:=by exact_mod_cast hn
  have hnC:‖(n:ℂ)‖=(n:ℝ):=by simp
  have hm:=RHHighChirpDFT.product_error (value D a) (value D w) z v
    1000 1 ε (1/10^36) hz hw ha hv hε (by norm_num)
  have hr:=mul_error D (by norm_num [D]) a w
  have hmul:‖value D (mul D a w)-z*v‖≤2/(D:ℝ)+ε+1000/10^36 := by
    have h:=(norm_sub_le_norm_sub_add_norm_sub (value D (mul D a w))
      (value D a*value D w) (z*v)).trans (add_le_add hr hm)
    nlinarith only [h]
  have hdiv:‖value D (mul D a w)/(n:ℂ)-z*v/(n:ℂ)‖≤2/(D:ℝ)+ε+1000/10^36 := by
    rw [←sub_div,norm_div,hnC]
    exact (div_le_self (norm_nonneg _) hnR).trans hmul
  have hround:=divide_error D n (by norm_num [D]) hn (mul D a w)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hround hdiv)).trans (by
    norm_num [D]
    linarith)
lemma seed_error (a u amp : Int×Int) (c phase e : ℂ)
    (ha:value D a=c) (hc:‖c‖≤1) (hp:‖phase‖≤1)
    (hu:‖value D u-phase‖≤2/(D:ℝ))
    (he:‖e‖≤2000) (hamp:‖value D amp-e‖≤1/10^25) :
    ‖value D (mul D (mul D a u) amp)-c*phase*e‖≤1/10^24 := by
  have hcpu:‖value D (mul D a u)-c*phase‖≤4/(D:ℝ) := by
    have hm:=mul_error D (by norm_num [D]) a u
    rw [ha] at hm
    have hu':‖c*value D u-c*phase‖≤2/(D:ℝ) := by
      rw [←mul_sub,norm_mul]
      exact (mul_le_mul hc hu (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hm hu')).trans_eq (by ring)
  have hcp:‖c*phase‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hc hp (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hA:‖value D amp‖≤2001 := by
    have h:=(norm_sub_le_norm_sub_add_norm_sub (value D amp) e 0)
    simp only [sub_zero] at h
    have hsmall:‖value D amp-e‖≤1:=hamp.trans (by norm_num)
    linarith only [h,he,hsmall]
  have hm:=RHHighChirpDFT.product_error (value D (mul D a u)) (value D amp)
    (c*phase) e 1 2001 (4/(D:ℝ)) (1/10^25) hcp hA hcpu hamp
    (by positivity) (by norm_num)
  have hr:=mul_error D (by norm_num [D]) (mul D a u) amp
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hr hm)).trans (by norm_num [D])
end RHHighContourCoefficient
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
set_option maxHeartbeats 500000
open Complex
namespace RHHighExpPerturbation
lemma exp_error (z w : ℂ) (h : ‖w-z‖≤1) :
    ‖Complex.exp z-Complex.exp w‖≤2*‖Complex.exp z‖*‖w-z‖ := by
  have he : Complex.exp w-Complex.exp z=
      Complex.exp z*(Complex.exp (w-z)-1) := by
    rw [mul_sub,mul_one,←Complex.exp_add]
    congr 1
    ring
  rw [norm_sub_rev (Complex.exp z) (Complex.exp w),he,norm_mul]
  have hp := mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le h) (norm_nonneg (Complex.exp z))
  convert hp using 1 <;> first | rfl | ring
lemma square_error (a b : ℂ) (ε : ℝ) (hε : 0≤ε ∧ ε≤1)
    (hb : ‖b‖≤1) (he : ‖a-b‖≤ε) : ‖a^2-b^2‖≤3*ε := by
  have ha : ‖a‖≤2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub a b 0
    simp only [sub_zero] at h
    linarith
  calc
    _ = ‖(a-b)*(a+b)‖ := by congr 1;ring
    _ = ‖a-b‖*‖a+b‖ := norm_mul _ _
    _ ≤ ε*(2+1) := mul_le_mul he ((norm_add_le _ _).trans (add_le_add ha hb))
      (norm_nonneg _) hε.1
    _ = _ := by ring
lemma repeated_square_error (a b : ℂ) (ε : ℝ) (hε : 0≤ε) (hb : ‖b‖≤1)
    (he : ‖a-b‖≤ε) (n : Nat) (hn : (3:ℝ)^n*ε≤1) :
    ‖a^(2^n)-b^(2^n)‖≤(3:ℝ)^n*ε := by
  induction n with
  | zero => simpa only [pow_zero,pow_one,one_mul] using he
  | succ n ih =>
    have hp : (3:ℝ)^n*ε≤1 := by
      have hmono : (3:ℝ)^n≤3^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans (mul_le_mul_of_nonneg_right hmono hε) hn
    have hi := ih hp
    have hb' : ‖b^(2^n)‖≤1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hb
    have hs := square_error (a^(2^n)) (b^(2^n)) ((3:ℝ)^n*ε) ⟨by positivity,hp⟩ hb' hi
    rw [show (2:Nat)^(n+1)=2^n*2 by rw [pow_succ],pow_mul,pow_mul]
    rw [show (3:ℝ)^(n+1)*ε=3*((3:ℝ)^n*ε) by rw [pow_succ];ring]
    exact hs
end RHHighExpPerturbation
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighPhaseQuantization
open RHHighDyadicRounding
lemma floor_scaled_error (a b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    |(a:ℝ)/(D:ℝ)-(b:ℝ)*(a/b:Nat)/(D:ℝ)|≤(b:ℝ)/(D:ℝ) := by
  have hb' : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have he : (a:ℝ)/(D:ℝ)-(b:ℝ)*(a/b:Nat)/(D:ℝ)=
      ((b:ℝ)/(D:ℝ))*((a:ℝ)/(b:ℝ)-(a/b:Nat)) := by field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(b:ℝ)/(D:ℝ))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (nat_division_error a b hb)
    (by positivity : (0:ℝ)≤(b:ℝ)/(D:ℝ))
lemma signed_error (a : Int) (Q D : Nat) (hQ : 0 < Q) (hD : 0 < D) :
    |(a:ℝ)/((D:ℝ)*(Q:ℝ))-
      (if a<0 then -(8:ℝ) else 8)*(a.natAbs/(8*Q):Nat)/(D:ℝ)|≤8/(D:ℝ) := by
  have hQ' : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  have habs : (a.natAbs:ℝ)=|(a:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have h := floor_scaled_error a.natAbs (8*Q) (D*Q) (by positivity) (by positivity)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  have hright : (8*(Q:ℝ))/((D:ℝ)*(Q:ℝ))=8/(D:ℝ) := by field_simp
  rw [hright,habs] at h
  by_cases hn : a<0
  · have hn' : (a:ℝ)<0 := by exact_mod_cast hn
    rw [if_pos hn]
    rw [abs_of_neg hn'] at h
    have he : (a:ℝ)/((D:ℝ)*(Q:ℝ))-(-8)*(a.natAbs/(8*Q):Nat)/(D:ℝ)=
        -((-(a:ℝ))/((D:ℝ)*(Q:ℝ))-(8*(Q:ℝ))*(a.natAbs/(8*Q):Nat)/((D:ℝ)*(Q:ℝ))) := by field_simp;ring
    rw [he,abs_neg]
    exact h
  · have hn' : (0:ℝ)≤a := by exact_mod_cast (le_of_not_gt hn)
    rw [if_neg hn]
    rw [abs_of_nonneg hn'] at h
    have he : (8*(Q:ℝ))*(a.natAbs/(8*Q):Nat)/((D:ℝ)*(Q:ℝ))=
        8*(a.natAbs/(8*Q):Nat)/(D:ℝ) := by field_simp
    rw [he] at h
    exact h
end RHHighPhaseQuantization
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
namespace RHHighPiSeed
def numerator50 : Nat := 314159265358979323846264338327950288419716939937510
lemma seed50 : (numerator50:ℝ)/10^50≤Real.pi ∧
    Real.pi≤(numerator50+1:ℝ)/10^50 := by
  have hp := TaoFivePrimes.rh_pi_enclosure_700
  have hl : (numerator50:ℝ)/10^50≤(TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  have hu : (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700≤(numerator50+1:ℝ)/10^50 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  exact ⟨hl.trans hp.1,hp.2.trans hu⟩
end RHHighPiSeed
end
section
section
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHHighGenericExpHorner
open Complex
lemma exp32_error (z : ℂ) (hz : ‖z‖≤1/2) :
    ‖Complex.exp z-∑ k ∈ Finset.range 32, z^k/(k.factorial:ℂ)‖≤1/10^40 := by
  have hp : ‖z‖^32≤(1/2:ℝ)^32 := pow_le_pow_left₀ (norm_nonneg _) hz _
  have he : Real.exp ‖z‖≤3 := le_trans (Real.exp_le_exp.mpr (by linarith)) Real.exp_one_lt_three.le
  calc
    _ ≤ (‖z‖^32/((32).factorial:ℝ))*Real.exp ‖z‖ := RHHighTaylor.exp_factorial_remainder z 32
    _ ≤ ((1/2:ℝ)^32/((32).factorial:ℝ))*3 := mul_le_mul
      (div_le_div_of_nonneg_right hp (by positivity)) he (by positivity) (by positivity)
    _ ≤ _ := by norm_num

lemma cast_horner (cs : List Nat) (x : Nat) :
    ((horner cs x:Nat):ℝ)=(cs.map (fun c : Nat => (c:ℝ))).foldr (fun c p => c+(x:ℝ)*p) 0 := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih =>
    change ((c+x*horner cs x:Nat):ℝ)=_
    simp only [Nat.cast_add,Nat.cast_mul,List.map_cons,List.foldr_cons,ih]
lemma polynomial_identity (D d : Nat) (hD : 0<D)
    (hc : d^2*horner (cn D) (d^4)≤horner (cp D) (d^4))
    (hs : d^2*horner (sn D) (d^4)≤horner (sp D) (d^4)) :
    (((horner (cp D) (d^4)-d^2*horner (cn D) (d^4):Nat):ℂ)+
      ((d*(horner (sp D) (d^4)-d^2*horner (sn D) (d^4)):Nat):ℂ)*I)/
        ((D:ℂ)^31*((31).factorial:ℂ))=
    ∑ k ∈ Finset.range 32, (((d:ℂ)/(D:ℂ))*I)^k/(k.factorial:ℂ) := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
  simp only [Nat.cast_sub hc,Nat.cast_sub hs,Nat.cast_mul,Nat.cast_pow]
  simp only [horner,cp,cn,sp,sn,List.foldr_cons,List.foldr_nil,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  simp only [mul_pow,div_pow]
  norm_num [Finset.sum_range_succ,Complex.I_pow_eq_pow_mod,Complex.I_sq]
  field_simp [hd]
  ring_nf
  simp only [Complex.I_sq,Complex.I_pow_three]
  ring
end RHHighGenericExpHorner
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighNegativeExp
open Complex RHHighGenericExpHorner RHHighDyadicRounding
lemma polynomial_identity (D d : Nat) (hD : 0 < D)
    (hp : d*horner (en D) (d^2)≤horner (ep D) (d^2)) :
    (((horner (ep D) (d^2)-d*horner (en D) (d^2):Nat):ℂ)/
      ((D:ℂ)^31*((31).factorial:ℂ)))=
      ∑ k ∈ Finset.range 32, (-(d:ℂ)/(D:ℂ))^k/(k.factorial:ℂ) := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
  simp only [Nat.cast_sub hp,Nat.cast_mul,Nat.cast_pow]
  simp only [horner,ep,en,List.foldr_cons,List.foldr_nil,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  norm_num [Finset.sum_range_succ]
  field_simp [hd]
  ring
lemma enclosure (D d : Nat) (hD : 0 < D) (hd : 2*d≤D)
    (hp : d*horner (en D) (d^2)≤horner (ep D) (d^2)) :
    ‖((seed D d:ℂ)/(D:ℂ))-Complex.exp (-(d:ℂ)/(D:ℂ))‖≤
      1/(D:ℝ)+1/10^40 := by
  let p : ℂ := (numerator D d:ℂ)/(denominator D:ℂ)
  have hden : 0 < denominator D := by unfold denominator;positivity
  have hr := scaled_rounding_error (numerator D d) (denominator D) D hden hD
  have hrr : ‖p-(seed D d:ℂ)/(D:ℂ)‖≤1/(D:ℝ) := by
    simpa only [p,seed,←Complex.ofReal_natCast,←Complex.ofReal_div,
      ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hr
  have hi : p=∑ k ∈ Finset.range 32, (-(d:ℂ)/(D:ℂ))^k/(k.factorial:ℂ) := by
    simpa only [p,numerator,denominator,Nat.cast_mul,Nat.cast_pow] using polynomial_identity D d hD hp
  have hz : ‖-(d:ℂ)/(D:ℂ)‖≤1/2 := by
    rw [norm_div,norm_neg,Complex.norm_natCast,Complex.norm_natCast]
    apply (div_le_iff₀ (show (0:ℝ)<D by exact_mod_cast hD)).mpr
    have h : (2:ℝ)*d≤D := by exact_mod_cast hd
    linarith
  have he := exp32_error (-(d:ℂ)/(D:ℂ)) hz
  rw [←hi] at he
  calc
    _ ≤ ‖(seed D d:ℂ)/(D:ℂ)-p‖+‖p-Complex.exp (-(d:ℂ)/(D:ℂ))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add ((norm_sub_rev _ _).trans_le hrr) ((norm_sub_rev _ _).trans_le he)
end RHHighNegativeExp
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighFixedPoint
open Complex RHHighDyadicRounding RHHighExpPerturbation
def step (D a : Nat) : Nat := a*a/D
def iter (D : Nat) (a : Nat) : Nat→Nat
  | 0 => a
  | n+1 => step D (iter D a n)
lemma step_round (D a : Nat) (hD : 0 < D) :
    ‖((step D a:ℂ)/(D:ℂ))-((a:ℂ)/(D:ℂ))^2‖≤1/(D:ℝ) := by
  have h := scaled_rounding_error (a*a) (D*D) D (by positivity) hD
  have hi : a*a*D/(D*D)=a*a/D := by
    rw [show a*a*D=D*(a*a) by ring,show D*D=D*D by rfl,Nat.mul_div_mul_left _ _ hD]
  rw [hi] at h
  simpa only [step,div_pow,pow_two,←Complex.ofReal_natCast,←Complex.ofReal_mul,
    ←Complex.ofReal_div,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm,Nat.cast_mul,div_mul_div_comm] using h
lemma iteration_error (D a : Nat) (hD : 0 < D) (w : ℂ) (hw : ‖w‖≤1)
    (ε : ℝ) (hε : 1/(D:ℝ)≤ε) (he : ‖(a:ℂ)/(D:ℂ)-w‖≤ε)
    (n : Nat) (hn : (4:ℝ)^n*ε≤1) :
    ‖(iter D a n:ℂ)/(D:ℂ)-w^(2^n)‖≤(4:ℝ)^n*ε := by
  have hε0 : 0≤ε := le_trans (by positivity) hε
  induction n with
  | zero => simpa [iter] using he
  | succ n ih =>
    have hp : (4:ℝ)^n*ε≤1 := by
      have hm : (4:ℝ)^n≤4^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact (mul_le_mul_of_nonneg_right hm hε0).trans hn
    have hx := ih hp
    have hw' : ‖w^(2^n)‖≤1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hw
    have hs := square_error ((iter D a n:ℂ)/(D:ℂ)) (w^(2^n)) ((4:ℝ)^n*ε)
      ⟨by positivity,hp⟩ hw' hx
    have hr := step_round D (iter D a n) hD
    have hsmall : 1/(D:ℝ)≤(4:ℝ)^n*ε :=
      hε.trans (le_mul_of_one_le_left hε0 (one_le_pow₀ (by norm_num)))
    calc
      _ = ‖(step D (iter D a n):ℂ)/(D:ℂ)-(w^(2^n))^2‖ := by
        rw [iter,show (2:Nat)^(n+1)=2^n*2 by rw [pow_succ],pow_mul]
      _ ≤ ‖(step D (iter D a n):ℂ)/(D:ℂ)-((iter D a n:ℂ)/(D:ℂ))^2‖+
          ‖((iter D a n:ℂ)/(D:ℂ))^2-(w^(2^n))^2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1/(D:ℝ)+3*((4:ℝ)^n*ε) := add_le_add hr hs
      _ ≤ (4:ℝ)^n*ε+3*((4:ℝ)^n*ε) := add_le_add_left hsmall _
      _ = _ := by rw [pow_succ];ring
end RHHighFixedPoint
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighGammaAmplitude
open RHHighGenericExpHorner RHHighNegativeExp RHHighFixedPoint
lemma amplitude_error (d : Nat) (hd : 2*d≤2^128)
    (hp : d*horner (en (2^128)) (d^2)≤horner (ep (2^128)) (d^2)) :
    ‖(iter (2^128) (seed (2^128) d) 8:ℂ)/(2:ℂ)^128-
      Complex.exp ((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)‖≤1/10^32 := by
  let D : Nat := 2^128
  let w : ℂ := Complex.exp (-(d:ℂ)/(D:ℂ))
  have hw : ‖w‖≤1 := by
    dsimp only [w]
    have hex : -(d:ℂ)/(D:ℂ)=((-(d:ℝ)/(D:ℝ):ℝ):ℂ) := by push_cast;rfl
    rw [hex,Complex.norm_exp,Complex.ofReal_re]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by positivity)
  have he := enclosure D d (by norm_num [D]) hd hp
  have h := iteration_error D (seed D d) (by norm_num [D]) w hw
    (1/(D:ℝ)+1/10^40) (by norm_num [D]) he 8 (by norm_num [D])
  have hh : w^((2:Nat)^8)=Complex.exp ((-256*(d:ℝ)/(D:ℝ):ℝ):ℂ) := by
    dsimp only [w]
    rw [←Complex.exp_nat_mul]
    congr 1
    push_cast
    norm_num
    ring
  rw [hh] at h
  have h' := h.trans (by norm_num [D] : (4:ℝ)^8*(1/(D:ℝ)+1/10^40)≤1/10^32)
  simpa only [D,Nat.cast_pow,Nat.cast_ofNat] using h'
end RHHighGammaAmplitude
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighGammaAmplitude
open RHHighGenericExpHorner RHHighNegativeExp RHHighFixedPoint RHHighExpPerturbation
lemma target_error (rr : Int) (hr : rr≤0) (d : Nat)
    (heq : d=(-rr).toNat/256) (hd : 2*d≤2^128)
    (hp : d*horner (en (2^128)) (d^2)≤horner (ep (2^128)) (d^2)) :
    ‖(iter (2^128) (seed (2^128) d) 8:ℂ)/(2:ℂ)^128-
      Complex.exp ((rr:ℂ)/(2:ℂ)^128)‖≤2/10^32 := by
  have hnat : ((-rr).toNat:ℝ)=-(rr:ℝ) := by
    have he := Int.toNat_of_nonneg (show (0:Int)≤-rr by omega)
    exact_mod_cast he
  have h := RHHighPhaseQuantization.floor_scaled_error (-rr).toNat 256 (2^128) (by norm_num) (by norm_num)
  rw [←heq,hnat] at h
  simp only [Nat.cast_pow,Nat.cast_ofNat] at h
  have hdif : |(rr:ℝ)/(2:ℝ)^128-(-256*(d:ℝ)/(2:ℝ)^128)|≤256/(2:ℝ)^128 := by
    convert h using 1
    rw [←abs_neg]
    congr 1
    ring
  have hex : ‖Complex.exp ((rr:ℂ)/(2:ℂ)^128)‖≤1 := by
    have he : (rr:ℂ)/(2:ℂ)^128=(((rr:ℝ)/(2:ℝ)^128:ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_exp,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hr) (by positivity))
  have hc : ‖((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)-(rr:ℂ)/(2:ℂ)^128‖≤256/(2:ℝ)^128 := by
    have he : ((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)-(rr:ℂ)/(2:ℂ)^128=
        ((-256*(d:ℝ)/(2:ℝ)^128-(rr:ℝ)/(2:ℝ)^128:ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact hdif
  have hh := exp_error ((rr:ℂ)/(2:ℂ)^128) (((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)) (hc.trans (by norm_num))
  have hb : ‖Complex.exp ((rr:ℂ)/(2:ℂ)^128)-
      Complex.exp ((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)‖≤512/(2:ℝ)^128 := by
    apply hh.trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hex (by norm_num)) hc (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (amplitude_error d hd hp) ((norm_sub_rev _ _).trans_le hb))).trans (by norm_num)
end RHHighGammaAmplitude
end
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Complex
namespace RHHighContourReference
open RHHighLogData
lemma iterate_eq (a k : Nat) : iterate a k=RHHighFixedPoint.iter D a k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate,RHHighFixedPoint.iter,RHHighFixedPoint.step,ih]
lemma pi_error : |Real.pi-(RHHighGammaArithmetic.P:ℝ)/10^50|≤1/10^50 := by
  have h:=RHHighPiSeed.seed50
  change (RHHighGammaArithmetic.P:ℝ)/10^50≤ Real.pi ∧ Real.pi≤((RHHighGammaArithmetic.P:ℝ)+1)/10^50 at h
  rw [abs_le]
  constructor <;> linarith
lemma pi_floor_error (m q : Nat) (hm:m≤1024) (hq:512≤ q) :
    |((RHHighGammaArithmetic.P*D*m/(q*10^50):Nat):ℝ)/D-Real.pi*(m:ℝ)/q|≤1/10^36 := by
  have hqr:(512:ℝ)≤ q:=by exact_mod_cast hq
  have hd:(0:ℝ)< D:=by norm_num [D]
  have h:=RHHighDyadicRounding.nat_division_error (RHHighGammaArithmetic.P*D*m) (q*10^50) (by omega)
  have h1:|((RHHighGammaArithmetic.P*D*m/(q*10^50):Nat):ℝ)/D-
      ((RHHighGammaArithmetic.P:ℝ)/10^50)*(m:ℝ)/q|≤1/(D:ℝ) := by
    have he:((RHHighGammaArithmetic.P*D*m/(q*10^50):Nat):ℝ)/D-
        ((RHHighGammaArithmetic.P:ℝ)/10^50)*(m:ℝ)/q=
        -((((RHHighGammaArithmetic.P*D*m:Nat):ℝ)/(q*10^50)-((RHHighGammaArithmetic.P*D*m/(q*10^50):Nat):ℝ))/D) := by
      push_cast
      field_simp
      ring
    rw [he,abs_neg,abs_div,abs_of_pos hd]
    exact div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h) hd.le
  have h2:|((RHHighGammaArithmetic.P:ℝ)/10^50)*(m:ℝ)/q-Real.pi*(m:ℝ)/q|≤2/10^50 := by
    have hdiv:(0:ℝ)≤(m:ℝ)/q:=div_nonneg (Nat.cast_nonneg m) (by linarith)
    rw [show ((RHHighGammaArithmetic.P:ℝ)/10^50)*(m:ℝ)/q-Real.pi*(m:ℝ)/q=
      (((RHHighGammaArithmetic.P:ℝ)/10^50)-Real.pi)*((m:ℝ)/q) by ring,
      abs_mul,abs_sub_comm,abs_of_nonneg hdiv]
    have hm':(m:ℝ)≤1024:=by exact_mod_cast hm
    have hmq:(m:ℝ)/q≤2:=(div_le_iff₀ (by linarith)).mpr (by linarith)
    exact (mul_le_mul pi_error hmq (by positivity) (by norm_num)).trans_eq (by ring)
  exact ((abs_sub_le _ _ _).trans (add_le_add h1 h2)).trans (by norm_num [D])
lemma amplitude_record (r : Record) :
    ‖(r.amplitude:ℂ)/(D:ℂ)-Complex.exp (((-Real.pi*(r.m:ℝ)/512:ℝ):ℂ))‖≤3/10^32 := by
  let m:=r.m
  have h:=r.valid
  simp only [check,decide_eq_true_eq] at h
  rcases h with ⟨hmlo,hmhi,hd,hs,ha,_,_,hdb,hp,_,_⟩
  have hm:1 ≤ m ∧ m≤1024:=⟨hmlo,hmhi⟩
  have hrr:rr m≤0:=by unfold rr;omega
  have he:=RHHighGammaAmplitude.target_error (rr m) hrr r.d hd hdb hp
  have he':‖(r.amplitude:ℂ)/(D:ℂ)-Complex.exp ((rr m:ℂ)/(D:ℂ))‖≤2/10^32 := by
    rw [ha,iterate_eq,hs]
    simpa only [D,Nat.cast_pow,Nat.cast_ofNat] using he
  have hr:|(rr m:ℝ)/D-(-Real.pi*(m:ℝ)/512)|≤1/10^36 := by
    have heq:(rr m:ℝ)/D-(-Real.pi*(m:ℝ)/512)=
      -(((RHHighGammaArithmetic.P*D*m/(512*10^50):Nat):ℝ)/D-Real.pi*(m:ℝ)/512) := by
      simp only [rr,Int.cast_neg,Int.cast_natCast]
      ring
    rw [heq,abs_neg]
    simpa only [Nat.cast_ofNat] using pi_floor_error m 512 hm.2 (by decide)
  have hc:‖(rr m:ℂ)/(D:ℂ)-(((-Real.pi*(m:ℝ)/512:ℝ):ℂ))‖≤1/10^36 := by
    have hh:(rr m:ℂ)/(D:ℂ)-(((-Real.pi*(m:ℝ)/512:ℝ):ℂ))=
      ((((rr m:ℝ)/D)-(-Real.pi*(m:ℝ)/512):ℝ):ℂ) := by push_cast;rfl
    rw [hh,Complex.norm_real,Real.norm_eq_abs]
    exact hr
  have hn:‖Complex.exp (((-Real.pi*(m:ℝ)/512:ℝ):ℂ))‖≤1 := by
    rw [Complex.norm_exp,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (Nat.cast_nonneg m)) (by norm_num))
  have hx:=RHHighExpPerturbation.exp_error (((-Real.pi*(m:ℝ)/512:ℝ):ℂ)) ((rr m:ℂ)/(D:ℂ)) (hc.trans (by norm_num))
  have hx':‖Complex.exp ((rr m:ℂ)/(D:ℂ))-Complex.exp (((-Real.pi*(m:ℝ)/512:ℝ):ℂ))‖≤2/10^36 := by
    rw [norm_sub_rev]
    exact hx.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hc (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add he' hx')).trans (by norm_num)
lemma amplitude_enclosure (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
    ‖((lookup m).amplitude:ℂ)/(D:ℂ)-Complex.exp (((-Real.pi*(m:ℝ)/512:ℝ):ℂ))‖≤3/10^32 := by
  have h:=amplitude_record (lookup m)
  rw [lookup_m m hm] at h
  exact h
end RHHighContourReference
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Complex
namespace RHHighContourReference
open RHHighLogData
lemma amplitude_real_record (r : Record) :
    |(r.amplitude:ℝ)/D-Real.exp (-Real.pi*(r.m:ℝ)/512)|≤3/10^32 := by
  have h:=amplitude_record r
  have he:(r.amplitude:ℂ)/(D:ℂ)-Complex.exp (((-Real.pi*(r.m:ℝ)/512:ℝ):ℂ))=
      ((((r.amplitude:ℝ)/D)-Real.exp (-Real.pi*(r.m:ℝ)/512):ℝ):ℂ) := by
    rw [←Complex.ofReal_exp]
    push_cast
    rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs] at h
  exact h
lemma inverse_real_record (r : Record) :
    |(r.inverse:ℝ)/D-Real.exp (Real.pi*(r.m:ℝ)/512)|≤1/10^25 := by
  have h:=r.valid
  simp only [check,decide_eq_true_eq] at h
  have hi:=h.2.2.2.2.2.1
  have hl:=h.2.2.2.2.2.2.2.2.2.1
  let A:ℝ:=(r.amplitude:ℝ)/D
  let E:ℝ:=Real.exp (-Real.pi*(r.m:ℝ)/512)
  have hd:(0:ℝ)<D:=by norm_num [D]
  have hA:(1/1000:ℝ)≤A := by
    dsimp [A]
    apply (le_div_iff₀ hd).mpr
    have hh:(D:ℝ)≤1000*(r.amplitude:ℝ):=by exact_mod_cast hl
    linarith
  have he:|A-E|≤3/10^32:=amplitude_real_record r
  have hE:(1/2000:ℝ)≤E:=by have hh:=abs_le.mp he;linarith
  have hapos:0<r.amplitude:=by
    have hdN:0<D:=by norm_num [D]
    omega
  have hround:|(r.inverse:ℝ)/D-1/A|≤1/(D:ℝ) := by
    have hr:=RHHighDyadicRounding.nat_division_error (D*D) r.amplitude hapos
    have heq:(r.inverse:ℝ)/D-1/A=
        -((((D*D:Nat):ℝ)/(r.amplitude:ℝ)-((D*D/r.amplitude:Nat):ℝ))/(D:ℝ)) := by
      rw [hi]
      dsimp only [A]
      push_cast
      field_simp
      ring
    rw [heq,abs_neg,abs_div,abs_of_pos hd]
    exact div_le_div_of_nonneg_right hr hd.le
  have hrec:|1/A-1/E|≤6/10^26 := by
    have hap:0<A:=by linarith
    have hep:0<E:=by linarith
    rw [show 1/A-1/E=(E-A)/(A*E) by field_simp,
      abs_div,abs_of_pos (mul_pos hap hep),abs_sub_comm]
    have hden:(1/2000000:ℝ)≤A*E := by
      have hh:=mul_le_mul hA hE (by norm_num) hap.le
      norm_num at hh
      exact hh
    have hh:=div_le_div₀ (by norm_num : (0:ℝ)≤3/10^32) he (by norm_num : (0:ℝ)<1/2000000) hden
    exact hh.trans_eq (by norm_num)
  have heq:1/E=Real.exp (Real.pi*(r.m:ℝ)/512) := by
    dsimp only [E]
    rw [show -Real.pi*(r.m:ℝ)/512=-(Real.pi*(r.m:ℝ)/512) by ring,Real.exp_neg,one_div,inv_inv]
  rw [←heq]
  exact ((abs_sub_le _ _ _).trans (add_le_add hround hrec)).trans (by norm_num [D])
lemma inverse_enclosure (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
    ‖((lookup m).inverse:ℂ)/(D:ℂ)-Complex.exp (((Real.pi*(m:ℝ)/512:ℝ):ℂ))‖≤1/10^25 := by
  have h:=inverse_real_record (lookup m)
  rw [lookup_m m hm] at h
  have he:((lookup m).inverse:ℂ)/(D:ℂ)-Complex.exp (((Real.pi*(m:ℝ)/512:ℝ):ℂ))=
      (((((lookup m).inverse:ℝ)/D)-Real.exp (Real.pi*(m:ℝ)/512):ℝ):ℂ) := by
    rw [←Complex.ofReal_exp]
    push_cast
    rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact h
lemma frequency_enclosure (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
    |((lookup m).x:ℝ)/D-Real.pi*(m:ℝ)/8192|≤1/10^36 := by
  have h:=(lookup m).valid
  simp only [check,decide_eq_true_eq,lookup_m m hm] at h
  rw [h.2.2.2.2.2.2.1]
  exact pi_floor_error m 8192 hm.2 (by decide)
end RHHighContourReference
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
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighContourReference
open RHHighLogData
lemma inverse_integer_bound (r : Record) : r.inverse≤1000*D := by
  have h:=r.valid
  simp only [check,decide_eq_true_eq] at h
  rcases h with ⟨_,_,_,_,_,hi,_,_,_,hl,_⟩
  rw [hi]
  apply Nat.div_le_of_le_mul
  calc D*D≤D*(1000*r.amplitude):=Nat.mul_le_mul_left D hl
       _=r.amplitude*(1000*D):=by ring
lemma inverse_real_bound (r : Record) : (r.inverse:ℝ)/D≤1000 := by
  have h: (r.inverse:ℝ)≤1000*(D:ℝ):=by exact_mod_cast inverse_integer_bound r
  exact (div_le_iff₀ (by norm_num [D] : (0:ℝ)<D)).mpr h
lemma positive_exp_bound (r : Record) : Real.exp (Real.pi*(r.m:ℝ)/512)≤2000 := by
  have he:=inverse_real_record r
  have hi:=inverse_real_bound r
  have hsmall:|(r.inverse:ℝ)/D-Real.exp (Real.pi*(r.m:ℝ)/512)|≤1:=he.trans (by norm_num)
  have hh:=abs_le.mp hsmall
  linarith only [hh.1,hi]
lemma negative_exp_bound (m : Nat) : Real.exp (-Real.pi*(m:ℝ)/512)≤1 := by
  apply Real.exp_le_one_iff.mpr
  have h:0≤Real.pi*(m:ℝ)/512:=by positivity
  linarith only [h]
lemma coefficient_half (m : Nat) (hm:1 ≤ m ∧ m≤1024) : ‖RHHighFourierPolynomial.coefficient m‖≤1/2 := by
  have h:=RHHighFourierPolynomial.coefficient_mass
  have hs:‖RHHighFourierPolynomial.coefficient m‖≤
      ∑ j∈Finset.range 1024,‖RHHighFourierPolynomial.coefficient (j+1)‖ := by
    have hh:=Finset.single_le_sum (fun j (hj:j∈Finset.range 1024)=>
      norm_nonneg (RHHighFourierPolynomial.coefficient (j+1)))
      (show m-1∈Finset.range 1024 by simp only [Finset.mem_range];omega)
    simpa only [Nat.sub_add_cancel hm.1] using hh
  nlinarith only [h,hs,norm_nonneg (RHHighFourierPolynomial.coefficient 0)]
lemma true_frequency_bound (m : Nat) (hm:m≤1024) :
    0≤Real.pi*(m:ℝ)/8192 ∧ Real.pi*(m:ℝ)/8192≤1/2 := by
  have hmR:(m:ℝ)≤1024:=by exact_mod_cast hm
  constructor
  · positivity
  · have hpi:Real.pi≤4:=Real.pi_lt_four.le
    have hh:=mul_le_mul hpi hmR (Nat.cast_nonneg m) (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
lemma proposed_frequency_bound (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
    0≤((lookup m).x:ℝ)/D ∧ ((lookup m).x:ℝ)/D≤1 := by
  have h:=frequency_enclosure m hm
  have he:|((lookup m).x:ℝ)/D-Real.pi*(m:ℝ)/8192|≤1/4:=h.trans (by norm_num)
  have ht:=true_frequency_bound m hm.2
  have hh:=abs_le.mp he
  constructor
  · positivity
  · linarith only [hh.2,ht.2]
end RHHighContourReference
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighContourUnit
noncomputable def exactUnit (j : Nat) : ℂ := match j%8 with
  | 0 => 1
  | 1 => (Real.sqrt 2:ℂ)/2+((Real.sqrt 2:ℂ)/2)*I
  | 2 => I
  | 3 => -(Real.sqrt 2:ℂ)/2+((Real.sqrt 2:ℂ)/2)*I
  | 4 => -1
  | 5 => -(Real.sqrt 2:ℂ)/2-((Real.sqrt 2:ℂ)/2)*I
  | 6 => -I
  | _ => (Real.sqrt 2:ℂ)/2-((Real.sqrt 2:ℂ)/2)*I
noncomputable def value (j : Nat) : ℂ := (((pair j).1:ℂ)+((pair j).2:ℂ)*I)/(D:ℂ)
lemma sqrt_interval : (H:ℝ)/D≤Real.sqrt 2/2 ∧ Real.sqrt 2/2≤((H:ℝ)+1)/D := by
  have h:=root_checked
  have hl:(2*(H:ℝ))^2≤2*(D:ℝ)^2:=by exact_mod_cast h.1
  have hu:2*(D:ℝ)^2≤(2*((H:ℝ)+1))^2:=by exact_mod_cast h.2
  have hd:(0:ℝ)<D:=by norm_num [D]
  have hs:(Real.sqrt (2:ℝ))^2=2:=Real.sq_sqrt (by norm_num)
  have hn:0≤Real.sqrt (2:ℝ):=Real.sqrt_nonneg _
  have hlo:(2*(H:ℝ)/D)^2≤2 := by
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hd)).mpr hl
  have hhi:2≤(2*((H:ℝ)+1)/D)^2 := by
    rw [div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr hu
  have hlo':2*(H:ℝ)/D≤Real.sqrt 2 :=
    (Real.le_sqrt (by positivity) (by norm_num)).mpr hlo
  have hhi':Real.sqrt 2≤2*((H:ℝ)+1)/D :=
    (Real.sqrt_le_left (by positivity)).mpr hhi
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    calc (H:ℝ)/D*2=2*(H:ℝ)/D := by ring
         _≤Real.sqrt 2 := hlo'
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    calc Real.sqrt 2≤2*((H:ℝ)+1)/D := hhi'
         _=(((H:ℝ)+1)/D)*2 := by ring
lemma root_error : |(H:ℝ)/D-Real.sqrt 2/2|≤1/(D:ℝ) := by
  have h:=sqrt_interval
  rw [abs_of_nonpos (by linarith)]
  have hd:(D:ℝ)≠0:=by norm_num [D]
  have he:((H:ℝ)+1)/D=(H:ℝ)/D+1/(D:ℝ):=by ring
  rw [he] at h
  linarith
lemma base_eq : exactUnit 1=Complex.exp (((Real.pi/4:ℝ):ℂ)*I) := by
  rw [Complex.exp_ofReal_mul_I,Real.cos_pi_div_four,Real.sin_pi_div_four]
  simp only [exactUnit,Nat.reduceMod,Complex.ofReal_div,Complex.ofReal_ofNat]
lemma small_step (j : Nat) (hj:j<7) : exactUnit (j+1)=exactUnit j*exactUnit 1 := by
  have hs:(Real.sqrt (2:ℝ):ℂ)^2=2:=by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  interval_cases j <;> norm_num only [exactUnit,Nat.reduceAdd,Nat.reduceMod] <;>
    ring_nf <;> simp only [I_sq,hs] <;> ring
lemma small_power (j : Nat) (hj:j<8) : exactUnit j=(exactUnit 1)^j := by
  induction j with
  | zero => simp [exactUnit]
  | succ j ih => rw [small_step j (by omega),ih (by omega),pow_succ]
lemma small_exp (j : Nat) (hj:j<8) : exactUnit j=Complex.exp (((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I) := by
  rw [small_power j hj,base_eq,←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma exact_exp (j : Nat) : exactUnit j=Complex.exp (((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I) := by
  have hm:j%8<8:=Nat.mod_lt _ (by decide)
  have h:=small_exp (j%8) hm
  have he:(((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I)=
      (((Real.pi*((j%8:Nat):ℝ)/4:ℝ):ℂ)*I)+((j/8:Nat):ℂ)*(2*(Real.pi:ℂ)*I) := by
    have hn:(j:ℂ)=((j%8:Nat):ℂ)+8*((j/8:Nat):ℂ):=by exact_mod_cast (Nat.mod_add_div j 8).symm
    push_cast
    rw [hn]
    ring
  rw [he,Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,mul_one]
  simpa only [exactUnit,Nat.mod_mod] using h
end RHHighContourUnit
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighContourUnit
noncomputable def table (r : ℝ) (j : Nat) : ℂ := match j%8 with
  | 0 => 1
  | 1 => (r:ℂ)+(r:ℂ)*I
  | 2 => I
  | 3 => -(r:ℂ)+(r:ℂ)*I
  | 4 => -1
  | 5 => -(r:ℂ)-(r:ℂ)*I
  | 6 => -I
  | _ => (r:ℂ)-(r:ℂ)*I
lemma exact_as_table (j : Nat) : exactUnit j=table (Real.sqrt 2/2) j := by
  have hj:j%8<8:=Nat.mod_lt _ (by decide)
  unfold exactUnit table
  generalize he:j%8=q at hj ⊢
  interval_cases q <;> push_cast <;> ring
lemma value_as_table (j : Nat) : value j=table ((H:ℝ)/D) j := by
  have hj:j%8<8:=Nat.mod_lt _ (by decide)
  have hd:(D:ℂ)≠0:=by norm_num [D]
  unfold value pair table
  generalize he:j%8=q at hj ⊢
  interval_cases q <;> push_cast <;> field_simp [hd] <;> ring
lemma table_lipschitz (a b : ℝ) (j : Nat) : ‖table a j-table b j‖≤2*|a-b| := by
  have h:=Complex.norm_le_abs_re_add_abs_im (table a j-table b j)
  have hj:j%8<8:=Nat.mod_lt _ (by decide)
  unfold table at h ⊢
  generalize he:j%8=q at hj h ⊢
  interval_cases q <;> simp at h ⊢ <;>
    (try simp only [show -a+b=-(a-b) by ring,abs_neg] at h) <;> nlinarith [abs_nonneg (a-b)]
lemma enclosure (j : Nat) :
    ‖value j-Complex.exp (((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I)‖≤2/(D:ℝ) := by
  rw [←exact_exp,value_as_table,exact_as_table]
  exact (table_lipschitz _ _ j).trans
    ((mul_le_mul_of_nonneg_left root_error (by norm_num)).trans_eq (by ring))
lemma value_norm (j : Nat) : ‖value j‖≤2 := by
  have h:=enclosure j
  have ht:‖Complex.exp (((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I)‖=1:=Complex.norm_exp_ofReal_mul_I _
  have hh:=norm_sub_le_norm_sub_add_norm_sub (value j)
    (Complex.exp (((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I)) 0
  simp only [sub_zero] at hh
  have hs:‖value j-Complex.exp (((Real.pi*(j:ℝ)/4:ℝ):ℂ)*I)‖≤1:=h.trans (by norm_num [D])
  linarith only [hh,ht,hs]
end RHHighContourUnit
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Complex
open scoped ComplexConjugate
namespace RHHighContourCoefficientData
open RHHighDyadicComplex
noncomputable def trueCoefficient (m : Nat) (positive : Bool) : ℂ :=
  if positive then RHHighFourierPolynomial.coefficient m else conj (RHHighFourierPolynomial.coefficient m)
noncomputable def trueAmplitude (m : Nat) (positive : Bool) : ℝ :=
  Real.exp ((if positive then -1 else 1)*Real.pi*(m:ℝ)/512)
noncomputable def trueFrequency (m : Nat) (positive : Bool) : ℂ :=
  ((if positive then (1:ℝ) else -1)*Real.pi*(m:ℝ)/8192:ℝ)*I
noncomputable def trueSeed (t : Fin 3) (positive : Bool) (m : Nat) : ℂ :=
  trueCoefficient m positive*RHHighContourUnit.exactUnit (rootIndex t positive m)*
    (trueAmplitude m positive:ℂ)
noncomputable def trueTerm (t : Fin 3) (positive : Bool) (m k : Nat) : ℂ :=
  trueSeed t positive m*(trueFrequency m positive)^k/(k.factorial:ℂ)
lemma input_value (m : Nat) (positive : Bool) :
    value D (inputCoefficient m positive)=trueCoefficient m positive := by
  cases positive <;> unfold value inputCoefficient trueCoefficient RHHighFourierPolynomial.coefficient
  all_goals simp only [Bool.false_eq_true,if_false,if_true,Int.cast_mul,Int.cast_pow,
    Int.cast_ofNat,Int.cast_neg,map_div₀,map_add,map_mul,map_intCast,Complex.conj_I,
    map_pow,Complex.conj_ofNat]
  all_goals norm_num [D] <;> ring
lemma coefficient_norm (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    ‖trueCoefficient m positive‖≤1/2 := by
  cases positive <;> simpa [trueCoefficient,Complex.norm_conj] using
    RHHighContourReference.coefficient_half m hm
lemma amplitude_error (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    ‖value D ((amplitude m positive:Int),0)-(trueAmplitude m positive:ℂ)‖≤1/10^25 := by
  cases positive
  · have h:=RHHighContourReference.inverse_enclosure m hm
    simpa only [amplitude,trueAmplitude,Bool.false_eq_true,if_false,one_mul,
      value,D,RHHighLogData.D,Int.cast_natCast,Int.cast_zero,zero_mul,add_zero,Complex.ofReal_exp] using h
  · have h:=(RHHighContourReference.amplitude_enclosure m hm).trans
      (show (3:ℝ)/10^32≤1/10^25 by norm_num)
    simpa only [amplitude,trueAmplitude,if_true,neg_one_mul,value,D,RHHighLogData.D,Int.cast_natCast,
      Int.cast_zero,zero_mul,add_zero,Complex.ofReal_exp] using h
lemma amplitude_norm (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    ‖(trueAmplitude m positive:ℂ)‖≤2000 := by
  have hp:0<trueAmplitude m positive:=by unfold trueAmplitude;exact Real.exp_pos _
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  cases positive
  · simpa only [trueAmplitude,Bool.false_eq_true,if_false,one_mul,
      RHHighContourReference.lookup_m m hm] using RHHighContourReference.positive_exp_bound (RHHighContourReference.lookup m)
  · simpa only [trueAmplitude,if_true,neg_one_mul] using
      (RHHighContourReference.negative_exp_bound m).trans (show (1:ℝ)≤2000 by norm_num)
lemma frequency_error (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    ‖value D (frequency m positive)-trueFrequency m positive‖≤1/10^36 := by
  have h:=RHHighContourReference.frequency_enclosure m hm
  cases positive <;> unfold value frequency trueFrequency
  all_goals simp only [Bool.false_eq_true,if_false,if_true,Int.cast_zero,Int.cast_natCast,
    Int.cast_neg,zero_add,one_mul,neg_one_mul]
  all_goals
    have he:((RHHighContourReference.lookup m).x:ℂ)*I/(D:ℂ)-
        ((Real.pi*(m:ℝ)/8192:ℝ):ℂ)*I=
        (((((RHHighContourReference.lookup m).x:ℝ)/D)-Real.pi*(m:ℝ)/8192:ℝ):ℂ)*I := by push_cast;ring
    first
    | rw [show -((RHHighContourReference.lookup m).x:ℂ)*I/(D:ℂ)-
        ((-Real.pi*(m:ℝ)/8192:ℝ):ℂ)*I=
        -(((RHHighContourReference.lookup m).x:ℂ)*I/(D:ℂ)-
        ((Real.pi*(m:ℝ)/8192:ℝ):ℂ)*I) by push_cast;ring,norm_neg]
    | skip
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    exact h
lemma frequency_norm (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    ‖value D (frequency m positive)‖≤1 := by
  have h:=RHHighContourReference.proposed_frequency_bound m hm
  cases positive <;> simp [value,frequency,norm_div,norm_mul,norm_pow,norm_ofNat,
    Complex.norm_natCast,Complex.norm_intCast,D,abs_of_nonneg] at *
  all_goals exact h.2
lemma true_frequency_norm (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    ‖trueFrequency m positive‖≤1 := by
  have h:=RHHighContourReference.true_frequency_bound m hm.2
  cases positive <;> simp only [trueFrequency,Bool.false_eq_true,if_false,if_true,
    one_mul,neg_one_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  all_goals simp only [show -Real.pi*(m:ℝ)/8192=-(Real.pi*(m:ℝ)/8192) by ring,
    abs_neg,abs_of_nonneg h.1];exact h.2.trans (by norm_num)
lemma seed_enclosure (t : Fin 3) (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
    ‖value D (seed t positive m)-trueSeed t positive m‖≤1/10^24 := by
  have hu:=RHHighContourUnit.enclosure (rootIndex t positive m)
  rw [←RHHighContourUnit.exact_exp] at hu
  have hp:‖RHHighContourUnit.exactUnit (rootIndex t positive m)‖≤1 := by
    rw [RHHighContourUnit.exact_exp,Complex.norm_exp_ofReal_mul_I]
  exact RHHighContourCoefficient.seed_error (inputCoefficient m positive)
    (RHHighContourUnit.pair (rootIndex t positive m)) ((amplitude m positive:Int),0)
    (trueCoefficient m positive) (RHHighContourUnit.exactUnit (rootIndex t positive m))
    (trueAmplitude m positive:ℂ) (input_value m positive)
    ((coefficient_norm m hm positive).trans (by norm_num)) hp hu
    (amplitude_norm m hm positive) (amplitude_error m hm positive)
end RHHighContourCoefficientData
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighContourCoefficientData
lemma seventh_root (m : Nat) : RHHighContourUnit.exactUnit (7*m)=
    Complex.exp (((-Real.pi*(m:ℝ)/4:ℝ):ℂ)*I) := by
  rw [RHHighContourUnit.exact_exp]
  have he:(((Real.pi*((7*m:Nat):ℝ)/4:ℝ):ℂ)*I)=
      (((-Real.pi*(m:ℝ)/4:ℝ):ℂ)*I)+(m:ℂ)*(2*(Real.pi:ℂ)*I) := by
    push_cast
    ring
  rw [he,Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,mul_one]
noncomputable def start (t : Fin 3) : ℝ := 64*((t.val:ℝ)-1)
lemma unit_at_start (t : Fin 3) (positive : Bool) (m : Nat) :
    RHHighContourUnit.exactUnit (rootIndex t positive m)=
      Complex.exp (((((if positive then (1:ℝ) else -1)*2*Real.pi*(m:ℝ)/512)*start t:ℝ):ℂ)*I) := by
  have ht:=t.isLt
  rcases t with ⟨t,ht⟩
  interval_cases t <;> cases positive
  all_goals norm_num [rootIndex,start]
  all_goals try rw [seventh_root]
  all_goals try rw [RHHighContourUnit.exact_exp]
  all_goals norm_num <;> congr 1 <;> push_cast <;> ring
end RHHighContourCoefficientData
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
open Complex
open scoped ComplexConjugate
namespace RHHighContourCoefficientData
noncomputable def basePoint (t : Fin 3) : ℂ := (start t:ℂ)+(1/2:ℂ)*I
lemma positive_seed (t : Fin 3) (m : Nat) : trueSeed t true m=
    RHHighFourierPolynomial.coefficient m*RHHighFourierPolynomial.phase m (basePoint t) := by
  rw [trueSeed,unit_at_start]
  simp only [trueCoefficient,trueAmplitude,if_true,one_mul,neg_one_mul,Complex.ofReal_exp]
  rw [mul_assoc,←Complex.exp_add]
  unfold RHHighFourierPolynomial.phase basePoint
  congr 1
  congr 1
  push_cast
  ring_nf
  simp only [I_sq]
  ring
lemma negative_seed (t : Fin 3) (m : Nat) : trueSeed t false m=
    conj (RHHighFourierPolynomial.coefficient m)*RHHighFourierPolynomial.phase m (-basePoint t) := by
  rw [trueSeed,unit_at_start]
  simp only [trueCoefficient,trueAmplitude,Bool.false_eq_true,if_false,one_mul,neg_one_mul,Complex.ofReal_exp]
  rw [mul_assoc,←Complex.exp_add]
  unfold RHHighFourierPolynomial.phase basePoint
  congr 1
  congr 1
  push_cast
  ring_nf
  simp only [I_sq]
  ring
lemma positive_frequency (m : Nat) : trueFrequency m true=RHHighFourierPolynomial.generator m*(1/32:ℂ) := by
  unfold trueFrequency RHHighFourierPolynomial.generator
  simp only [if_true,one_mul]
  push_cast
  ring
lemma negative_frequency (m : Nat) : trueFrequency m false=-RHHighFourierPolynomial.generator m*(1/32:ℂ) := by
  unfold trueFrequency RHHighFourierPolynomial.generator
  simp only [Bool.false_eq_true,if_false,neg_one_mul]
  push_cast
  ring
lemma positive_term (t : Fin 3) (m k : Nat) : trueTerm t true m k=
    RHHighFourierPolynomial.coefficient m*RHHighFourierPolynomial.phase m (basePoint t)*
      (RHHighFourierPolynomial.generator m*(1/32:ℂ))^k/(k.factorial:ℂ) := by
  rw [trueTerm,positive_seed,positive_frequency]
lemma negative_term (t : Fin 3) (m k : Nat) : trueTerm t false m k=
    conj (RHHighFourierPolynomial.coefficient m)*RHHighFourierPolynomial.phase m (-basePoint t)*
      (-RHHighFourierPolynomial.generator m*(1/32:ℂ))^k/(k.factorial:ℂ) := by
  rw [trueTerm,negative_seed,negative_frequency]
end RHHighContourCoefficientData
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighContourCoefficientData
lemma polynomial_phase_add (m : Nat) (z w : ℂ) :
    RHHighFourierPolynomial.phase m (z+w)=
      RHHighFourierPolynomial.phase m z*RHHighFourierPolynomial.phase m w := by
  unfold RHHighFourierPolynomial.phase
  rw [←Complex.exp_add]
  congr 1
  ring
lemma polynomial_phase_step (m : Nat) (r : Fin 16384) :
    RHHighFourierPolynomial.phase m ((r.val:ℂ)/32)=
      RHHighChirpDFT.phase (2*(m:ℝ)*(r.val:ℝ)/16384) := by
  unfold RHHighFourierPolynomial.phase RHHighChirpDFT.phase
  congr 1
  push_cast
  ring
lemma polynomial_phase_neg_step (m : Nat) (r : Fin 16384) :
    RHHighFourierPolynomial.phase m (-((r.val:ℂ)/32))=
      RHHighChirpDFT.phase (-2*(m:ℝ)*(r.val:ℝ)/16384) := by
  unfold RHHighFourierPolynomial.phase RHHighChirpDFT.phase
  congr 1
  push_cast
  ring
lemma jet_advance (t : Fin 3) (k : Nat) (r : Fin 16384) :
    RHHighFourierPolynomial.jet (basePoint t+(r.val:ℂ)/32) (1/32) k=
      (if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)+
      ∑ m:Fin 1024,(trueTerm t true (m.val+1) k*
        RHHighChirpDFT.phase (2*((m.val:ℝ)+1)*(r.val:ℝ)/16384)+
        trueTerm t false (m.val+1) k*
        RHHighChirpDFT.phase (-2*((m.val:ℝ)+1)*(r.val:ℝ)/16384)) := by
  unfold RHHighFourierPolynomial.jet
  rw [Finset.sum_range]
  apply congrArg (fun z:ℂ=>(if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)+z)
  apply Finset.sum_congr rfl
  intro m hm
  rw [positive_term,negative_term,polynomial_phase_add,
    neg_add,polynomial_phase_add,polynomial_phase_step,polynomial_phase_neg_step]
  push_cast
  ring
noncomputable def exactSpectrum (t : Fin 3) (k : Nat) : Fin 16384→ℂ :=
  RHHighSparseContourDFT.spectrum (if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)
    (fun m=>trueTerm t true (m.val+1) k) (fun m=>trueTerm t false (m.val+1) k)
lemma exact_dft (t : Fin 3) (k : Nat) (r : Fin 16384) :
    RHHighChirpDFT.dft (exactSpectrum t k) r=
      RHHighFourierPolynomial.jet (basePoint t+(r.val:ℂ)/32) (1/32) k := by
  rw [exactSpectrum,RHHighSparseContourDFT.spectrum_dft,jet_advance]
end RHHighContourCoefficientData
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighContourCoefficientData
open RHHighDyadicComplex
lemma trueSeed_norm (t : Fin 3) (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) :
    ‖trueSeed t positive m‖≤1000 := by
  have hp:‖RHHighContourUnit.exactUnit (rootIndex t positive m)‖=1:=by
    rw [RHHighContourUnit.exact_exp,Complex.norm_exp_ofReal_mul_I]
  rw [trueSeed,norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_mul (coefficient_norm m hm positive) (amplitude_norm m hm positive)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
lemma trueTerm_norm (t : Fin 3) (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) (k : Nat) :
    ‖trueTerm t positive m k‖≤1000 := by
  have hp:‖trueFrequency m positive‖^k≤1:=
    pow_le_one₀ (norm_nonneg _) (true_frequency_norm m hm positive)
  have hn:(1:ℝ)≤(k.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos k
  rw [trueTerm,norm_div,norm_mul,norm_pow,Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right
    ((mul_le_mul (trueSeed_norm t positive m hm) hp (by positivity) (by norm_num)).trans_eq (by ring))
    (Nat.cast_nonneg _)).trans (div_le_self (by norm_num) hn)
lemma trueTerm_zero (t : Fin 3) (positive : Bool) (m : Nat) : trueTerm t positive m 0=trueSeed t positive m := by
  simp [trueTerm]
lemma trueTerm_succ (t : Fin 3) (positive : Bool) (m k : Nat) :
    trueTerm t positive m (k+1)=trueTerm t positive m k*trueFrequency m positive/((k+1:Nat):ℂ) := by
  unfold trueTerm
  rw [pow_succ,Nat.factorial_succ,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
lemma coefficient_enclosure (t : Fin 3) (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) (k : Nat) :
    ‖value D (coefficient t positive m k)-trueTerm t positive m k‖≤((k:ℝ)+1)/10^24 := by
  induction k with
  | zero => simpa only [coefficient,trueTerm_zero,Nat.cast_zero,zero_add,one_div] using seed_enclosure t positive m hm
  | succ k ih =>
    have h:=RHHighContourCoefficient.step_error (coefficient t positive m k) (frequency m positive)
      (trueTerm t positive m k) (trueFrequency m positive) (k+1) (by omega)
      (((k:ℝ)+1)/10^24) (by positivity) (trueTerm_norm t positive m hm k)
      (frequency_norm m hm positive) ih (frequency_error m hm positive)
    change ‖value D (coefficient t positive m (k+1))-
      trueTerm t positive m k*trueFrequency m positive/((k+1:Nat):ℂ)‖≤_ at h
    rw [←trueTerm_succ] at h
    exact h.trans (by push_cast;linarith)
lemma comparison_error (a b : Int×Int)
    (h:|a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52) :
    ‖value D a-value (2^80) b‖≤2*(2:ℝ)^52/(2:ℝ)^128 := by
  have hr:|((a.1-b.1*2^48:Int):ℝ)|≤(2:ℝ)^52:=by exact_mod_cast h.1
  have hi:|((a.2-b.2*2^48:Int):ℝ)|≤(2:ℝ)^52:=by exact_mod_cast h.2
  have he:value D a-value (2^80) b=
      (((a.1-b.1*2^48:Int):ℂ)+((a.2-b.2*2^48:Int):ℂ)*I)/(2:ℂ)^128 := by
    unfold value D
    push_cast
    norm_num
    ring
  rw [he,norm_div,norm_pow,norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh:=norm_add_le ((a.1-b.1*2^48:Int):ℂ) (((a.2-b.2*2^48:Int):ℂ)*I)
  simp only [norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one] at hh
  nlinarith only [hh,hr,hi]
lemma proposed_enclosure (t : Fin 3) (positive : Bool) (m k : Nat)
    (hm:1 ≤ m ∧ m≤1024) (hk:k<8) (v : List Nat)
    (h:let a:=coefficient t positive m k;let b:=proposed v positive m;
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52) :
    ‖value (2^80) (proposed v positive m)-trueTerm t positive m k‖≤1/10^21 := by
  have hc:=comparison_error (coefficient t positive m k) (proposed v positive m) h
  rw [norm_sub_rev] at hc
  have ha:=coefficient_enclosure t positive m hm k
  have hkr:(k:ℝ)≤7:=by exact_mod_cast (show k≤7 by omega)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hc ha)).trans (by
    norm_num
    nlinarith only [hkr])
end RHHighContourCoefficientData
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighContourCoefficientData
open RHHighDyadicComplex
lemma word_magnitude (p : Nat)
    (h:|(decode p).1|+|(decode p).2|≤(2:Int)^80) :
    ‖value (2^80) (decode p)‖≤1 := by
  have hr: |((decode p).1:ℝ)|+|((decode p).2:ℝ)|≤(2:ℝ)^80:=by exact_mod_cast h
  unfold value
  rw [norm_div,Complex.norm_natCast,Nat.cast_pow,Nat.cast_ofNat]
  apply (div_le_one (by positivity)).mpr
  have hh:=norm_add_le ((decode p).1:ℂ) (((decode p).2:ℂ)*I)
  simp only [norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one] at hh
  exact hh.trans hr
lemma proposed_magnitude (v : List Nat) (positive : Bool) (m : Nat)
    (h:|(proposed v positive m).1|+|(proposed v positive m).2|≤(2:Int)^80) :
    ‖value (2^80) (proposed v positive m)‖≤1 := by
  exact word_magnitude _ h
lemma true_term_magnitude (t : Fin 3) (positive : Bool) (m k : Nat)
    (hm:1 ≤ m ∧ m≤1024) (hk:k<8) (v : List Nat)
    (hc:let a:=coefficient t positive m k;let b:=proposed v positive m;
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (hb:|(proposed v positive m).1|+|(proposed v positive m).2|≤(2:Int)^80) :
    ‖trueTerm t positive m k‖≤2 := by
  have he:=proposed_enclosure t positive m k hm hk v hc
  have hp:=proposed_magnitude v positive m hb
  have he':‖trueTerm t positive m k-value (2^80) (proposed v positive m)‖≤1/10^21:=by
    simpa only [norm_sub_rev] using he
  have hs:‖trueTerm t positive m k-value (2^80) (proposed v positive m)‖≤1:=he'.trans (by norm_num)
  have hh:=norm_sub_le_norm_sub_add_norm_sub (trueTerm t positive m k)
    (value (2^80) (proposed v positive m)) 0
  simp only [sub_zero] at hh
  linarith only [hh,hs,hp]
end RHHighContourCoefficientData
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighSparseContourDFT
def posIndex (m : Fin 1024) : Fin 16384 := ⟨16383-m.val,by omega⟩
def negIndex (m : Fin 1024) : Fin 16384 := ⟨m.val+1,by omega⟩
lemma pos_injective : Function.Injective posIndex := by
  intro m n h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp only [posIndex] at hv
  omega
lemma neg_injective : Function.Injective negIndex := by
  intro m n h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp only [negIndex] at hv
  omega
lemma spike_sum_eq {M N : Nat} (p : Fin M→Fin N) (hp:Function.Injective p)
    (a : Fin M→ℂ) (m : Fin M) :
    (∑ q:Fin M,spike (p q) (a q) (p m))=a m := by
  simp [spike,hp.eq_iff]
lemma spike_sum_zero {M N : Nat} (p : Fin M→Fin N) (a : Fin M→ℂ)
    (j : Fin N) (h:∀ q,j≠p q) : (∑ q:Fin M,spike (p q) (a q) j)=0 := by
  apply Finset.sum_eq_zero
  intro q hq
  exact if_neg (h q)
lemma spectrum_norm (a0 : ℂ) (ap an : Fin 1024→ℂ) (A : ℝ)
    (hA:0≤A) (h0:‖a0‖≤A) (hp:∀m,‖ap m‖≤A) (hn:∀m,‖an m‖≤A)
    (j : Fin 16384) : ‖spectrum a0 ap an j‖≤A := by
  have he:spectrum a0 ap an j=spike ⟨0,by decide⟩ a0 j+
      (∑ m:Fin 1024,spike (posIndex m) (ap m) j)+
      (∑ m:Fin 1024,spike (negIndex m) (an m) j) := by
    unfold spectrum posIndex negIndex
    rw [Finset.sum_add_distrib]
    ring
  by_cases hz:j.val=0
  · have hj:j=⟨0,by decide⟩:=Fin.ext hz
    have hpos:∀m,j≠posIndex m:=by
      intro m h
      have hv:=congrArg Fin.val h
      dsimp only [posIndex] at hv
      omega
    have hneg:∀m,j≠negIndex m:=by
      intro m h
      have hv:=congrArg Fin.val h
      dsimp only [negIndex] at hv
      omega
    rw [he,spike_sum_zero _ _ j hpos,spike_sum_zero _ _ j hneg,spike,if_pos hj,add_zero,add_zero]
    exact h0
  · have hzne:j≠⟨0,by decide⟩:=by intro h;exact hz (congrArg Fin.val h)
    by_cases hlo:j.val≤1024
    · let m:Fin 1024:=⟨j.val-1,by omega⟩
      have hj:j=negIndex m:=by apply Fin.ext;dsimp only [negIndex,m];omega
      have hpos:∀q,j≠posIndex q:=by
        intro q h
        have hv:=congrArg Fin.val h
        dsimp only [posIndex] at hv
        omega
      have hs:(∑ q:Fin 1024,spike (negIndex q) (an q) j)=an m:=by rw [hj];exact spike_sum_eq _ neg_injective _ m
      rw [he,spike_sum_zero _ _ j hpos,hs,spike,if_neg hzne,zero_add,zero_add]
      exact hn m
    · by_cases hhi:15360≤j.val
      · let m:Fin 1024:=⟨16383-j.val,by omega⟩
        have hj:j=posIndex m:=by apply Fin.ext;dsimp only [posIndex,m];omega
        have hneg:∀q,j≠negIndex q:=by
          intro q h
          have hv:=congrArg Fin.val h
          dsimp only [negIndex] at hv
          omega
        have hs:(∑ q:Fin 1024,spike (posIndex q) (ap q) j)=ap m:=by rw [hj];exact spike_sum_eq _ pos_injective _ m
        rw [he,hs,spike_sum_zero _ _ j hneg,spike,if_neg hzne,zero_add,add_zero]
        exact hp m
      · have hpos:∀q,j≠posIndex q:=by
          intro q h
          have hv:=congrArg Fin.val h
          dsimp only [posIndex] at hv
          omega
        have hneg:∀q,j≠negIndex q:=by
          intro q h
          have hv:=congrArg Fin.val h
          dsimp only [negIndex] at hv
          omega
        rw [he,spike_sum_zero _ _ j hpos,spike_sum_zero _ _ j hneg,spike,if_neg hzne,add_zero,add_zero,norm_zero]
        exact hA
end RHHighSparseContourDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHHighSparseContourDFT
lemma spectrum_at (a0 : ℂ) (ap an : Nat→ℂ) (j : Fin 16384) :
 spectrum a0 (fun m=>ap m.val) (fun m=>an m.val) j=
  if j.val=0 then a0 else if j.val≤1024 then an (j.val-1)
   else if 15360≤j.val then ap (16383-j.val) else 0 := by
  have he:spectrum a0 (fun m=>ap m.val) (fun m=>an m.val) j=spike ⟨0,by decide⟩ a0 j+
      (∑ m:Fin 1024,spike (posIndex m) (ap m.val) j)+
      (∑ m:Fin 1024,spike (negIndex m) (an m.val) j) := by
    unfold spectrum posIndex negIndex
    rw [Finset.sum_add_distrib]
    ring
  by_cases hz:j.val=0
  · have hj:j=⟨0,by decide⟩:=Fin.ext hz
    have hpos:∀m,j≠posIndex m:=by
      intro m h
      have hv:=congrArg Fin.val h
      dsimp only [posIndex] at hv
      omega
    have hneg:∀m,j≠negIndex m:=by
      intro m h
      have hv:=congrArg Fin.val h
      dsimp only [negIndex] at hv
      omega
    rw [he,spike_sum_zero _ _ j hpos,spike_sum_zero _ _ j hneg,spike,if_pos hj,add_zero,add_zero]
    simp only [hz,if_true]
  · have hzne:j≠⟨0,by decide⟩:=by intro h;exact hz (congrArg Fin.val h)
    by_cases hlo:j.val≤1024
    · let m:Fin 1024:=⟨j.val-1,by omega⟩
      have hj:j=negIndex m:=by apply Fin.ext;dsimp only [negIndex,m];omega
      have hpos:∀q,j≠posIndex q:=by
        intro q h
        have hv:=congrArg Fin.val h
        dsimp only [posIndex] at hv
        omega
      have hs:(∑ q:Fin 1024,spike (negIndex q) (an q.val) j)=an m.val:=by rw [hj];exact spike_sum_eq _ neg_injective _ m
      rw [he,spike_sum_zero _ _ j hpos,hs,spike,if_neg hzne,zero_add,zero_add]
      simp only [hz,if_false,hlo,if_true];rfl
    · by_cases hhi:15360≤j.val
      · let m:Fin 1024:=⟨16383-j.val,by omega⟩
        have hj:j=posIndex m:=by apply Fin.ext;dsimp only [posIndex,m];omega
        have hneg:∀q,j≠negIndex q:=by
          intro q h
          have hv:=congrArg Fin.val h
          dsimp only [negIndex] at hv
          omega
        have hs:(∑ q:Fin 1024,spike (posIndex q) (ap q.val) j)=ap m.val:=by rw [hj];exact spike_sum_eq _ pos_injective _ m
        rw [he,hs,spike_sum_zero _ _ j hneg,spike,if_neg hzne,zero_add,add_zero]
        simp only [hz,if_false,hlo,if_false,hhi,if_true];rfl
      · have hpos:∀q,j≠posIndex q:=by
          intro q h
          have hv:=congrArg Fin.val h
          dsimp only [posIndex] at hv
          omega
        have hneg:∀q,j≠negIndex q:=by
          intro q h
          have hv:=congrArg Fin.val h
          dsimp only [negIndex] at hv
          omega
        rw [he,spike_sum_zero _ _ j hpos,spike_sum_zero _ _ j hneg,spike,if_neg hzne,add_zero,add_zero]
        simp only [hz,if_false,hlo,if_false,hhi,if_false]
end RHHighSparseContourDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighContourCoefficientData
lemma vector_coefficient (v : List Nat) (positive : Bool) (m : Nat) :
    RHHighContourVector.coefficient v positive m=proposed v positive m := rfl
lemma vector_value (p : Int×Int) :
    RHHighContourVector.value p=RHHighDyadicComplex.value (2^80) p := by
  unfold RHHighContourVector.value RHHighDyadicComplex.value
  norm_cast
lemma spectrum_error (t : Fin 3) (k : Nat) (hk:k<8) (v : List Nat)
    (hzero:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
      if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)
    (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let a:=coefficient t positive m k;let b:=proposed v positive m;
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (j : Fin 16384) :
    ‖exactSpectrum t k j-RHHighContourVector.value (RHHighContourVector.vector v j.val)‖≤1/10^21 := by
  rw [exactSpectrum,RHHighSparseContourDFT.spectrum_at _
    (fun n=>trueTerm t true (n+1) k) (fun n=>trueTerm t false (n+1) k) j]
  unfold RHHighContourVector.vector
  by_cases hz:j.val=0
  · simp only [hz,if_true]
    rw [hzero,sub_self,norm_zero]
    positivity
  · simp only [hz,if_false]
    by_cases hlo:j.val≤1024
    · simp only [hlo,if_true]
      rw [vector_value,vector_coefficient,norm_sub_rev]
      have he:j.val-1+1=j.val:=by omega
      simpa only [he] using proposed_enclosure t false j.val k (by omega) hk v (hc false j.val (by omega))
    · simp only [hlo,if_false]
      by_cases hhi:15360≤j.val
      · simp only [hhi,if_true]
        rw [vector_value,vector_coefficient,norm_sub_rev]
        have he:16383-j.val+1=16384-j.val:=by omega
        simpa only [he] using proposed_enclosure t true (16384-j.val) k (by omega) hk v (hc true (16384-j.val) (by omega))
      · simp only [hhi,if_false,RHHighContourVector.value,Int.cast_zero,zero_mul,add_zero,zero_div,sub_self,norm_zero]
        positivity
end RHHighContourCoefficientData
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighContourCoefficientData
lemma spectrum_bound (t : Fin 3) (k : Nat) (hk:k<8) (v : List Nat)
    (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let a:=coefficient t positive m k;let b:=proposed v positive m;
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (hmag:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      |(proposed v positive m).1|+|(proposed v positive m).2|≤(2:Int)^80)
    (j : Fin 16384) : ‖exactSpectrum t k j‖≤2 := by
  apply (RHHighSparseContourDFT.spectrum_norm _ _ _ 2 (by norm_num) ?_ ?_ ?_ j).trans (by norm_num)
  · by_cases hk0:k=0
    · simp only [hk0,if_true]
      have h:=RHHighFourierPolynomial.coefficient_mass
      have hs:0≤∑m∈Finset.range 1024,‖RHHighFourierPolynomial.coefficient (m+1)‖:=by positivity
      linarith only [h,hs]
    · simp only [hk0,if_false,norm_zero];norm_num
  · intro m
    exact true_term_magnitude t true (m.val+1) k (by omega) hk v (hc true _ (by omega)) (hmag true _ (by omega))
  · intro m
    exact true_term_magnitude t false (m.val+1) k (by omega) hk v (hc false _ (by omega)) (hmag false _ (by omega))
lemma vector_bound (t : Fin 3) (k : Nat) (hk:k<8) (v : List Nat)
    (hzero:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
      if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)
    (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let a:=coefficient t positive m k;let b:=proposed v positive m;
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (hmag:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      |(proposed v positive m).1|+|(proposed v positive m).2|≤(2:Int)^80)
    (j : Fin 16384) :
    ‖RHHighContourVector.value (RHHighContourVector.vector v j.val)‖≤18 := by
  have he:=spectrum_error t k hk v hzero hc j
  have hb:=spectrum_bound t k hk v hc hmag j
  have ht:=norm_sub_le_norm_sub_add_norm_sub (RHHighContourVector.value (RHHighContourVector.vector v j.val))
    (exactSpectrum t k j) 0
  rw [norm_sub_rev] at he
  simp only [sub_zero] at ht
  linarith only [he,hb,ht]
lemma jet_of_vector (t : Fin 3) (k : Nat) (hk:k<8) (v : List Nat)
    (hzero:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
      if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)
    (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let a:=coefficient t positive m k;let b:=proposed v positive m;
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (r : Fin 16384) (out : ℂ)
    (hfft:‖RHHighChirpDFT.dft (fun j:Fin 16384=>RHHighContourVector.value (RHHighContourVector.vector v j.val)) r-out‖≤1/10^13) :
    ‖RHHighPolynomialJet.jet (basePoint t+(r.val:ℂ)/32) (1/32) k-out‖≤1/10^12 := by
  have he:=RHHighChirpDFT.dft_error (exactSpectrum t k)
    (fun j:Fin 16384=>RHHighContourVector.value (RHHighContourVector.vector v j.val))
    (1/10^21) (spectrum_error t k hk v hzero hc) r
  rw [exact_dft] at he
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add he hfft)).trans (by norm_num)
end RHHighContourCoefficientData
end
end RHHighRepairedContourFFT
theorem solution (t : Fin 3) (k : Nat) (hk:k<8) (v : List Nat)
    (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hzero:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
      if k=0 then RHHighFourierPolynomial.coefficient 0 else 0)
    (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let a:=RHHighContourCoefficientData.coefficient t positive m k
      let b:=RHHighContourCoefficientData.proposed v positive m
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (hmag:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let b:=RHHighContourCoefficientData.proposed v positive m
      |b.1|+|b.2|≤(2:Int)^80)
    (hinput:∀ j:Fin 16384,RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp j.val=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (r : Fin 2048) :
    ‖RHHighPolynomialJet.jet (64*(t.val:ℂ)-64+(1/2:ℂ)*Complex.I+(r.val:ℂ)/32) (1/32) k-
        (let p:=((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
          (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
          RHHighFFTArithmeticBase.chirp)[r.val]?).getD (0,0)
         ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^80)‖≤1/10^12 := by
  have hf:=TaoFivePrimes.rh_high_height_vector_fft_semantic v ar ai br bi hAr hAi hBr hBi
    (RHHighRepairedContourFFT.RHHighContourCoefficientData.vector_bound t k hk v hzero hc hmag) hinput hkernel r
  have h:=RHHighRepairedContourFFT.RHHighContourCoefficientData.jet_of_vector t k hk v hzero hc ⟨r.val,by omega⟩ _ hf
  have ht:RHHighRepairedContourFFT.RHHighContourCoefficientData.basePoint t=64*(t.val:ℂ)-64+(1/2:ℂ)*Complex.I := by
    fin_cases t <;> norm_num [RHHighRepairedContourFFT.RHHighContourCoefficientData.basePoint,RHHighRepairedContourFFT.RHHighContourCoefficientData.start]
  rw [ht] at h
  exact h
