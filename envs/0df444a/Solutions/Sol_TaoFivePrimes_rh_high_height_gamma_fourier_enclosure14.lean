-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fourier_enclosure14
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:45:30.125512+00:00
-- url     : https://prove2.me/submissions/b3682690-fc1e-4602-8890-0b82f9585f28

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_semantic
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_kernel_interface
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds14
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_actual_input14
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation14
namespace RHHighGammaFourierOrder14
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
end RHHighGammaFourierOrder14
open scoped FourierTransform
theorem solution (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive14.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 14) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by
  let R:=RHHighFFTInputR14.rows
  let J:=RHHighFFTInputI14.rows
  let brs:=RHHighFFTChirpR.rows.flatten
  let bis:=RHHighFFTChirpI.rows.flatten
  let bss:=RHHighFFTChirpS.rows.flatten
  have hR:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds14 R (by simp only [R,List.mem_cons,true_or])
  have hJ:=TaoFivePrimes.rh_high_height_gamma_fft_array_bounds14 J (by simp only [J,List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only [List.mem_cons,true_or])
  have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false])
  let ar:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.entry R.flatten j.val
  let ai:Fin 16384→Nat:=fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.entry J.flatten j.val
  let br:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.entry brs j.val
  let bi:Fin 32767→Nat:=fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.entry bis j.val
  have hi (j:Fin 16384):
    let p:=RHHighMomentArithmetic.moment j.val (RHHighGammaArithmetic.compute j.val) 14
    let c:=RHHighFFTArithmeticBase.chirp j.val
    (p.1*c.1+p.2*c.2,p.2*c.1-p.1*c.2)=((ar j:Int)-2^166,(ai j:Int)-2^166) := by
    have h:=TaoFivePrimes.rh_high_height_fft_actual_input14 j.val j.isLt
    have hr:=RHHighGammaFourierOrder14.RHHighFFTListInterface.uniform_lookup R j.val
      (RHHighGammaFourierOrder14.RHHighFFTListInterface.lengths_from_bound R (2^167) hR.2) (by rw [hR.1];exact j.isLt)
    have hj:=RHHighGammaFourierOrder14.RHHighFFTListInterface.uniform_lookup J j.val
      (RHHighGammaFourierOrder14.RHHighFFTListInterface.lengths_from_bound J (2^167) hJ.2) (by rw [hJ.1];exact j.isLt)
    change _=(((RHHighGammaFourierOrder14.RHHighFFTListInterface.entry R.flatten j.val:Int)-2^166),
      ((RHHighGammaFourierOrder14.RHHighFFTListInterface.entry J.flatten j.val:Int)-2^166))
    rw [hr,hj]
    exact h
  have hk (j:Fin 32767):((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs :=
    (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j.val j.isLt).1
  have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
      (List.ofFn (fun j=>br j+bi j)) RHHighFFTArithmeticBase.chirp=
      RHHighPackedFFT.decode RHHighFFTPositive14.rows.flatten := by
    have hs:List.ofFn (fun j:Fin 32767=>br j+bi j)=bss := by
      apply RHHighGammaFourierOrder14.RHHighFFTListInterface.ofFn_add brs bis bss hKR hKI hKS
      intro j hj
      exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 j hj).2
    rw [hs,RHHighGammaFourierOrder14.RHHighFFTListInterface.ofFn_at R.flatten hR.1,
      RHHighGammaFourierOrder14.RHHighFFTListInterface.ofFn_at J.flatten hJ.1,
      RHHighGammaFourierOrder14.RHHighFFTListInterface.ofFn_at brs hKR,RHHighGammaFourierOrder14.RHHighFFTListInterface.ofFn_at bis hKI]
    exact TaoFivePrimes.rh_high_height_fft_computation14
  have h:=TaoFivePrimes.rh_high_height_gamma_fft_semantic 14 (by decide) ar ai br bi
    (fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.bounded_at R.flatten (2^167)
      (RHHighGammaFourierOrder14.RHHighFFTListInterface.flatten_bounded R (2^167) hR.2) j.val)
    (fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.bounded_at J.flatten (2^167)
      (RHHighGammaFourierOrder14.RHHighFFTListInterface.flatten_bounded J (2^167) hJ.2) j.val)
    (fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.bounded_at brs (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 j.val)
    (fun j=>RHHighGammaFourierOrder14.RHHighFFTListInterface.bounded_at bis (2^82)
      TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 j.val) hi hk ⟨m,by omega⟩ (by change m≤1953;omega)
  rw [hout] at h
  have hv:RHHighFFTPositive14.rows.flatten.length=2048:=by decide +kernel
  rw [RHHighGammaFourierOrder14.RHHighGammaSignedPhase.sample_decode _ m (by rw [hv];omega)] at h
  have he:=RHHighGammaFourierOrder14.RHHighGammaSignedPhase.value RHHighFFTPositive14.rows.flatten m
  simp only [mul_div_assoc] at he
  rw [he] at h
  exact h
