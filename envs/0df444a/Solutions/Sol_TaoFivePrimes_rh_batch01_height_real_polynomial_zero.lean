-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_real_polynomial_zero
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:21:31.902823+00:00
-- url     : https://prove2.me/submissions/ae4b0afb-4f20-41d3-bf66-9a740fff4565

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_fft_semantic
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_kernel_interface
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_reference_zero
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_actual_input_zero
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_fft_zero
namespace RHBatch01RealPolynomialZero
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
set_option maxHeartbeats 1000000
namespace RHBatch01FFTListInterface
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
  apply RHBatch01FlatRows.lookup 512 (by decide) 0 rows
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
end RHBatch01FFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01FFTListInterface
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
end RHBatch01FFTListInterface
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
end RHBatch01RealPolynomialZero
theorem solution (j : Nat) (hj:j<2048) :
 ‖RHBatch01FourierPolynomial.polynomial (0+(j:ℂ)/32)-
 RHHighContourVector.value (RHHighContourVector.decode ((RHBatch01ContourOutputRealZero.rows.flatten[j]?).getD 0))‖≤1/10^12 := by
 let R:=RHBatch01ContourInputRRealZero.rows
 let J:=RHBatch01ContourInputIRealZero.rows
 let v:=RHBatch01RealSpectrumZero.rows.flatten
 let brs:=RHHighFFTChirpR.rows.flatten
 let bis:=RHHighFFTChirpI.rows.flatten
 let bss:=RHHighFFTChirpS.rows.flatten
 have hR:R.flatten.length=16384:=by decide +kernel
 have hJ:J.flatten.length=16384:=by decide +kernel
 have hr:R.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 have hi:J.all (fun row=>decide (row.length=512))=true:=by decide +kernel
 let ar:Fin 16384→Nat:=fun i=>RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.entry R.flatten i.val
 let ai:Fin 16384→Nat:=fun i=>RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.entry J.flatten i.val
 let br:Fin 32767→Nat:=fun i=>RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.entry brs i.val
 let bi:Fin 32767→Nat:=fun i=>RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.entry bis i.val
 have hri (i : Fin 16384) :
  RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp i.val=((ar i:Int)-2^166,(ai i:Int)-2^166) ∧ ar i≤2^167 ∧ ai i≤2^167 := by
  have h:=TaoFivePrimes.rh_batch01_height_real_actual_input_zero i.val i.isLt
  have hR':=RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.uniform_lookup R i.val hr (by rw[hR];exact i.isLt)
  have hJ':=RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.uniform_lookup J i.val hi (by rw[hJ];exact i.isLt)
  dsimp only[ar,ai]
  rw[hR',hJ']
  exact h
 have hKR:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpR.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKI:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpI.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hKS:=TaoFivePrimes.rh_high_height_fft_kernel_interface.1 RHHighFFTChirpS.rows (by simp only[List.mem_cons,List.mem_nil_iff,true_or,or_true,or_false])
 have hker (i : Fin 32767) : ((br i:Int)-2^81,(bi i:Int)-2^81)=RHHighFFTArithmeticBase.chirp ((i.val:Int)-16383).natAbs :=
  (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i.val i.isLt).1
 have hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=RHBatch01FourierPolynomial.coefficient 0 := by
  have h0:=TaoFivePrimes.rh_batch01_height_real_reference_zero.1
  change ((v[0]?).getD 0)=RHBatch01FourierPolynomial.word 0 at h0
  simp only[h0,RHHighContourVector.value,RHHighContourVector.decode,RHBatch01FourierPolynomial.coefficient,
   RHBatch01FourierPolynomial.realInteger,RHBatch01FourierPolynomial.imagInteger]
 have hout:RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
  (List.ofFn (fun i=>br i+bi i)) RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHBatch01ContourOutputRealZero.rows.flatten := by
  have hs:List.ofFn (fun i:Fin 32767=>br i+bi i)=bss := by
   apply RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.ofFn_add brs bis bss hKR hKI hKS
   intro i hi
   exact (TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.2 i hi).2
  rw[hs,RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.ofFn_at R.flatten hR,
   RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.ofFn_at J.flatten hJ,
   RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.ofFn_at brs hKR,RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.ofFn_at bis hKI]
  exact TaoFivePrimes.rh_batch01_height_real_fft_zero
 have h:=TaoFivePrimes.rh_batch01_height_real_fft_semantic ⟨1,by decide⟩ v ar ai br bi
  (fun i=>(hri i).2.1) (fun i=>(hri i).2.2)
  (fun i=>RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.bounded_at brs (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.1 i.val)
  (fun i=>RHBatch01RealPolynomialZero.RHBatch01FFTListInterface.bounded_at bis (2^82) TaoFivePrimes.rh_high_height_fft_kernel_interface.2.2.1 i.val)
  hz (fun positive m hm=>(TaoFivePrimes.rh_batch01_height_real_reference_zero.2 m hm positive).1)
  (fun i=>(hri i).1) hker ⟨j,hj⟩
 rw[hout] at h
 have hv:RHBatch01ContourOutputRealZero.rows.flatten.length=2048:=by decide +kernel
 rw[RHBatch01RealPolynomialZero.RHBatch01FFTOutputSample.at_index _ j (by rw[hv];exact hj)] at h
 norm_num only [Fin.val_mk,Nat.cast_ofNat] at h ⊢
 exact h
#print axioms solution
