-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:28:04.822832+00:00
-- url     : https://prove2.me/submissions/b07dd4e4-2344-42db-9361-9439ddaa3014

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00_slice00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00_slice01
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00_slice02
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00_slice30
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00_slice31
namespace RHHighSparseAggregateRHHighContourActualInputUpperZeroK00
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
    List.ofFn (fun j:Fin N=> entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=> decide (x≤ M))=true) (j : Nat) : entry xs j≤ M := by
  by_cases hj:j< xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=> decide (row.length=512) && row.all (fun x=> decide (x≤ M)))=true) :
    rows.flatten.all (fun x=> decide (x≤ M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=> decide (row.length=512))=true)
    (hi:i< rows.flatten.length) :
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
    (h:rows.all (fun row=> decide (row.length=512) && row.all (fun x=> decide (x≤ M)))=true) :
    rows.all (fun row=> decide (row.length=512))=true := by
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
set_option maxRecDepth 100000
namespace RHHighSparseInput
open RHHighFFTListInterface
lemma middle_at (xs : List Nat) (i : Nat) (hlen:xs.length=16384) (hi:1025 ≤ i ∧ i<15360)
 (h:((xs.drop 1025).take 14335).all (fun x=> decide (x=2^166))=true) : entry xs i=2^166 := by
 let j:=i-1025
 have hj:j<14335:=by dsimp[j];omega
 have hl:((xs.drop 1025).take 14335).length=14335:=by simp only[List.length_take,List.length_drop,hlen];decide
 have hh:=(List.all_eq_true.mp h) (((xs.drop 1025).take 14335)[j]) (List.getElem_mem (by rw[hl];exact hj))
 have heq:(((xs.drop 1025).take 14335)[j]?).getD 0=(((xs.drop 1025).take 14335)[j]):=by rw[List.getElem?_eq_getElem (by rw[hl];exact hj),Option.getD_some]
 rw[←heq] at hh
 have he:1025+j=i:=by dsimp[j];omega
 simpa only[List.getElem?_take,List.getElem?_drop,hj,if_true,he,decide_eq_true_eq,entry] using hh
lemma raw_zero (v : List Nat) (chirp : Nat→Int×Int) (i : Nat) (hi:1025 ≤ i ∧ i<15360) :
 RHHighContourVector.raw v chirp i=(0,0) := by
 have hv:RHHighContourVector.vector v i=(0,0):=by
  simp only[RHHighContourVector.vector,if_neg (show i≠0 by omega),
   if_neg (show ¬i≤1024 by omega),if_neg (show ¬15360≤ i by omega)]
 simp only[RHHighContourVector.raw,hv,Prod.fst,Prod.snd,zero_mul,zero_add,zero_sub,neg_zero]
end RHHighSparseInput
end
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHHighFFTListInterface RHHighSparseInput
theorem real_shapes : RHHighContourInputRUpperZeroK00.rows.flatten.length=16384 ∧ RHHighContourInputRUpperZeroK00.rows.all (fun row=> decide (row.length=512))=true := by decide +kernel
theorem imag_shapes : RHHighContourInputIUpperZeroK00.rows.flatten.length=16384 ∧ RHHighContourInputIUpperZeroK00.rows.all (fun row=> decide (row.length=512))=true := by decide +kernel
theorem real_middle : ((RHHighContourInputRUpperZeroK00.rows.flatten.drop 1025).take 14335).all (fun x=> decide (x=2^166))=true := by decide +kernel
theorem imag_middle : ((RHHighContourInputIUpperZeroK00.rows.flatten.drop 1025).take 14335).all (fun x=> decide (x=2^166))=true := by decide +kernel
end RHHighSparseAggregateRHHighContourActualInputUpperZeroK00
open RHHighSparseAggregateRHHighContourActualInputUpperZeroK00
theorem solution :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighContourSpectrumUpperZeroK00.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputRUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputIUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputRUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by
 intro i hi
 by_cases hmid:1025 ≤ i ∧ i<15360
 · have hR:=RHHighSparseInput.middle_at RHHighContourInputRUpperZeroK00.rows.flatten i real_shapes.1 hmid real_middle
   have hI:=RHHighSparseInput.middle_at RHHighContourInputIUpperZeroK00.rows.flatten i imag_shapes.1 hmid imag_middle
   rw[RHHighFFTListInterface.uniform_lookup RHHighContourInputRUpperZeroK00.rows i real_shapes.2 (by rw[real_shapes.1];exact hi)] at hR
   rw[RHHighFFTListInterface.uniform_lookup RHHighContourInputIUpperZeroK00.rows i imag_shapes.2 (by rw[imag_shapes.1];exact hi)] at hI
   rw[RHHighSparseInput.raw_zero _ _ i hmid,hR,hI]
   norm_num
 · have hb:i/512=0 ∨ i/512=1 ∨ i/512=2 ∨ i/512=30 ∨ i/512=31 := by omega
   have he:512*(i/512)+i%512=i:=by omega
   rcases hb with hb|hb|hb|hb|hb
   · have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice00 (i%512) (by omega : i%512<512)
     have he':0+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice01 (i%512) (by omega : i%512<512)
     have he':512+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice02 (i%512) (by omega : i%512<1)
     have he':1024+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice30 (i%512) (by omega : i%512<512)
     have he':15360+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice31 (i%512) (by omega : i%512<512)
     have he':15872+i%512=i:=by omega
     simpa only [hb,he'] using h
