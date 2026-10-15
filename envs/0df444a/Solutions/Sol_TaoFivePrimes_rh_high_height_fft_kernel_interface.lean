-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_fft_kernel_interface
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T07:02:44.619598+00:00
-- url     : https://prove2.me/submissions/d79033ba-2402-4d56-a898-6ba7e2f359ec

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_chirp_arithmetic
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
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighFFTKernelInterface
lemma shapes :
    (∀rows∈[RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows],
      rows.flatten.length=32767 ∧ rows.length=64 ∧
      rows.all (fun row=> decide (row.length≤512))=true ∧
      rows.dropLast.all (fun row=> decide (row.length=512))=true) := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl|rfl <;> decide +kernel
lemma bounded : RHHighFFTChirpR.rows.flatten.all (fun x=> decide (x≤2^82))=true ∧
    RHHighFFTChirpI.rows.flatten.all (fun x=> decide (x≤2^82))=true := by decide +kernel
lemma flat_lookup (rows : List (List Nat))
    (hr:rows∈[RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows])
    (i : Nat) (hi:i<32767) :
    ((rows.flatten[i]?).getD 0)=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  have h:=shapes rows hr
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hm
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h.2.2.1) row hm)
  · intro row hm
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h.2.2.2) row hm)
  · rwa [h.1]
lemma kernel (i : Nat) (hi:i<32767) :
    ((((RHHighFFTChirpR.rows.flatten[i]?).getD 0:Nat):Int)-2^81,
      (((RHHighFFTChirpI.rows.flatten[i]?).getD 0:Nat):Int)-2^81)=
       RHHighFFTArithmeticBase.chirp ((i:Int)-16383).natAbs ∧
    ((RHHighFFTChirpS.rows.flatten[i]?).getD 0)=
      ((RHHighFFTChirpR.rows.flatten[i]?).getD 0)+((RHHighFFTChirpI.rows.flatten[i]?).getD 0) := by
  have hc:i/512<64:=by omega
  have hj:i%512< min 512 (32767-512*(i/512)):=by omega
  have h:=TaoFivePrimes.rh_high_height_fft_chirp_arithmetic (i/512) hc (i%512) hj
  have he:(512:Int)*(i/512:Nat)+(i%512:Nat)=(i:Int):=by
    exact_mod_cast (show 512*(i/512)+i%512=i by omega)
  dsimp only at h
  rw [he] at h
  rw [flat_lookup _ (by simp only [List.mem_cons,true_or]) i hi,
    flat_lookup _ (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false]) i hi,
    flat_lookup _ (by simp only [List.mem_cons,List.mem_nil_iff,or_true,true_or,or_false]) i hi]
  constructor
  · apply Prod.ext <;> dsimp only
    · linarith only [h.1]
    · linarith only [h.2.1]
  · exact h.2.2
end RHHighFFTKernelInterface
theorem solution :
 (∀rows∈[RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows],rows.flatten.length=32767) ∧
 RHHighFFTChirpR.rows.flatten.all (fun x=>decide (x≤2^82))=true ∧
 RHHighFFTChirpI.rows.flatten.all (fun x=>decide (x≤2^82))=true ∧
 (∀i:Nat,i<32767 →
    ((((RHHighFFTChirpR.rows.flatten[i]?).getD 0:Nat):Int)-2^81,
      (((RHHighFFTChirpI.rows.flatten[i]?).getD 0:Nat):Int)-2^81)=
       RHHighFFTArithmeticBase.chirp ((i:Int)-16383).natAbs ∧
    ((RHHighFFTChirpS.rows.flatten[i]?).getD 0)=
      ((RHHighFFTChirpR.rows.flatten[i]?).getD 0)+((RHHighFFTChirpI.rows.flatten[i]?).getD 0)) := by
  refine ⟨?_,RHHighFFTKernelInterface.bounded.1,RHHighFFTKernelInterface.bounded.2,RHHighFFTKernelInterface.kernel⟩
  intro rows hr
  exact (RHHighFFTKernelInterface.shapes rows hr).1
