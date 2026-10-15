-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_actual_bin_semantics
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T07:23:36.04166+00:00
-- url     : https://prove2.me/submissions/610b978c-340f-4f85-b0b9-8a9e24d52cd9

import Definitions.Def_TaoFivePrimes_RHHighAllDirichletWords
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_all_dirichlet_word_arithmetic
import Theorems.Thm_TaoFivePrimes_rh_high_height_global_binning_semantics
namespace RHHighCertifiedBinGroups
namespace RHHighAllDirichletWords
export _root_.RHHighAllDirichletWords (packets values values_length word)
end RHHighAllDirichletWords
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHHighDirichletArithmetic
export _root_.RHHighDirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHHighDirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHHighDirichletValues00
export _root_.RHHighDirichletValues00 (row00 row01 row02 rows)
end RHHighDirichletValues00
namespace RHHighDirichletValues01
export _root_.RHHighDirichletValues01 (row00 row01 row02 rows)
end RHHighDirichletValues01
namespace RHHighDirichletValues02
export _root_.RHHighDirichletValues02 (row00 row01 row02 rows)
end RHHighDirichletValues02
namespace RHHighDirichletValues03
export _root_.RHHighDirichletValues03 (row00 row01 row02 rows)
end RHHighDirichletValues03
namespace RHHighDirichletValues04
export _root_.RHHighDirichletValues04 (row00 row01 row02 rows)
end RHHighDirichletValues04
namespace RHHighDirichletValues05
export _root_.RHHighDirichletValues05 (row00 row01 row02 rows)
end RHHighDirichletValues05
namespace RHHighDirichletValues06
export _root_.RHHighDirichletValues06 (row00 row01 row02 rows)
end RHHighDirichletValues06
namespace RHHighDirichletValues07
export _root_.RHHighDirichletValues07 (row00 row01 row02 rows)
end RHHighDirichletValues07
namespace RHHighDirichletValues08
export _root_.RHHighDirichletValues08 (row00 row01 row02 rows)
end RHHighDirichletValues08
namespace RHHighDirichletValues09
export _root_.RHHighDirichletValues09 (row00 row01 row02 rows)
end RHHighDirichletValues09
namespace RHHighDirichletValues10
export _root_.RHHighDirichletValues10 (row00 row01 row02 rows)
end RHHighDirichletValues10
namespace RHHighDirichletValues11
export _root_.RHHighDirichletValues11 (row00 row01 row02 rows)
end RHHighDirichletValues11
namespace RHHighDirichletValues12
export _root_.RHHighDirichletValues12 (row00 row01 row02 rows)
end RHHighDirichletValues12
namespace RHHighDirichletValues13
export _root_.RHHighDirichletValues13 (row00 row01 row02 rows)
end RHHighDirichletValues13
namespace RHHighDirichletValues14
export _root_.RHHighDirichletValues14 (row00 row01 row02 rows)
end RHHighDirichletValues14
namespace RHHighDirichletValues15
export _root_.RHHighDirichletValues15 (row00 row01 row02 rows)
end RHHighDirichletValues15
namespace RHHighDirichletValues16
export _root_.RHHighDirichletValues16 (row00 row01 row02 rows)
end RHHighDirichletValues16
namespace RHHighDirichletValues17
export _root_.RHHighDirichletValues17 (row00 row01 row02 rows)
end RHHighDirichletValues17
namespace RHHighDirichletValues18
export _root_.RHHighDirichletValues18 (row00 row01 row02 rows)
end RHHighDirichletValues18
namespace RHHighDirichletValues19
export _root_.RHHighDirichletValues19 (row00 row01 row02 rows)
end RHHighDirichletValues19
namespace RHHighDirichletValues20
export _root_.RHHighDirichletValues20 (row00 row01 row02 rows)
end RHHighDirichletValues20
namespace RHHighDirichletValues21
export _root_.RHHighDirichletValues21 (row00 row01 row02 rows)
end RHHighDirichletValues21
namespace RHHighDirichletValues22
export _root_.RHHighDirichletValues22 (row00 row01 row02 rows)
end RHHighDirichletValues22
namespace RHHighDirichletValues23
export _root_.RHHighDirichletValues23 (row00 row01 row02 rows)
end RHHighDirichletValues23
namespace RHHighDirichletValues24
export _root_.RHHighDirichletValues24 (row00 row01 row02 rows)
end RHHighDirichletValues24
namespace RHHighDirichletValues25
export _root_.RHHighDirichletValues25 (row00 row01 row02 rows)
end RHHighDirichletValues25
namespace RHHighDirichletValues26
export _root_.RHHighDirichletValues26 (row00 row01 row02 rows)
end RHHighDirichletValues26
namespace RHHighDirichletValues27
export _root_.RHHighDirichletValues27 (row00 row01 row02 rows)
end RHHighDirichletValues27
namespace RHHighDirichletValues28
export _root_.RHHighDirichletValues28 (row00 row01 row02 rows)
end RHHighDirichletValues28
namespace RHHighDirichletValues29
export _root_.RHHighDirichletValues29 (row00 row01 row02 rows)
end RHHighDirichletValues29
namespace RHHighDirichletValues30
export _root_.RHHighDirichletValues30 (row00 row01 row02 rows)
end RHHighDirichletValues30
namespace RHHighDirichletValues31
export _root_.RHHighDirichletValues31 (row00 row01 row02 rows)
end RHHighDirichletValues31
namespace RHHighDirichletValues32
export _root_.RHHighDirichletValues32 (row00 row01 rows)
end RHHighDirichletValues32
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
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHHighDirichletTermsPure
open RHHighLogData RHHighDirichletArithmetic RHHighDirichletBinning
lemma power_succ (n k : Nat) : power n (k+1)=power n k*delta n/(D:Int) := by
  unfold power
  rw [List.range_succ,List.foldl_append]
  rfl
lemma power_iterates (n k : Nat) : power n k=(fun v:Int=>v*delta n/(2:Int)^128)^[k] (2^128) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [power_succ,ih,Function.iterate_succ_apply'];rfl
lemma termsAux_iterates (K : Nat) (d wr wi p : Int) :
    termsAux K d wr wi p=(List.range K).map (fun k=>
      (wr*((fun v:Int=>v*d/(2:Int)^128)^[k] p)/(2:Int)^128,
       wi*((fun v:Int=>v*d/(2:Int)^128)^[k] p)/(2:Int)^128)) := by
  induction K generalizing p with
  | zero => rfl
  | succ K ih =>
    rw [termsAux,List.range_succ_eq_map,List.map_cons,List.map_map,ih]
    congr 1
lemma terms_eq (w n : Nat) (hr:field w 0=(compute n).gammaRe)
    (hi:field w 1=(compute n).gammaIm) (hd:field w 2=delta n) :
    terms w=(List.range 24).map (fun k=>coefficient n k) := by
  rw [terms,termsAux_iterates,hr,hi,hd]
  apply List.map_congr_left
  intro k hk
  rw [←power_iterates]
  rfl
lemma coefficientAt_eq (w n k : Nat) (hk:k<24) (hr:field w 0=(compute n).gammaRe)
    (hi:field w 1=(compute n).gammaIm) (hd:field w 2=delta n) :
    RHHighBinningSemantic.coefficientAt (terms w) k=
      ((coefficient n k).1:ℂ)+((coefficient n k).2:ℂ)*I := by
  rw [terms_eq w n hr hi hd]
  unfold RHHighBinningSemantic.coefficientAt
  rw [List.getElem?_eq_getElem (by simp only [List.length_map,List.length_range];exact hk)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range,RHHighBinningSemantic.pairValue]
end RHHighDirichletTermsPure
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
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
namespace RHHighAllDirichletWords
noncomputable def rows : List (List Nat) := packets.flatten
theorem rows_length : rows.length=98 := by decide +kernel
theorem row_lengths_checked :
    rows.all (fun r=>decide (r.length≤512))=true ∧
    rows.dropLast.all (fun r=>decide (r.length=512))=true := by decide +kernel
theorem packet_lengths_checked :
    packets.all (fun r=>decide (r.length≤3))=true ∧
    packets.dropLast.all (fun r=>decide (r.length=3))=true := by decide +kernel
lemma word_flat (n : Nat) (hn:1 ≤ n ∧ n≤50000) :
    (values[n-1]?).getD 0=word n := by
  let i:=n-1
  have hi:i<50000:=by dsimp [i];omega
  have hr:∀ r∈rows,r.length≤512:=by
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp row_lengths_checked.1) r hr)
  have hf:∀ r∈rows.dropLast,r.length=512:=by
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp row_lengths_checked.2) r hr)
  have h:=RHHighFlatRows.lookup 512 (by decide) 0 rows hr hf i
    (by change i<values.length;rw [values_length];exact hi)
  have hp:∀ r∈packets,r.length≤3:=by
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp packet_lengths_checked.1) r hr)
  have hpf:∀ r∈packets.dropLast,r.length=3:=by
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp packet_lengths_checked.2) r hr)
  have hrows:=RHHighFlatRows.lookup 3 (by decide) ([]:List Nat) packets hp hpf (i/512)
    (by change i/512<rows.length;rw [rows_length];omega)
  have hd:(i/512)/3=i/1536:=by rw [Nat.div_div_eq_div_mul]
  have hm:(i/512)%3=(i%1536)/512:=by omega
  rw [hd,hm] at hrows
  change (values[i]?).getD 0=word n
  change (values[i]?).getD 0=_ at h
  rw [h,rows,hrows] <;> rfl
end RHHighAllDirichletWords
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex Finset
namespace RHHighActualBinSemantics
open RHHighAllDirichletWords
lemma values_eq : values=List.ofFn (fun n:Fin 50000=>word (n.val+1)) := by
  apply List.ext_getElem
  · rw [values_length,List.length_ofFn]
  · intro i hi hi'
    have hi0:i<50000:=by rwa [values_length] at hi
    have hw:((values[i]?).getD 0)=word (i+1):=by
      simpa only [Nat.add_sub_cancel] using word_flat (i+1) ⟨by omega,by omega⟩
    rw [List.getElem?_eq_getElem hi,Option.getD_some] at hw
    simpa only [List.getElem_ofFn] using hw
noncomputable def proposed (n k : Nat) : ℂ :=
  let c:=RHHighDirichletArithmetic.coefficient n k
  ((c.1:ℂ)+(c.2:ℂ)*I)/(2:ℂ)^128
lemma grouped (m k : Nat) (hm:m<929) (hk:k<24) :
    RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient m k)/(2:ℂ)^128=
      ∑n:Fin 50000,if RHHighDirichletArithmetic.bin (n.val+1)=m then proposed (n.val+1) k else 0 := by
  have h:=TaoFivePrimes.rh_high_height_global_binning_semantics m hm k hk
  rw [values_eq] at h
  simp only [List.map_ofFn,List.sum_ofFn] at h
  rw [h,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hw:=TaoFivePrimes.rh_high_height_all_dirichlet_word_arithmetic (n.val+1) ⟨by omega,by omega⟩
  dsimp only at hw
  simp only [Function.comp_apply]
  rw [←hw.2.2.2,RHHighDirichletTermsPure.coefficientAt_eq _ _ k hk hw.1.symm hw.2.1.symm hw.2.2.1.symm]
  split_ifs <;> simp only [proposed,zero_div]
end RHHighActualBinSemantics
end
end RHHighCertifiedBinGroups
theorem solution :
 ∀m:Nat,m<929 → ∀k:Nat,k<24 →
 RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient m k)/(2:ℂ)^128=
  ∑n:Fin 50000,if RHHighDirichletArithmetic.bin (n.val+1)=m then
   (let c:=RHHighDirichletArithmetic.coefficient (n.val+1) k
    ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0 := by
 intro m hm k hk
 exact RHHighCertifiedBinGroups.RHHighActualBinSemantics.grouped m k hm hk
