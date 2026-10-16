-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_actual_bin_semantics
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:20:46.741699+00:00
-- url     : https://prove2.me/submissions/6e27873e-c38c-41d8-aff5-7a81070118b3

import Definitions.Def_TaoFivePrimes_RHBatch01AllDirichletWords
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_dirichlet_word_arithmetic
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_global_binning_semantics
namespace RHBatch01CertifiedBinGroups
namespace RHBatch01AllDirichletWords
export _root_.RHBatch01AllDirichletWords (packets values values_length word)
end RHBatch01AllDirichletWords
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHBatch01DirichletArithmetic
export _root_.RHBatch01DirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHBatch01DirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHBatch01DirichletValues00
export _root_.RHBatch01DirichletValues00 (row00 row01 row02 rows)
end RHBatch01DirichletValues00
namespace RHBatch01DirichletValues01
export _root_.RHBatch01DirichletValues01 (row00 row01 row02 rows)
end RHBatch01DirichletValues01
namespace RHBatch01DirichletValues02
export _root_.RHBatch01DirichletValues02 (row00 row01 row02 rows)
end RHBatch01DirichletValues02
namespace RHBatch01DirichletValues03
export _root_.RHBatch01DirichletValues03 (row00 row01 row02 rows)
end RHBatch01DirichletValues03
namespace RHBatch01DirichletValues04
export _root_.RHBatch01DirichletValues04 (row00 row01 row02 rows)
end RHBatch01DirichletValues04
namespace RHBatch01DirichletValues05
export _root_.RHBatch01DirichletValues05 (row00 row01 row02 rows)
end RHBatch01DirichletValues05
namespace RHBatch01DirichletValues06
export _root_.RHBatch01DirichletValues06 (row00 row01 row02 rows)
end RHBatch01DirichletValues06
namespace RHBatch01DirichletValues07
export _root_.RHBatch01DirichletValues07 (row00 row01 row02 rows)
end RHBatch01DirichletValues07
namespace RHBatch01DirichletValues08
export _root_.RHBatch01DirichletValues08 (row00 row01 row02 rows)
end RHBatch01DirichletValues08
namespace RHBatch01DirichletValues09
export _root_.RHBatch01DirichletValues09 (row00 row01 row02 rows)
end RHBatch01DirichletValues09
namespace RHBatch01DirichletValues10
export _root_.RHBatch01DirichletValues10 (row00 row01 row02 rows)
end RHBatch01DirichletValues10
namespace RHBatch01DirichletValues11
export _root_.RHBatch01DirichletValues11 (row00 row01 row02 rows)
end RHBatch01DirichletValues11
namespace RHBatch01DirichletValues12
export _root_.RHBatch01DirichletValues12 (row00 row01 row02 rows)
end RHBatch01DirichletValues12
namespace RHBatch01DirichletValues13
export _root_.RHBatch01DirichletValues13 (row00 row01 row02 rows)
end RHBatch01DirichletValues13
namespace RHBatch01DirichletValues14
export _root_.RHBatch01DirichletValues14 (row00 row01 row02 rows)
end RHBatch01DirichletValues14
namespace RHBatch01DirichletValues15
export _root_.RHBatch01DirichletValues15 (row00 row01 row02 rows)
end RHBatch01DirichletValues15
namespace RHBatch01DirichletValues16
export _root_.RHBatch01DirichletValues16 (row00 row01 row02 rows)
end RHBatch01DirichletValues16
namespace RHBatch01DirichletValues17
export _root_.RHBatch01DirichletValues17 (row00 row01 row02 rows)
end RHBatch01DirichletValues17
namespace RHBatch01DirichletValues18
export _root_.RHBatch01DirichletValues18 (row00 row01 row02 rows)
end RHBatch01DirichletValues18
namespace RHBatch01DirichletValues19
export _root_.RHBatch01DirichletValues19 (row00 row01 row02 rows)
end RHBatch01DirichletValues19
namespace RHBatch01DirichletValues20
export _root_.RHBatch01DirichletValues20 (row00 row01 row02 rows)
end RHBatch01DirichletValues20
namespace RHBatch01DirichletValues21
export _root_.RHBatch01DirichletValues21 (row00 row01 row02 rows)
end RHBatch01DirichletValues21
namespace RHBatch01DirichletValues22
export _root_.RHBatch01DirichletValues22 (row00 row01 row02 rows)
end RHBatch01DirichletValues22
namespace RHBatch01DirichletValues23
export _root_.RHBatch01DirichletValues23 (row00 row01 row02 rows)
end RHBatch01DirichletValues23
namespace RHBatch01DirichletValues24
export _root_.RHBatch01DirichletValues24 (row00 row01 row02 rows)
end RHBatch01DirichletValues24
namespace RHBatch01DirichletValues25
export _root_.RHBatch01DirichletValues25 (row00 row01 row02 rows)
end RHBatch01DirichletValues25
namespace RHBatch01DirichletValues26
export _root_.RHBatch01DirichletValues26 (row00 row01 row02 rows)
end RHBatch01DirichletValues26
namespace RHBatch01DirichletValues27
export _root_.RHBatch01DirichletValues27 (row00 row01 row02 rows)
end RHBatch01DirichletValues27
namespace RHBatch01DirichletValues28
export _root_.RHBatch01DirichletValues28 (row00 row01 row02 rows)
end RHBatch01DirichletValues28
namespace RHBatch01DirichletValues29
export _root_.RHBatch01DirichletValues29 (row00 row01 row02 rows)
end RHBatch01DirichletValues29
namespace RHBatch01DirichletValues30
export _root_.RHBatch01DirichletValues30 (row00 row01 row02 rows)
end RHBatch01DirichletValues30
namespace RHBatch01DirichletValues31
export _root_.RHBatch01DirichletValues31 (row00 row01 row02 rows)
end RHBatch01DirichletValues31
namespace RHBatch01DirichletValues32
export _root_.RHBatch01DirichletValues32 (row00 row01 rows)
end RHBatch01DirichletValues32
namespace RHBatch01GammaArithmetic
export _root_.RHBatch01GammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHBatch01GammaArithmetic
namespace RHBatch01GammaGuards
export _root_.RHBatch01GammaGuards (guard)
end RHBatch01GammaGuards
namespace RHBatch01GenericExpHorner
export _root_.RHBatch01GenericExpHorner (cn cp horner sn sp)
end RHBatch01GenericExpHorner
namespace RHBatch01HomogeneousHorner
export _root_.RHBatch01HomogeneousHorner (hom)
end RHBatch01HomogeneousHorner
namespace RHBatch01LogData
export _root_.RHBatch01LogData (D F coefficients denominator log2 log2pi numerator rounded)
end RHBatch01LogData
namespace RHBatch01NegativeExp
export _root_.RHBatch01NegativeExp (denominator en ep numerator seed)
end RHBatch01NegativeExp
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHBatch01DirichletTermsPure
open RHBatch01LogData RHBatch01DirichletArithmetic RHHighDirichletBinning
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
end RHBatch01DirichletTermsPure
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
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
namespace RHBatch01AllDirichletWords
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
  have h:=RHBatch01FlatRows.lookup 512 (by decide) 0 rows hr hf i
    (by change i<values.length;rw [values_length];exact hi)
  have hp:∀ r∈packets,r.length≤3:=by
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp packet_lengths_checked.1) r hr)
  have hpf:∀ r∈packets.dropLast,r.length=3:=by
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp packet_lengths_checked.2) r hr)
  have hrows:=RHBatch01FlatRows.lookup 3 (by decide) ([]:List Nat) packets hp hpf (i/512)
    (by change i/512<rows.length;rw [rows_length];omega)
  have hd:(i/512)/3=i/1536:=by rw [Nat.div_div_eq_div_mul]
  have hm:(i/512)%3=(i%1536)/512:=by omega
  rw [hd,hm] at hrows
  change (values[i]?).getD 0=word n
  change (values[i]?).getD 0=_ at h
  rw [h,rows,hrows] <;> rfl
end RHBatch01AllDirichletWords
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex Finset
namespace RHBatch01ActualBinSemantics
open RHBatch01AllDirichletWords
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
  let c:=RHBatch01DirichletArithmetic.coefficient n k
  ((c.1:ℂ)+(c.2:ℂ)*I)/(2:ℂ)^128
lemma grouped (m k : Nat) (hm:m<929) (hk:k<24) :
    RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m k)/(2:ℂ)^128=
      ∑n:Fin 50000,if RHBatch01DirichletArithmetic.bin (n.val+1)=m then proposed (n.val+1) k else 0 := by
  have h:=TaoFivePrimes.rh_batch01_height_global_binning_semantics m hm k hk
  rw [values_eq] at h
  simp only [List.map_ofFn,List.sum_ofFn] at h
  rw [h,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hw:=TaoFivePrimes.rh_batch01_height_all_dirichlet_word_arithmetic (n.val+1) ⟨by omega,by omega⟩
  dsimp only at hw
  simp only [Function.comp_apply]
  rw [←hw.2.2.2,RHBatch01DirichletTermsPure.coefficientAt_eq _ _ k hk hw.1.symm hw.2.1.symm hw.2.2.1.symm]
  split_ifs <;> simp only [proposed,zero_div]
end RHBatch01ActualBinSemantics
end
end RHBatch01CertifiedBinGroups
theorem solution :
 ∀m:Nat,m<929 → ∀k:Nat,k<24 →
 RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m k)/(2:ℂ)^128=
  ∑n:Fin 50000,if RHBatch01DirichletArithmetic.bin (n.val+1)=m then
   (let c:=RHBatch01DirichletArithmetic.coefficient (n.val+1) k
    ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0 := by
 intro m hm k hk
 exact RHBatch01CertifiedBinGroups.RHBatch01ActualBinSemantics.grouped m k hm hk
#print axioms solution
