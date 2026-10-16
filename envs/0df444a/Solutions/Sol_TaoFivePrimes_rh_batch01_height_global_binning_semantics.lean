-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_global_binning_semantics
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:14:42.999707+00:00
-- url     : https://prove2.me/submissions/2055582a-256f-44bb-a7f2-49519436918c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins
import Definitions.Def_TaoFivePrimes_RHBatch01AllDirichletWords
import Definitions.Def_TaoFivePrimes_RHHighBinningMerge
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_global_binning
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning00
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning01
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning02
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning03
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning04
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning05
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning06
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning07
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning08
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning09
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning10
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning11
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning12
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning13
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning14
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning15
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning16
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning17
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning18
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning19
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning20
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning21
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning22
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning23
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning24
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning25
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning26
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning27
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning28
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning29
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning30
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning31
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning32
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighBinningSemantic
open RHHighDirichletBinning
lemma field_shift (w k : Nat) : field (w/2^320) k=field w (k+2) := by
  unfold field
  rw [Nat.div_div_eq_div_mul]
  have he:(2:Nat)^320*2^(160*k)=2^(160*(k+2)) := by
    rw [←pow_add]
    congr 1
    omega
  rw [he]
lemma decodeCoefficients_length (K w : Nat) : (decodeCoefficients K w).length=K := by
  induction K generalizing w with
  | zero => rfl
  | succ K ih => simp only [decodeCoefficients,List.length_cons,ih]
lemma decoded_at (K w k : Nat) (hk:k<K) :
    ((decodeCoefficients K w)[k]?).getD (0,0)=(field w (2*k),field w (2*k+1)) := by
  induction K generalizing w k with
  | zero => omega
  | succ K ih =>
    cases k with
    | zero => simp only [decodeCoefficients,List.getElem?_cons_zero,Option.getD_some,Nat.mul_zero,Nat.zero_add]
    | succ k =>
      simp only [decodeCoefficients,List.getElem?_cons_succ]
      rw [ih (w/2^320) k (by omega),field_shift,field_shift]
      congr 1 <;> congr 1 <;> omega
lemma coefficientAt_decode (K w k : Nat) (hk:k<K) :
    coefficientAt (decodeCoefficients K w) k=pairValue (field w (2*k),field w (2*k+1)) := by
  rw [coefficientAt,decoded_at K w k hk]
end RHHighBinningSemantic
namespace RHHighBinningSemantic
open RHBatch01GlobalDirichletBins
open RHHighDirichletBinning RHHighGlobalBinTree
theorem zero_fields_checked : (List.range 48).all (fun j=>decide (field zeroWord j=0))=true := by decide +kernel
lemma zero_fields (j : Nat) (hj:j<48) : field zeroWord j=0 :=
  of_decide_eq_true ((List.all_eq_true.mp zero_fields_checked) j (List.mem_range.mpr hj))
lemma filtered_value (xs : List Nat) (m k : Nat) (hk:k<24) :
    sparseValue m k (xs.filterMap (fun j=>if word j=zeroWord then none
      else some (j,decodeCoefficients 24 (word j))))=
    ((xs.map (fun j=>if j=m then pairValue (coefficient j k) else 0)).sum) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    by_cases hz:word j=zeroWord
    · simp only [List.filterMap_cons,if_pos hz,List.map_cons,List.sum_cons,ih]
      have he:pairValue (coefficient j k)=0 := by
        rw [coefficient,hz,zero_fields (2*k) (by omega),zero_fields (2*k+1) (by omega)]
        simp [pairValue]
      simp only [he,ite_self,zero_add]
    · simp only [List.filterMap_cons,if_neg hz,sparseValue_cons,List.map_cons,List.sum_cons,ih]
      rw [coefficientAt_decode 24 (word j) k hk]
      rfl
lemma group_value (m k : Nat) (hm:m<929) (hk:k<24) :
    sparseValue m k groups=pairValue (coefficient m k) := by
  rw [groups,filtered_value _ m k hk]
  have he:((List.range 929).map (fun j=>if j=m then pairValue (coefficient j k) else 0))=
      List.ofFn (fun j:Fin 929=>if j.val=m then pairValue (coefficient j.val k) else 0) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro j hj hj';simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [he,List.sum_ofFn]
  have heq (j:Fin 929):j.val=m↔j=⟨m,hm⟩:=by simp only [Fin.ext_iff]
  simp only [heq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
end RHHighBinningSemantic
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
namespace RHHighBinningSemantic
open RHHighBinningMerge
open RHHighDirichletBinning
lemma auxiliary_value (m k j : Nat) (a : List (Int×Int)) (gs : List (Nat×List (Int×Int)))
    (hk:k<24) (ha:a.length=24) (hg:∀ g∈gs,g.2.length=24) :
    sparseValue m k (auxiliary j a gs)=(if j=m then coefficientAt a k else 0)+sparseValue m k gs := by
  induction gs generalizing j a with
  | nil => simp [auxiliary,sparseValue]
  | cons g gs ih =>
    rcases g with ⟨q,b⟩
    have hb:b.length=24:=hg (q,b) (by simp)
    have hgs:∀ g∈gs,g.2.length=24:=by intro g h;exact hg g (by simp [h])
    by_cases hq:q=j
    · rw [auxiliary,if_pos hq,ih j (add a b) (by rw [add_length,ha,hb];rfl) hgs,
        coefficientAt_add a b k (by omega) (by omega),sparseValue_cons]
      rw [hq]
      by_cases hj:j=m <;> simp only [hj,if_true,if_false] <;> ring
    · rw [auxiliary,if_neg hq,sparseValue_cons,ih q b hb hgs,sparseValue_cons]
lemma merge_value (m k : Nat) (gs : List (Nat×List (Int×Int))) (hk:k<24)
    (hg:∀ g∈gs,g.2.length=24) : sparseValue m k (merge gs)=sparseValue m k gs := by
  cases gs with
  | nil => rfl
  | cons g gs =>
    rcases g with ⟨j,a⟩
    exact auxiliary_value m k j a gs hk (hg (j,a) (by simp)) (by intro g h;exact hg g (by simp [h]))
end RHHighBinningSemantic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace RHHighBinningSemantic
open RHHighDirichletBinning
lemma flatten_twice {α : Type} (xss : List (List (List α))) :
    xss.flatten.flatten=(xss.map List.flatten).flatten := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp only [List.flatten_cons,List.flatten_append,List.map_cons,ih]
lemma sparse_append (m k : Nat) (xs ys : List (Nat×List (Int×Int))) :
    sparseValue m k (xs++ys)=sparseValue m k xs+sparseValue m k ys := by
  simp only [sparseValue,List.map_append,List.sum_append]
lemma sparse_flatten (m k : Nat) (gs : List (List (Nat×List (Int×Int)))) :
    sparseValue m k gs.flatten=(gs.map (sparseValue m k)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.flatten_cons,sparse_append,List.map_cons,List.sum_cons,ih]
lemma binned_packets_value (m k : Nat) (hk:k<24) (ws : List (List Nat)) :
    sparseValue m k (ws.map bins).flatten=
      ((ws.flatten.map (fun w=>if bin w=m then coefficientAt (terms w) k else 0)).sum) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.flatten_cons,sparse_append,bins_value _ _ _ hk,ih,
      List.map_append,List.sum_append]
lemma decoded_group_length (w : Nat) : (decode w).2.length=24 :=
  decodeCoefficients_length 24 (w/2^16)
lemma decoded_groups_valid (xs : List Nat) : ∀ g∈xs.map decode,g.2.length=24 := by
  intro g hg
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hg
  exact decoded_group_length w
end RHHighBinningSemantic
namespace RHBatch01GlobalBinningSound
open RHHighBinningSemantic
noncomputable def parts := [RHBatch01DirichletBins00.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins01.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins02.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins03.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins04.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins05.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins06.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins07.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins08.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins09.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins10.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins11.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins12.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins13.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins14.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins15.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins16.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins17.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins18.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins19.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins20.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins21.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins22.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins23.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins24.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins25.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins26.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins27.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins28.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins29.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins30.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins31.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins32.values.map RHHighDirichletBinning.decode]
noncomputable def wordPackets := [RHBatch01DirichletValues00.rows.flatten,RHBatch01DirichletValues01.rows.flatten,RHBatch01DirichletValues02.rows.flatten,RHBatch01DirichletValues03.rows.flatten,RHBatch01DirichletValues04.rows.flatten,RHBatch01DirichletValues05.rows.flatten,RHBatch01DirichletValues06.rows.flatten,RHBatch01DirichletValues07.rows.flatten,RHBatch01DirichletValues08.rows.flatten,RHBatch01DirichletValues09.rows.flatten,RHBatch01DirichletValues10.rows.flatten,RHBatch01DirichletValues11.rows.flatten,RHBatch01DirichletValues12.rows.flatten,RHBatch01DirichletValues13.rows.flatten,RHBatch01DirichletValues14.rows.flatten,RHBatch01DirichletValues15.rows.flatten,RHBatch01DirichletValues16.rows.flatten,RHBatch01DirichletValues17.rows.flatten,RHBatch01DirichletValues18.rows.flatten,RHBatch01DirichletValues19.rows.flatten,RHBatch01DirichletValues20.rows.flatten,RHBatch01DirichletValues21.rows.flatten,RHBatch01DirichletValues22.rows.flatten,RHBatch01DirichletValues23.rows.flatten,RHBatch01DirichletValues24.rows.flatten,RHBatch01DirichletValues25.rows.flatten,RHBatch01DirichletValues26.rows.flatten,RHBatch01DirichletValues27.rows.flatten,RHBatch01DirichletValues28.rows.flatten,RHBatch01DirichletValues29.rows.flatten,RHBatch01DirichletValues30.rows.flatten,RHBatch01DirichletValues31.rows.flatten,RHBatch01DirichletValues32.rows.flatten]
lemma aggregate_eq : RHHighBinningMerge.merge parts.flatten=RHBatch01GlobalDirichletBins.groups := by
  exact TaoFivePrimes.rh_batch01_height_global_binning
lemma word_packets_eq : RHBatch01AllDirichletWords.values=wordPackets.flatten := by
  unfold RHBatch01AllDirichletWords.values
  rw [flatten_twice]
  rfl
lemma parts_eq : parts=wordPackets.map RHHighDirichletBinning.bins := by
  change [RHBatch01DirichletBins00.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins01.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins02.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins03.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins04.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins05.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins06.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins07.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins08.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins09.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins10.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins11.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins12.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins13.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins14.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins15.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins16.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins17.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins18.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins19.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins20.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins21.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins22.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins23.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins24.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins25.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins26.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins27.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins28.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins29.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins30.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins31.values.map RHHighDirichletBinning.decode,RHBatch01DirichletBins32.values.map RHHighDirichletBinning.decode]=[RHHighDirichletBinning.bins (RHBatch01DirichletValues00.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues01.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues02.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues03.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues04.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues05.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues06.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues07.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues08.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues09.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues10.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues11.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues12.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues13.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues14.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues15.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues16.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues17.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues18.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues19.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues20.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues21.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues22.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues23.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues24.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues25.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues26.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues27.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues28.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues29.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues30.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues31.rows.flatten),RHHighDirichletBinning.bins (RHBatch01DirichletValues32.rows.flatten)]
  simp only [TaoFivePrimes.rh_batch01_height_dirichlet_binning00,TaoFivePrimes.rh_batch01_height_dirichlet_binning01,TaoFivePrimes.rh_batch01_height_dirichlet_binning02,TaoFivePrimes.rh_batch01_height_dirichlet_binning03,TaoFivePrimes.rh_batch01_height_dirichlet_binning04,TaoFivePrimes.rh_batch01_height_dirichlet_binning05,TaoFivePrimes.rh_batch01_height_dirichlet_binning06,TaoFivePrimes.rh_batch01_height_dirichlet_binning07,TaoFivePrimes.rh_batch01_height_dirichlet_binning08,TaoFivePrimes.rh_batch01_height_dirichlet_binning09,TaoFivePrimes.rh_batch01_height_dirichlet_binning10,TaoFivePrimes.rh_batch01_height_dirichlet_binning11,TaoFivePrimes.rh_batch01_height_dirichlet_binning12,TaoFivePrimes.rh_batch01_height_dirichlet_binning13,TaoFivePrimes.rh_batch01_height_dirichlet_binning14,TaoFivePrimes.rh_batch01_height_dirichlet_binning15,TaoFivePrimes.rh_batch01_height_dirichlet_binning16,TaoFivePrimes.rh_batch01_height_dirichlet_binning17,TaoFivePrimes.rh_batch01_height_dirichlet_binning18,TaoFivePrimes.rh_batch01_height_dirichlet_binning19,TaoFivePrimes.rh_batch01_height_dirichlet_binning20,TaoFivePrimes.rh_batch01_height_dirichlet_binning21,TaoFivePrimes.rh_batch01_height_dirichlet_binning22,TaoFivePrimes.rh_batch01_height_dirichlet_binning23,TaoFivePrimes.rh_batch01_height_dirichlet_binning24,TaoFivePrimes.rh_batch01_height_dirichlet_binning25,TaoFivePrimes.rh_batch01_height_dirichlet_binning26,TaoFivePrimes.rh_batch01_height_dirichlet_binning27,TaoFivePrimes.rh_batch01_height_dirichlet_binning28,TaoFivePrimes.rh_batch01_height_dirichlet_binning29,TaoFivePrimes.rh_batch01_height_dirichlet_binning30,TaoFivePrimes.rh_batch01_height_dirichlet_binning31,TaoFivePrimes.rh_batch01_height_dirichlet_binning32]
lemma parts_valid : ∀ g∈parts.flatten,g.2.length=24 := by
  intro g hg
  obtain ⟨gs,hgs,hg⟩:=List.mem_flatten.mp hg
  simp only [parts,List.mem_cons,List.mem_nil_iff,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact decoded_groups_valid _ g hg
end RHBatch01GlobalBinningSound
theorem solution :
  ∀ m:Nat,m<929 → ∀ k:Nat,k<24 →
  RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m k)=
    ((RHBatch01AllDirichletWords.values.map (fun w=>if RHHighDirichletBinning.bin w=m then
      RHHighBinningSemantic.coefficientAt (RHHighDirichletBinning.terms w) k else 0)).sum) := by
  intro m hm k hk
  change RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m k)=_
  rw [←RHHighBinningSemantic.group_value m k hm hk,←RHBatch01GlobalBinningSound.aggregate_eq]
  rw [RHHighBinningSemantic.merge_value m k _ hk RHBatch01GlobalBinningSound.parts_valid,RHBatch01GlobalBinningSound.parts_eq,
    RHHighBinningSemantic.binned_packets_value m k hk,←RHBatch01GlobalBinningSound.word_packets_eq]
#print axioms solution
