-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_global_binning_semantics
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:56:13.327826+00:00
-- url     : https://prove2.me/submissions/cfa0b4d0-efae-4155-b37c-638c90ce9089

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins
import Definitions.Def_TaoFivePrimes_RHHighAllDirichletWords
import Definitions.Def_TaoFivePrimes_RHHighBinningMerge
import Theorems.Thm_TaoFivePrimes_rh_high_height_global_binning
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning00
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning01
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning02
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning03
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning04
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning05
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning06
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning07
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning08
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning09
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning10
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning11
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning12
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning13
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning14
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning15
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning16
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning17
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning18
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning19
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning20
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning21
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning22
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning23
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning24
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning25
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning26
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning27
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning28
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning29
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning30
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning31
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning32
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
open RHHighGlobalDirichletBins
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
namespace RHHighGlobalBinningSound
open RHHighBinningSemantic
noncomputable def parts := [RHHighDirichletBins00.values.map RHHighDirichletBinning.decode,RHHighDirichletBins01.values.map RHHighDirichletBinning.decode,RHHighDirichletBins02.values.map RHHighDirichletBinning.decode,RHHighDirichletBins03.values.map RHHighDirichletBinning.decode,RHHighDirichletBins04.values.map RHHighDirichletBinning.decode,RHHighDirichletBins05.values.map RHHighDirichletBinning.decode,RHHighDirichletBins06.values.map RHHighDirichletBinning.decode,RHHighDirichletBins07.values.map RHHighDirichletBinning.decode,RHHighDirichletBins08.values.map RHHighDirichletBinning.decode,RHHighDirichletBins09.values.map RHHighDirichletBinning.decode,RHHighDirichletBins10.values.map RHHighDirichletBinning.decode,RHHighDirichletBins11.values.map RHHighDirichletBinning.decode,RHHighDirichletBins12.values.map RHHighDirichletBinning.decode,RHHighDirichletBins13.values.map RHHighDirichletBinning.decode,RHHighDirichletBins14.values.map RHHighDirichletBinning.decode,RHHighDirichletBins15.values.map RHHighDirichletBinning.decode,RHHighDirichletBins16.values.map RHHighDirichletBinning.decode,RHHighDirichletBins17.values.map RHHighDirichletBinning.decode,RHHighDirichletBins18.values.map RHHighDirichletBinning.decode,RHHighDirichletBins19.values.map RHHighDirichletBinning.decode,RHHighDirichletBins20.values.map RHHighDirichletBinning.decode,RHHighDirichletBins21.values.map RHHighDirichletBinning.decode,RHHighDirichletBins22.values.map RHHighDirichletBinning.decode,RHHighDirichletBins23.values.map RHHighDirichletBinning.decode,RHHighDirichletBins24.values.map RHHighDirichletBinning.decode,RHHighDirichletBins25.values.map RHHighDirichletBinning.decode,RHHighDirichletBins26.values.map RHHighDirichletBinning.decode,RHHighDirichletBins27.values.map RHHighDirichletBinning.decode,RHHighDirichletBins28.values.map RHHighDirichletBinning.decode,RHHighDirichletBins29.values.map RHHighDirichletBinning.decode,RHHighDirichletBins30.values.map RHHighDirichletBinning.decode,RHHighDirichletBins31.values.map RHHighDirichletBinning.decode,RHHighDirichletBins32.values.map RHHighDirichletBinning.decode]
noncomputable def wordPackets := [RHHighDirichletValues00.rows.flatten,RHHighDirichletValues01.rows.flatten,RHHighDirichletValues02.rows.flatten,RHHighDirichletValues03.rows.flatten,RHHighDirichletValues04.rows.flatten,RHHighDirichletValues05.rows.flatten,RHHighDirichletValues06.rows.flatten,RHHighDirichletValues07.rows.flatten,RHHighDirichletValues08.rows.flatten,RHHighDirichletValues09.rows.flatten,RHHighDirichletValues10.rows.flatten,RHHighDirichletValues11.rows.flatten,RHHighDirichletValues12.rows.flatten,RHHighDirichletValues13.rows.flatten,RHHighDirichletValues14.rows.flatten,RHHighDirichletValues15.rows.flatten,RHHighDirichletValues16.rows.flatten,RHHighDirichletValues17.rows.flatten,RHHighDirichletValues18.rows.flatten,RHHighDirichletValues19.rows.flatten,RHHighDirichletValues20.rows.flatten,RHHighDirichletValues21.rows.flatten,RHHighDirichletValues22.rows.flatten,RHHighDirichletValues23.rows.flatten,RHHighDirichletValues24.rows.flatten,RHHighDirichletValues25.rows.flatten,RHHighDirichletValues26.rows.flatten,RHHighDirichletValues27.rows.flatten,RHHighDirichletValues28.rows.flatten,RHHighDirichletValues29.rows.flatten,RHHighDirichletValues30.rows.flatten,RHHighDirichletValues31.rows.flatten,RHHighDirichletValues32.rows.flatten]
lemma aggregate_eq : RHHighBinningMerge.merge parts.flatten=RHHighGlobalDirichletBins.groups := by
  exact TaoFivePrimes.rh_high_height_global_binning
lemma word_packets_eq : RHHighAllDirichletWords.values=wordPackets.flatten := by
  unfold RHHighAllDirichletWords.values
  rw [flatten_twice]
  rfl
lemma parts_eq : parts=wordPackets.map RHHighDirichletBinning.bins := by
  change [RHHighDirichletBins00.values.map RHHighDirichletBinning.decode,RHHighDirichletBins01.values.map RHHighDirichletBinning.decode,RHHighDirichletBins02.values.map RHHighDirichletBinning.decode,RHHighDirichletBins03.values.map RHHighDirichletBinning.decode,RHHighDirichletBins04.values.map RHHighDirichletBinning.decode,RHHighDirichletBins05.values.map RHHighDirichletBinning.decode,RHHighDirichletBins06.values.map RHHighDirichletBinning.decode,RHHighDirichletBins07.values.map RHHighDirichletBinning.decode,RHHighDirichletBins08.values.map RHHighDirichletBinning.decode,RHHighDirichletBins09.values.map RHHighDirichletBinning.decode,RHHighDirichletBins10.values.map RHHighDirichletBinning.decode,RHHighDirichletBins11.values.map RHHighDirichletBinning.decode,RHHighDirichletBins12.values.map RHHighDirichletBinning.decode,RHHighDirichletBins13.values.map RHHighDirichletBinning.decode,RHHighDirichletBins14.values.map RHHighDirichletBinning.decode,RHHighDirichletBins15.values.map RHHighDirichletBinning.decode,RHHighDirichletBins16.values.map RHHighDirichletBinning.decode,RHHighDirichletBins17.values.map RHHighDirichletBinning.decode,RHHighDirichletBins18.values.map RHHighDirichletBinning.decode,RHHighDirichletBins19.values.map RHHighDirichletBinning.decode,RHHighDirichletBins20.values.map RHHighDirichletBinning.decode,RHHighDirichletBins21.values.map RHHighDirichletBinning.decode,RHHighDirichletBins22.values.map RHHighDirichletBinning.decode,RHHighDirichletBins23.values.map RHHighDirichletBinning.decode,RHHighDirichletBins24.values.map RHHighDirichletBinning.decode,RHHighDirichletBins25.values.map RHHighDirichletBinning.decode,RHHighDirichletBins26.values.map RHHighDirichletBinning.decode,RHHighDirichletBins27.values.map RHHighDirichletBinning.decode,RHHighDirichletBins28.values.map RHHighDirichletBinning.decode,RHHighDirichletBins29.values.map RHHighDirichletBinning.decode,RHHighDirichletBins30.values.map RHHighDirichletBinning.decode,RHHighDirichletBins31.values.map RHHighDirichletBinning.decode,RHHighDirichletBins32.values.map RHHighDirichletBinning.decode]=[RHHighDirichletBinning.bins (RHHighDirichletValues00.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues01.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues02.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues03.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues04.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues05.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues06.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues07.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues08.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues09.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues10.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues11.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues12.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues13.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues14.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues15.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues16.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues17.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues18.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues19.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues20.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues21.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues22.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues23.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues24.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues25.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues26.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues27.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues28.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues29.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues30.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues31.rows.flatten),RHHighDirichletBinning.bins (RHHighDirichletValues32.rows.flatten)]
  simp only [TaoFivePrimes.rh_high_height_dirichlet_binning00,TaoFivePrimes.rh_high_height_dirichlet_binning01,TaoFivePrimes.rh_high_height_dirichlet_binning02,TaoFivePrimes.rh_high_height_dirichlet_binning03,TaoFivePrimes.rh_high_height_dirichlet_binning04,TaoFivePrimes.rh_high_height_dirichlet_binning05,TaoFivePrimes.rh_high_height_dirichlet_binning06,TaoFivePrimes.rh_high_height_dirichlet_binning07,TaoFivePrimes.rh_high_height_dirichlet_binning08,TaoFivePrimes.rh_high_height_dirichlet_binning09,TaoFivePrimes.rh_high_height_dirichlet_binning10,TaoFivePrimes.rh_high_height_dirichlet_binning11,TaoFivePrimes.rh_high_height_dirichlet_binning12,TaoFivePrimes.rh_high_height_dirichlet_binning13,TaoFivePrimes.rh_high_height_dirichlet_binning14,TaoFivePrimes.rh_high_height_dirichlet_binning15,TaoFivePrimes.rh_high_height_dirichlet_binning16,TaoFivePrimes.rh_high_height_dirichlet_binning17,TaoFivePrimes.rh_high_height_dirichlet_binning18,TaoFivePrimes.rh_high_height_dirichlet_binning19,TaoFivePrimes.rh_high_height_dirichlet_binning20,TaoFivePrimes.rh_high_height_dirichlet_binning21,TaoFivePrimes.rh_high_height_dirichlet_binning22,TaoFivePrimes.rh_high_height_dirichlet_binning23,TaoFivePrimes.rh_high_height_dirichlet_binning24,TaoFivePrimes.rh_high_height_dirichlet_binning25,TaoFivePrimes.rh_high_height_dirichlet_binning26,TaoFivePrimes.rh_high_height_dirichlet_binning27,TaoFivePrimes.rh_high_height_dirichlet_binning28,TaoFivePrimes.rh_high_height_dirichlet_binning29,TaoFivePrimes.rh_high_height_dirichlet_binning30,TaoFivePrimes.rh_high_height_dirichlet_binning31,TaoFivePrimes.rh_high_height_dirichlet_binning32]
lemma parts_valid : ∀ g∈parts.flatten,g.2.length=24 := by
  intro g hg
  obtain ⟨gs,hgs,hg⟩:=List.mem_flatten.mp hg
  simp only [parts,List.mem_cons,List.mem_nil_iff,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact decoded_groups_valid _ g hg
end RHHighGlobalBinningSound
theorem solution :
  ∀ m:Nat,m<929 → ∀ k:Nat,k<24 →
  RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient m k)=
    ((RHHighAllDirichletWords.values.map (fun w=>if RHHighDirichletBinning.bin w=m then
      RHHighBinningSemantic.coefficientAt (RHHighDirichletBinning.terms w) k else 0)).sum) := by
  intro m hm k hk
  change RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient m k)=_
  rw [←RHHighBinningSemantic.group_value m k hm hk,←RHHighGlobalBinningSound.aggregate_eq]
  rw [RHHighBinningSemantic.merge_value m k _ hk RHHighGlobalBinningSound.parts_valid,RHHighGlobalBinningSound.parts_eq,
    RHHighBinningSemantic.binned_packets_value m k hk,←RHHighGlobalBinningSound.word_packets_eq]
