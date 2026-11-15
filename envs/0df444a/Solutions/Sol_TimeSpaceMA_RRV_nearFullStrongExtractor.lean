-- Prove2me | solution 1 for TimeSpaceMA.RRV.nearFullStrongExtractor
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T20:44:46.765166+00:00
-- url     : https://prove2.me/submissions/0ee09171-d0e5-4d5c-9607-9f64507af131

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Basic
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Binary
import Definitions.Def_TimeSpaceMA_GUVFieldOperations
import Definitions.Def_TimeSpaceMA_RRVNearFull
import Definitions.Def_TimeSpaceMA_TUZExtractorComponents
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_TimeSpaceMA_GUV_fieldOperations_exists


namespace TimeSpaceMA.RRV

open scoped BigOperators
open Finset

/-- Read a coordinate of a design row, with zero for missing coordinates. -/
def designGet (row : List ℕ) (a : ℕ) : ℕ := row[a]?.getD 0

/-- The number of block coordinates where a partial row agrees with a previous row. -/
def designMatches (row prior : List ℕ) : ℕ :=
  (List.range row.length).countP (fun j => designGet row j == designGet prior j)

/-- The overlap moment a new row incurs against the previously chosen rows. -/
def designCost (rows : List (List ℕ)) (row : List ℕ) : ℕ :=
  (rows.map fun prior => 2 ^ designMatches row prior).sum

/-- Find a minimizer of the coordinate cost by scanning a finite initial interval. -/
def designMin (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => let a := designMin f b; if f b < f a then b else a

theorem designMin_le (f : ℕ → ℕ) (b : ℕ) :
    designMin f b < max 1 b := by
  induction b with
  | zero => simp [designMin]
  | succ b ih =>
    change (if f b < f (designMin f b) then b else designMin f b) < max 1 (b+1)
    split <;> omega

private theorem designMin_min (f : ℕ → ℕ) (b j : ℕ) (hj : j < b) :
    f (designMin f b) ≤ f j := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases he : j=b
    · subst j
      rw [designMin]
      split <;> omega
    · have hi := ih (by omega)
      rw [designMin]
      split <;> omega

/-- Append a coordinate that minimizes the current overlap moment. -/
def designExtend (q : ℕ) (rows : List (List ℕ)) (row : List ℕ) : List ℕ :=
  row ++ [designMin (fun a => designCost rows (row ++ [a])) q]

private theorem designMatches_extend (row prior : List ℕ) (a : ℕ) :
    designMatches (row ++ [a]) prior =
      designMatches row prior + if a = designGet prior row.length then 1 else 0 := by
  unfold designMatches
  rw [List.length_append, List.length_singleton, List.range_succ, List.countP_append]
  congr 1
  · apply List.countP_congr
    intro j hj
    rw [designGet, List.getElem?_append_left (List.mem_range.mp hj)]
    rfl
  · simp [designGet]; rfl

private theorem designCost_extend_sum (q : ℕ) (rows : List (List ℕ)) (row : List ℕ)
    (h : ∀ prior ∈ rows, designGet prior row.length < q) :
    (∑ a ∈ Finset.range q, designCost rows (row ++ [a])) = (q+1)*designCost rows row := by
  induction rows with
  | nil => simp [designCost]
  | cons prior rows ih =>
    have hp := h prior List.mem_cons_self
    have ht := ih (fun p hmem => h p (List.mem_cons_of_mem _ hmem))
    simp only [designCost, List.map_cons, List.sum_cons] at ht ⊢
    rw [Finset.sum_add_distrib, ht, Nat.mul_add]
    have hterm (a : ℕ) :
        2 ^ designMatches (row ++ [a]) prior =
          2 ^ designMatches row prior + if a = designGet prior row.length then
            2 ^ designMatches row prior else 0 := by
      rw [designMatches_extend]
      split
      · rw [pow_succ]
        omega
      · simp
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hp)]
    simp [Nat.add_mul]

private theorem designCost_extend_le (q : ℕ) (rows : List (List ℕ)) (row : List ℕ)
    (h : ∀ prior ∈ rows, designGet prior row.length < q) :
    q*designCost rows (designExtend q rows row) ≤ (q+1)*designCost rows row := by
  rw [← designCost_extend_sum _ _ _ h]
  calc
    _ = ∑ _a ∈ Finset.range q, designCost rows (designExtend q rows row) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun a ha =>
      designMin_min (fun t => designCost rows (row ++ [t])) q a (mem_range.mp ha))

/-- Choose the rows within a single stage. Each row has ell entries in
the interval of 2*ell+1 choices per coordinate. -/
def designBaseRow (ell : ℕ) (rows : List (List ℕ)) : List ℕ :=
  (designExtend (2*ell+1) rows)^[ell] []

/-- The first m rows of the single-stage deterministic greedy design. -/
def designBaseRows (ell : ℕ) : ℕ → List (List ℕ)
  | 0 => []
  | i+1 => let rows := designBaseRows ell i; rows ++ [designBaseRow ell rows]

private theorem designExtend_length (q : ℕ) (rows : List (List ℕ)) (row : List ℕ) :
    (designExtend q rows row).length = row.length+1 := by simp [designExtend]

private theorem designExtend_get_lt {q : ℕ} (hq : 0 < q) (rows : List (List ℕ)) {row : List ℕ}
    (h : ∀ j, designGet row j < q) : ∀ j, designGet (designExtend q rows row) j < q := by
  intro j
  by_cases hj : j < row.length
  · simpa [designGet,designExtend,List.getElem?_append_left hj] using h j
  · by_cases hj' : j = row.length
    · subst j
      have hh := designMin_le (fun a => designCost rows (row ++ [a])) q
      rw [max_eq_right (by omega : 1 ≤ q)] at hh
      simpa [designGet,designExtend,List.getElem?_append_right] using hh
    · have hh : (designExtend q rows row).length ≤ j := by
        rw [designExtend_length]
        omega
      simpa [designGet,List.getElem?_eq_none hh] using hq

private theorem designBaseRow_spec (ell : ℕ) (rows : List (List ℕ))
    (hrows : ∀ prior ∈ rows, ∀ j, designGet prior j < 2*ell+1) :
    (designBaseRow ell rows).length = ell ∧
    (∀ j, designGet (designBaseRow ell rows) j < 2*ell+1) ∧
    designCost rows (designBaseRow ell rows) ≤ 2*rows.length := by
  let q := 2*ell+1
  have hq : 0 < q := by dsimp [q]; omega
  have hiter (r : ℕ) (hr : r ≤ ell) :
      let row := (designExtend q rows)^[r] []
      row.length = r ∧ (∀ j, designGet row j < q) ∧
      (q-r)*designCost rows row ≤ q*rows.length := by
    induction r with
    | zero =>
      simp [designCost,designMatches,List.sum_replicate,designGet,hq,Nat.mul_comm]
    | succ r ih =>
      obtain ⟨hLen,hGet,hBound⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      dsimp only
      refine ⟨by rw [designExtend_length,hLen], designExtend_get_lt hq rows hGet, ?_⟩
      let a := designCost rows ((designExtend q rows)^[r] [])
      let b := designCost rows (designExtend q rows ((designExtend q rows)^[r] []))
      change (q-(r+1))*b ≤ q*rows.length
      change (q-r)*a ≤ q*rows.length at hBound
      have hgreedy : q*b ≤ (q+1)*a := designCost_extend_le _ _ _ (fun prior hp => hrows _ hp _)
      have hsub : q-r = (q-(r+1))+1 := by dsimp [q]; omega
      have hfac : (q-(r+1))*(q+1) ≤ (q-r)*q := by
        rw [hsub,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
        have : q-(r+1) ≤ q := Nat.sub_le .. 
        omega
      apply Nat.le_of_mul_le_mul_right _ hq
      calc
        _ = (q-(r+1))*(q*b) := by ac_rfl
        _ ≤ (q-(r+1))*((q+1)*a) := Nat.mul_le_mul_left _ hgreedy
        _ = ((q-(r+1))*(q+1))*a := by ac_rfl
        _ ≤ ((q-r)*q)*a := Nat.mul_le_mul_right _ hfac
        _ = ((q-r)*a)*q := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right _ hBound
  obtain ⟨hlen,hget,hcost⟩ := hiter ell le_rfl
  refine ⟨hlen,hget,?_⟩
  have hq' : q-ell = ell+1 := by dsimp [q]; omega
  rw [hq'] at hcost
  have hle : q ≤ (ell+1)*2 := by dsimp [q]; omega
  apply Nat.le_of_mul_le_mul_left _ (show 0<ell+1 by omega)
  calc
    _ ≤ q*rows.length := hcost
    _ ≤ _ := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hle

theorem designBaseRows_length (ell i : ℕ) : (designBaseRows ell i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [designBaseRows,ih]

theorem designBaseRows_bounded (ell i : ℕ) :
    ∀ row ∈ designBaseRows ell i, ∀ j, designGet row j < 2*ell+1 := by
  induction i with
  | zero => simp [designBaseRows]
  | succ i ih =>
    intro row h
    simp only [designBaseRows,List.mem_append,List.mem_singleton] at h
    rcases h with h|rfl
    · exact ih _ h
    · exact (designBaseRow_spec ell _ ih).2.1

/-- The single-stage design's row at index i. -/
def designRow (ell i : ℕ) : List ℕ := designBaseRow ell (designBaseRows ell i)

theorem designRow_length (ell i : ℕ) : (designRow ell i).length = ell :=
  (designBaseRow_spec ell _ (designBaseRows_bounded ell i)).1

private theorem designRow_bounded (ell i j : ℕ) : designGet (designRow ell i) j < 2*ell+1 :=
  (designBaseRow_spec ell _ (designBaseRows_bounded ell i)).2.1 j

theorem designBaseRows_eq (ell i : ℕ) :
    designBaseRows ell i = (List.range i).map (designRow ell) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [designBaseRows,List.range_succ,ih,designRow]

private theorem designCost_base (ell i : ℕ) : designCost (designBaseRows ell i) (designRow ell i) ≤ 2*i := by
  simpa only [designBaseRows_length, designRow] using
    (designBaseRow_spec ell _ (designBaseRows_bounded ell i)).2.2


private theorem designCost_eq_sum (ell i : ℕ) :
    designCost (designBaseRows ell i) (designRow ell i) =
      ∑ j ∈ Finset.range i, 2 ^ designMatches (designRow ell i) (designRow ell j) := by
  rw [designBaseRows_eq]
  unfold designCost
  rw [List.map_map]
  generalize (designRow ell i) = row
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    rfl

/-- The number of bits used by the disjoint weak design stages. -/
def designWidth (m ell : ℕ) : ℕ := m.size * (ell * (2*ell+1))

/-- Remaining indices are grouped by binary length, largest groups first. -/
def designStage (m i : ℕ) : ℕ := (m-i).size-1

/-- Index of the first row of the stage containing i. -/
def designStart (m i : ℕ) : ℕ := m - min m (2^(m-i).size-1)

private theorem designStart_le {m i : ℕ} (hi : i < m) : designStart m i ≤ i := by
  have hsize : m-i < 2^(m-i).size := Nat.size_le.mp le_rfl
  unfold designStart
  omega

private theorem designStage_eq_iff {m i j : ℕ} (hi : i < m) (hj : j ≤ i) :
    designStage m j = designStage m i ↔ designStart m i ≤ j := by
  have hij : m-i ≤ m-j := by omega
  have hh : (m-i).size ≤ (m-j).size := Nat.size_le_size hij
  have hp : 0 < (m-i).size := Nat.size_pos.mpr (by omega)
  rw [designStage,designStage,show ((m-j).size-1 = (m-i).size-1) ↔
    (m-j).size ≤ (m-i).size by omega, Nat.size_le]
  unfold designStart
  omega

private theorem designLocal_le_remaining {m i : ℕ} (hi : i < m) :
    i-designStart m i ≤ m-i-1 := by
  have hp : 0 < (m-i).size := Nat.size_pos.mpr (by omega)
  have hpow : 2^((m-i).size-1) ≤ m-i := Nat.lt_size.mp (by omega)
  have hpow' : 2^(m-i).size = 2 * 2^((m-i).size-1) := by
    calc
      _ = 2^(((m-i).size-1)+1) := congrArg (fun k : ℕ => (2:ℕ)^k) (by omega)
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  unfold designStart
  omega

/-- Block label and its selected coordinate, encoded in a single seed position. -/
def designPosition (m ell i j : ℕ) : ℕ :=
  (designStage m i * ell + j) * (2*ell+1) +
    designGet (designRow ell (i-designStart m i)) j

private theorem designPosition_div (m ell i j : ℕ) :
    designPosition m ell i j / (2*ell+1) = designStage m i * ell + j := by
  unfold designPosition
  rw [Nat.mul_comm _ (2*ell+1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt (designRow_bounded ..)]
  omega

private theorem designPosition_mod (m ell i j : ℕ) :
    designPosition m ell i j % (2*ell+1) =
      designGet (designRow ell (i-designStart m i)) j := by
  unfold designPosition
  rw [Nat.mul_comm _ (2*ell+1), Nat.mul_add_mod, Nat.mod_eq_of_lt (designRow_bounded ..)]

theorem designPosition_lt {m ell i j : ℕ} (hi : i < m) (hj : j < ell) :
    designPosition m ell i j < designWidth m ell := by
  have hstage : designStage m i < m.size := by
    have hh := Nat.size_le_size (Nat.sub_le m i)
    have hp : 0 < (m-i).size := Nat.size_pos.mpr (by omega)
    unfold designStage
    omega
  have ha := Nat.mul_le_mul_right ell (show designStage m i+1 ≤ m.size by omega)
  rw [Nat.add_mul, Nat.one_mul] at ha
  have hb : designStage m i * ell + j < m.size * ell := by omega
  have hc := Nat.mul_le_mul_right (2*ell+1)
    (show designStage m i * ell + j + 1 ≤ m.size*ell by omega)
  rw [Nat.add_mul,Nat.one_mul] at hc
  have hd := designRow_bounded ell (i-designStart m i) j
  unfold designPosition designWidth
  rw [← Nat.mul_assoc]
  omega

/-- The injective selection of seed coordinates for a given output bit. -/
def weakDesignCoord (m ell : ℕ) (i : Fin m) : Fin ell ↪ Fin (designWidth m ell) where
  toFun j := ⟨designPosition m ell i.val j.val, designPosition_lt i.isLt j.isLt⟩
  inj' := by
    intro j k h
    have he := congrArg (fun x : Fin (designWidth m ell) => x.val/(2*ell+1)) h
    change designPosition m ell i.val j.val / (2*ell+1) =
      designPosition m ell i.val k.val / (2*ell+1) at he
    rw [designPosition_div,designPosition_div] at he
    exact Fin.ext (by omega)

private theorem designPosition_eq_iff {m ell i i' j j' : ℕ} (hj : j < ell) (hj' : j' < ell) :
    designPosition m ell i j = designPosition m ell i' j' ↔
      designStage m i = designStage m i' ∧ j=j' ∧
        designGet (designRow ell (i-designStart m i)) j =
          designGet (designRow ell (i'-designStart m i')) j' := by
  constructor
  · intro h
    have hq := congrArg (· / (2*ell+1)) h
    rw [designPosition_div,designPosition_div] at hq
    have hs := congrArg (· / ell) hq
    rw [Nat.mul_comm (designStage m i) ell, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj,
      Nat.mul_comm (designStage m i') ell, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj'] at hs
    simp only [Nat.add_zero] at hs
    have hjj : j=j' := by rw [hs] at hq; omega
    have hr := congrArg (· % (2*ell+1)) h
    rw [designPosition_mod,designPosition_mod] at hr
    exact ⟨hs,hjj,hr⟩
  · rintro ⟨h1,h2,h3⟩
    unfold designPosition
    rw [h1,h2] at *
    rw [h3]

private theorem designMatches_eq_card (ell i i' : ℕ) :
    designMatches (designRow ell i) (designRow ell i') =
      ((Finset.univ : Finset (Fin ell)).filter
        (fun j => designGet (designRow ell i) j.val = designGet (designRow ell i') j.val)).card := by
  unfold designMatches
  rw [designRow_length, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  rw [List.toFinset_filter, List.toFinset_range]
  rw [Finset.card_filter, Finset.card_filter]
  simp only [beq_iff_eq]
  exact Finset.sum_range _

private theorem weakDesign_inter_card (m ell : ℕ) (i j : Fin m) :
    ((Finset.univ.map (weakDesignCoord m ell i)) ∩
      (Finset.univ.map (weakDesignCoord m ell j))).card =
    if designStage m i = designStage m j then
      designMatches (designRow ell (i.val-designStart m i.val))
        (designRow ell (j.val-designStart m j.val))
    else 0 := by
  let A := Finset.univ.map (weakDesignCoord m ell i)
  let B := Finset.univ.map (weakDesignCoord m ell j)
  have hf : A ∩ B = (Finset.univ.filter fun a : Fin ell =>
      ∃ b : Fin ell, weakDesignCoord m ell i a = weakDesignCoord m ell j b).map
        (weakDesignCoord m ell i) := by
    ext x
    simp only [A,B,Finset.mem_inter,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨a,rfl⟩,⟨b,hb⟩⟩
      exact ⟨a,⟨b,hb.symm⟩,rfl⟩
    · rintro ⟨a,⟨b,hb⟩,rfl⟩
      exact ⟨⟨a,rfl⟩,⟨b,hb.symm⟩⟩
  change (A ∩ B).card = _
  rw [hf,Finset.card_map]
  have he (a : Fin ell) : (∃ b : Fin ell, weakDesignCoord m ell i a =
      weakDesignCoord m ell j b) ↔ designStage m i = designStage m j ∧
       designGet (designRow ell (i.val-designStart m i.val)) a.val =
         designGet (designRow ell (j.val-designStart m j.val)) a.val := by
    constructor
    · rintro ⟨b,hb⟩
      have hh := (designPosition_eq_iff a.isLt b.isLt).mp (congrArg Fin.val hb)
      rw [← hh.2.1] at hh
      exact ⟨hh.1,hh.2.2⟩
    · rintro ⟨hs,hr⟩
      exact ⟨a,Fin.ext ((designPosition_eq_iff a.isLt a.isLt).mpr ⟨hs,rfl,hr⟩)⟩
  simp only [he]
  split
  · rename_i h
    simpa only [h,true_and] using
      (designMatches_eq_card ell (i.val-designStart m i.val)
        (j.val-designStart m j.val)).symm
  · rename_i h
    simp [h]


private theorem designStart_eq_of_stage_eq {m i j : ℕ} (hi : i < m) (hj : j < m)
    (h : designStage m i = designStage m j) :
    designStart m i = designStart m j := by
  have hsize_i : 0 < (m-i).size := Nat.size_pos.mpr (by omega)
  have hsize_j : 0 < (m-j).size := Nat.size_pos.mpr (by omega)
  unfold designStage at h
  unfold designStart
  rw [show (m-i).size = (m-j).size by omega]

/-- The ordered selection is an exact weak design. Earlier rows' overlap moments
sum to at most m−1 for every current row. -/
theorem weakDesign_bound (m ell : ℕ) (i : Fin m) :
    (∑ j : Fin i.val, 2 ^ ((Finset.univ.map (weakDesignCoord m ell i)) ∩
      (Finset.univ.map (weakDesignCoord m ell ⟨j.val, j.isLt.trans i.isLt⟩))).card) ≤ m-1 := by
  let t := designStart m i.val
  let r := i.val-t
  have ht : t ≤ i.val := designStart_le i.isLt
  have htr : t+r = i.val := by dsimp [r]; omega
  let weight (j : ℕ) : ℕ :=
    if designStage m j = designStage m i.val then
      2^designMatches (designRow ell r) (designRow ell (j-t)) else 1
  have hsum : (∑ j : Fin i.val, 2 ^ ((Finset.univ.map (weakDesignCoord m ell i)) ∩
      (Finset.univ.map (weakDesignCoord m ell ⟨j.val, j.isLt.trans i.isLt⟩))).card) =
      ∑ j ∈ Finset.range i.val, weight j := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hj := j.isLt
    rw [weakDesign_inter_card]
    change (2:ℕ)^(if designStage m i.val = designStage m j.val then
      designMatches (designRow ell r) (designRow ell (j.val - designStart m j.val)) else 0) =
        weight j.val
    by_cases hs : designStage m j.val = designStage m i.val
    · rw [if_pos hs.symm]
      simp only [weight,hs,if_true]
      rw [designStart_eq_of_stage_eq (hj.trans i.isLt) i.isLt hs]
    · rw [if_neg (Ne.symm hs)]
      simp [weight,hs]
  rw [hsum, ← htr, Finset.sum_range_add]
  have hbefore : (∑ j ∈ Finset.range t, weight j) = t := by
    calc
      _ = ∑ _j ∈ Finset.range t, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hs : designStage m j ≠ designStage m i.val := by
          intro h
          have hle := (designStage_eq_iff i.isLt (show j ≤ i.val by omega)).mp h
          change t ≤ j at hle
          omega
        simp [weight,hs]
      _ = _ := by simp
  have hwithin : (∑ j ∈ Finset.range r, weight (t+j)) = designCost (designBaseRows ell r) (designRow ell r) := by
    rw [designCost_eq_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hs := (designStage_eq_iff i.isLt (show t+j ≤ i.val by omega)).mpr
      (show designStart m i.val ≤ t+j by change t ≤ t+j; omega)
    simp [weight,hs]
  rw [hbefore,hwithin]
  have hc := designCost_base ell r
  have hr : r ≤ m-i.val-1 := designLocal_le_remaining i.isLt
  omega

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxHeartbeats 1200000

private abbrev encDesignRow := encList encUnary
private abbrev encDesignRows := encList encDesignRow

private theorem designGet_poly {α : Type} {enc : α ↪ List Bool} {l : α → List ℕ} {i : α → ℕ}
    (hl : ComputableTidilyInPolyTime l enc encDesignRow)
    (hi : ComputableTidilyInPolyTime i enc encUnary) :
    ComputableTidilyInPolyTime (fun x => designGet (l x) (i x)) enc encUnary := by
  simpa only [designGet, Function.comp_def, ← List.getD_eq_getElem?_getD] using
    (listGetD (encL := encDesignRow) (encA := encUnary) 0).comp (hl.prod hi)

private theorem designMatches_poly :
    ComputableTidilyInPolyTime (fun p : List ℕ × List ℕ => designMatches p.1 p.2)
      (encPair encDesignRow encDesignRow) encUnary := by
  let encRows := encPair encDesignRow encDesignRow
  have hindex := snd encRows encUnary
  have hpair := fst encRows encUnary
  exact countPWithInput (range.comp ((length_list encUnary).comp (fst encDesignRow encDesignRow)))
    (unary_beq (designGet_poly ((fst encDesignRow encDesignRow).comp hpair) hindex)
      (designGet_poly ((snd encDesignRow encDesignRow).comp hpair) hindex))

private theorem designCost_poly :
    ComputableTidilyInPolyTime (fun p : List (List ℕ) × List ℕ => designCost p.1 p.2)
      (encPair encDesignRows encDesignRow) encNat := by
  let encInput := encPair encDesignRows encDesignRow
  have hp := fst encInput encDesignRow
  have hprior := snd encInput encDesignRow
  have hrow := (snd encDesignRows encDesignRow).comp hp
  exact binary_sum.comp
    (mapWithInput (fst encDesignRows encDesignRow)
      (binary_two_pow.comp (designMatches_poly.comp (hrow.prod hprior))))

private theorem snoc_poly {α β : Type} {enc : α ↪ List Bool} {out : β ↪ List Bool}
    {l : α → List β} {a : α → β} (hl : ComputableTidilyInPolyTime l enc (encList out))
    (ha : ComputableTidilyInPolyTime a enc out) :
    ComputableTidilyInPolyTime (fun x => l x ++ [a x]) enc (encList out) :=
  (ComputableTidilyInDegree.snoc out).computableTidilyInPolyTime.comp (hl.prod ha)

private theorem designExtend_poly :
    ComputableTidilyInPolyTime
      (fun p : ((ℕ × List (List ℕ)) × List ℕ) => designExtend p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encDesignRows) encDesignRow) encDesignRow := by
  let encQ := encPair encUnary encDesignRows
  let encP := encPair encQ encDesignRow
  let f (p : (ℕ × List (List ℕ)) × List ℕ) (a : ℕ) := designCost p.1.2 (p.2 ++ [a])
  let stateEnc := encPair encUnary encUnary
  let step (p : (ℕ × List (List ℕ)) × List ℕ) (s : ℕ × ℕ) :=
    (s.1+1, if f p s.1 < f p s.2 then s.1 else s.2)
  have hq := (fst encUnary encDesignRows).comp (fst encQ encDesignRow)
  have hstep : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List (List ℕ)) × List ℕ) × (ℕ × ℕ)) => step p.1 p.2)
      (encPair encP stateEnc) stateEnc := by
    have hpar := fst encP stateEnc
    have hs := snd encP stateEnc
    have hscan := (fst encUnary encUnary).comp hs
    have hbest := (snd encUnary encUnary).comp hs
    have hprior := (snd encUnary encDesignRows).comp ((fst encQ encDesignRow).comp hpar)
    have hrow := (snd encQ encDesignRow).comp hpar
    have hval := designCost_poly.comp (hprior.prod (snoc_poly hrow hscan))
    have hprev := designCost_poly.comp (hprior.prod (snoc_poly hrow hbest))
    simpa only [step, f, Function.comp_def, decide_eq_true_eq] using
      (unary_add.comp (hscan.prod (const 1))).prod
        ((binary_lt' hval hprev).cond hscan hbest)
  have hMin (p : (ℕ × List (List ℕ)) × List ℕ) (i : ℕ) :
      (step p)^[i] (0,0) = (i,designMin (f p) i) := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih]; rfl
  have hiter : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List (List ℕ)) × List ℕ) => (step p)^[p.1.1] (0,0)) encP stateEnc := by
    apply iterateWith id' hq (const (0,0)) hstep
      (bound := fun p => 3*p.1.1+2) ((PolyBounded.const 3).mul hq.polyBounded |>.add (.const 2))
    intro p i hi
    rw [hMin]
    simp only [stateEnc,length_encPair,encUnary_apply,List.length_replicate]
    have hb := designMin_le (f p) i
    change i ≤ p.1.1 at hi
    omega
  have hresult := snoc_poly (snd encQ encDesignRow) ((snd encUnary encUnary).comp hiter)
  simpa only [Function.comp_def, hMin, designExtend, f] using hresult

private theorem length_encList_snoc' {α : Type} (enc : α ↪ List Bool) (l : List α) (x : α) :
    (encList enc (l ++ [x])).length = (encList enc l).length+2*(enc x).length+1 := by
  simp [length_encList, Nat.add_assoc]

private theorem designBaseRow_poly :
    ComputableTidilyInPolyTime (fun p : ℕ × List (List ℕ) => designBaseRow p.1 p.2)
      (encPair encUnary encDesignRows) encDesignRow := by
  let encP := encPair encUnary encDesignRows
  have hell := fst encUnary encDesignRows
  let par (p : ℕ × List (List ℕ)) := (2*p.1+1,p.2)
  have hq := unary_add.comp ((unary_mul.comp ((const 2).prod hell)).prod (const 1))
  have hpar : ComputableTidilyInPolyTime par encP encP := hq.prod (snd encUnary encDesignRows)
  unfold designBaseRow
  apply iterateWith_of_bounded_growth (step := fun p => designExtend p.1 p.2)
    hpar hell (const []) designExtend_poly
    (growth := fun p => 2*(2*p.1+1)+1)
  · exact ((PolyBounded.const 2).mul hq.polyBounded).add (.const 1)
  · intro p state
    unfold designExtend
    rw [length_encList_snoc']
    simp only [encUnary_apply,List.length_replicate]
    have hb := designMin_le (fun a => designCost (par p).2 (state ++ [a])) (par p).1
    dsimp [par] at hb
    change (encDesignRow state).length+
       2*designMin (fun a => designCost p.2 (state ++ [a])) (2*p.1+1)+1 ≤
       (encDesignRow state).length+(2*(2*p.1+1)+1)
    omega

private theorem designBaseRows_poly :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => designBaseRows p.1 p.2)
      (encPair encUnary encUnary) encDesignRows := by
  let encP := encPair encUnary encUnary
  let step (ell : ℕ) (rows : List (List ℕ)) := rows ++ [designBaseRow ell rows]
  have hell := fst encUnary encUnary
  have hcount := snd encUnary encUnary
  have hstep : ComputableTidilyInPolyTime
      (fun p : ℕ × List (List ℕ) => step p.1 p.2) (encPair encUnary encDesignRows) encDesignRows :=
    snoc_poly (snd encUnary encDesignRows) designBaseRow_poly
  have hIter (ell i : ℕ) : (step ell)^[i] [] = designBaseRows ell i := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih]; rfl
  have hpoly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (step p.1)^[p.2] [])
      encP encDesignRows := by
    have hq : PolyBounded (fun p : ℕ × ℕ => (encP p).length) (fun p => 2*p.1+1) :=
      ((PolyBounded.const 2).mul hell.polyBounded).add (.const 1)
    have hB : PolyBounded (fun p : ℕ × ℕ => (encP p).length)
        (fun p => p.2*(2*(p.1*(2*(2*p.1+1)+1))+1)) :=
      hcount.polyBounded.mul (((PolyBounded.const 2).mul
        (hell.polyBounded.mul (((PolyBounded.const 2).mul hq).add (.const 1)))).add (.const 1))
    apply iterateWith hell hcount (const []) hstep hB
    intro p i hi
    rw [hIter]
    refine (length_encList_le encDesignRow _ (b := p.1*(2*(2*p.1+1)+1)) ?_).trans ?_
    · intro row hrow
      have hlen : row.length = p.1 := by
        rw [designBaseRows_eq] at hrow
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hrow
        exact designRow_length .. 
      calc
        _ ≤ row.length*(2*(2*p.1+1)+1) := by
          apply length_encList_le encUnary
          intro a ha
          obtain ⟨j,hj,hja⟩ := List.mem_iff_getElem.mp ha
          have hb := designBaseRows_bounded p.1 i row hrow j
          rw [designGet, List.getElem?_eq_getElem hj, Option.getD_some, hja] at hb
          simpa [encUnary_apply] using hb.le
        _ = _ := by rw [hlen]
    · rw [designBaseRows_length]
      exact Nat.mul_le_mul_right _ hi
  simpa only [hIter] using hpoly

private theorem designRow_poly {α : Type} {enc : α ↪ List Bool} {ell i : α → ℕ}
    (hell : ComputableTidilyInPolyTime ell enc encUnary)
    (hi : ComputableTidilyInPolyTime i enc encUnary) :
    ComputableTidilyInPolyTime (fun x => designRow (ell x) (i x)) enc encDesignRow := by
  have harg : ComputableTidilyInPolyTime (fun x => (ell x, i x)) enc
      (encPair encUnary encUnary) := hell.prod hi
  have hl : ComputableTidilyInPolyTime (fun x => designBaseRows (ell x) (i x)) enc encDesignRows := by
    simpa only [Function.comp_def] using designBaseRows_poly.comp harg
  have hp : ComputableTidilyInPolyTime (fun x => (ell x, designBaseRows (ell x) (i x))) enc
      (encPair encUnary encDesignRows) := hell.prod hl
  simpa only [designRow, Function.comp_def] using designBaseRow_poly.comp hp

private theorem designSizeU {α : Type} {enc : α ↪ List Bool} {v : α → ℕ}
    (hv : ComputableTidilyInPolyTime v enc encUnary) :
    ComputableTidilyInPolyTime (fun x => (v x).size) enc encUnary :=
  ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hv)

theorem designWidth_polytime {α : Type} {enc : α ↪ List Bool} {m ell : α → ℕ}
    (hm : ComputableTidilyInPolyTime m enc encUnary)
    (hell : ComputableTidilyInPolyTime ell enc encUnary) :
    ComputableTidilyInPolyTime (fun x => designWidth (m x) (ell x)) enc encUnary :=
  unary_mul.comp ((designSizeU hm).prod (unary_mul.comp
    (hell.prod (unary_add.comp ((unary_mul.comp ((const 2).prod hell)).prod (const 1))))))

/-- Compute the numeric index of a selected seed bit with unary inputs and output. -/
theorem designPosition_polytime {α : Type} {enc : α ↪ List Bool} {m ell i j : α → ℕ}
    (hm : ComputableTidilyInPolyTime m enc encUnary)
    (hell : ComputableTidilyInPolyTime ell enc encUnary)
    (hi : ComputableTidilyInPolyTime i enc encUnary)
    (hj : ComputableTidilyInPolyTime j enc encUnary) :
    ComputableTidilyInPolyTime (fun x => designPosition (m x) (ell x) (i x) (j x)) enc encUnary := by
  have hrem := unary_sub.comp (hm.prod hi)
  have hsize := designSizeU hrem
  have hstage := unary_sub.comp (hsize.prod (const 1))
  have hcap := binary_sub.comp ((binary_two_pow.comp hsize).prod (const 1))
  have hstart := unary_sub.comp (hm.prod
    (ComputableInPolyTime.binary_min_unary' hm.computableInPolyTime hcap.computableInPolyTime).tidy)
  have hlocal := unary_sub.comp (hi.prod hstart)
  have hq := unary_add.comp ((unary_mul.comp ((const 2).prod hell)).prod (const 1))
  have hblock := unary_add.comp ((unary_mul.comp (hstage.prod hell)).prod hj)
  exact unary_add.comp ((unary_mul.comp (hblock.prod hq)).prod
    (designGet_poly (designRow_poly hell hlocal) hj))

end TimeSpaceMA.RRV
#print axioms TimeSpaceMA.RRV.weakDesign_bound
#print axioms TimeSpaceMA.RRV.designPosition_polytime
#print axioms TimeSpaceMA.RRV.designWidth_polytime

open scoped BigOperators

namespace TimeSpaceMA

/-- Natural output label, with coordinate zero assigned the least significant bit. -/
def packBits {m : ℕ} (bits : Fin m → ZMod 2) : ℕ :=
  ∑ i, (bits i).val * 2^i.val

/-- Unpack a natural label into its little-endian bit vector. -/
def unpackBits {m : ℕ} (x : Fin (2^m)) : Fin m → ZMod 2 :=
  fun i => (x.val / 2^i.val : ℕ)

theorem pack_unpackBits {m : ℕ} (x : Fin (2^m)) : packBits (unpackBits x) = x.val := by
  have h : ∀ (m z : ℕ), z < 2^m →
      (∑ i : Fin m, (z / 2^i.val % 2) * 2^i.val) = z := by
    intro m
    induction m with
    | zero => intro z hz; simp at hz; simp [hz]
    | succ m ih =>
      intro z hz
      have hz' : z / 2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hz)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one, Fin.val_succ]
      have hs (i : Fin m) : (z / 2^(i.val+1) % 2) * 2^(i.val+1) =
          2 * ((z/2 / 2^i.val % 2) * 2^i.val) := by
        rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm 2 (2^i.val)]
        ac_rfl
      simp_rw [hs]
      rw [← Finset.mul_sum, ih _ hz']
      exact Nat.mod_add_div z 2
  simpa only [packBits, unpackBits, ZMod.val_natCast] using h m x.val x.isLt

/-- The canonical equivalence between numerical labels and bit vectors. -/
noncomputable def bitsEquiv (m : ℕ) : Fin (2^m) ≃ (Fin m → ZMod 2) := by
  let e : Fin (2^m) ≃ (Fin m → ZMod 2) := Fintype.equivOfCardEq (by simp)
  have hi : Function.Injective (unpackBits (m := m)) :=
    fun x y he => Fin.ext (by simpa only [pack_unpackBits] using congrArg packBits he)
  exact Equiv.ofBijective unpackBits ⟨hi, (Finite.injective_iff_surjective_of_equiv e).mp hi⟩

theorem bitsEquiv_apply {m : ℕ} (v : Fin (2^m)) : bitsEquiv m v = unpackBits v :=
  rfl

theorem bitsEquiv_symm_val {m : ℕ} (v : Fin m → ZMod 2) :
    ((bitsEquiv m).symm v).val = packBits v := by
  calc
    _ = packBits (unpackBits ((bitsEquiv m).symm v)) := (pack_unpackBits _).symm
    _ = packBits v := congrArg packBits ((bitsEquiv m).apply_symm_apply v)

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

theorem Toeplitz.sum_range_map {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range, Finset.sum_range]

/-- One output coordinate of a binary diagonal hash, evaluated with arithmetic on labels. -/
def Toeplitz.bit (p : (ℕ × ℕ × ℕ) × ℕ) : ℕ :=
  (((List.range p.1.1).map fun j =>
    (p.1.2.1 / 2^j % 2) * (p.1.2.2 / 2^(p.2+j) % 2)).sum) % 2

private abbrev Toeplitz.encBitInput : ((ℕ × ℕ × ℕ) × ℕ) ↪ List Bool :=
  encPair (encPair encUnary (encPair encNat encNat)) encUnary

theorem Toeplitz.bit_polytime :
    ComputableTidilyInPolyTime Toeplitz.bit Toeplitz.encBitInput encNat := by
  let input := Toeplitz.encBitInput
  have hn : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ × ℕ) × ℕ => p.1.1) input encUnary :=
    (fst _ _).fst'
  have hl := range.comp hn
  have hf : ComputableTidilyInPolyTime (fun p : ((ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      (p.1.1.2.1 / 2^p.2 % 2) * (p.1.1.2.2 / 2^(p.1.2+p.2) % 2))
      (encPair input encUnary) encNat := by
    have houter := fst input encUnary
    have hj := snd input encUnary
    have hi := houter.snd'
    have hx := houter.fst'.snd'.fst'
    have hs := houter.fst'.snd'.snd'
    have hp := binary_two_pow.comp hj
    have hq := binary_two_pow.comp (unary_add.comp (hi.prod hj))
    exact binary_mul'
      (binary_mod' (binary_div' hx hp) (const 2))
      (binary_mod' (binary_div' hs hq) (const 2))
  exact binary_mod' (binary_sum.comp (mapWithInput hl hf)) (const 2)

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA.RRV

/-- Agreement interpreted as a signed coordinate; the product is one exactly when
the two Boolean bits agree. -/
def signBit (b : Bool) : ℝ := if b then 1 else -1

private theorem signBit_mul (a b : Bool) :
    signBit a * signBit b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [signBit]

theorem sign_correlation {I : Type} [Fintype I] (f g : I → Bool) :
    (∑ i, signBit (f i) * signBit (g i)) =
      2 * ((Finset.univ.filter fun i => f i = g i).card : ℝ) - Fintype.card I := by
  simp_rw [signBit_mul]
  have he (i : I) : (if f i = g i then (1:ℝ) else -1) =
      2 * (if f i = g i then (1:ℝ) else 0) - 1 := by split <;> norm_num
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  simp [nsmul_eq_mul]

/-- The signed distance bound behind RRV Appendix A. A codeword with agreement
at least one half plus δ has correlation at least 2δ with the center, while
pairwise distance at least one half minus δ²/2 gives cross-correlation at most δ².
No algorithm for list decoding is required by the extractor analysis. -/
theorem signed_list_size {X I : Type} [Fintype I] (C : X → I → Bool) (g : I → Bool)
    (B : Finset X) {δ : ℝ} (hδ : 0 < δ) (hI : 0 < Fintype.card I)
    (hcross : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      (∑ i, signBit (C x i)*signBit (C y i)) ≤ δ^2 * Fintype.card I)
    (hcenter : ∀ x ∈ B, 2*δ*Fintype.card I ≤ ∑ i, signBit (C x i)*signBit (g i)) :
    (B.card : ℝ) ≤ 1/(3*δ^2) := by
  classical
  let N : ℝ := Fintype.card I
  let L : ℝ := B.card
  let v i := ∑ x ∈ B, signBit (C x i)
  let w i := signBit (g i)
  have hn : 0 < N := by dsimp [N]; exact_mod_cast hI
  have hl : 0 ≤ L := Nat.cast_nonneg _
  have hvw : 2*δ*N*L ≤ ∑ i, v i*w i := by
    simp_rw [v, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _x ∈ B, 2*δ*N := by simp [nsmul_eq_mul, L, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hcenter x hx)
  have hw : ∑ i, (w i)^2 = N := by
    have h (i : I) : (w i)^2 = 1 := by dsimp [w, signBit]; split <;> norm_num
    simp [h,N]
  have hv : ∑ i, (v i)^2 ≤ L*N+L*L*δ^2*N := by
    simp_rw [v, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset I)) (t := B)]
    have hT (x y : X) (hx : x ∈ B) (hy : y ∈ B) :
        (∑ i, signBit (C x i)*signBit (C y i)) ≤
          (if x = y then N else 0) + (δ^2*N) := by
      by_cases hh : x = y
      · subst y
        simp only [signBit_mul, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one]
        exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hn.le)
      · simpa [hh] using hcross x hx y hy
    have hsum (x : X) (hx : x ∈ B) :
        (∑ y ∈ B, ∑ i, signBit (C x i)*signBit (C y i)) ≤ N + L*(δ^2*N) := by
      refine (Finset.sum_le_sum fun y hy => hT x y hx hy).trans_eq ?_
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hx]
      simp [L,nsmul_eq_mul]
    refine (Finset.sum_le_sum fun x hx => hsum x hx).trans_eq ?_
    simp only [Finset.sum_const,nsmul_eq_mul,L]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I) v w
  rw [hw] at hcs
  have hpos : 0 ≤ 2*δ*N*L := by positivity
  have hsq := (pow_le_pow_left₀ hpos hvw 2).trans hcs
  have hfull := hsq.trans (mul_le_mul_of_nonneg_right hv hn.le)
  have he : (3*δ^2*L)* (L*N^2) ≤ 1*(L*N^2) := by nlinarith only [hfull]
  change L ≤ _
  rcases hl.eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · have hdiv : 3*δ^2*L ≤ 1 :=
      le_of_mul_le_mul_right he (mul_pos h0 (pow_pos hn _))
    exact (le_div_iff₀ (by positivity : 0 < 3*δ^2)).2 (by linarith)

/-- Near-half pairwise distance bounds the number of input labels whose codewords
are within a radius (1/2−δ) of a single center. -/
theorem hamming_list_size {X I : Type} [Fintype I] (C : X → I → Bool) (g : I → Bool)
    (B : Finset X) {δ : ℝ} (hδ : 0 < δ) (hI : 0 < Fintype.card I)
    (hcross : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      ((Finset.univ.filter fun i => C x i = C y i).card : ℝ) ≤
        (1/2 + δ^2/2)*(Fintype.card I : ℝ))
    (hcenter : ∀ x ∈ B, (1/2+δ)*(Fintype.card I : ℝ) ≤
      ((Finset.univ.filter fun i => C x i = g i).card : ℝ)) :
    (B.card : ℝ) ≤ 1/(3*δ^2) := by
  apply signed_list_size C g B hδ hI
  · intro x hx y hy hne
    rw [sign_correlation]
    linarith [hcross x hx y hy hne]
  · intro x hx
    rw [sign_correlation]
    linarith [hcenter x hx]

end TimeSpaceMA.RRV

namespace TimeSpaceMA.GUV
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Polynomial

namespace BinaryFieldArithmetic

variable {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)

attribute [local instance] BinaryFieldArithmetic.fieldK BinaryFieldArithmetic.fieldF
def radix (a n : ℕ) := 2^(2*halfSeed a n)

theorem radix_pos (a n : ℕ) : 0 < radix a n := by unfold radix; positivity

def clip (a n w : ℕ) : ℕ := w % radix a n

def word (a n w : ℕ) : FieldWord a n := ⟨clip a n w, Nat.mod_lt _ (radix_pos ..)⟩

def addWord (n u v : ℕ) : ℕ := clip a n (I.add (n,u,v))
def mulWord (n u v : ℕ) : ℕ := clip a n (I.mul (n,u,v))
def coeffWord (n : ℕ) (b : Bool) : ℕ := clip a n (I.coeff (n,b))
def zeroWord (n : ℕ) : ℕ := clip a n (I.zero n)
def generatorWord (n : ℕ) : ℕ := clip a n (I.generator n)

theorem clip_bound (a n u : ℕ) : clip a n u < radix a n :=
  Nat.mod_lt _ (radix_pos ..)

theorem clip_eq (a n u : ℕ) (hu : u < radix a n) : clip a n u = u :=
  Nat.mod_eq_of_lt hu

theorem size_le_of_lt {u a n : ℕ} (hu : u < radix a n) :
    u.size ≤ 2*halfSeed a n := Nat.size_le.mpr hu

theorem word_val (a n w : ℕ) (hw : w < radix a n) :
    (word a n w).val = w := clip_eq a n w hw

theorem code_apply_addWord (n : ℕ) (hn : 1 ≤ n) (u v : ℕ)
    (hu : u < radix a n) (hv : v < radix a n) :
    I.codeF n (word a n (I.addWord n u v)) =
      I.codeF n (word a n u) + I.codeF n (word a n v) := by
  have H := I.add_correct n hn (word a n u) (word a n v)
  rw [word_val _ _ _ hu, word_val _ _ _ hv] at H
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans H

theorem code_apply_mulWord (n : ℕ) (hn : 1 ≤ n) (u v : ℕ)
    (hu : u < radix a n) (hv : v < radix a n) :
    I.codeF n (word a n (I.mulWord n u v)) =
      I.codeF n (word a n u) * I.codeF n (word a n v) := by
  have H := I.mul_correct n hn (word a n u) (word a n v)
  rw [word_val _ _ _ hu, word_val _ _ _ hv] at H
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans H

theorem code_apply_coeffWord (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (j : Fin n) :
    I.codeF n (word a n (I.coeffWord n (x.val.testBit j.val))) =
      I.embed n (inputCode (I.codeK n) (halfSeed_pos ha n) x j) := by
  have H := I.coeff_correct n hn (x.val.testBit j.val)
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [word_val _ _ _ (show I.coeffWord n (x.val.testBit j.val) < radix a n from clip_bound ..)]
  change I.coeff (n,x.val.testBit j.val) % 2^(2*halfSeed a n) = _
  rw [H]
  congr 4
  apply Fin.ext
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have hl := Nat.mod_lt (x.val / 2^j.val) (by decide : 0 < 2)
  by_cases h : x.val / 2^j.val % 2 = 1
  · simp [h]
  · have h0 : x.val / 2^j.val % 2 = 0 := by omega
    simp [h0]

theorem code_apply_zeroWord (n : ℕ) (hn : 1 ≤ n) :
    I.codeF n (word a n (I.zeroWord n)) = 0 := by
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans (I.zero_correct n hn)

theorem code_apply_generatorWord (n : ℕ) (hn : 1 ≤ n) :
    I.codeF n (word a n (I.generatorWord n)) = I.embed n (I.primitive n) := by
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans (I.generator_correct n hn)

theorem native_halfSeed {α : Type} {enc : α ↪ List Bool} (a : ℕ) {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => halfSeed a (n x)) enc encUnary := by
  let hb := (binary_le' (const 1) (unary_to_binary.comp hn))
  have hm : ComputableTidilyInPolyTime (fun x => max 1 (n x)) enc encUnary := by
    apply (hb.ite_decide hn (const 1)).of_enc_eq
    intro x
    by_cases h : 1 ≤ n x
    · simp [h, max_eq_right h]
    · simp [h, max_eq_left (by omega : n x ≤ 1)]
  exact unary_mul.comp ((const a).prod
    (ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hm)))

private theorem native_radix {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => radix a (n x)) enc encNat := by
  exact binary_two_pow.comp (unary_mul.comp ((const 2).prod (native_halfSeed a hn)))

private theorem native_clip {α : Type} {enc : α ↪ List Bool} {n w : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hw : ComputableTidilyInPolyTime w enc encNat) :
    ComputableTidilyInPolyTime (fun x => clip a (n x) (w x)) enc encNat :=
  binary_mod' hw (native_radix hn)

private theorem native_fieldBin {α : Type} {enc : α ↪ List Bool} {n u v : α → ℕ}
    {f : FieldBinInput → ℕ} (hf : ComputableInPolyTime f encFieldBinInput encNat)
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hu : ComputableTidilyInPolyTime u enc encNat)
    (hv : ComputableTidilyInPolyTime v enc encNat) :
    ComputableTidilyInPolyTime (fun x => clip a (n x) (f (n x,u x,v x))) enc encNat :=
  native_clip hn (hf.tidy.comp (hn.prod (hu.prod hv)))

abbrev HornerInput := ℕ × ℕ × ℕ
abbrev encHornerInput : HornerInput ↪ List Bool := encPair encUnary (encPair encNat encNat)
abbrev HornerState := ℕ × ℕ
abbrev encHornerState : HornerState ↪ List Bool := encPair encUnary encNat

def hornerStep (p : HornerInput) (s : HornerState) : HornerState :=
  let (n,x,y) := p
  let j := s.1-1
  (j, I.addWord n (I.coeffWord n (x.testBit j)) (I.mulWord n s.2 y))

def horner (n x y : ℕ) : ℕ :=
  ((I.hornerStep (n,x,y))^[n] (n, I.zeroWord n)).2

theorem horner_bound (n x y : ℕ) : I.horner n x y < radix a n := by
  generalize n = j at ⊢
  cases j with
  | zero => exact clip_bound ..
  | succ t =>
    unfold horner
    rw [Function.iterate_succ_apply']
    exact clip_bound ..

theorem horner_polytime : ComputableTidilyInPolyTime
    (fun p : HornerInput => I.horner p.1 p.2.1 p.2.2) encHornerInput encNat := by
  let np : ComputableTidilyInPolyTime (fun p : HornerInput => p.1) encHornerInput encUnary := fst _ _
  let init : ComputableTidilyInPolyTime (fun p : HornerInput => (p.1,I.zeroWord p.1))
      encHornerInput encHornerState := np.prod (native_clip np (I.zero_native.tidy.comp np))
  let joint := encPair encHornerInput encHornerState
  let pars := fst encHornerInput encHornerState
  let state := snd encHornerInput encHornerState
  let n := pars.fst'
  let x := pars.snd'.fst'
  let y := pars.snd'.snd'
  let j := unary_sub.comp (state.fst'.prod (const 1))
  let bit := binary_testBit x j
  have hstep : ComputableTidilyInPolyTime (fun p : HornerInput × HornerState =>
      I.hornerStep p.1 p.2) joint encHornerState :=
    j.prod (native_fieldBin I.add_native n
      (native_clip n (I.coeff_native.tidy.comp (n.prod bit)))
      (native_fieldBin I.mul_native n state.snd' y))
  let size : HornerInput → ℕ := fun p => 2*p.1 + 1 + 2*halfSeed a p.1
  have hsize : PolyBounded (fun p => (encHornerInput p).length) size := by
    have hs := np.polyBounded
    have hc := (native_halfSeed a np).polyBounded
    apply ((hs.add hs).add (.const 1)).add (hc.add hc) |>.mono
    intro p
    dsimp [size]
    omega
  have hstates (p : HornerInput) (j : ℕ) : j ≤ p.1 →
      (encHornerState ((I.hornerStep p)^[j] (p.1,I.zeroWord p.1))).length ≤ size p := by
    have ht (j : ℕ) : ((I.hornerStep p)^[j] (p.1,I.zeroWord p.1)).1 ≤ p.1 ∧
        ((I.hornerStep p)^[j] (p.1,I.zeroWord p.1)).2 < radix a p.1 := by
      induction j with
      | zero => exact ⟨le_rfl, clip_bound ..⟩
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact ⟨(Nat.sub_le _ _).trans ih.1, clip_bound ..⟩
    have hj := ht j
    have hd := size_le_of_lt hj.2
    intro _
    simp only [encHornerState, length_encPair, encUnary_apply, List.length_replicate,
      encNat_apply, Nat.size_eq_bits_len]
    dsimp [size]
    omega
  exact (snd encUnary encNat).comp (iterateWith id' np init hstep hsize hstates)

theorem horner_correct (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (y : FieldWord a n) :
    I.codeF n (word a n (I.horner n x.val y.val)) =
      ((vectorPoly (inputCode (I.codeK n) (halfSeed_pos ha n) x)).map
        (I.embed n)).eval (I.codeF n y) := by
  let B := I.codeF n y
  let γ (j : ℕ) := I.codeF n (word a n (I.coeffWord n (x.val.testBit j)))
  let H (i : ℕ) := ((I.hornerStep (n,x.val,y.val))^[i] (n,I.zeroWord n))
  have hy : y.val < radix a n := y.isLt
  have hwy : word a n y.val = y := Fin.ext (word_val _ _ _ hy)
  have hH (i : ℕ) (hi : i ≤ n) :
      (H i).1 = n-i ∧ (H i).2 < radix a n ∧
      I.codeF n (word a n (H i).2) =
        ∑ j ∈ Finset.range i, γ (n-i+j) * B^j := by
    induction i with
    | zero => simpa only [H, Function.iterate_zero_apply, Nat.sub_zero, Finset.range_zero,
        Finset.sum_empty, true_and] using
        (show I.zeroWord n < radix a n ∧ _ from ⟨clip_bound .., I.code_apply_zeroWord n hn⟩)
    | succ i ih =>
      obtain ⟨hcounter, hwidth, heval⟩ := ih (by omega)
      have hstep : H (i+1) = I.hornerStep (n,x.val,y.val) (H i) := by
        simp only [H, Function.iterate_succ_apply']
      have hj : (H i).1-1 = n-(i+1) := by rw [hcounter]; omega
      rw [hstep]
      refine ⟨hj, clip_bound .., ?_⟩
      change I.codeF n (word a n (I.addWord n (I.coeffWord n (x.val.testBit ((H i).1-1)))
          (I.mulWord n (H i).2 y.val))) = _
      have hc : I.coeffWord n (x.val.testBit ((H i).1-1)) < radix a n := clip_bound ..
      have hm : I.mulWord n (H i).2 y.val < radix a n := clip_bound ..
      rw [I.code_apply_addWord n hn _ _ hc hm,
        I.code_apply_mulWord n hn _ _ hwidth hy, hwy, heval, hj,
        Finset.sum_range_succ', Finset.sum_mul]
      change γ (n-(i+1)) + (∑ j ∈ Finset.range i, γ (n-i+j) * B^j * B) =
        (∑ j ∈ Finset.range i, γ (n-(i+1)+(j+1)) * B^(j+1)) + _ 
      rw [add_comm, pow_zero, mul_one, Nat.add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj'
      have hidx : n - i + j = n - (i+1) + (j+1) := by omega
      rw [hidx, pow_succ, mul_assoc]
  have h := (hH n le_rfl).2.2
  dsimp [horner, H] at h ⊢
  rw [h, Nat.sub_self]
  simp_rw [zero_add]
  rw [vectorPoly, Polynomial.map_sum, Polynomial.eval_finsetSum]
  simp only [Polynomial.map_monomial, Polynomial.eval_monomial, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (· * B^j.val) (I.code_apply_coeffWord n hn x j)

end BinaryFieldArithmetic

end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open TimeSpaceMA.GUV Polynomial

/-- Inner product modulo two, with the bits indexed least significant first. -/
def hadamard {e : ℕ} (v u : Fin e → ZMod 2) : ZMod 2 := ∑ i, v i*u i

theorem hadamard_agreement_le {e : ℕ} {v w : Fin e → ZMod 2} (hvw : v ≠ w) :
    (Finset.univ.filter (fun u : Fin e → ZMod 2 => hadamard v u = hadamard w u)).card * 2 ≤ 2^e := by
  classical
  have hex : ∃ i, v i ≠ w i := by
    by_contra! hall
    exact hvw (funext hall)
  obtain ⟨i, hi⟩ := hex
  let C := Finset.univ.filter (fun u : Fin e → ZMod 2 => hadamard v u = hadamard w u)
  let flip (u : Fin e → ZMod 2) := Function.update u i (u i + 1)
  have hflip (u : Fin e → ZMod 2) : flip (flip u) = u := by
    funext j
    by_cases h : j = i
    · subst j
      have hh : (1:ZMod 2) + 1 = 0 := by decide
      simp [flip,add_assoc,hh]
    · simp [flip,Function.update_of_ne h]
  let F : (Fin e → ZMod 2) ↪ (Fin e → ZMod 2) := ⟨flip,Function.LeftInverse.injective hflip⟩
  have hdiff (u : Fin e → ZMod 2) :
      hadamard v (flip u) - hadamard w (flip u) =
      (hadamard v u - hadamard w u) + (v i-w i) := by
    unfold hadamard
    have hN (z : Fin e → ZMod 2) :
        (∑ j, z j * flip u j) = (∑ j, z j * u j)+z i := by
      calc
        _ = (∑ j ∈ (Finset.univ : Finset (Fin e)).erase i, z j * flip u j) +
            z i * flip u i := (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
        _ = (∑ j ∈ (Finset.univ : Finset (Fin e)).erase i, z j * u j) +
            z i * (u i+1) := by
          rw [show flip u i = u i+1 by simp [flip]]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          simp [flip,Function.update_of_ne (Finset.mem_erase.mp hj).1]
        _ = (∑ j, z j * u j)+z i := by
          rw [← Finset.sum_erase_add _ (fun j => z j * u j) (Finset.mem_univ i)]
          ring
    rw [hN v,hN w]
    ring
  have hdis : Disjoint C (C.map F) := by
    apply Finset.disjoint_left.mpr
    intro u hu hm
    obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hm
    change flip t = u at he
    subst u
    have h0 := sub_eq_zero.mpr ((Finset.mem_filter.mp hu).2)
    have h1 := sub_eq_zero.mpr ((Finset.mem_filter.mp ht).2)
    rw [hdiff t, h1, zero_add] at h0
    exact hi (sub_eq_zero.mp h0)
  have hcard := Finset.card_le_card (Finset.subset_univ (C ∪ C.map F))
  rw [Finset.card_union_of_disjoint hdis, Finset.card_map, Finset.card_univ] at hcard
  have heq : Fintype.card (Fin e → ZMod 2) = 2^e := by simp
  rw [heq] at hcard
  simpa [C,Nat.mul_two] using hcard

/-- A Reed–Solomon symbol is encoded as a binary Hadamard codeword. -/
def rsHad {F : Type} [Field F] {e : ℕ} (code : F ≃ (Fin e → ZMod 2))
    (p : F[X]) (ab : F × (Fin e → ZMod 2)) : ZMod 2 :=
  hadamard (code (p.eval ab.1)) ab.2

theorem rsHad_agreement {F : Type} [Field F] [Fintype F] {e : ℕ}
    (code : F ≃ (Fin e → ZMod 2)) {p q : F[X]} (hpq : p ≠ q) {b : ℕ}
    (hdeg : (p-q).natDegree ≤ b) :
    (Finset.univ.filter fun ab => rsHad code p ab = rsHad code q ab).card * 2 ≤
      (Fintype.card F + b)*2^e := by
  classical
  let R := Finset.univ.filter (fun a : F => p.eval a = q.eval a)
  have hR : R.card ≤ b := by
    have hEq : R = (p-q).roots.toFinset := by
      ext a
      simp [R, Polynomial.mem_roots (sub_ne_zero.mpr hpq), eval_sub, sub_eq_zero]
    rw [hEq]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hdeg)
  have hf : (Finset.univ.filter (fun ab => rsHad code p ab = rsHad code q ab)).card =
      ∑ a : F, (Finset.univ.filter (fun u : Fin e → ZMod 2 =>
        hadamard (code (p.eval a)) u = hadamard (code (q.eval a)) u)).card := by
    simp_rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    rfl
  rw [hf,Finset.sum_mul]
  have he : Fintype.card (Fin e → ZMod 2) = 2^e := by simp
  calc
    _ ≤ ∑ a : F, (2^e + if a ∈ R then 2^e else 0) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hr : a ∈ R
      · have h : p.eval a = q.eval a := (Finset.mem_filter.mp hr).2
        simp [h,hr,he,Nat.mul_two]
      · have h : p.eval a ≠ q.eval a := by simpa [R] using hr
        simpa [hr] using hadamard_agreement_le (fun h' => h (code.injective h'))
    _ = (Fintype.card F + R.card)*2^e := by
      rw [Nat.add_mul,Finset.sum_add_distrib,← Finset.sum_filter]
      simp [R]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_left hR _)


section CodedField

variable {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)

attribute [local instance] BinaryFieldArithmetic.fieldK BinaryFieldArithmetic.fieldF

def codeWidth (a n : ℕ) : ℕ := 4*halfSeed a n

noncomputable def rsPolynomial (n : ℕ) (_hn : 1 ≤ n) (x : Fin (2^n)) : (I.F n)[X] :=
  (vectorPoly (inputCode (I.codeK n) (halfSeed_pos ha n) x)).map (I.embed n)

private theorem rsPolynomial_coeff (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (j : Fin n) :
    (rsPolynomial I n hn x).coeff j.val =
      I.embed n (inputCode (I.codeK n) (halfSeed_pos ha n) x j) := by
  classical
  rw [rsPolynomial, coeff_map, vectorPoly, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have hne : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp [hne]
  · simp

private theorem rsPolynomial_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (rsPolynomial I n hn) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · let k : Fin n := ⟨j,hj⟩
    have he := congrArg (fun p : (I.F n)[X] => p.coeff k.val) h
    change (rsPolynomial I n hn x).coeff k.val = (rsPolynomial I n hn y).coeff k.val at he
    rw [rsPolynomial_coeff,rsPolynomial_coeff] at he
    have hEq := (I.codeK n).injective ((I.embed n).injective he)
    have hEq := congrArg Fin.val hEq
    change x.val/2^j%2 = y.val/2^j%2 at hEq
    simp only [Nat.testBit_eq_decide_div_mod_eq,hEq]
  · have hx := x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj))
    have hy := y.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj))
    rw [Nat.testBit_lt_two_pow hx,Nat.testBit_lt_two_pow hy]

private theorem rsPolynomial_degree (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) :
    (rsPolynomial I n hn x).natDegree ≤ n := by
  unfold rsPolynomial
  apply natDegree_map_le.trans
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans i.isLt.le

noncomputable def rsSymbolEquiv (n : ℕ) : I.F n ≃ (Fin (2*halfSeed a n) → ZMod 2) :=
  (I.codeF n).symm.trans (bitsEquiv (2*halfSeed a n))

private def seedSplit (d h : ℕ) : Fin (2^(d+h)) ≃ Fin (2^d) × Fin (2^h) :=
  (finCongr (pow_add 2 d h)).trans finProdFinEquiv.symm

noncomputable def rsSeedEquiv (n : ℕ) :
    Fin (2^(codeWidth a n)) ≃ I.F n × (Fin (2*halfSeed a n) → ZMod 2) :=
  let e := 2*halfSeed a n
  ((finCongr (show (2:ℕ)^codeWidth a n = 2^(e+e) by
    congr 1
    unfold codeWidth
    omega)).trans (seedSplit e e)).trans
      ((I.codeF n).prodCongr (bitsEquiv e))

noncomputable def rsCode (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (s : Fin (2^(codeWidth a n))) :
    Bool := decide ((rsHad (rsSymbolEquiv I n) (rsPolynomial I n hn x) (rsSeedEquiv I n s)).val = 1)

private theorem zmod_two_decide_eq_iff (x y : ZMod 2) :
    (decide (x.val = 1) = decide (y.val = 1)) ↔ x = y := by
  constructor
  · intro h
    apply ZMod.val_injective 2
    have hx := x.val_lt
    have hy := y.val_lt
    by_cases hz : x.val = 1
    · rw [decide_eq_true hz] at h
      have hh : y.val = 1 := by simpa using h.symm
      exact hz.trans hh.symm
    · have hy' : y.val ≠ 1 := by
        intro hyy
        simp [hz,hyy] at h
      omega
  · intro h
    rw [h]

theorem rsCode_agreement (n : ℕ) (hn : 1 ≤ n) (x y : Fin (2^n)) (hxy : x ≠ y) :
    2 * (Finset.univ.filter fun s => rsCode I n hn x s = rsCode I n hn y s).card ≤
      (2^(2*halfSeed a n)+n) * 2^(2*halfSeed a n) := by
  classical
  let Q : ℕ := 2^(2*halfSeed a n)
  let e := rsSeedEquiv I n
  let f := fun ab => rsHad (rsSymbolEquiv I n) (rsPolynomial I n hn x) ab =
    rsHad (rsSymbolEquiv I n) (rsPolynomial I n hn y) ab
  let F := I.F n
  let : Fintype F := Fintype.ofEquiv (Fin Q) (I.codeF n)
  have hF : Fintype.card F = Q := by
    rw [← Fintype.card_congr (I.codeF n),Fintype.card_fin]
  have hv := rsHad_agreement (rsSymbolEquiv I n) (fun h => hxy (rsPolynomial_injective I n hn h))
    (natDegree_sub_le_of_le (rsPolynomial_degree I n hn x) (rsPolynomial_degree I n hn y))
  simp only [max_self] at hv
  change (Finset.univ.filter f).card * 2 ≤ (Fintype.card F + n)*Q at hv
  rw [hF] at hv
  have hmap : ((Finset.univ.filter (fun s => rsCode I n hn x s = rsCode I n hn y s)).map e.toEmbedding) =
      Finset.univ.filter f := by
    ext ab
    have hs (s : Fin (2^(codeWidth a n))) :
        rsCode I n hn x s = rsCode I n hn y s ↔ f (e s) := by
      exact zmod_two_decide_eq_iff _ _
    constructor
    · intro hab
      obtain ⟨s,ht,he⟩ := Finset.mem_map.mp hab
      change e s = ab at he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ (hs _).mp (Finset.mem_filter.mp ht).2⟩
    · intro hab
      apply Finset.mem_map.mpr
      refine ⟨e.symm ab,Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hs _).mpr ?_⟩,
        e.apply_symm_apply _⟩
      simpa using (Finset.mem_filter.mp hab).2
  rw [← hmap,Finset.card_map] at hv
  simpa [Q,mul_comm] using hv


open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- A Reed–Solomon/Hadamard code bit. The high field block is the RS evaluation
point, and the low block is the independent Hadamard vector. -/
def rsCodeNat (p : ℕ × ℕ × ℕ) : ℕ :=
  let n := p.1
  let e := 2*halfSeed a n
  let base := 2^e
  let y := p.2.2 / base
  let v := I.horner n p.2.1 y
  Toeplitz.bit ((e,v,p.2.2 % base),0)

theorem rsCodeNat_polytime :
    ComputableInPolyTime (rsCodeNat I) BinaryFieldArithmetic.encHornerInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  have hn := fst encUnary (encPair encNat encNat)
  have hx := (snd encUnary (encPair encNat encNat)).fst'
  have hz := (snd encUnary (encPair encNat encNat)).snd'
  have he := unary_mul.comp ((const 2).prod (BinaryFieldArithmetic.native_halfSeed a hn))
  have hr := binary_two_pow.comp he
  have hy := binary_div' hz hr
  have hv := I.horner_polytime.comp (hn.prod (hx.prod hy))
  have hw := binary_mod' hz hr
  exact Toeplitz.bit_polytime.comp ((he.prod (hv.prod hw)).prod (const 0))

private theorem hadamard_bit {e : ℕ} (x y : Fin (2^e)) :
    Toeplitz.bit ((e,x.val,y.val),0) = (hadamard (bitsEquiv e x) (bitsEquiv e y)).val := by
  unfold Toeplitz.bit hadamard
  rw [Toeplitz.sum_range_map]
  simp only [zero_add, bitsEquiv_apply, unpackBits]
  rw [← ZMod.val_natCast 2]
  congr 1
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have hm (z : ℕ) : ((z % 2 : ℕ) : ZMod 2) = (z : ZMod 2) := by
    apply ZMod.val_injective 2
    simp [ZMod.val_natCast]
  simp only [hm]

theorem rsCodeNat_correct (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n))
    (s : Fin (2^(codeWidth a n))) :
    decide (rsCodeNat I (n,x.val,s.val) = 1) = rsCode I n hn x s := by
  let e := 2*halfSeed a n
  have hwidth : (2:ℕ)^codeWidth a n = 2^(e+e) := by
    congr 1
    unfold codeWidth
    omega
  let t := seedSplit e e (Fin.cast hwidth s)
  have ht0 : t.1.val = s.val / 2^e := rfl
  have ht1 : t.2.val = s.val % 2^e := rfl
  have hh := I.horner_correct n hn x t.1
  change I.codeF n (BinaryFieldArithmetic.word a n (I.horner n x.val t.1.val)) =
    (rsPolynomial I n hn x).eval (I.codeF n t.1) at hh
  have hval : ((I.codeF n).symm ((rsPolynomial I n hn x).eval (I.codeF n t.1))) =
      BinaryFieldArithmetic.word a n (I.horner n x.val t.1.val) := by rw [← hh, Equiv.symm_apply_apply]
  let v := BinaryFieldArithmetic.word a n (I.horner n x.val t.1.val)
  have hv : v.val = I.horner n x.val t.1.val :=
    BinaryFieldArithmetic.word_val a n _ (I.horner_bound n x.val t.1.val)
  have hb := hadamard_bit v t.2
  rw [hv,ht0,ht1] at hb
  unfold rsCodeNat rsCode rsHad
  change decide (Toeplitz.bit ((e,I.horner n x.val (s.val / 2^e),s.val % 2^e),0)=1) =
    decide ((hadamard (bitsEquiv e ((I.codeF n).symm
      ((rsPolynomial I n hn x).eval (I.codeF n t.1)))) (bitsEquiv e t.2)).val=1)
  rw [hb,hval]


end CodedField

/-- Choose one field width coefficient for all n and m≤n. The coefficient absorbs
the fixed desired extraction error; n times (4m/ε)^2 fits in the field cardinality. -/
theorem rsFieldWidth_exists (ε : ℝ) (hε : 0 < ε) : ∃ a : ℕ, 0 < a ∧
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ n → (n:ℝ) ≤
      (ε/(4*(m:ℝ)))^2 * (2:ℝ)^(2*halfSeed a n) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (16/ε^2)
  let a := M+3
  refine ⟨a,by dsimp [a]; omega,?_⟩
  intro n m hn hm hmn
  let s := n.size
  have hs : 1 ≤ s := Nat.size_pos.mpr hn
  have hn2n : (n:ℝ) ≤ (2:ℝ)^s := by
    exact_mod_cast (Nat.lt_size_self n).le
  have hM2n : (M:ℝ) ≤ (2:ℝ)^(M*s) := by
    have hN : M ≤ 2^(M*s) := (Nat.lt_two_pow_self (n := M)).le.trans
      (Nat.pow_le_pow_right (by decide) (by simpa using Nat.mul_le_mul_left M hs))
    exact_mod_cast hN
  have hM4n : (M:ℝ) * (n:ℝ)^3 ≤ (2:ℝ)^(M*s+3*s) := by
    rw [pow_add, Nat.mul_comm 3 s, pow_mul (2:ℝ) s 3]
    exact mul_le_mul hM2n (pow_le_pow_left₀ (Nat.cast_nonneg _) hn2n 3)
      (by positivity) (by positivity)
  have hW : M*s+3*s ≤ 2*halfSeed a n := by
    simp only [halfSeed, max_eq_right hn, a, Nat.add_mul, s]
    omega
  have hBig : (M:ℝ)*(n:ℝ)^3 ≤ (2:ℝ)^(2*halfSeed a n) :=
    hM4n.trans (pow_le_pow_right₀ (by norm_num) hW)
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have hM' := (div_lt_iff₀ hε2).1 hM
  have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hn' : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have htmp1 : 16*(m:ℝ)^2*(n:ℝ) ≤ 16*(n:ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm'.le hmn' 2) hn'
    nlinarith
  have htmp2 : 16*(n:ℝ)^3 ≤ (M:ℝ)*(n:ℝ)^3*ε^2 := by
    have h := mul_le_mul_of_nonneg_right hM'.le (by positivity : 0 ≤ (n:ℝ)^3)
    nlinarith
  have htmp3 : 16*(m:ℝ)^2*(n:ℝ) ≤ ε^2*(2:ℝ)^(2*halfSeed a n) := by
    have hh := mul_le_mul_of_nonneg_left hBig hε2.le
    rw [mul_comm (ε^2) ((M:ℝ)*(n:ℝ)^3)] at hh
    exact htmp1.trans (htmp2.trans hh)
  rw [div_pow, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (4*(m:ℝ))^2)).2
  nlinarith only [htmp3]


/-- The code coordinate accepts a little-endian weak-design word. -/
noncomputable def rrvCode {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)
    (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n))
    (s : Fin (codeWidth a n) → Bool) : Bool :=
  rsCode I n hn x (Cslib.BitString.equivFin _ s)

theorem rrvCodeNat_correct {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)
    (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (s : Fin (codeWidth a n) → Bool) :
    decide (rsCodeNat I (n,x.val,(Cslib.BitString.equivFin _ s).val) = 1) =
      rrvCode I n hn x s := rsCodeNat_correct I n hn x _

/-- The RS/Hadamard code admits only a small list of candidates agreeing with any
given center on a one-half plus η fraction of its coordinates. -/
theorem rrvCode_list {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)
    (n : ℕ) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η)
    (hwidth : (n:ℝ) ≤ η^2 * (2:ℝ)^(2*halfSeed a n))
    (g : (Fin (codeWidth a n) → Bool) → Bool)
    (B : Finset (Fin (2^n)))
    (hcenter : ∀ x ∈ B, (1/2+η)*(Fintype.card (Fin (codeWidth a n) → Bool) : ℝ) ≤
      ((Finset.univ.filter fun s => rrvCode I n hn x s = g s).card : ℝ)) :
    (B.card : ℝ) ≤ 1/(3*η^2) := by
  classical
  apply hamming_list_size (rrvCode I n hn) g B hη (by simp) _ hcenter
  intro x _ y _ hxy
  let e := Cslib.BitString.equivFin (codeWidth a n)
  let R := Finset.univ.filter (fun s => rrvCode I n hn x s = rrvCode I n hn y s)
  let S := Finset.univ.filter (fun s => rsCode I n hn x s = rsCode I n hn y s)
  have heq : R.map e.toEmbedding = S := by
    ext q
    constructor
    · intro hq
      obtain ⟨s,hs,he⟩ := Finset.mem_map.mp hq
      change e s = q at he
      have hh : rsCode I n hn x (e s) = rsCode I n hn y (e s) := (Finset.mem_filter.mp hs).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ hh⟩
    · intro hq
      have hq' := (Finset.mem_filter.mp hq).2
      refine Finset.mem_map.mpr ⟨e.symm q, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
        e.apply_symm_apply _⟩
      change rsCode I n hn x (e (e.symm q)) = rsCode I n hn y (e (e.symm q))
      simpa using hq'
  have hcard : R.card = S.card := by rw [← heq,Finset.card_map]
  have hc := rsCode_agreement I n hn x y hxy
  change 2*S.card ≤ _ at hc
  let q : ℝ := (2:ℝ)^(2*halfSeed a n)
  have hReal : 2 * (S.card:ℝ) ≤ (q + n)*q := by
    dsimp [q]
    exact_mod_cast hc
  have hU : (Fintype.card (Fin (codeWidth a n) → Bool) : ℝ) = q*q := by
    rw [Fintype.card_congr e,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
    congr 1
    unfold codeWidth
    omega
  have hmul := mul_le_mul_of_nonneg_right hwidth (by positivity : 0 ≤ q)
  change (R.card:ℝ) ≤ _
  rw [hcard,hU]
  nlinarith only [hReal, hmul]

end TimeSpaceMA.RRV


open scoped BigOperators

namespace TimeSpaceMA.RRV

abbrev Bits (n : ℕ) := Fin n → Bool

def splice {m : ℕ} (i : ℕ) (a b : Bits m) : Bits m :=
  fun j => if j.val < i then a j else b j

def fixedBit {m : ℕ} (i : Fin m) (a : Bits m) (b : Bool) : Bits m :=
  Function.update a i b

def toggle {m : ℕ} (i : Fin m) (a : Bits m) : Bits m :=
  fixedBit i a (!a i)

theorem toggle_toggle {m : ℕ} (i : Fin m) (a : Bits m) : toggle i (toggle i a) = a := by
  funext j
  by_cases h : j = i
  · subst j
    simp [toggle, fixedBit]
  · simp [toggle, fixedBit, Function.update_of_ne h]

def toggleEquiv {m : ℕ} (i : Fin m) : Bits m ≃ Bits m :=
  (Function.Involutive.toPerm (toggle i) (toggle_toggle i))

private theorem splice_succ_eq {m : ℕ} (i : Fin m) (a b : Bits m) :
    splice (i.val+1) a b = fixedBit i (splice i.val a b) (a i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [splice, fixedBit]
  · have ht : j.val < i.val+1 ↔ j.val < i.val := by
      have hh : j.val ≠ i.val := fun he => h (Fin.ext he)
      omega
    simp [splice, fixedBit, Function.update_of_ne h, ht]

noncomputable def score {m d : ℕ} (T : Bits d × Bits m → Bool)
    (i : Fin m) (y : Bits d) (a r : Bits m) : ℝ :=
  let b := splice i.val a r
  (if T (y, fixedBit i b (a i)) then 1 else 0) -
    (if T (y, fixedBit i b (!a i)) then 1 else 0)

noncomputable def predictor {m d : ℕ} (T : Bits d × Bits m → Bool)
    (i : Fin m) (y : Bits d) (b : Bits m) (coin : Bool) : Bool :=
  if T (y,fixedBit i b true) = T (y,fixedBit i b false) then coin
  else T (y,fixedBit i b true)

private theorem score_eq_prediction {m d : ℕ} (T : Bits d × Bits m → Bool)
    (i : Fin m) (y : Bits d) (a r : Bits m) :
    score T i y a r =
      (∑ c : Bool, if predictor T i y (splice i.val a r) c = a i then (1 : ℝ) else 0) - 1 := by
  classical
  cases ha : a i <;>
    cases ht : T (y, fixedBit i (splice i.val a r) true) <;>
    cases hf : T (y, fixedBit i (splice i.val a r) false) <;>
    norm_num [score,predictor,ha,ht,hf]

variable {X : Type} [Fintype X]
variable {d m : ℕ}
variable (eval : X → Bits d → Bits m) (p : X → ℝ)

noncomputable def stage (T : Bits d × Bits m → Bool) (i : ℕ) : ℝ :=
  ∑ x : X, p x * (∑ y : Bits d, ∑ r : Bits m,
    if T (y,splice i (eval x y) r) then (1:ℝ) else 0) /
    (Fintype.card (Bits d) * Fintype.card (Bits m) : ℝ)

noncomputable def strongAdvantage (T : Bits d × Bits m → Bool) (i : Fin m)
    (r : Bits m) (coin : Bool) : ℝ :=
  (∑ x : X, p x * (∑ y : Bits d,
    if predictor T i y (splice i.val (eval x y) r) coin = (eval x y) i then (1:ℝ) else 0)) /
    (Fintype.card (Bits d) : ℝ) - 1/2

private theorem score_mean (T : Bits d × Bits m → Bool) (i : Fin m)
    (y : Bits d) (a : Bits m) :
    (∑ r : Bits m, score T i y a r) = 2 * (∑ r : Bits m,
      ((if T (y,splice (i.val+1) a r) then (1:ℝ) else 0) -
      (if T (y,splice i.val a r) then (1:ℝ) else 0))) := by
  classical
  let A (r : Bits m) : ℝ := if T (y,splice (i.val+1) a r) then 1 else 0
  let B (r : Bits m) : ℝ := if T (y,splice i.val a r) then 1 else 0
  let O (r : Bits m) : ℝ := if T (y,fixedBit i (splice i.val a r) (!a i)) then 1 else 0
  have hb (r : Bits m) : B r + B (toggle i r) = A r + O r := by
    unfold A B O
    rw [splice_succ_eq]
    have hfix (b : Bool) : splice i.val a (fixedBit i r b) = fixedBit i (splice i.val a r) b := by
      funext j
      by_cases h : j = i
      · subst j; simp [splice, fixedBit]
      · simp only [fixedBit, Function.update_of_ne h, splice]
    have horig : fixedBit i (splice i.val a r) (r i) = splice i.val a r := by
      funext j
      by_cases h : j = i
      · subst j; simp [fixedBit,splice]
      · simp [fixedBit,Function.update_of_ne h]
    rw [toggle, hfix, ← horig]
    cases a i <;> cases r i <;> simp [fixedBit, Function.update_idem] <;> ac_rfl
  have he := Fintype.sum_equiv (toggleEquiv i) (fun r => B (toggle i r)) B (by intro r; rfl)
  have hh := Finset.sum_congr (rfl : (Finset.univ : Finset (Bits m)) = Finset.univ)
    (fun r _ => hb r)
  simp only [Finset.sum_add_distrib, he] at hh
  simp only [score, ← splice_succ_eq]
  change (∑ r, (A r - O r)) = 2 * (∑ r, (A r - B r))
  simp only [Finset.sum_sub_distrib]
  linarith

private theorem stage_difference (T : Bits d × Bits m → Bool) (i : Fin m) (hp : ∑ x, p x = 1) :
    (∑ r : Bits m, ∑ c : Bool, strongAdvantage eval p T i r c) =
      2 * (Fintype.card (Bits m) : ℝ) * (stage eval p T (i.val+1) - stage eval p T i.val) := by
  classical
  let N : ℝ := Fintype.card (Bits d)
  let M : ℝ := Fintype.card (Bits m)
  have hN : 0 < N := by
    dsimp [N, Bits]
    simp
  have hM : 0 < M := by
    dsimp [M, Bits]
    simp
  let H (r : Bits m) (c : Bool) (x : X) (y : Bits d) : ℝ :=
    if predictor T i y (splice i.val (eval x y) r) c = (eval x y) i then 1 else 0
  let A (x : X) (y : Bits d) (r : Bits m) := score T i y (eval x y) r
  have hsum : (∑ r : Bits m, ∑ c : Bool, ∑ x : X, ∑ y : Bits d, p x * H r c x y) =
     (∑ x : X, p x * (∑ y : Bits d, ∑ r : Bits m, A x y r)) + N*M := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Bits m)))]
    conv_lhs => enter [2,c]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => enter [2,x]; rw [Finset.sum_comm]
    conv_lhs => enter [2,x,2,r]; rw [Finset.sum_comm]
    conv_lhs => enter [2,x]; rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have he (x : X) (y : Bits d) (r : Bits m) :
        (∑ c : Bool, H r c x y) = A x y r + 1 := by
      have hh := score_eq_prediction T i y (eval x y) r
      change A x y r = (∑ c, H r c x y) - 1 at hh
      linarith
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, mul_one, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
  have hA (x : X) (y : Bits d) := score_mean T i y (eval x y)
  unfold stage strongAdvantage
  change (∑ r : Bits m, ∑ c : Bool, ((∑ x : X, p x * (∑ y : Bits d, H r c x y)) / N - 1/2)) =
    2*M * ((∑ x : X, p x * (∑ y : Bits d, ∑ r : Bits m,
      if T (y,splice (i.val+1) (eval x y) r) then (1:ℝ) else 0) / (N*M)) -
      (∑ x : X, p x * (∑ y : Bits d, ∑ r : Bits m,
      if T (y,splice i.val (eval x y) r) then (1:ℝ) else 0) / (N*M)))
  simp_rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.mul_sum]
  change (∑ r : Bits m, ∑ c : Bool, ∑ x : X, ∑ y : Bits d, p x * H r c x y) / N -
    (∑ _r : Bits m, ∑ _c : Bool, (1:ℝ)) / 2 = _
  rw [hsum]
  simp_rw [A, hA, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  simp only [M, Finset.sum_sub_distrib, mul_sub]
  ring_nf
  simp only [Finset.sum_mul]

theorem strongEvents_of_predictor (hp : ∑ x, p x = 1) (ε : ℝ)
    (h : ∀ (T : Bits d × Bits m → Bool) (i : Fin m) (r : Bits m) (coin : Bool),
      strongAdvantage eval p T i r coin ≤ ε) :
    WeightedExtractorEvents (fun x y => (y,eval x y)) p (m*ε) := by
  classical
  intro U
  let T (w : Bits d × Bits m) := decide (w ∈ U)
  let N : ℝ := Fintype.card (Bits d)
  let M : ℝ := Fintype.card (Bits m)
  have hN : 0 < N := by simp [N, Bits]
  have hM : 0 < M := by simp [M, Bits]
  have hstep (i : ℕ) (hi : i < m) : stage eval p T (i+1) - stage eval p T i ≤ ε := by
    let j : Fin m := ⟨i,hi⟩
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Bits m)))
      (fun r _ => Finset.sum_le_sum (s := (Finset.univ : Finset Bool)) (fun c _ => h T j r c))
    rw [stage_difference eval p T j hp] at hs
    have hc : (∑ _r : Bits m, ∑ _c : Bool, ε) = 2*M*ε := by
      simp [M, nsmul_eq_mul]; ring
    rw [hc] at hs
    exact le_of_mul_le_mul_left hs (by positivity : 0 < 2*M)
  have htotal : stage eval p T m - stage eval p T 0 ≤ (m:ℝ)*ε := by
    rw [← Finset.sum_range_sub (stage eval p T) m]
    apply (Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))).trans_eq
    simp [nsmul_eq_mul]
  have hzero : stage eval p T 0 = (U.card : ℝ)/(N*M) := by
    unfold stage
    simp_rw [show ∀ a b : Bits m, splice 0 a b = b by intro a b; funext j; simp [splice]]
    rw [← Fintype.sum_prod_type (fun w : Bits d × Bits m => if T w then (1:ℝ) else 0), ← Finset.sum_div]
    rw [← Finset.sum_mul, hp, one_mul]
    have hcount := Finset.card_filter (s := (Finset.univ : Finset (Bits d × Bits m)))
      (fun w => w ∈ U)
    rw [show (Finset.univ.filter (· ∈ U)) = U by ext z; simp] at hcount
    have hh : (U.card : ℝ) = ∑ w : Bits d × Bits m, if w ∈ U then (1 : ℝ) else 0 := by
      exact_mod_cast hcount
    simp only [T, decide_eq_true_eq, hh, N, M]
  have hfull : stage eval p T m = weightedExtractionProbability (fun x y => (y,eval x y)) p U := by
    unfold stage weightedExtractionProbability
    have hsplice (a b : Bits m) : splice m a b = a := by
      funext j
      simp [splice, j.isLt]
    simp only [hsplice, T, decide_eq_true_eq, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    field_simp
  rw [hzero,hfull] at htotal
  exact (by simpa only [Fintype.card_prod, Nat.cast_mul] using htotal)

end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open Classical

variable {X : Type} [Fintype X]
variable {l d m : ℕ}
variable (p : X → ℝ)

abbrev Design (l d m : ℕ) := Fin m → (Fin l ↪ Fin d)

def nw (S : Design l d m) (code : X → Bits l → Bool) (x : X) (y : Bits d) : Bits m :=
  fun j => code x (y ∘ S j)

def Inside (e : Fin l ↪ Fin d) (j : Fin d) : Prop := j ∈ Set.range e
abbrev Outside (e : Fin l ↪ Fin d) := { j : Fin d // ¬Inside e j } → Bool

noncomputable def restrictSeedSplit (e : Fin l ↪ Fin d) : Bits d ≃ Bits l × Outside e :=
  (Equiv.piEquivPiSubtypeProd (Inside e) (fun _ => Bool)).trans
    ((Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm (Equiv.refl Bool)).prodCongr (Equiv.refl _))

theorem restrictSeedSplit_inside (e : Fin l ↪ Fin d) (y : Bits d) (j : Fin l) :
    (restrictSeedSplit e y).1 j = y (e j) := rfl

theorem restrictSeedSplit_outside (e : Fin l ↪ Fin d) (y : Bits d) (j : { j : Fin d // ¬Inside e j }) :
    (restrictSeedSplit e y).2 j = y j.val := rfl

theorem seedJoin_inside (e : Fin l ↪ Fin d) (z : Bits l) (w : Outside e) (j : Fin l) :
    (restrictSeedSplit e).symm (z,w) (e j) = z j := by
  have he := congrArg (fun p : Bits l × Outside e => p.1 j) ((restrictSeedSplit e).apply_symm_apply (z,w))
  exact (restrictSeedSplit_inside e _ j).symm.trans he

theorem seedJoin_outside (e : Fin l ↪ Fin d) (z : Bits l) (w : Outside e)
    (j : { j : Fin d // ¬Inside e j }) :
    (restrictSeedSplit e).symm (z,w) j.val = w j := by
  have he := congrArg (fun p : Bits l × Outside e => p.2 j) ((restrictSeedSplit e).apply_symm_apply (z,w))
  exact (restrictSeedSplit_outside e _ j).symm.trans he

abbrev OverlapBits (S : Design l d m) (i j : Fin m) :=
  { u : Fin l // Inside (S i) (S j u) } → Bool

abbrev Earlier (i : Fin m) := { j : Fin m // j < i }

abbrev RestrictionTable (S : Design l d m) (i : Fin m) :=
  (j : Earlier i) → OverlapBits S i j.val → Bool

noncomputable def overlapWidth (S : Design l d m) (i j : Fin m) : ℕ :=
  (Finset.univ.filter (fun u : Fin l => Inside (S i) (S j u))).card

theorem card_overlap (S : Design l d m) (i j : Fin m) :
    Fintype.card { u : Fin l // Inside (S i) (S j u) } = overlapWidth S i j := by
  exact Fintype.card_of_subtype _ (by intro u; simp)

theorem card_restrictionTable (S : Design l d m) (i : Fin m) :
    Fintype.card (RestrictionTable S i) =
      2^(∑ j : Earlier i, 2^overlapWidth S i j.val) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_bool,
    card_overlap, Finset.prod_pow_eq_pow_sum]

noncomputable def fillRestricted (S : Design l d m) (i j : Fin m) (w : Outside (S i))
    (b : OverlapBits S i j) : Bits l :=
  fun u => if h : Inside (S i) (S j u) then b ⟨u,h⟩ else w ⟨S j u,h⟩

noncomputable def takeOverlap (S : Design l d m) (i j : Fin m) (z : Bits l) (w : Outside (S i)) :
    OverlapBits S i j := fun u => (restrictSeedSplit (S i)).symm (z,w) (S j u.val)

theorem fillRestricted_takeOverlap (S : Design l d m) (i j : Fin m) (z : Bits l)
    (w : Outside (S i)) :
    fillRestricted S i j w (takeOverlap S i j z w) = (restrictSeedSplit (S i)).symm (z,w) ∘ S j := by
  funext u
  by_cases h : Inside (S i) (S j u)
  · simp [fillRestricted, takeOverlap, h]
  · simp only [fillRestricted, dif_neg h, Function.comp_apply]
    exact (seedJoin_outside (S i) z w ⟨S j u,h⟩).symm

noncomputable def tableOf (S : Design l d m) (i : Fin m) (w : Outside (S i))
    (code : X → Bits l → Bool) (x : X) : RestrictionTable S i :=
  fun j b => code x (fillRestricted S i j.val w b)

noncomputable def decodePredictor (S : Design l d m) (i : Fin m) (w : Outside (S i))
    (T : Bits d × Bits m → Bool) (r : Bits m) (coin : Bool) (L : RestrictionTable S i) :
    Bits l → Bool :=
  fun z =>
    let b : Bits m := fun j => if h : j < i then L ⟨j,h⟩ (takeOverlap S i j z w) else r j
    predictor T i ((restrictSeedSplit (S i)).symm (z,w)) b coin

omit [Fintype X] in
theorem decodePredictor_tableOf (S : Design l d m) (i : Fin m) (w : Outside (S i))
    (T : Bits d × Bits m → Bool) (r : Bits m) (coin : Bool)
    (code : X → Bits l → Bool) (x : X) (z : Bits l) :
    let y := (restrictSeedSplit (S i)).symm (z,w)
    decodePredictor S i w T r coin (tableOf S i w code x) z =
      predictor T i y (splice i.val (nw S code x y) r) coin := by
  intro y
  unfold decodePredictor
  dsimp only
  apply congrArg (fun f => predictor T i y f coin)
  funext j
  dsimp [splice,nw,tableOf,y]
  by_cases hj : j < i
  · have hval : j.val < i.val := hj
    simp [hj,hval,fillRestricted_takeOverlap]
  · have hval : ¬j.val < i.val := hj
    simp [hj,hval]

noncomputable def agreement (code : X → Bits l → Bool) (x : X) (P : Bits l → Bool) : ℝ :=
  (∑ z : Bits l, if P z = code x z then (1:ℝ) else 0) / Fintype.card (Bits l)

def HasListBound (code : X → Bits l → Bool) (η L : ℝ) : Prop :=
  ∀ P : Bits l → Bool, ∀ B : Finset X,
    (∀ x ∈ B, 1/2+η ≤ agreement code x P) → (B.card : ℝ) ≤ L

omit [Fintype X] in
theorem agreement_nonneg (code : X → Bits l → Bool) (x : X) (P : Bits l → Bool) :
    0 ≤ agreement code x P := by
  unfold agreement
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun z _ => by split <;> norm_num)

omit [Fintype X] in
theorem agreement_le_one (code : X → Bits l → Bool) (x : X) (P : Bits l → Bool) :
    agreement code x P ≤ 1 := by
  unfold agreement
  have hp : 0 < (Fintype.card (Bits l) : ℝ) := by simp
  apply (div_le_iff₀ hp).mpr
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Bits l)))
    (g := fun _ => (1 : ℝ)) (f := fun z => if P z = code x z then 1 else 0)
    (fun z _ => by split <;> norm_num)
  simpa using h

private theorem bad_card (S : Design l d m) (i : Fin m) (w : Outside (S i))
    (code : X → Bits l → Bool) (T : Bits d × Bits m → Bool) (r : Bits m) (coin : Bool)
    (η L : ℝ) (hlist : HasListBound code η L) :
    let B : Finset X := Finset.univ.filter (fun x =>
      1/2+η ≤ agreement code x (decodePredictor S i w T r coin (tableOf S i w code x)))
    (B.card : ℝ) ≤ (Fintype.card (RestrictionTable S i) : ℝ)*L := by
  intro B
  let D (P : RestrictionTable S i) := (Finset.univ : Finset X).filter (fun x =>
    1/2+η ≤ agreement code x (decodePredictor S i w T r coin P))
  have hsub : B ⊆ (Finset.univ : Finset (RestrictionTable S i)).biUnion D := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨tableOf S i w code x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (Finset.mem_filter.mp hx).2
  have hcount := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ (∑ P : RestrictionTable S i, ((D P).card : ℝ)) := by exact_mod_cast hcount
    _ ≤ ∑ _P : RestrictionTable S i, L := Finset.sum_le_sum (fun P _ => hlist
      (decodePredictor S i w T r coin P) (D P) (fun x hx => (Finset.mem_filter.mp hx).2))
    _ = _ := by simp [nsmul_eq_mul]

private theorem avgAgreement_bound {K : ℕ}
    (hp : ∑ x : X, p x = 1)
    (hcap : ∀ x : X, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K)
    (S : Design l d m) (i : Fin m) (w : Outside (S i))
    (code : X → Bits l → Bool) (T : Bits d × Bits m → Bool) (r : Bits m) (coin : Bool)
    (η L : ℝ) (hη : 0 ≤ η) (hlist : HasListBound code η L) :
    (∑ x : X, p x * agreement code x (decodePredictor S i w T r coin (tableOf S i w code x))) ≤
      1/2+η + (Fintype.card (RestrictionTable S i) : ℝ)*L / (2:ℝ)^K := by
  let v (x : X) := agreement code x (decodePredictor S i w T r coin (tableOf S i w code x))
  let B := (Finset.univ : Finset X).filter (fun x => 1/2+η ≤ v x)
  have hb (x : X) : v x ≤ 1/2+η + if x ∈ B then (1:ℝ) else 0 := by
    by_cases h : x ∈ B
    · rw [if_pos h]
      have H := agreement_le_one code x (decodePredictor S i w T r coin (tableOf S i w code x))
      dsimp [v] at *
      linarith
    · rw [if_neg h, add_zero]
      exact (lt_of_not_ge (fun hh => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))).le
  have hB : ∑ x ∈ B, p x ≤ (Fintype.card (RestrictionTable S i) : ℝ)*L / (2:ℝ)^K := by
    have hcnt := bad_card S i w code T r coin η L hlist
    calc
      _ ≤ ∑ _x ∈ B, 1/(2:ℝ)^K := Finset.sum_le_sum (fun x _ => (hcap x).2)
      _ = (B.card : ℝ)/(2:ℝ)^K := by simp [nsmul_eq_mul]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hcnt (by positivity)
  change ∑ x, p x * v x ≤ _
  calc
    _ ≤ ∑ x : X, p x * (1/2+η + if x ∈ B then (1:ℝ) else 0) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hb x) (hcap x).1)
    _ = 1/2+η + ∑ x ∈ B, p x := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul, mul_ite,
        mul_one, mul_zero, ← Finset.sum_filter]
      rw [show Finset.univ.filter (· ∈ B) = B by ext x; simp]
    _ ≤ _ := add_le_add_right hB _

theorem strongAdvantage_of_list {K : ℕ}
    (hp : ∑ x : X, p x = 1)
    (hcap : ∀ x : X, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K)
    (S : Design l d m) (i : Fin m)
    (code : X → Bits l → Bool) (T : Bits d × Bits m → Bool) (r : Bits m) (coin : Bool)
    (η L : ℝ) (hη : 0 ≤ η) (hlist : HasListBound code η L) :
    strongAdvantage (nw S code) p T i r coin ≤
      η + (Fintype.card (RestrictionTable S i) : ℝ)*L / (2:ℝ)^K := by
  let e := restrictSeedSplit (S i)
  let N : ℝ := Fintype.card (Bits l)
  let M : ℝ := Fintype.card (Outside (S i))
  have hN : 0 < N := by simp [N]
  have hM : 0 < M := by simp [M]
  have hcard : (Fintype.card (Bits d) : ℝ) = N*M := by
    have h := Fintype.card_congr e
    rw [Fintype.card_prod] at h
    dsimp [N,M]
    exact_mod_cast h
  let v (x : X) (w : Outside (S i)) : ℝ :=
    agreement code x (decodePredictor S i w T r coin (tableOf S i w code x))
  have hsum (x : X) :
      (∑ y : Bits d,
        if predictor T i y (splice i.val (nw S code x y) r) coin = nw S code x y i then (1:ℝ) else 0)
      = (∑ w : Outside (S i), v x w) * N := by
    let f (y : Bits d) : ℝ :=
      if predictor T i y (splice i.val (nw S code x y) r) coin = nw S code x y i then 1 else 0
    let g (z : Bits l) (w : Outside (S i)) : ℝ :=
      if decodePredictor S i w T r coin (tableOf S i w code x) z = code x z then 1 else 0
    have hval (z : Bits l) (w : Outside (S i)) : f (e.symm (z,w)) = g z w := by
      unfold f g
      rw [decodePredictor_tableOf]
      have hword : (e.symm (z,w)) ∘ S i = z := funext (seedJoin_inside (S i) z w)
      simp only [nw, hword, e]
    change ∑ y, f y = _
    rw [Fintype.sum_equiv e f (fun t => g t.1 t.2) (fun y => by
      have hh := hval (e y).1 (e y).2
      simpa using hh), Fintype.sum_prod_type, Finset.sum_comm]
    have hh (w : Outside (S i)) : (∑ z : Bits l, g z w) = v x w * N := by
      change (∑ z : Bits l, g z w) = ((∑ z : Bits l, g z w)/N)*N
      field_simp
    simp_rw [hh, Finset.sum_mul]
  have hscore : strongAdvantage (nw S code) p T i r coin =
      (∑ w : Outside (S i), ∑ x : X, p x * v x w) / M - 1/2 := by
    unfold strongAdvantage
    simp only [hsum, hcard]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hs : (∑ x : X, p x * ∑ w : Outside (S i), v x w) =
        ∑ w : Outside (S i), ∑ x : X, p x * v x w := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hs]
    field_simp
  rw [hscore]
  let E : ℝ := 1/2+η+(Fintype.card (RestrictionTable S i) : ℝ)*L/(2:ℝ)^K
  have hh (w : Outside (S i)) : (∑ x, p x * v x w) ≤ E :=
    avgAgreement_bound p hp hcap S i w code T r coin η L hη hlist
  have hAvg := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Outside (S i)))) => hh w)
  rw [Finset.sum_const, nsmul_eq_mul] at hAvg
  have h' := (div_le_iff₀ hM).mpr (hAvg.trans_eq (mul_comm _ _))
  have h'' : (∑ w : Outside (S i), ∑ x : X, p x * v x w)/M ≤ E := h'
  dsimp [E] at h''
  linarith

/-- Seeded NW extraction from one list-decodable binary code and a weak design.
Freezing the seed outside the tested row before counting tables leaves only the
weak-overlap budget to pay in the reconstruction bound. -/
theorem strongNW_of_list {K : ℕ}
    (hp : ∑ x : X, p x = 1) (hcap : ∀ x : X, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K)
    (S : Design l d m) (code : X → Bits l → Bool)
    (η L ε : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hlist : HasListBound code η L)
    (hdesign : ∀ i : Fin m, (∑ j : Earlier i, 2^overlapWidth S i j.val) ≤ m-1)
    (he : (m:ℝ)*(η + ((2:ℝ)^(m-1)*L)/(2:ℝ)^K) ≤ ε) :
    WeightedExtractorEvents (fun x y => (y,nw S code x y)) p ε := by
  have h := strongEvents_of_predictor (nw S code) p hp
    (η + ((2:ℝ)^(m-1)*L)/(2:ℝ)^K) (fun T i r coin => by
    apply (strongAdvantage_of_list p hp hcap S i code T r coin η L hη hlist).trans
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hL
    rw [card_restrictionTable, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (hdesign i))
  intro U
  exact (h U).trans he

omit [Fintype X] in
theorem hasListBound_of_counts (code : X → Bits l → Bool) (η L : ℝ)
    (h : ∀ P : Bits l → Bool, ∀ B : Finset X,
      (∀ x ∈ B, (1/2+η)*(Fintype.card (Bits l):ℝ) ≤
        (((Finset.univ : Finset (Bits l)).filter (fun z => code x z = P z)).card : ℝ)) →
      (B.card:ℝ) ≤ L) : HasListBound code η L := by
  intro P B hb
  apply h P B
  intro x hx
  have H := hb x hx
  unfold agreement at H
  apply ((le_div_iff₀ (by simp : 0 < (Fintype.card (Bits l):ℝ))).mp H).trans_eq
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hz : code x z = P z <;> simp [hz, eq_comm]

end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open Classical

theorem overlapWidth_eq_inter {l d m : ℕ} (S : Design l d m) (i j : Fin m) :
    overlapWidth S i j = ((Finset.univ.map (S i)) ∩ (Finset.univ.map (S j))).card := by
  unfold overlapWidth
  let A := Finset.univ.filter (fun u : Fin l => Inside (S i) (S j u))
  suffices heq : A.map (S j) = (Finset.univ.map (S i)) ∩ (Finset.univ.map (S j)) by
    rw [← heq, Finset.card_map]
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, Finset.mem_inter, true_and, A, Finset.mem_filter,
    Inside, Set.mem_range]
  constructor
  · rintro ⟨u, ⟨v,hv⟩,rfl⟩
    exact ⟨⟨v,hv⟩,⟨u,rfl⟩⟩
  · rintro ⟨⟨v,hv⟩,⟨u,rfl⟩⟩
    exact ⟨u,⟨v,hv⟩,rfl⟩

def earlierEquiv {m : ℕ} (i : Fin m) : Earlier i ≃ Fin i.val where
  toFun j := ⟨j.val.val,j.property⟩
  invFun j := ⟨⟨j.val,j.isLt.trans i.isLt⟩,j.isLt⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem weakDesign_reconstruction_bound (m l : ℕ) (i : Fin m) :
    (∑ j : Earlier i, 2^overlapWidth (weakDesignCoord m l) i j.val) ≤ m-1 := by
  simp_rw [overlapWidth_eq_inter]
  let cost (j : Fin m) := 2 ^ ((Finset.univ.map (weakDesignCoord m l i)) ∩
    (Finset.univ.map (weakDesignCoord m l j))).card
  change (∑ j : Earlier i, cost j.val) ≤ m-1
  rw [Fintype.sum_equiv (earlierEquiv i) (fun j => cost j.val)
    (fun j => cost ⟨j.val,j.isLt.trans i.isLt⟩) (by intro j; rfl)]
  exact weakDesign_bound m l i

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

open TimeSpaceMA.GUV

/-- A cubic budget accommodates a block design seed and the logarithmic advice/list
loss. An exact K-B·size(w)^3 payload fits the remaining entropy. -/
theorem trevisanBudget (a : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧ ∀ w m : ℕ, 1 ≤ w → 1 ≤ m → m ≤ w →
      let ℓ := 4*halfSeed a w
      let d := m.size*(ℓ*(2*ℓ+1))
      ∃ slack : ℕ, d+slack ≤ B*w.size^3 ∧
        1 ≤ (ε/(4*(m:ℝ)))^3 * (2:ℝ)^slack := by
  obtain ⟨M, hM⟩ := exists_nat_gt (64/ε^3)
  let c := 4*a
  let B := c*(2*c+1)+(M+3)
  refine ⟨B,by dsimp [B]; omega,?_⟩
  intro w m hw hm hmw ℓ d
  let s := w.size
  have hs : 1 ≤ s := Nat.size_pos.mpr hw
  have hw2 : (w:ℝ) ≤ (2:ℝ)^s := by exact_mod_cast (Nat.lt_size_self w).le
  have hM2 : (M:ℝ) ≤ (2:ℝ)^(M*s) := by
    have hN : M ≤ 2^(M*s) := (Nat.lt_two_pow_self (n := M)).le.trans
      (Nat.pow_le_pow_right (by decide) (by simpa using Nat.mul_le_mul_left M hs))
    exact_mod_cast hN
  have hM4 : (M:ℝ)*(w:ℝ)^3 ≤ (2:ℝ)^((M+3)*s) := by
    rw [Nat.add_mul,pow_add,Nat.mul_comm 3 s,pow_mul (2:ℝ) s 3]
    exact mul_le_mul hM2 (pow_le_pow_left₀ (Nat.cast_nonneg _) hw2 3)
      (by positivity) (by positivity)
  have hε3 : 0 < ε^3 := by positivity
  have hM' := (div_lt_iff₀ hε3).1 hM
  have hmw' : (m:ℝ) ≤ (w:ℝ) := by exact_mod_cast hmw
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hmp : (m:ℝ)^3 ≤ (w:ℝ)^3 := pow_le_pow_left₀ hm'.le hmw' 3
  have hl : ℓ = c*s := by dsimp [ℓ,c,s]; rw [halfSeed_of_pos hw, Nat.mul_assoc]
  have hs1 : 2*ℓ+1 ≤ (2*c+1)*s := by
    rw [hl,Nat.add_mul]
    simpa [Nat.mul_assoc] using Nat.add_le_add_left hs (2*(c*s))
  have hd : d ≤ c*(2*c+1)*s^3 := by
    dsimp [d]
    calc
      _ ≤ s * (ℓ * ((2*c+1)*s)) :=
        Nat.mul_le_mul (Nat.size_le_size hmw) (Nat.mul_le_mul_left ℓ hs1)
      _ = _ := by rw [hl]; ring
  have hss : s ≤ s^3 := by
    calc
      _ = s*1 := (Nat.mul_one _).symm
      _ ≤ s*(s*s) := Nat.mul_le_mul_left _ (Nat.mul_pos hs hs)
      _ = _ := by ring
  refine ⟨(M+3)*s, ?_, ?_⟩
  · change d+(M+3)*s ≤ B*s^3
    change d+(M+3)*s ≤ (c*(2*c+1)+(M+3))*s^3
    rw [Nat.add_mul (c*(2*c+1)) (M+3)]
    exact Nat.add_le_add hd (Nat.mul_le_mul_left _ hss)
  · have h0 : 64*(m:ℝ)^3 ≤ 64*(w:ℝ)^3 := by gcongr
    have h1 : 64*(w:ℝ)^3 ≤ ((M:ℝ)*ε^3)*(w:ℝ)^3 :=
      mul_le_mul_of_nonneg_right hM'.le (by positivity)
    have h2 : ε^3*((M:ℝ)*(w:ℝ)^3) ≤ ε^3*(2:ℝ)^((M+3)*s) :=
      mul_le_mul_of_nonneg_left hM4 hε3.le
    rw [div_pow,div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < (4*(m:ℝ))^3)).2
    nlinarith [h0.trans h1]

/-- The advice family and the list of candidates together consume at most η
of any source with K bits of min-entropy when this exponential slack holds. -/
theorem adviceListMass {η : ℝ} (hη : 0 < η) {d m K slack : ℕ}
    (hK : d+m+slack ≤ K) (hs : 1 ≤ η^3*(2:ℝ)^slack) :
    (2:ℝ)^(d+m) * (1/(3*η^2)) * (1/(2:ℝ)^K) ≤ η := by
  have h2 : (2:ℝ)^(d+m+slack) ≤ (2:ℝ)^K := pow_le_pow_right₀ (by norm_num) hK
  have h0 : (2:ℝ)^(d+m) ≤ η^3 * (2:ℝ)^K := by
    have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2:ℝ)^(d+m))
    have h' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ η^3)
    rw [pow_add] at h'
    nlinarith only [h,h']
  have h1 : 0 < (3*η^2) * (2:ℝ)^K := by positivity
  rw [mul_one_div,mul_one_div,div_div]
  apply (div_le_iff₀ h1).2
  have h3 : 0 ≤ η * η * η * (2:ℝ)^K := by positivity
  nlinarith only [h0,h3]


theorem designWidth_le_cubic (a w m : ℕ) (hw : 1 ≤ w) (hm : m ≤ w) :
    designWidth m (codeWidth a w) ≤ (4*a)*(2*(4*a)+1)*w.size^3 := by
  let c := 4*a
  let s := w.size
  have hs : 1 ≤ s := Nat.size_pos.mpr hw
  have hl : codeWidth a w = c*s := by
    unfold codeWidth c s
    rw [halfSeed_of_pos hw,Nat.mul_assoc]
  have hbase : 2*(c*s)+1 ≤ (2*c+1)*s := by
    rw [Nat.add_mul]
    simpa [Nat.mul_assoc] using Nat.add_le_add_left hs (2*(c*s))
  rw [designWidth,hl]
  change m.size*(c*s*(2*(c*s)+1)) ≤ c*(2*c+1)*s^3
  calc
    _ ≤ s*(c*s*((2*c+1)*s)) :=
      Nat.mul_le_mul (Nat.size_le_size hm) (Nat.mul_le_mul_left _ hbase)
    _ = _ := by ring

theorem codeWidth_polytime (a : ℕ) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime (codeWidth a)
      Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary := by
  open Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  exact unary_mul.comp ((const 4).prod (BinaryFieldArithmetic.native_halfSeed a id'))


/-- For fixed error, the logarithmic missing-entropy margin absorbs both the
list size and the probability required to violate the next-bit bound. -/
theorem trevisanLogGap (ε : ℝ) (hε : 0 < ε) : ∃ C : ℕ, 0 < C ∧
    ∀ w m K : ℕ, 1 ≤ w → 1 ≤ m → m ≤ w → m+C*w.size ≤ K →
      let η := ε/(4*(m:ℝ))
      (m:ℝ)*(η+((2:ℝ)^(m-1)/(3*η^2))/(2:ℝ)^K) ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (64/ε^3)
  let C := M+3
  refine ⟨C,by dsimp [C]; omega,?_⟩
  intro w m K hw hm hmw hgap η
  let s := w.size
  have hs : 1 ≤ s := Nat.size_pos.mpr hw
  have hw2 : (w:ℝ) ≤ (2:ℝ)^s := by
    dsimp [s]
    exact_mod_cast (Nat.lt_size_self w).le
  have hM2 : (M:ℝ) ≤ (2:ℝ)^(M*s) := by
    have hN : M ≤ 2^(M*s) := (Nat.lt_two_pow_self (n := M)).le.trans
      (Nat.pow_le_pow_right (by decide) (by simpa using Nat.mul_le_mul_left M hs))
    exact_mod_cast hN
  have hM4 : (M:ℝ)*(w:ℝ)^3 ≤ (2:ℝ)^(C*s) := by
    unfold C
    rw [Nat.add_mul,pow_add,Nat.mul_comm 3 s,pow_mul (2:ℝ) s 3]
    exact mul_le_mul hM2 (pow_le_pow_left₀ (Nat.cast_nonneg _) hw2 3)
      (by positivity) (by positivity)
  have hε3 : 0 < ε^3 := by positivity
  have hM' := (div_lt_iff₀ hε3).1 hM
  have hmw' : (m:ℝ) ≤ (w:ℝ) := by exact_mod_cast hmw
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have h0 : 64*(m:ℝ)^3 ≤ 64*(w:ℝ)^3 := by gcongr
  have h1 : 64*(w:ℝ)^3 ≤ ((M:ℝ)*ε^3)*(w:ℝ)^3 :=
    mul_le_mul_of_nonneg_right hM'.le (by positivity)
  have h2 : ε^3*((M:ℝ)*(w:ℝ)^3) ≤ ε^3*(2:ℝ)^(C*s) :=
    mul_le_mul_of_nonneg_left hM4 hε3.le
  have h3 : 1 ≤ η^3*(2:ℝ)^(C*s) := by
    dsimp [η]
    rw [div_pow,div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < (4*(m:ℝ))^3)).2
    nlinarith [h0.trans h1]
  have hη : 0 < η := by dsimp [η]; positivity
  have hB : (2:ℝ)^((m-1)+C*s) ≤ (2:ℝ)^K := by
    apply pow_le_pow_right₀ (by norm_num)
    exact (Nat.add_le_add_right (Nat.sub_le m 1) _).trans hgap
  rw [pow_add] at hB
  have hB' := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ η^3)
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ (2:ℝ)^(m-1))
  have h4 : (2:ℝ)^(m-1) ≤ η^3*(2:ℝ)^K := by nlinarith only [hB',h3']
  have h5 : ((2:ℝ)^(m-1)/(3*η^2))/(2:ℝ)^K ≤ η := by
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < 3*η^2*(2:ℝ)^K)).2
    have h := mul_nonneg (show 0 ≤ η^3 from by positivity) (show 0 ≤ (2:ℝ)^K from by positivity)
    nlinarith only [h4,h]
  have h6 : (m:ℝ)*η = ε/4 := by
    dsimp [η]
    field_simp
  calc
    _ ≤ (m:ℝ)*(η+η) := mul_le_mul_of_nonneg_left (add_le_add_right h5 _) hm'.le
    _ = ε/2 := by linarith only [h6]
    _ ≤ ε := by linarith

end TimeSpaceMA.RRV
open scoped BigOperators

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def paddedSeedEquiv (t extra : ℕ) : Fin (2^(t+extra)) ≃ Fin (2^t) × Fin (2^extra) :=
  (finCongr (pow_add 2 t extra)).trans finProdFinEquiv.symm

/-- Encode the original output and the independently appended seed back into one label. -/
def paddedOutputEquiv (m extra : ℕ) : Fin (2^m) × Fin (2^extra) ≃ Fin (2^(m+extra)) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 m extra).symm)

theorem equiv_weighted_event {X S S' O O' : Type}
    [Fintype X] [Fintype S] [Fintype S'] [Fintype O] [Fintype O']
    [DecidableEq O] [DecidableEq O']
    (f : X → S → O) (p : X → ℝ) (ε : ℝ) (es : S' ≃ S) (eo : O ≃ O')
    (h : WeightedExtractorEvents f p ε) :
    WeightedExtractorEvents (fun x s => eo (f x (es s))) p ε := by
  classical
  intro U
  let V := U.map eo.symm.toEmbedding
  have hV y : y ∈ V ↔ eo y ∈ U := by
    constructor
    · intro hy
      obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hy
      change eo.symm z = y at he
      simpa [← he] using hz
    · intro hy
      exact Finset.mem_map.mpr ⟨_,hy,eo.symm_apply_apply y⟩
  have heq : weightedExtractionProbability (fun x s => eo (f x (es s))) p U =
      weightedExtractionProbability f p V := by
    unfold weightedExtractionProbability
    rw [Fintype.card_congr es]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hfilter : ((Finset.univ : Finset S').filter (fun s => eo (f x (es s)) ∈ U)).map
          es.toEmbedding = (Finset.univ : Finset S).filter (fun s => f x s ∈ V) := by
      ext s
      constructor
      · intro hs
        obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hs
        change es t = s at he
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (hV _).mpr (by simpa [← he] using (Finset.mem_filter.mp ht).2)⟩
      · intro hs
        have hs' := (hV _).mp (Finset.mem_filter.mp hs).2
        exact Finset.mem_map.mpr ⟨es.symm s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa using hs'⟩, es.apply_symm_apply _⟩
    rw [← hfilter, Finset.card_map]
  have hU := h V
  change weightedExtractionProbability f p V - (V.card : ℝ) / Fintype.card O ≤ ε at hU
  rw [Fintype.card_congr eo] at hU
  change weightedExtractionProbability _ p U - (U.card : ℝ) / Fintype.card O' ≤ ε
  rw [heq]
  simpa only [V, Finset.card_map] using hU

section Independent
variable {X S O B : Type} [Fintype X] [Fintype S] [Fintype O] [Fintype B]
  [DecidableEq O] [DecidableEq B]
private theorem weighted_fibers (f : X → S → O) (p : X → ℝ) (U : Finset (O × B)) :
    let F := fun b : B => Finset.univ.filter (fun y : O => (y,b) ∈ U)
    weightedExtractionProbability (fun x (s : S × B) => (f x s.1,s.2)) p U =
      (∑ b, weightedExtractionProbability f p (F b)) / Fintype.card B := by
  classical
  dsimp only
  unfold weightedExtractionProbability
  rw [Fintype.card_prod, Nat.cast_mul, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← div_div, ← Finset.sum_div, ← Finset.mul_sum]
  congr 3
  simp only [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_sum]
  rw [Finset.sum_comm]

/-- The output of an extractor stays uniform when it includes extra independent seed bits. -/
theorem weighted_independent_seed (f : X → S → O) (p : X → ℝ) {ε : ℝ}
    (hB : 0 < Fintype.card B) (h : WeightedExtractorEvents f p ε) :
    WeightedExtractorEvents (fun x (s : S × B) => (f x s.1,s.2)) p ε := by
  classical
  intro U
  let F := fun b : B => Finset.univ.filter (fun y : O => (y,b) ∈ U)
  have hcount : U.card = ∑ b, (F b).card := by
    have hU : U = (Finset.univ : Finset (O × B)).filter (· ∈ U) := by ext; simp
    conv_lhs => rw [hU, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp_rw [F, Finset.card_filter]
    rw [Finset.sum_comm]
  have hr : (U.card : ℝ) = ∑ b, ((F b).card : ℝ) := by exact_mod_cast hcount
  have hb : 0 < (Fintype.card B : ℝ) := by exact_mod_cast hB
  have hsum : ∑ b, (weightedExtractionProbability f p (F b) -
      ((F b).card : ℝ) / Fintype.card O) ≤ (Fintype.card B : ℝ) * ε := by
    calc
      _ ≤ ∑ _b : B, ε := Finset.sum_le_sum (fun b _ => h (F b))
      _ = _ := by simp [nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hr] at hsum
  change weightedExtractionProbability _ p U - (U.card : ℝ) / Fintype.card (O × B) ≤ ε
  rw [weighted_fibers, Fintype.card_prod, Nat.cast_mul, ← div_div, ← sub_div]
  exact (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hsum)

end Independent

theorem weighted_drop_initial_seed_bits {X : Type} [Fintype X]
    {d m : ℕ} (hm : m ≤ d) (p : X → ℝ) {ε : ℝ} (hP : ∑ x, p x = 1) (hε : 0 ≤ ε) :
    WeightedExtractorEvents (fun (_ : X) (y : Fin (2^d)) =>
      ⟨y.val % 2^m, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩ : X → Fin (2^d) → Fin (2^m)) p ε := by
  classical
  have hsplit : d-m+m = d := Nat.sub_add_cancel hm
  let es : Fin (2^d) ≃ Fin (2^(d-m)) × Fin (2^m) :=
    (finCongr (congrArg (fun n : ℕ => 2^n) hsplit.symm)).trans (paddedSeedEquiv (d-m) m)
  apply equiv_weighted_event (fun _ (b : Fin (2^(d-m)) × Fin (2^m)) => b.2) p ε es (Equiv.refl _)
  intro U
  unfold weightedExtractionProbability
  have hfilter : (Finset.univ.filter (fun z : Fin (2^(d-m)) × Fin (2^m) => z.2 ∈ U)) =
      (Finset.univ : Finset (Fin (2^(d-m)))) ×ˢ U := by ext z; simp
  change (∑ x, p x * (((Finset.univ.filter (fun z : Fin (2^(d-m)) × Fin (2^m) => z.2 ∈ U)).card : ℕ) : ℝ) /
        Fintype.card (Fin (2^(d-m)) × Fin (2^m))) -
      (U.card : ℝ) / Fintype.card (Fin (2^m)) ≤ ε
  rw [hfilter, Finset.card_product, Finset.card_univ, Nat.cast_mul, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, ← Finset.sum_mul, hP, one_mul]
  have hp : 0 < (Fintype.card (Fin (2^(d-m))) : ℝ) := by simp
  rw [mul_div_mul_left _ _ hp.ne', sub_self]
  exact hε


end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The first stage has a native seed schedule indexed by input and payload widths.
Its statistical certificate requires an additive bound on the missing entropy. -/
def HasStrongExtractionWithLogGap (ε : ℝ) : Prop :=
  ∃ (A C : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ),
    ComputableInPolyTime schedule (encPair encUnary encNat) encUnary ∧
    ComputableInPolyTime base encExtractorInput encNat ∧
    ∀ w m : ℕ, 1 ≤ w → m ≤ w →
      schedule (w,m) ≤ A*w.size^3 ∧
      ∀ K : ℕ, K ≤ w → m+C*w.size ≤ K →
        ∀ p : Fin (2^w) → ℝ, (∑ x, p x) = 1 →
          (∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K) →
          WeightedExtractorEvents (fun x s =>
            (s, fixedOutput base w m (schedule (w,m)) m x s)) p ε

/-- Interpret the second argument as entropy for the outer interface and payload
width in the underlying evaluator. Use the high bits of the supplied seed. -/
def firstPad (B : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ) :
    ExtractorInput → ℕ :=
  fun (w,K,d,x,y) =>
    let m := min K w-B*w.size^3
    let ds := schedule (w,m)
    base (w,m,ds,x,y/2^(d-ds))

theorem firstPad_polytime (B : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ)
    (hs : ComputableInPolyTime schedule (encPair encUnary encNat) encUnary)
    (hb : ComputableInPolyTime base encExtractorInput encNat) :
    ComputableInPolyTime (firstPad B schedule base) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let I := encExtractorInput
  have hw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.1) I encUnary := fst _ _
  have hk0 : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1) I encNat := (snd _ _).fst'
  have hk := (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime hk0.computableInPolyTime).tidy
  have hsize := ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hw)
  have hcube := unary_mul.comp ((const B).prod ((unary_pow 3).comp hsize))
  have hm := unary_sub.comp (hk.prod hcube)
  have hmB := unary_to_binary.comp hm
  have hs' := hs.tidy.comp (hw.prod hmB)
  have hd : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.1) I encUnary :=
    (snd _ _).snd'.fst'
  have hx : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.1) I encNat :=
    (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.2) I encNat :=
    (snd _ _).snd'.snd'.snd'
  have h := hb.tidy.comp (hw.prod (hmB.prod (hs'.prod
    (hx.prod (binary_div' hy (binary_two_pow.comp (unary_sub.comp (hd.prod hs'))))))))
  convert h using 1
  funext p
  rcases p with ⟨w,K,d,x,y⟩
  simp [firstPad,min_comm]

theorem weightedStrong_zero {X : Type} [Fintype X] (p : X → ℝ)
    {d m : ℕ} (hm : m = 0) (f : X → Fin (2^d) → Fin (2^m)) {ε : ℝ} (hP : ∑ x, p x = 1) (hε : 0 ≤ ε) :
    WeightedExtractorEvents (fun x s => (s,f x s)) p ε := by
  classical
  subst m
  let I : Fin (2^d) ≃ Fin (2^d) × Fin 1 :=
    (Equiv.prodUnique (Fin (2^d)) (Fin 1)).symm
  have he : (fun x s => (s,f x s)) = (fun (_ : X) (s : Fin (2^d)) => I s) := by
    funext x s
    apply Prod.ext
    · rfl
    · change (f x s : Fin 1) = (I s).2
      apply Fin.ext
      have h1 := (f x s).isLt
      have h2 := (I s).2.isLt
      change (f x s).val < 1 at h1
      omega
  rw [he]
  have H := weighted_drop_initial_seed_bits (X := X) (d := d) (m := d) le_rfl p hP hε
  have HH := equiv_weighted_event _ p ε (Equiv.refl (Fin (2^d))) I H
  simpa [Nat.mod_eq_of_lt (Fin.isLt _)] using HH

private theorem firstPad_events {ε : ℝ} (B : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ)
    {w K : ℕ} (hK : K ≤ w) (p : Fin (2^w) → ℝ) (hP : ∑ x, p x = 1) (hε : 0 ≤ ε)
    (hd : schedule (w,K-B*w.size^3) ≤ B*w.size^3)
    (h : 0 < K-B*w.size^3 →
      let m := K-B*w.size^3
      let ds := schedule (w,m)
      WeightedExtractorEvents (fun x s => (s,fixedOutput base w m ds m x s)) p ε) :
    let d := B*w.size^3
    WeightedExtractorEvents (fun x s =>
      (s,fixedOutput (firstPad B schedule base) w K d (K-d) x s)) p ε := by
  let d := B*w.size^3
  let m := K-d
  let ds := schedule (w,m)
  by_cases nonempty : 0 < m
  · let b := d-ds
    have hs : ds+b = d := Nat.add_sub_of_le hd
    let iseed : Fin (2^d) ≃ Fin (2^ds) × Fin (2^b) :=
      (finCongr (congrArg (2^·) hs.symm)).trans (paddedSeedEquiv ds b)
    let f : Fin (2^w) → Fin (2^ds) → Fin (2^m) := fixedOutput base w m ds m
    let o : ((Fin (2^ds) × Fin (2^m)) × Fin (2^b)) ≃ Fin (2^d) × Fin (2^m) :=
      { toFun := fun z => (iseed.symm (z.1.1,z.2),z.1.2)
        invFun := fun z => (((iseed z.1).1,z.2),(iseed z.1).2)
        left_inv := by rintro ⟨⟨s,m⟩,b⟩; simp
        right_inv := by rintro ⟨s,m⟩; simp }
    have h1 := weighted_independent_seed (B := Fin (2^b)) (fun x s => (s,f x s)) p (by simp)
      (h nonempty)
    have h2 := equiv_weighted_event _ p ε iseed o h1
    change WeightedExtractorEvents (fun x s =>
      (s,fixedOutput (firstPad B schedule base) w K d m x s)) p ε
    convert h2 using 2
    rename_i x
    funext y
    apply Prod.ext
    · change y = iseed.symm (iseed y)
      exact (iseed.symm_apply_apply y).symm
    · apply Fin.ext
      change firstPad B schedule base (w,K,d,x.val,y.val) % 2^m =
        base (w,m,ds,x.val,(iseed y).1.val) % 2^m
      have hs1 : (iseed y).1.val = y.val / 2^b := rfl
      simp [firstPad,min_eq_left hK,hs1,m,ds,d,b]
  · have hz : K-d = 0 := Nat.eq_zero_of_not_pos nonempty
    let f := fixedOutput (firstPad B schedule base) w K d (K-d)
    change WeightedExtractorEvents (fun x s => (s,f x s)) p ε
    exact weightedStrong_zero p hz f hP hε

theorem hasNearFullStrongExtractor_of_logGap {ε : ℝ} (hε : 0 ≤ ε)
    (h : HasStrongExtractionWithLogGap ε) : HasNearFullStrongExtractor ε := by
  obtain ⟨A,C,schedule,base,hs,hb,h⟩ := h
  let B := A + C + 1
  refine ⟨B,firstPad B schedule base,by unfold B; omega,firstPad_polytime B schedule base hs hb,?_⟩
  intro w K hw hK p hP hc
  let d := B*w.size^3
  have hW : w.size ≤ w.size^3 := by
    simpa using Nat.pow_le_pow_right (Nat.size_pos.mpr hw) (by decide : 1 ≤ 3)
  have hA : A*w.size^3 ≤ d := Nat.mul_le_mul_right _ (by unfold B; omega)
  have hC : C*w.size ≤ d :=
    (Nat.mul_le_mul_left C hW).trans (Nat.mul_le_mul_right _ (by unfold B; omega))
  obtain ⟨hseed,hstat⟩ := h w (K-d) hw (by omega)
  apply firstPad_events B schedule base hK p hP hε (hseed.trans hA)
  intro hm
  exact hstat K hK (by omega) p hP hc

end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev IndexInput := ℕ × ℕ × ℕ × ℕ
abbrev encIndexInput : IndexInput ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary encUnary))
abbrev encTrevisanCodeInput : (ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encUnary (encPair encNat encNat)

/-- Pack the bits at the chosen seed coordinates into one binary code position. -/
def readRestricted (position : IndexInput → ℕ) (m ell i seed : ℕ) : ℕ :=
  ((List.range ell).map fun j => (seed / 2^(position (m,ell,i,j)) % 2)*2^j).sum

private theorem sum_range_eq {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range, Finset.sum_range]

/-- The native evaluator uses an index for each row and each column. It reads the
design seed coordinates, calls the bit code, and packs the requested payload. -/
def trevisanEval (position : IndexInput → ℕ) (width : ℕ → ℕ)
    (code : ℕ × ℕ × ℕ → ℕ) : ExtractorInput → ℕ :=
  fun (w,m,_d,x,y) =>
    let m := min m w
    let ell := width w
    ((List.range m).map
      fun i => (if code (w,x,readRestricted position m ell i y) = 1 then 1 else 0)*2^i).sum

private theorem readRestricted_polytime {α : Type} {input : α ↪ List Bool}
    (position : IndexInput → ℕ)
    (hPos : ComputableInPolyTime position encIndexInput encUnary)
    {m ell i y : α → ℕ}
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (he : ComputableTidilyInPolyTime ell input encUnary)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hy : ComputableTidilyInPolyTime y input encNat) :
    ComputableTidilyInPolyTime (fun p => readRestricted position (m p) (ell p) (i p) (y p)) input encNat := by
  have hl := range.comp he
  have hp := fst input encUnary
  have hj := snd input encUnary
  have hIndex := hPos.tidy.comp ((hm.comp hp).prod ((he.comp hp).prod ((hi.comp hp).prod hj)))
  have hDigit := binary_mod' (binary_div' (hy.comp hp) (binary_two_pow.comp hIndex)) (const 2)
  exact binary_sum.comp (mapWithInput hl (binary_mul' hDigit (binary_two_pow.comp hj)))

theorem trevisanEval_polytime (position : IndexInput → ℕ) (width : ℕ → ℕ)
    (code : ℕ × ℕ × ℕ → ℕ)
    (hp : ComputableInPolyTime position encIndexInput encUnary)
    (hwid : ComputableInPolyTime width encUnary encUnary)
    (hc : ComputableInPolyTime code encTrevisanCodeInput encNat) :
    ComputableInPolyTime (trevisanEval position width code) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let I := encExtractorInput
  have hw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.1) I encUnary := fst _ _
  have hMr : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1) I encNat := (snd _ _).fst'
  have hm := (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime
    hMr.computableInPolyTime).tidy
  have hℓ := hwid.tidy.comp hw
  have hx : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.1) I encNat :=
    (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.2) I encNat :=
    (snd _ _).snd'.snd'.snd'
  have hJ := fst I encUnary
  have hI := snd I encUnary
  have hRead := readRestricted_polytime position hp (hm.comp hJ) (hℓ.comp hJ) hI (hy.comp hJ)
  have hCode := hc.tidy.comp ((hw.comp hJ).prod ((hx.comp hJ).prod hRead))
  let payload (p : ExtractorInput) (i : ℕ) :=
    code (p.1,p.2.2.2.1,readRestricted position (min p.1 p.2.1) (width p.1) i p.2.2.2.2)
  have hCode' : ComputableTidilyInPolyTime (fun p : ExtractorInput × ℕ => payload p.1 p.2)
      (encPair I encUnary) encNat := hCode
  have hOne := binary_lt' hCode' (const 2)
  have hZero := binary_lt' hCode' (const 1)
  have hbit := hOne.ite' (hZero.ite' (const 0) (const (encMid := encNat) 1)) (const 0)
  let digit (p : ExtractorInput) (i : ℕ) :=
    (if decide (payload p i < 2) then (if decide (payload p i < 1) then 0 else 1) else 0)*2^i
  have hdigit : ComputableTidilyInPolyTime (fun p : ExtractorInput × ℕ => digit p.1 p.2)
      (encPair I encUnary) encNat := binary_mul' hbit (binary_two_pow.comp hI)
  have hValue := binary_sum.comp (mapWithInput (f := digit) (range.comp hm) hdigit)
  convert hValue using 1
  funext p
  rcases p with ⟨w,m,d,x,y⟩
  unfold trevisanEval
  simp only [Function.comp_apply, min_comm,digit,payload]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [decide_eq_true_eq]
  let c := code (w,x,readRestricted position (min w m) (width w) i y)
  change (if c=1 then 1 else 0)*2^i = (if c<2 then (if c<1 then 0 else 1) else 0)*2^i
  congr 1
  by_cases h : c=1
  · simp [h]
  · by_cases hh : c<2
    · have h0 : c=0 := by omega
      simp [h0]
    · simp [h,hh]

private theorem readRestricted_eq {m ell d : ℕ} (position : IndexInput → ℕ)
    (location : Fin m → Fin ell ↪ Fin d)
    (hPos : ∀ i j, (location i j).val = position (m,ell,i.val,j.val))
    (i : Fin m) (s : Fin (2^d)) :
    readRestricted position m ell i.val s.val =
      (Cslib.BitString.equivFin ell (fun j => (Cslib.BitString.equivFin d).symm s (location i j))).val := by
  unfold readRestricted
  rw [Cslib.BitString.val_equivFin_eq_sum,sum_range_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [Cslib.BitString.equivFin_symm_apply,hPos]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have hh : s.val / 2^position (m,ell,i.val,j.val) % 2 < 2 := Nat.mod_lt _ (by decide)
  have he : (decide (s.val / 2^position (m,ell,i.val,j.val) % 2 = 1)).toNat =
      s.val / 2^position (m,ell,i.val,j.val) % 2 := by
    by_cases h1 : s.val / 2^position (m,ell,i.val,j.val) % 2 = 1
    · simp [h1]
    · have h0 : s.val / 2^position (m,ell,i.val,j.val) % 2 = 0 := by omega
      simp [h0]
  rw [he]

theorem trevisanEval_eq {w m d : ℕ} (position : IndexInput → ℕ) (width : ℕ → ℕ)
    (code : ℕ × ℕ × ℕ → ℕ) (bitCode : Fin (2^w) → (Fin (width w) → Bool) → Bool)
    (location : Fin m → Fin (width w) ↪ Fin d)
    (hPos : ∀ i j, (location i j).val = position (m,width w,i.val,j.val))
    (hBit : ∀ x b, decide (code (w,x.val,(Cslib.BitString.equivFin _ b).val) = 1) = bitCode x b)
    (hm : m ≤ w) (x : Fin (2^w)) (s : Fin (2^d)) :
    fixedOutput (trevisanEval position width code) w m d m x s =
      Cslib.BitString.equivFin m (fun i =>
        bitCode x (fun j => (Cslib.BitString.equivFin d).symm s (location i j))) := by
  let output := Cslib.BitString.equivFin m (fun i =>
    bitCode x (fun j => (Cslib.BitString.equivFin d).symm s (location i j)))
  have he : trevisanEval position width code (w,m,d,x.val,s.val) = output.val := by
    unfold trevisanEval output
    simp only [min_eq_left hm]
    rw [Cslib.BitString.val_equivFin_eq_sum,sum_range_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [readRestricted_eq position location hPos i s, ← hBit]
    split <;> simp_all
  apply Fin.ext
  change trevisanEval position width code (w,m,d,x.val,s.val) % 2^m = output.val
  rw [he,Nat.mod_eq_of_lt output.isLt]

end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open TimeSpaceMA.GUV Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def trevisanSchedule (a : ℕ) (p : ℕ × ℕ) : ℕ :=
  designWidth (min p.1 p.2) (codeWidth a p.1)

private theorem trevisanSchedule_polytime (a : ℕ) :
    ComputableInPolyTime (trevisanSchedule a) (encPair encUnary encNat) encUnary := by
  let hw := fst encUnary encNat
  let hm := (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime
    (snd encUnary encNat).computableInPolyTime).tidy
  let hsize := ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hm)
  let hℓ := (codeWidth_polytime a).comp hw
  let hb := unary_add.comp ((unary_mul.comp ((const 2).prod hℓ)).prod (const 1))
  exact (unary_mul.comp (hsize.prod (unary_mul.comp (hℓ.prod hb)))).computableInPolyTime

private theorem trevisanSchedule_bound (a : ℕ) {w m : ℕ} (hw : 1 ≤ w) (hm : m ≤ w) :
    trevisanSchedule a (w,m) ≤ ((4*a)*(2*(4*a)+1))*w.size^3 := by
  simpa [trevisanSchedule,min_eq_right hm] using designWidth_le_cubic a w m hw hm

private theorem native_strong_events {ε : ℝ} {a : ℕ} {ha : 0 < a}
    (I : BinaryFieldArithmetic a ha) (w m : ℕ) (hw : 1 ≤ w) (hm : m ≤ w)
    (p : Fin (2^w) → ℝ)
    (position : IndexInput → ℕ)
    (hPos : ∀ i j : ℕ, i < m → j < codeWidth a w →
      position (m,codeWidth a w,i,j) = designPosition m (codeWidth a w) i j)
    (hStat : WeightedExtractorEvents (fun x s =>
      (s, nw (weakDesignCoord m (codeWidth a w)) (rrvCode I w hw) x s)) p ε) :
    WeightedExtractorEvents (fun x s =>
      (s, fixedOutput (trevisanEval position (codeWidth a) (rsCodeNat I)) w m
        (trevisanSchedule a (w,m)) m x s)) p ε := by
  let d := designWidth m (codeWidth a w)
  have hd : trevisanSchedule a (w,m) = d := by simp [trevisanSchedule,min_eq_right hm,d]
  rw [hd]
  let es : Fin (2^d) ≃ Bits d := (Cslib.BitString.equivFin d).symm
  let eo : Bits d × Bits m ≃ Fin (2^d) × Fin (2^m) :=
    (Cslib.BitString.equivFin d).prodCongr (Cslib.BitString.equivFin m)
  have hE := equiv_weighted_event _ p ε es eo hStat
  convert hE using 2
  rename_i x
  funext y
  apply Prod.ext
  · exact ((Cslib.BitString.equivFin d).apply_symm_apply y).symm
  · exact trevisanEval_eq position (codeWidth a) (rsCodeNat I) (rrvCode I w hw)
      (weakDesignCoord m (codeWidth a w)) (fun i j => (hPos _ _ i.isLt j.isLt).symm)
      (rrvCodeNat_correct I w hw) hm x y

private theorem strong_event_zero {w : ℕ} (I : ExtractorInput → ℕ) (d : ℕ)
    (p : Fin (2^w) → ℝ) (hp : ∑ x, p x = 1) {ε : ℝ} (hε : 0 ≤ ε) :
    WeightedExtractorEvents (fun x s => (s,fixedOutput I w 0 d 0 x s)) p ε :=
  weightedStrong_zero p rfl _ hp hε

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

open TimeSpaceMA.GUV Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The Trevisan strong extractor combines the greedy weak design with the
Reed–Solomon/Hadamard code and the weighted reconstruction bound. -/
theorem strongExtractionWithLogGap_of_design {ε : ℝ} (hε : 0 < ε)
    (position : IndexInput → ℕ)
    (hPosNative : ComputableInPolyTime position encIndexInput encUnary)
    (hPos : ∀ m ell i j : ℕ, i < m → j < ell →
      position (m,ell,i,j) = designPosition m ell i j) :
    HasStrongExtractionWithLogGap ε := by
  obtain ⟨a,ha,hField⟩ := rsFieldWidth_exists ε hε
  obtain ⟨I⟩ := fieldOperations_exists a ha
  obtain ⟨C,_,hGap⟩ := trevisanLogGap ε hε
  let eval := trevisanEval position (codeWidth a) (rsCodeNat I)
  let schedule := trevisanSchedule a
  refine ⟨(4*a)*(2*(4*a)+1),C,schedule,eval,trevisanSchedule_polytime a,
    trevisanEval_polytime position (codeWidth a) (rsCodeNat I) hPosNative
      (codeWidth_polytime a).computableInPolyTime (rsCodeNat_polytime I),?_⟩
  intro w m hw hm
  refine ⟨trevisanSchedule_bound a hw hm,?_⟩
  intro K hKw hK p hp hcap
  by_cases hz : m = 0
  · subst m
    exact strong_event_zero eval _ p hp hε.le
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hz
  let η := ε/(4*(m:ℝ))
  have hη : 0 < η := by unfold η; positivity
  have hwidth : (w:ℝ) ≤ η^2*(2:ℝ)^(2*halfSeed a w) := hField w m hw hm1 hm
  let code := rrvCode I w hw
  let S := weakDesignCoord m (codeWidth a w)
  have hList := hasListBound_of_counts code η (1/(3*η^2))
    (rrvCode_list I w hw hη hwidth)
  have hnum : (m:ℝ)*(η + (2:ℝ)^(m-1)*(1/(3*η^2))/(2:ℝ)^K) ≤ ε := by
    simpa only [mul_one_div] using hGap w m K hw hm1 hm hK
  have h := strongNW_of_list p hp hcap S code η (1/(3*η^2)) ε hη.le
    (by positivity) hList (weakDesign_reconstruction_bound m (codeWidth a w)) hnum
  exact native_strong_events I w m hw hm p position (hPos m (codeWidth a w)) h

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

private def greedyPosition (p : IndexInput) : ℕ := designPosition p.1 p.2.1 p.2.2.1 p.2.2.2

private theorem greedyPosition_polytime : ComputableInPolyTime greedyPosition encIndexInput encUnary :=
  (designPosition_polytime (fst _ _) (snd _ _).fst' (snd _ _).snd'.fst'
    (snd _ _).snd'.snd').computableInPolyTime

end TimeSpaceMA.RRV

open TimeSpaceMA TimeSpaceMA.RRV

theorem solution (ε : ℝ) (hε : 0 < ε) (_hε' : ε ≤ 1/32) :
    HasNearFullStrongExtractor ε :=
  hasNearFullStrongExtractor_of_logGap hε.le
    (strongExtractionWithLogGap_of_design hε greedyPosition greedyPosition_polytime
      (fun _ _ _ _ _ _ => rfl))
