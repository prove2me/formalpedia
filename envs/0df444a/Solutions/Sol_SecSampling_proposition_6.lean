-- Prove2me | solution 1 for SecSampling.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:36:30.232029+00:00
-- url     : https://prove2.me/submissions/cdaedd97-6db5-459b-82c5-a90a1c6576a8

import Mathlib
import Definitions.Def_SecSampling_AOSp
import Definitions.Def_SecSampling_ColoredLastZero

namespace Aux_SecSampling_proposition_6

open SecSampling

/-! ### Generic facts on last zeros -/

theorem lt_idxOf_ne {α : Type} [BEq α] [LawfulBEq α] (b : α) :
    ∀ (l : List α) (j : ℕ), j < l.idxOf b → l[j]? ≠ some b
  | [], j, h => by simp at h
  | x :: xs, 0, h => by
    rw [List.idxOf_cons] at h
    cases hx : (x == b)
    · have hxb : x ≠ b := by
        intro e; rw [e] at hx; simp at hx
      simpa using hxb
    · rw [hx] at h; simp at h
  | x :: xs, j + 1, h => by
    rw [List.idxOf_cons] at h
    cases hx : (x == b)
    · rw [hx] at h
      have h' : j < xs.idxOf b := by simp at h; omega
      simpa using lt_idxOf_ne b xs j h'
    · rw [hx] at h; simp at h

theorem lz_spec (I : List Bool) (h : false ∈ I) :
    0 < lastZero I ∧ lastZero I ≤ I.length ∧ I[lastZero I - 1]? = some false ∧
      ∀ i, lastZero I ≤ i → i < I.length → I[i]? = some true := by
  have hr : false ∈ I.reverse := List.mem_reverse.mpr h
  have hk : I.reverse.idxOf false < I.reverse.length := List.idxOf_lt_length_iff.mpr hr
  have hlen : I.reverse.length = I.length := List.length_reverse
  have hlz : lastZero I = I.length - I.reverse.idxOf false := by
    unfold lastZero; rw [if_pos h]
  have hget : I.reverse[I.reverse.idxOf false]? = some false := by
    rw [List.getElem?_eq_getElem hk, List.getElem_idxOf hk]
  obtain ⟨k, hkdef⟩ : ∃ k, k = I.reverse.idxOf false := ⟨_, rfl⟩
  rw [← hkdef] at hget hk hlz
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hlz]
    have e : I.length - k - 1 = I.length - 1 - k := by omega
    rw [e, ← List.getElem?_reverse (l := I) (i := k) (by omega)]
    exact hget
  · intro i hi1 hi2
    have hne := lt_idxOf_ne false I.reverse (I.length - 1 - i) (by omega)
    rw [List.getElem?_reverse (l := I) (i := I.length - 1 - i) (by omega)] at hne
    have e : I.length - 1 - (I.length - 1 - i) = i := by omega
    rw [e, List.getElem?_eq_getElem hi2] at hne
    rw [List.getElem?_eq_getElem hi2]
    cases hb : I[i]
    · rw [hb] at hne; exact absurd rfl hne
    · rfl

theorem count_split (I : List Bool) (a : ℕ) :
    I.count true = (I.take a).count true + (I.drop a).count true := by
  conv_lhs => rw [← List.take_append_drop a I]
  rw [List.count_append]

theorem getLast_take (Q : List Bool) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Q.length) :
    (Q.take j).getLast? = Q[j - 1]? := by
  rw [List.getLast?_eq_getElem?, List.length_take, min_eq_left h2, List.getElem?_take,
    if_pos (by omega)]

/-! ### The colored strategy simulating `A` -/

/-- The history of an AOSp algorithm rebuilt from a prefix `h` of the bit string: one entry for
each zero, `(r - #ones up to it, 0)`. -/
def histB (r : ℕ) (h : List Bool) : List (ℕ × ℕ) :=
  ((List.range h.length).filter (fun i => decide (h[i]? = some false))).map
    (fun i => (r - (h.take (i + 1)).count true, 0))

noncomputable def Bst (A : Algorithm) (n r b : ℕ) (h : List Bool) : ℝ :=
  if h.getLast? = some false then A n (r + b) (histB r h) else 0

theorem Bst_col (A : Algorithm) (hA : IsAlgorithm A) : IsColStrategy (Bst A) := by
  intro n r b h
  unfold Bst
  split_ifs
  · exact hA n (r + b) (histB r h)
  · exact ⟨le_refl 0, zero_le_one⟩

/-! ### Bit strings of sample sets -/

def bits {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn (fun i : Fin n => decide (i ∈ S))

theorem bits_length {n : ℕ} (S : Finset (Fin n)) : (bits S).length = n := List.length_ofFn

theorem bits_get {n : ℕ} (S : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (bits S)[i]? = some (decide ((⟨i, hi⟩ : Fin n) ∈ S)) := by
  unfold bits
  rw [List.getElem?_ofFn, dif_pos hi]

theorem ct_bits {n : ℕ} (S : Finset (Fin n)) : ∀ j : ℕ,
    ((bits S).take j).count true = (S.filter (fun y => y.val < j)).card
  | 0 => by
    rw [List.take_zero]
    simp
  | j + 1 => by
    rw [List.take_succ, List.count_append, ct_bits S j]
    by_cases hj : j < n
    · rw [bits_get S j hj]
      have hsplit : (S.filter (fun y => y.val < j + 1)).card =
          (S.filter (fun y => y.val < j)).card + (if (⟨j, hj⟩ : Fin n) ∈ S then 1 else 0) := by
        rw [Finset.card_filter, Finset.card_filter]
        have : ∀ y ∈ S, (if y.val < j + 1 then 1 else 0) =
            (if y.val < j then 1 else 0) + (if y = (⟨j, hj⟩ : Fin n) then 1 else 0) := by
          intro y _
          by_cases h1 : y.val < j
          · have h2 : y ≠ ⟨j, hj⟩ := by
              intro h; rw [h] at h1; exact lt_irrefl _ h1
            rw [if_pos (by omega), if_pos h1, if_neg h2]
          · by_cases h3 : y.val = j
            · have h2 : y = ⟨j, hj⟩ := Fin.ext h3
              rw [if_pos (by omega), if_neg h1, if_pos h2]
            · have h2 : y ≠ ⟨j, hj⟩ := by
                intro h; rw [h] at h3; exact h3 rfl
              rw [if_neg (by omega), if_neg h1, if_neg h2]
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
      rw [hsplit]
      by_cases hS : (⟨j, hj⟩ : Fin n) ∈ S
      · simp [hS]
      · simp [hS]
    · have hnone : (bits S)[j]? = none :=
        List.getElem?_eq_none (by rw [bits_length]; omega)
      rw [hnone]
      have : S.filter (fun y => y.val < j + 1) = S.filter (fun y => y.val < j) := by
        apply Finset.filter_congr
        intro y _
        have := y.isLt
        constructor <;> intro h <;> omega
      rw [this]
      simp

theorem bitNorm_bits {n : ℕ} (S : Finset (Fin n)) : bitNorm (bits S) = S.card := by
  unfold bitNorm
  have h := ct_bits S n
  rw [List.take_of_length_le (show (bits S).length ≤ n by rw [bits_length])] at h
  rw [h]
  congr 1
  apply Finset.filter_true_of_mem
  intro y _
  exact y.isLt

theorem weight_bits (p : ℝ) {n : ℕ} (S : Finset (Fin n)) :
    weight p (bits S) = sampleWeight p S := by
  unfold weight sampleWeight
  rw [bitNorm_bits, bits_length]

theorem perf_eq (p : ℝ) (Q : ColStrategy) (m n : ℕ) :
    perfColored p Q m n = ∑ S : Finset (Fin n), sampleWeight p S * winColored Q m (bits S) := by
  unfold perfColored strings
  rw [Finset.sum_image (fun f _ g _ h => List.ofFn_injective h)]
  symm
  apply Fintype.sum_bijective (fun S : Finset (Fin n) => fun i => decide (i ∈ S))
  · constructor
    · intro S T h
      ext x
      have := congrFun h x
      simpa using this
    · intro f
      refine ⟨Finset.univ.filter (fun i => f i = true), ?_⟩
      funext i
      simp
  · intro S
    show sampleWeight p S * winColored Q m (bits S) = weight p (bits S) * winColored Q m (bits S)
    rw [weight_bits]

/-! ### The arrival order -/

theorem mem_io {n : ℕ} (S : Finset (Fin n)) (z : Fin n) : z ∈ indexOrder n S ↔ z ∉ S := by
  unfold indexOrder
  simp

theorem io_sorted (n : ℕ) (S : Finset (Fin n)) : (indexOrder n S).Pairwise (· < ·) := by
  unfold indexOrder
  exact List.Pairwise.filter _ (List.pairwise_lt_finRange n)

/-! ### The AOSp recursion -/

theorem stop_le_one (A : Algorithm) (hA : IsAlgorithm A) {n : ℕ} (v : Fin n → ℝ)
    (S : Finset (Fin n)) (L : List (Fin n)) :
    ∀ (rest seen : List (Fin n)), stopAtMaxProb A v S L seen rest ≤ 1
  | [], seen => by rw [stopAtMaxProb]; norm_num
  | x :: rest, seen => by
    rw [stopAtMaxProb]
    have ih := stop_le_one A hA v S L rest (seen ++ [x])
    have h0 := (hA n S.card (hist v S (seen ++ [x]))).1
    have h1 := (hA n S.card (hist v S (seen ++ [x]))).2
    have hi : (if ∀ y ∈ L, v y ≤ v x then A n S.card (hist v S (seen ++ [x])) else 0) ≤
        A n S.card (hist v S (seen ++ [x])) := by
      split_ifs
      · exact le_refl _
      · exact h0
    nlinarith

theorem stop_zero (A : Algorithm) {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n))
    (L : List (Fin n)) :
    ∀ (rest seen : List (Fin n)), (∀ y ∈ rest, ¬ ∀ z ∈ L, v z ≤ v y) →
      stopAtMaxProb A v S L seen rest = 0
  | [], seen, _ => by rw [stopAtMaxProb]
  | x :: rest, seen, h => by
    rw [stopAtMaxProb, if_neg (h x (by simp)),
      stop_zero A v S L rest (seen ++ [x]) (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    ring

theorem filter_le_eq {n : ℕ} (L X Y : List (Fin n)) (a : Fin n) (hL : L = X ++ a :: Y)
    (hs : L.Pairwise (· < ·)) : L.filter (fun z => decide (z ≤ a)) = X ++ [a] := by
  subst hL
  rw [List.pairwise_append] at hs
  obtain ⟨_, hY, hXY⟩ := hs
  rw [List.pairwise_cons] at hY
  have e1 : X.filter (fun z => decide (z ≤ a)) = X := by
    apply List.filter_eq_self.mpr
    intro z hz
    have := hXY z hz a (by simp)
    simp only [decide_eq_true_eq]
    exact le_of_lt this
  have e2 : Y.filter (fun z => decide (z ≤ a)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hz
    have := hY.1 z hz
    simp only [decide_eq_true_eq, not_le]
    exact this
  rw [List.filter_append, List.filter_cons, if_pos (by simp), e1, e2]

theorem stop_formula (A : Algorithm) {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n))
    (L : List (Fin n)) (hs : L.Pairwise (· < ·)) (xs : Fin n) (post : List (Fin n))
    (hmax : ∀ z ∈ L, v z ≤ v xs) (hnot : ∀ y ∈ L, y ≠ xs → ¬ ∀ z ∈ L, v z ≤ v y) :
    ∀ (pre seen : List (Fin n)), seen ++ (pre ++ xs :: post) = L →
      stopAtMaxProb A v S L seen (pre ++ xs :: post) =
        (pre.map (fun y => 1 - A n S.card (hist v S (L.filter (fun z => decide (z ≤ y)))))).prod *
          A n S.card (hist v S (L.filter (fun z => decide (z ≤ xs))))
  | [], seen, hL => by
    simp only [List.nil_append] at hL ⊢
    rw [stopAtMaxProb, if_pos hmax]
    have hpost : ∀ y ∈ post, ¬ ∀ z ∈ L, v z ≤ v y := by
      intro y hy
      apply hnot y (by rw [← hL]; simp [hy])
      intro hy'
      rw [← hL, List.pairwise_append, List.pairwise_cons] at hs
      have := hs.2.1.1 y hy
      rw [hy'] at this
      exact lt_irrefl _ this
    rw [stop_zero A v S L post (seen ++ [xs]) hpost,
      filter_le_eq L seen post xs hL.symm hs]
    simp
  | a :: pre, seen, hL => by
    simp only [List.cons_append] at hL ⊢
    rw [stopAtMaxProb]
    have hfa : L.filter (fun z => decide (z ≤ a)) = seen ++ [a] :=
      filter_le_eq L seen (pre ++ xs :: post) a hL.symm hs
    have hane : a ≠ xs := by
      intro h
      rw [← hL, List.pairwise_append, List.pairwise_cons] at hs
      have := hs.2.1.1 xs (by simp)
      rw [h] at this
      exact lt_irrefl _ this
    have hrec := stop_formula A v S L hs xs post hmax hnot pre (seen ++ [a])
      (by rw [← hL]; simp)
    rw [if_neg (hnot a (by rw [← hL]; simp) hane), hrec, List.map_cons, List.prod_cons, hfa]
    ring

/-! ### Histories of red arrivals -/

theorem hist_map {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (l : List (Fin n))
    (hl : l.Pairwise (fun a b => v a < v b)) :
    hist v S l = l.map (fun x => ((S.filter (fun y => v x < v y)).card, 0)) := by
  unfold hist
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, rankPair]
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    rw [List.length_take] at hi
    have hij : i < j := lt_of_lt_of_le hi (min_le_left _ _)
    have hil : i < l.length := by omega
    have hjl : j < l.length := by simpa using h2
    rw [← hia, List.getElem_take]
    have := List.pairwise_iff_getElem.mp hl i j hil hjl hij
    simp only [decide_eq_true_eq, not_lt]
    exact le_of_lt this

section Red

variable (n m : ℕ) (hmn : m ≤ n) (v : Fin n → ℝ) (S : Finset (Fin n))
  (hred : ∀ i j : Fin n, i < j → (j : ℕ) < m → v i < v j)
  (hpos : ∀ i : Fin n, (i : ℕ) < m → 0 < v i)
  (hneg : ∀ i : Fin n, m ≤ (i : ℕ) → v i < 0)

include hred hpos hneg in
theorem cnt_eq (x : Fin n) (hx : x.val < m) :
    (S.filter (fun y => v x < v y)).card =
      bitNorm ((bits S).take m) - ((bits S).take (x.val + 1)).count true := by
  unfold bitNorm
  rw [ct_bits, ct_bits, ← Finset.card_sdiff_of_subset]
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hy, hv⟩
      have hym : y.val < m := by
        by_contra h
        push_neg at h
        have := hneg y h
        have := hpos x hx
        linarith
      refine ⟨⟨hy, hym⟩, ?_⟩
      rintro ⟨_, hyx⟩
      rcases lt_or_eq_of_le (show y.val ≤ x.val by omega) with h | h
      · have := hred y x (Fin.lt_def.mpr h) hx
        linarith
      · have : y = x := Fin.ext h
        rw [this] at hv
        exact lt_irrefl _ hv
    · rintro ⟨⟨hy, hym⟩, hn⟩
      refine ⟨hy, ?_⟩
      have hxy : x < y := by
        rw [Fin.lt_def]
        by_contra h
        exact hn ⟨hy, by omega⟩
      exact hred x y hxy hym
  · intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, by omega⟩

include hmn hred hpos hneg in
theorem histB_eq (i : ℕ) (hi : i < n) (him : i < m) :
    histB (bitNorm ((bits S).take m)) ((bits S).take (i + 1)) =
      hist v S ((indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n)))) := by
  have hLm : ∀ b ∈ (indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n))),
      b.val ≤ i := by
    intro b hb
    have := (List.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at this
    exact Fin.le_def.mp this
  have hLs : ((indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n)))).Pairwise
      (· < ·) := List.Pairwise.filter _ (io_sorted n S)
  have hpw : ((indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n)))).Pairwise
      (fun a b => v a < v b) :=
    List.Pairwise.imp_of_mem (fun {a b} _ hb hab => hred a b hab (by have := hLm b hb; omega))
      hLs
  have hR : hist v S ((indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n)))) =
      (((indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n)))).map Fin.val).map
        (fun j => (bitNorm ((bits S).take m) - ((bits S).take (j + 1)).count true, 0)) := by
    rw [hist_map v S _ hpw, List.map_map]
    apply List.map_congr_left
    intro x hx
    have hxm : x.val < m := by have := hLm x hx; omega
    show ((S.filter (fun y => v x < v y)).card, 0) =
      (bitNorm ((bits S).take m) - ((bits S).take (x.val + 1)).count true, 0)
    rw [cnt_eq n m v S hred hpos hneg x hxm]
  have hlen : ((bits S).take (i + 1)).length = i + 1 := by
    rw [List.length_take, bits_length]; omega
  have hL : histB (bitNorm ((bits S).take m)) ((bits S).take (i + 1)) =
      ((List.range (i + 1)).filter (fun j => decide ((bits S)[j]? = some false))).map
        (fun j => (bitNorm ((bits S).take m) - ((bits S).take (j + 1)).count true, 0)) := by
    unfold histB
    rw [hlen]
    have hf : (List.range (i + 1)).filter
        (fun j => decide (((bits S).take (i + 1))[j]? = some false)) =
        (List.range (i + 1)).filter (fun j => decide ((bits S)[j]? = some false)) := by
      apply List.filter_congr
      intro j hj
      rw [List.mem_range] at hj
      rw [List.getElem?_take, if_pos hj]
    rw [hf]
    apply List.map_congr_left
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp (List.mem_filter.mp hj).1
    rw [List.take_take, min_eq_left (show j + 1 ≤ i + 1 by omega)]
  have hidx : (List.range (i + 1)).filter (fun j => decide ((bits S)[j]? = some false)) =
      ((indexOrder n S).filter (fun z => decide (z ≤ (⟨i, hi⟩ : Fin n)))).map Fin.val := by
    apply List.SortedLT.eq_of_mem_iff
    · exact List.Pairwise.sortedLT (List.Pairwise.filter _ List.pairwise_lt_range)
    · exact List.Pairwise.sortedLT (List.Pairwise.map Fin.val (fun a b h => h) hLs)
    · intro j
      rw [List.mem_filter, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨hj, hd⟩
        have hjn : j < n := by omega
        rw [decide_eq_true_eq, bits_get S j hjn] at hd
        have hjS : (⟨j, hjn⟩ : Fin n) ∉ S := by simpa using hd
        refine ⟨⟨j, hjn⟩, ?_, rfl⟩
        rw [List.mem_filter, decide_eq_true_eq]
        exact ⟨(mem_io S _).mpr hjS, Fin.le_def.mpr (by show j ≤ i; omega)⟩
      · rintro ⟨z, hz, rfl⟩
        have hzi := hLm z hz
        have hzS := (mem_io S z).mp (List.mem_filter.mp hz).1
        refine ⟨by omega, ?_⟩
        rw [decide_eq_true_eq, bits_get S z.val z.isLt]
        simpa using hzS
  rw [hR, hL, hidx]

end Red

/-! ### The pointwise comparison -/

theorem pointwise (A : Algorithm) (hA : IsAlgorithm A) (m n : ℕ) (hmn : m ≤ n)
    (v : Fin n → ℝ) (hv : Function.Injective v)
    (hred : ∀ i j : Fin n, i < j → (j : ℕ) < m → v i < v j)
    (hpos : ∀ i : Fin n, (i : ℕ) < m → 0 < v i)
    (hneg : ∀ i : Fin n, m ≤ (i : ℕ) → v i < 0) (S : Finset (Fin n)) :
    winOnSample A v S (indexOrder n S) ≤ winColored (Bst A) m (bits S) := by
  by_cases hz : false ∈ (bits S).take m
  · obtain ⟨h0, hle, hlast, hafter⟩ := lz_spec _ hz
    have hlenm : ((bits S).take m).length = m := by
      rw [List.length_take, bits_length]; omega
    obtain ⟨k, hk⟩ : ∃ k, lastZero ((bits S).take m) = k + 1 :=
      ⟨lastZero ((bits S).take m) - 1, by omega⟩
    have hkm : k < m := by omega
    have hkn : k < n := by omega
    have hxsS : (⟨k, hkn⟩ : Fin n) ∉ S := by
      rw [hk, Nat.add_sub_cancel, List.getElem?_take, if_pos hkm, bits_get S k hkn] at hlast
      simpa using hlast
    have hafterS : ∀ i (hi : i < n), k < i → i < m → (⟨i, hi⟩ : Fin n) ∈ S := by
      intro i hi h1 h2
      have := hafter i (by omega) (by omega)
      rw [List.getElem?_take, if_pos h2, bits_get S i hi] at this
      simpa using this
    have hxsL : (⟨k, hkn⟩ : Fin n) ∈ indexOrder n S := (mem_io S _).mpr hxsS
    have hsort := io_sorted n S
    have hmax : ∀ z ∈ indexOrder n S, v z ≤ v ⟨k, hkn⟩ := by
      intro z hz'
      have hzS := (mem_io S z).mp hz'
      rcases lt_trichotomy z.val k with h | h | h
      · exact le_of_lt (hred z ⟨k, hkn⟩ (Fin.lt_def.mpr h) hkm)
      · have : z = ⟨k, hkn⟩ := Fin.ext h
        exact le_of_eq (congrArg v this)
      · by_cases hzm : z.val < m
        · exact absurd (hafterS z.val z.isLt h hzm) hzS
        · push_neg at hzm
          have := hneg z hzm
          have := hpos ⟨k, hkn⟩ hkm
          linarith
    have hnot : ∀ y ∈ indexOrder n S, y ≠ ⟨k, hkn⟩ → ¬ ∀ z ∈ indexOrder n S, v z ≤ v y := by
      intro y hy hne hall
      have h1 := hall _ hxsL
      have h2 := hmax y hy
      exact hne (hv (le_antisymm h2 h1))
    obtain ⟨pre, post, hdec⟩ := List.append_of_mem hxsL
    have hne : indexOrder n S ≠ [] := List.ne_nil_of_mem hxsL
    have e := stop_formula A v S (indexOrder n S) hsort ⟨k, hkn⟩ post hmax hnot pre []
      (by rw [hdec]; simp)
    rw [← hdec] at e
    have hwin : winOnSample A v S (indexOrder n S) =
        (pre.map (fun y => 1 - A n S.card
          (hist v S ((indexOrder n S).filter (fun z => decide (z ≤ y)))))).prod *
          A n S.card (hist v S ((indexOrder n S).filter
            (fun z => decide (z ≤ (⟨k, hkn⟩ : Fin n))))) := by
      unfold winOnSample
      rw [if_neg hne]
      exact e
    have hrb : bitNorm ((bits S).take m) + bitNorm ((bits S).drop m) = S.card := by
      unfold bitNorm
      rw [← count_split]
      exact bitNorm_bits S
    have hB : ∀ i (hi : i < n), Bst A n (bitNorm ((bits S).take m)) (bitNorm ((bits S).drop m))
        ((bits S).take (i + 1)) =
        if (⟨i, hi⟩ : Fin n) ∈ S then 0
        else A n S.card (histB (bitNorm ((bits S).take m)) ((bits S).take (i + 1))) := by
      intro i hi
      unfold Bst
      rw [getLast_take (bits S) (i + 1) (by omega) (by rw [bits_length]; omega), Nat.add_sub_cancel,
        bits_get S i hi, hrb]
      by_cases h : (⟨i, hi⟩ : Fin n) ∈ S
      · simp [h]
      · simp [h]
    have hpre_mem : ∀ y : Fin n, y ∈ pre ↔ y.val < k ∧ y ∉ S := by
      intro y
      have hs' := hsort
      rw [hdec, List.pairwise_append] at hs'
      constructor
      · intro hy
        have hyL : y ∈ indexOrder n S := by rw [hdec]; simp [hy]
        refine ⟨?_, (mem_io S y).mp hyL⟩
        have := hs'.2.2 y hy ⟨k, hkn⟩ (by simp)
        exact Fin.lt_def.mp this
      · rintro ⟨hyk, hyS⟩
        have hyL := (mem_io S y).mpr hyS
        rw [hdec, List.mem_append, List.mem_cons] at hyL
        rcases hyL with h | h | h
        · exact h
        · rw [h] at hyk
          exact absurd hyk (lt_irrefl _)
        · have := (List.pairwise_cons.mp hs'.2.1).1 y h
          have h2 : k < y.val := Fin.lt_def.mp this
          omega
    have hpre_nd : pre.Nodup := by
      have hs' := hsort
      rw [hdec, List.pairwise_append] at hs'
      exact hs'.1.nodup
    have hprod : ∏ j ∈ Finset.Ico 1 (k + 1),
        (1 - Bst A n (bitNorm ((bits S).take m)) (bitNorm ((bits S).drop m)) ((bits S).take j)) =
        (pre.map (fun y => 1 - A n S.card
          (hist v S ((indexOrder n S).filter (fun z => decide (z ≤ y)))))).prod := by
      rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
      calc ∏ i ∈ Finset.range k, (1 - Bst A n (bitNorm ((bits S).take m))
              (bitNorm ((bits S).drop m)) ((bits S).take (1 + i)))
          = ∏ i ∈ Finset.range n, (if i < k then (1 - Bst A n (bitNorm ((bits S).take m))
              (bitNorm ((bits S).drop m)) ((bits S).take (1 + i))) else 1) := by
            rw [← Finset.prod_filter]
            congr 1
            ext i
            simp only [Finset.mem_range, Finset.mem_filter]
            exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
        _ = ∏ y : Fin n, (if y.val < k then (1 - Bst A n (bitNorm ((bits S).take m))
              (bitNorm ((bits S).drop m)) ((bits S).take (1 + y.val))) else 1) :=
            (Fin.prod_univ_eq_prod_range (fun i => if i < k then (1 - Bst A n
              (bitNorm ((bits S).take m)) (bitNorm ((bits S).drop m))
              ((bits S).take (1 + i))) else 1) n).symm
        _ = ∏ y : Fin n, (if y.val < k ∧ y ∉ S then (1 - A n S.card
              (hist v S ((indexOrder n S).filter (fun z => decide (z ≤ y))))) else 1) := by
            apply Finset.prod_congr rfl
            intro y _
            rw [add_comm 1 y.val, hB y.val y.isLt, Fin.eta]
            by_cases hyk : y.val < k
            · by_cases hyS : y ∈ S
              · rw [if_pos hyk, if_pos hyS, if_neg (fun h => h.2 hyS)]
                ring
              · rw [if_pos hyk, if_neg hyS, if_pos ⟨hyk, hyS⟩,
                  histB_eq n m hmn v S hred hpos hneg y.val y.isLt (by omega), Fin.eta]
            · rw [if_neg hyk, if_neg (fun h => hyk h.1)]
        _ = ∏ y ∈ Finset.univ.filter (fun y : Fin n => y.val < k ∧ y ∉ S), (1 - A n S.card
              (hist v S ((indexOrder n S).filter (fun z => decide (z ≤ y))))) :=
            (Finset.prod_filter _ _).symm
        _ = ∏ y ∈ pre.toFinset, (1 - A n S.card
              (hist v S ((indexOrder n S).filter (fun z => decide (z ≤ y))))) := by
            congr 1
            ext y
            rw [Finset.mem_filter, List.mem_toFinset, hpre_mem]
            simp
        _ = _ := List.prod_toFinset _ hpre_nd
    have hcol : winColored (Bst A) m (bits S) =
        (pre.map (fun y => 1 - A n S.card
          (hist v S ((indexOrder n S).filter (fun z => decide (z ≤ y)))))).prod *
          A n S.card (hist v S ((indexOrder n S).filter
            (fun z => decide (z ≤ (⟨k, hkn⟩ : Fin n))))) := by
      unfold winColored
      rw [if_pos hz, hk, bits_length, hprod, hB k hkn, if_neg hxsS,
        histB_eq n m hmn v S hred hpos hneg k hkn hkm]
      ring
    rw [hwin, hcol]
  · unfold winColored
    rw [if_neg hz]
    unfold winOnSample
    split_ifs
    · exact le_refl _
    · exact stop_le_one A hA v S _ _ []

theorem main (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (A : Algorithm) (hA : IsAlgorithm A)
    (m n : ℕ) (hmn : m ≤ n) (v : Fin n → ℝ) (hv : Function.Injective v)
    (hred : ∀ i j : Fin n, i < j → (j : ℕ) < m → v i < v j)
    (hpos : ∀ i : Fin n, (i : ℕ) < m → 0 < v i)
    (hneg : ∀ i : Fin n, m ≤ (i : ℕ) → v i < 0) :
    winProb p A v (indexOrder n) ≤ perfColored p (Bst A) m n := by
  rw [perf_eq]
  unfold winProb
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left (pointwise A hA m n hmn v hv hred hpos hneg S)
  unfold sampleWeight
  exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)

end Aux_SecSampling_proposition_6

open SecSampling Aux_SecSampling_proposition_6 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (A : Algorithm) (hA : IsAlgorithm A) :
    ∃ B : ColStrategy, IsColStrategy B ∧
      ∀ (m n : ℕ), m ≤ n → ∀ v : Fin n → ℝ, Function.Injective v →
        (∀ i j : Fin n, i < j → (j : ℕ) < m → v i < v j) →
        (∀ i : Fin n, (i : ℕ) < m → 0 < v i) →
        (∀ i : Fin n, m ≤ (i : ℕ) → v i < 0) →
        winProb p A v (indexOrder n) ≤ perfColored p B m n :=
  ⟨Bst A, Bst_col A hA, fun m n hmn v hv hred hpos hneg =>
    main p hp0 hp1 A hA m n hmn v hv hred hpos hneg⟩
