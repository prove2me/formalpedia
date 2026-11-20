-- Prove2me | solution 2 for TetrisHard.Rows.cleared_rows_inapproximability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:03:37.344312+00:00
-- url     : https://prove2.me/submissions/84269c12-82f4-4a23-b23a-047fdef8a90f

import Definitions.Def_TetrisHard_Rows_Reservoir
import Definitions.Def_TetrisHard_Rows_PaddedGapReduction
import Theorems.Thm_TetrisHard_Rows_Padded_paddedNoBound_code_polytime
import Theorems.Thm_TetrisHard_Rows_Padded_paddedGapGame_code_polytime
import Theorems.Thm_TetrisHard_Rows_Padded_paddedReservoir_completeness
import Theorems.Thm_TetrisHard_Rows_Padded_paddedReservoir_soundness
import Theorems.Thm_TetrisHard_Rows_three_partition_strong_np_complete
import Theorems.Thm_TetrisHard_Rows_unary_lt_decider
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairFst
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairSnd
import Theorems.Thm_CookPvsNP_polyTimeComputable_tagged_pair
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false

namespace TetrisHard.Rows.Padded
open TetrisHard.Rows

lemma baseBoard_has_false (P : ThreePartition) (staging : ℕ) (y : ℕ)
    (hy : y < (baseBoard P staging).height) :
    ∃ x : ℕ, x < 6 * P.s + 3 ∧ (baseBoard P staging).occupied (x, y) = false := by
  have hy' : y < baseHeight P + 3 * P.s + staging := hy
  by_cases hH : y < baseHeight P
  · by_cases h2 : y + 2 = baseHeight P
    · refine ⟨6 * P.s, by omega, ?_⟩
      simp [Board.occupied, baseBoard, hH, h2]
      omega
    · refine ⟨6 * P.s + 2, by omega, ?_⟩
      simp [Board.occupied, baseBoard, hH, h2]
      have : (6 * (P.s : ℤ) + 2).toNat = 6 * P.s + 2 := by omega
      simp [this]
      omega
  · refine ⟨0, by omega, ?_⟩
    simp [Board.occupied, baseBoard, hH]
    omega

lemma paddedReservoirBoard_legal (P : ThreePartition) (pad K staging r : ℕ) (hpad : 1 ≤ pad) :
    (paddedReservoirBoard P pad K staging r).Legal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [paddedReservoirBoard, baseBoard, baseHeight]
  · simp [paddedReservoirBoard]
  · intro y
    by_cases h1 : y.val < r
    · refine ⟨⟨1, by simp [paddedReservoirBoard]⟩, ?_⟩
      simp [paddedReservoirBoard, h1]
    · by_cases h2 : y.val = r
      · refine ⟨⟨6 * (P.s + pad), by simp [paddedReservoirBoard]⟩, ?_⟩
        simp [paddedReservoirBoard, h2]
      · by_cases h3 : y.val = r + 1
        · refine ⟨⟨6 * (P.s + pad), by simp [paddedReservoirBoard]⟩, ?_⟩
          simp [paddedReservoirBoard, h3]
        · by_cases h4 : y.val < r + 2 + 4 * K
          · refine ⟨⟨6 * (P.s + pad) - 1, by simp [paddedReservoirBoard]; omega⟩, ?_⟩
            simp [paddedReservoirBoard, h1, h2, h3, h4]
          · by_cases h5 : y.val < r + 2 + 4 * K + 12 * pad
            · refine ⟨⟨6 * P.s + 2, by simp [paddedReservoirBoard]⟩, ?_⟩
              simp [paddedReservoirBoard, h1, h2, h3, h4, h5]
            · have hy' : y.val - (r + 2 + 4 * K + 12 * pad) < (baseBoard P staging).height := by
                have := y.isLt; simp [paddedReservoirBoard] at this; omega
              obtain ⟨x, hx, hocc⟩ := baseBoard_has_false P staging _ hy'
              refine ⟨⟨x, by simp [paddedReservoirBoard]; omega⟩, ?_⟩
              simp only [paddedReservoirBoard, h1, h2, h3, h4, h5, hx, ↓reduceIte]
              have hcast : (y.val : ℤ) - (r + 2 + 4 * K + 12 * pad) =
                  ((y.val - (r + 2 + 4 * K + 12 * pad) : ℕ) : ℤ) := by omega
              rw [hcast]
              exact hocc
  · intro y ⟨y', x', hyy', htrue⟩
    by_cases h1 : y.val < r
    · refine ⟨⟨0, by simp [paddedReservoirBoard]⟩, ?_⟩
      simp [paddedReservoirBoard, h1]
    · by_cases h2 : y.val = r
      · refine ⟨⟨0, by simp [paddedReservoirBoard]⟩, ?_⟩
        simp [paddedReservoirBoard, h2]; omega
      · by_cases h3 : y.val = r + 1
        · refine ⟨⟨0, by simp [paddedReservoirBoard]⟩, ?_⟩
          simp [paddedReservoirBoard, h3]; omega
        · by_cases h4 : y.val < r + 2 + 4 * K
          · refine ⟨⟨0, by simp [paddedReservoirBoard]⟩, ?_⟩
            simp only [paddedReservoirBoard, h1, h2, h3, h4, ↓reduceIte, decide_eq_true_eq]
            omega
          · by_cases h5 : y.val < r + 2 + 4 * K + 12 * pad
            · refine ⟨⟨0, by simp [paddedReservoirBoard]⟩, ?_⟩
              simp [paddedReservoirBoard, h1, h2, h3, h4, h5]
            · by_cases h6 : y.val < r + 2 + 4 * K + 12 * pad + baseHeight P
              · refine ⟨⟨6 * P.s + 3, by simp [paddedReservoirBoard]; omega⟩, ?_⟩
                simp [paddedReservoirBoard, h1, h2, h3, h4, h5, h6]
              · exfalso
                have h1' : ¬ y'.val < r := by omega
                have h2' : ¬ y'.val = r := by omega
                have h3' : ¬ y'.val = r + 1 := by omega
                have h4' : ¬ y'.val < r + 2 + 4 * K := by omega
                have h5' : ¬ y'.val < r + 2 + 4 * K + 12 * pad := by omega
                have h6' : ¬ y'.val < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
                simp only [paddedReservoirBoard, h1', h2', h3', h4', h5', h6', ↓reduceIte] at htrue
                split_ifs at htrue with hx'
                · have hy'lt : y'.val - (r + 2 + 4 * K + 12 * pad) < (baseBoard P staging).height := by
                    have := y'.isLt; simp [paddedReservoirBoard] at this; omega
                  have hge : baseHeight P ≤ y'.val - (r + 2 + 4 * K + 12 * pad) := by omega
                  have hcast : (y'.val : ℤ) - (r + 2 + 4 * K + 12 * pad) =
                      ((y'.val - (r + 2 + 4 * K + 12 * pad) : ℕ) : ℤ) := by omega
                  rw [hcast] at htrue
                  simp [Board.occupied, baseBoard, hge] at htrue
                  simp [baseBoard] at hy'lt
                  omega
                · simp at htrue

theorem paddedReservoirGame_pieces_length (P : ThreePartition) (pad K st r : ℕ) :
    (paddedReservoirGame P pad K st r).pieces.length =
      (basePieces P).length + 3 * pad + K + 1 + r * (6 * (P.s + pad) + 2) / 4 := by
  simp [paddedReservoirGame]; omega

theorem paddedReservoirGame_pieces_le (P : ThreePartition) (pad K st r : ℕ) (hr : 1 ≤ r) :
    (paddedReservoirGame P pad K st r).pieces.length ≤ paddedPieceFactor P pad K * r := by
  rw [paddedReservoirGame_pieces_length]
  unfold paddedPieceFactor
  have h1 : r * (6 * (P.s + pad) + 2) / 4 ≤ r * (6 * (P.s + pad) + 2) := Nat.div_le_self _ _
  have h2 : (basePieces P).length + 3 * pad + K + 1 ≤
      ((basePieces P).length + 3 * pad + K + 1) * r :=
    Nat.le_mul_of_pos_right _ hr
  have h3 : r * (6 * (P.s + pad) + 2) + r = (6 * (P.s + pad) + 3) * r := by ring
  have h4 : ((basePieces P).length + 3 * pad + K + 1 + 6 * (P.s + pad) + 3) * r =
      ((basePieces P).length + 3 * pad + K + 1) * r + (6 * (P.s + pad) + 3) * r := by ring
  omega

theorem paddedReservoirGame_pieces_ne_nil (P : ThreePartition) (pad K st r : ℕ) :
    (paddedReservoirGame P pad K st r).pieces ≠ [] := by
  simp [paddedReservoirGame]

end TetrisHard.Rows.Padded

namespace TetrisHard.Rows.PaddedRoot

open TetrisHard.Rows TetrisHard.Rows.Padded CookPvsNP

/-! ### Unary codes are injective -/

theorem rep_true_false_inj : ∀ (n m : ℕ) (l l' : List Bool),
    List.replicate n true ++ false :: l = List.replicate m true ++ false :: l' →
      n = m ∧ l = l'
  | 0, 0, l, l', h => by simpa using h
  | 0, m + 1, l, l', h => by simp [List.replicate_succ] at h
  | n + 1, 0, l, l', h => by simp [List.replicate_succ] at h
  | n + 1, m + 1, l, l', h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      have := rep_true_false_inj n m l l' h
      exact ⟨by omega, this.2⟩

theorem unaryCode_cons (n : ℕ) (ns : List ℕ) :
    unaryCode (n :: ns) = List.replicate n true ++ false :: unaryCode ns := by
  simp [unaryCode]

theorem unaryCode_nil : unaryCode [] = [] := by simp [unaryCode]

theorem unaryCode_inj : ∀ (ns ms : List ℕ), unaryCode ns = unaryCode ms → ns = ms
  | [], [], _ => rfl
  | [], m :: ms, h => by
      rw [unaryCode_nil, unaryCode_cons] at h
      exact absurd h.symm (by simp)
  | n :: ns, [], h => by
      rw [unaryCode_nil, unaryCode_cons] at h
      exact absurd h (by simp)
  | n :: ns, m :: ms, h => by
      rw [unaryCode_cons, unaryCode_cons] at h
      obtain ⟨rfl, h2⟩ := rep_true_false_inj _ _ _ _ h
      rw [unaryCode_inj ns ms h2]

theorem unaryCode_append_inj : ∀ (ns ms : List ℕ) (l l' : List Bool),
    ns.length = ms.length → unaryCode ns ++ l = unaryCode ms ++ l' → ns = ms ∧ l = l'
  | [], [], l, l', _, h => by simpa [unaryCode_nil] using h
  | n :: ns, m :: ms, l, l', hlen, h => by
      rw [unaryCode_cons, unaryCode_cons] at h
      simp only [List.append_assoc, List.cons_append] at h
      obtain ⟨rfl, h2⟩ := rep_true_false_inj n m _ _ h
      obtain ⟨rfl, rfl⟩ := unaryCode_append_inj ns ms l l' (by simpa using hlen) h2
      exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h

/-! ### Codes of instances and games are injective -/

theorem ThreePartition_code_inj {P Q : ThreePartition} (h : P.code = Q.code) : P = Q := by
  obtain ⟨s, T, e⟩ := P
  obtain ⟨s', T', e'⟩ := Q
  have h' := unaryCode_inj _ _ h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h'
  obtain ⟨rfl, rfl, h3⟩ := h'
  have : e = e' := List.ofFn_injective h3
  subst this
  rfl

theorem eq_of_flatten_eq {β : Type} (n : ℕ) : ∀ (L L' : List (List β)),
    L.length = L'.length → (∀ l ∈ L, l.length = n) → (∀ l ∈ L', l.length = n) →
      L.flatten = L'.flatten → L = L'
  | [], [], _, _, _, _ => rfl
  | l :: L, l' :: L', hlen, hL, hL', h => by
      simp only [List.flatten_cons] at h
      have hl : l.length = l'.length := by
        rw [hL l (by simp), hL' l' (by simp)]
      obtain ⟨rfl, h2⟩ := List.append_inj h hl
      rw [eq_of_flatten_eq n L L' (by simpa using hlen) (fun x hx => hL x (by simp [hx]))
        (fun x hx => hL' x (by simp [hx])) h2]
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h

theorem Board_rows_length_flatten (B : Board) :
    B.rows.flatten.length = B.height * B.width := by
  simp [Board.rows, List.sum_ofFn]

theorem Board_eq_of_rows {B B' : Board} (hh : B.height = B'.height) (hw : B.width = B'.width)
    (hr : B.rows.flatten = B'.rows.flatten) : B = B' := by
  obtain ⟨h, w, c⟩ := B
  obtain ⟨h', w', c'⟩ := B'
  simp only at hh hw
  subst hh hw
  have hrows : (List.ofFn fun y => List.ofFn fun x => c y x) =
      (List.ofFn fun y => List.ofFn fun x => c' y x) := by
    apply eq_of_flatten_eq w
    · simp
    · intro l hl; simp only [List.mem_ofFn] at hl; obtain ⟨y, rfl⟩ := hl; simp
    · intro l hl; simp only [List.mem_ofFn] at hl; obtain ⟨y, rfl⟩ := hl; simp
    · exact hr
  have : c = c' := by
    funext y x
    have h1 := congrFun (List.ofFn_injective hrows) y
    exact congrFun (List.ofFn_injective h1) x
  subst this
  rfl

theorem Piece_code_injective : Function.Injective Piece.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [Piece.code] at h)

theorem Game_code_inj {G G' : Game} (h : G.code = G'.code) : G = G' := by
  unfold Game.code at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := unaryCode_append_inj [G.board.height, G.board.width]
    [G'.board.height, G'.board.width] _ _ rfl h
  simp only [List.cons.injEq, and_true] at h1
  obtain ⟨hh, hw⟩ := h1
  have hlen : G.board.rows.flatten.length = G'.board.rows.flatten.length := by
    rw [Board_rows_length_flatten, Board_rows_length_flatten, hh, hw]
  obtain ⟨h3, h4⟩ := List.append_inj h2 hlen
  have hB : G.board = G'.board := Board_eq_of_rows hh hw h3
  have h5 := unaryCode_inj _ _ h4
  simp only [List.cons.injEq] at h5
  have hp : G.pieces = G'.pieces :=
    (List.map_injective_iff.mpr Piece_code_injective) h5.2
  cases G; cases G'
  simp only at hB hp
  rw [hB, hp]

/-! ### Scaling and the fixed instances -/

theorem ThreePartition_scale_valid {P : ThreePartition} (hP : P.Valid) : P.scale.Valid := by
  obtain ⟨s, T, e⟩ := P
  obtain ⟨hsum, hbd⟩ := hP
  change (∑ i : Fin (3 * s), e i) = s * T at hsum
  change ∀ i : Fin (3 * s), T < 4 * e i ∧ 2 * e i < T at hbd
  refine ⟨?_, fun i => ?_⟩
  · show (∑ i : Fin (3 * s), 6 * s * e i) = s * (6 * s * T)
    rw [← Finset.mul_sum, hsum]; ring
  · have hs : 0 < s := by
      have : (i : ℕ) < 3 * s := i.2
      omega
    obtain ⟨h1, h2⟩ := hbd i
    show 6 * s * T < 4 * (6 * s * e i) ∧ 2 * (6 * s * e i) < 6 * s * T
    constructor <;> nlinarith

theorem ThreePartition_scale_hasSolution_iff (P : ThreePartition) :
    P.scale.HasSolution ↔ P.HasSolution := by
  obtain ⟨s, T, e⟩ := P
  constructor
  · intro hsol
    obtain ⟨assign, h⟩ : ∃ assign : Fin (3 * s) → Fin s, ∀ j : Fin s,
        (∑ i ∈ Finset.univ.filter (fun i => assign i = j), 6 * s * e i) = 6 * s * T := hsol
    refine ⟨assign, fun j => ?_⟩
    have hs : 0 < s := by
      have : (j : ℕ) < s := j.2
      omega
    have := h j
    rw [← Finset.mul_sum] at this
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · intro hsol
    obtain ⟨assign, h⟩ : ∃ assign : Fin (3 * s) → Fin s, ∀ j : Fin s,
        (∑ i ∈ Finset.univ.filter (fun i => assign i = j), e i) = T := hsol
    show ∃ assign : Fin (3 * s) → Fin s, ∀ j : Fin s,
        (∑ i ∈ Finset.univ.filter (fun i => assign i = j), 6 * s * e i) = 6 * s * T
    refine ⟨assign, fun j => ?_⟩
    rw [← Finset.mul_sum, h j]

theorem ThreePartition_scale_normalized {P : ThreePartition} (hP : P.Valid) (hs : 0 < P.s) :
    P.scale.Normalized := by
  obtain ⟨s, T, e⟩ := P
  simp only [ThreePartition.scale, ThreePartition.Valid, ThreePartition.Normalized] at hP hs ⊢
  obtain ⟨hsum, hbd⟩ := hP
  have hT : 0 < T := by
    obtain ⟨_, h2⟩ := hbd ⟨0, by omega⟩
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    rw [← Finset.mul_sum] at hA
    have hA' : (∑ i ∈ A, e i) = T := Nat.eq_of_mul_eq_mul_left (by omega) hA
    have hne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hA'
      omega
    have h4 : A.card * T < 4 * T := by
      have : (∑ i ∈ A, T) < ∑ i ∈ A, 4 * e i :=
        Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hbd i).1)
      rw [Finset.sum_const, ← Finset.mul_sum, hA'] at this
      simpa using this
    have h2 : 2 * T < A.card * T := by
      have : (∑ i ∈ A, 2 * e i) < ∑ i ∈ A, T :=
        Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hbd i).2)
      rw [Finset.sum_const, ← Finset.mul_sum, hA'] at this
      simpa using this
    have h4' := lt_of_mul_lt_mul_right h4 (Nat.zero_le _)
    have h2' := lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
    omega
  · exact ⟨3 * s * T, by ring⟩
  · intro A hA
    rw [← Finset.mul_sum] at hA
    have hne : (∑ i ∈ A, e i) ≠ T := by
      intro h; exact hA (by rw [h])
    have key : ((6 * s * T : ℕ) : ℤ) - ∑ i ∈ A, ((6 * s * e i : ℕ) : ℤ) =
        (6 * s : ℤ) * ((T : ℤ) - ((∑ i ∈ A, e i : ℕ) : ℤ)) := by
      push_cast
      rw [mul_sub, Finset.mul_sum]
    rw [key, abs_mul]
    have h1 : (1 : ℤ) ≤ |(T : ℤ) - ((∑ i ∈ A, e i : ℕ) : ℤ)| := by
      have : (T : ℤ) - ((∑ i ∈ A, e i : ℕ) : ℤ) ≠ 0 := by
        intro h0; apply hne; omega
      exact Int.one_le_abs this
    have h6 : (0 : ℤ) ≤ 6 * s := by positivity
    rw [abs_of_nonneg h6]
    nlinarith

theorem yesInstance_valid : yesInstance.Valid := by
  unfold ThreePartition.Valid yesInstance; decide

theorem yesInstance_hasSolution : yesInstance.HasSolution := by
  refine ⟨fun _ => ⟨0, by decide⟩, ?_⟩
  unfold yesInstance; decide

theorem noInstance_valid : noInstance.Valid := by
  unfold ThreePartition.Valid noInstance; decide

theorem noInstance_not_hasSolution : ¬ noInstance.HasSolution := by
  classical
  rintro ⟨assign, h⟩
  have h0 := h ⟨0, by decide⟩
  have hev : Even (∑ i ∈ Finset.univ.filter (fun i => assign i = ⟨0, by decide⟩),
      noInstance.entry i) := by
    apply Finset.even_sum
    intro i _
    fin_cases i <;> decide
  rw [h0] at hev
  exact absurd hev (by decide)

theorem rawInstance_spec (w : List Bool) :
    (rawInstance w).Valid ∧ 0 < (rawInstance w).s ∧
      (w ∈ threePartitionLanguage ↔ (rawInstance w).HasSolution) := by
  classical
  unfold rawInstance
  by_cases h : ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code
  · rw [dif_pos h]
    obtain ⟨hv, hs, hw⟩ := Classical.choose_spec h
    refine ⟨hv, hs, ?_⟩
    constructor
    · rintro ⟨Q, -, hQ, hwQ⟩
      have : Q = Classical.choose h := ThreePartition_code_inj (hwQ.symm.trans hw)
      rw [← this]; exact hQ
    · intro hsol
      exact ⟨_, hv, hsol, hw⟩
  · rw [dif_neg h]
    by_cases h' : ∃ P : ThreePartition, P.Valid ∧ w = P.code
    · rw [if_pos h']
      refine ⟨yesInstance_valid, by decide, ?_⟩
      obtain ⟨P, hv, hw⟩ := h'
      have hs : P.s = 0 := by
        by_contra hne
        exact h ⟨P, hv, Nat.pos_of_ne_zero hne, hw⟩
      refine ⟨fun _ => yesInstance_hasSolution, fun _ => ⟨P, hv, ?_, hw⟩⟩
      refine ⟨fun i => (Fin.cast (by rw [hs]) i : Fin 0).elim0, fun j => ?_⟩
      exact (Fin.cast hs j).elim0
    · rw [if_neg h']
      refine ⟨noInstance_valid, by decide, ?_⟩
      constructor
      · rintro ⟨P, hv, -, hw⟩
        exact absurd ⟨P, hv, hw⟩ h'
      · intro hsol; exact absurd hsol noInstance_not_hasSolution

theorem normInstance_spec (w : List Bool) :
    (normInstance w).Valid ∧ (normInstance w).Normalized ∧ 0 < (normInstance w).s ∧
      (w ∈ threePartitionLanguage ↔ (normInstance w).HasSolution) := by
  obtain ⟨hv, hs, hiff⟩ := rawInstance_spec w
  refine ⟨ThreePartition_scale_valid hv, ThreePartition_scale_normalized hv hs, hs, ?_⟩
  unfold normInstance
  rw [ThreePartition_scale_hasSolution_iff]
  exact hiff

/-! ### The arithmetic gap -/

theorem gap_ineq (a M k p : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hk : 1 ≤ (k : ℝ) * δ)
    (hM : 1 ≤ M) (hp1 : 1 ≤ p) (hp : p ≤ M * (2 * (a * M + 1) ^ k)) :
    (a : ℝ) * (p : ℝ) ^ (1 - δ) < ((2 * (a * M + 1) ^ k : ℕ) : ℝ) := by
  set B : ℕ := a * M + 1 with hBdef
  set r : ℕ := 2 * B ^ k with hrdef
  have hB1 : (1 : ℝ) ≤ B := by
    have : 1 ≤ B := by omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) < r := by
    have : 0 < r := by positivity
    exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hexp : 0 ≤ 1 - δ := by linarith
  have hpM : (p : ℝ) ^ (1 - δ) ≤ (M : ℝ) * (r : ℝ) ^ (1 - δ) := by
    have h1 : (p : ℝ) ^ (1 - δ) ≤ ((M : ℝ) * r) ^ (1 - δ) := by
      apply Real.rpow_le_rpow hp0.le _ hexp
      exact_mod_cast hp
    rw [Real.mul_rpow (by linarith) hr0.le] at h1
    have h2 : (M : ℝ) ^ (1 - δ) ≤ (M : ℝ) := by
      calc (M : ℝ) ^ (1 - δ) ≤ (M : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
        _ = M := Real.rpow_one _
    have h3 : 0 ≤ (r : ℝ) ^ (1 - δ) := Real.rpow_nonneg hr0.le _
    nlinarith
  have hrδ : ((a : ℝ) * M) < (r : ℝ) ^ δ := by
    have hBk : ((B : ℝ) ^ k) ≤ r := by
      have : (B : ℝ) ^ k ≤ 2 * (B : ℝ) ^ k := by
        have : 0 ≤ (B : ℝ) ^ k := by positivity
        linarith
      simpa [hrdef] using this
    have h1 : ((B : ℝ) ^ k) ^ δ ≤ (r : ℝ) ^ δ :=
      Real.rpow_le_rpow (by positivity) hBk hδ0.le
    have h2 : ((B : ℝ) ^ k) ^ δ = (B : ℝ) ^ ((k : ℝ) * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have h3 : (B : ℝ) ^ (1 : ℝ) ≤ (B : ℝ) ^ ((k : ℝ) * δ) :=
      Real.rpow_le_rpow_of_exponent_le hB1 hk
    rw [Real.rpow_one] at h3
    have h4 : ((a : ℝ) * M) < B := by
      rw [hBdef]; push_cast; linarith
    linarith
  have hsplit : (r : ℝ) = (r : ℝ) ^ δ * (r : ℝ) ^ (1 - δ) := by
    rw [← Real.rpow_add hr0]; simp
  have hpos : 0 < (r : ℝ) ^ (1 - δ) := Real.rpow_pos_of_pos hr0 _
  have ha0 : (0 : ℝ) ≤ a := by positivity
  calc (a : ℝ) * (p : ℝ) ^ (1 - δ) ≤ (a : ℝ) * ((M : ℝ) * (r : ℝ) ^ (1 - δ)) :=
        mul_le_mul_of_nonneg_left hpM ha0
    _ = ((a : ℝ) * M) * (r : ℝ) ^ (1 - δ) := by ring
    _ < (r : ℝ) ^ δ * (r : ℝ) ^ (1 - δ) := mul_lt_mul_of_pos_right hrδ hpos
    _ = r := hsplit.symm

end TetrisHard.Rows.PaddedRoot


namespace TetrisHard.Rows

open TetrisHard.Rows.Padded TetrisHard.Rows.PaddedRoot CookPvsNP

/-- Clean soundness hypothesis for `paddedReservoirGame` at the canonical parameters
`pad = max R.radius 2 + 2`, `K = maxJump R + 2`, `st = 5 * max R.radius 2 + 12`.
Plug in `Work.PaddedSoundness_Carbon`'s soundness theorem to discharge this hypothesis! -/
def PaddedReservoirSoundness (R : Rotation) : Prop :=
  let pad := max R.radius 2 + 2
  let K := maxJump R + 2
  let st := 5 * max R.radius 2 + 12
  ∀ (P : ThreePartition), P.Valid → P.Normalized → 0 < P.s → ¬ P.HasSolution →
    ∀ (r : ℕ), Even r → 1 ≤ r →
      ∀ (v : ℕ), Attainable R (paddedReservoirGame P pad K st r) v →
        v ≤ paddedNoBound P pad K st

/-- Root reduction for Theorem 6.5 (`TetrisHard.Rows.cleared_rows_inapproximability`)
using the padded + chimney reservoir construction. Once `Work.PaddedSoundness_Carbon`
finishes, replace `(hsound : PaddedReservoirSoundness R)` with its soundness proof! -/
theorem cleared_rows_inapproximability_proof
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (ε : ℝ) (hε : 0 < ε) :
    (rowSearch R ε).NPHard := by
  intro α _ _ L hL
  obtain ⟨f, hfpoly, hf⟩ := three_partition_strong_np_complete.2 α L hL
  set δ : ℝ := min ε 1 with hδdef
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set k : ℕ := ⌈1 / δ⌉₊ with hkdef
  have hk : 1 ≤ (k : ℝ) * δ := by
    have h1 : 1 / δ ≤ (k : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hδ0] at h1
    linarith
  set pad : ℕ := max R.radius 2 + 2 with hpad_def
  set K : ℕ := maxJump R + 2 with hK_def
  set st : ℕ := 5 * max R.radius 2 + 12 with hst_def
  obtain ⟨fst, hfst, hfst_eq⟩ := polyTimeComputable_pairFst α Bool
  obtain ⟨snd, hsnd, hsnd_eq⟩ := polyTimeComputable_pairSnd α Bool
  obtain ⟨cmp, hcmp, hcmp_eq⟩ := unary_lt_decider
  let thr : List Bool → List Bool := fun w => unaryCode [paddedNoBound (normInstance w) pad K st]
  have hthr : PolyTimeComputable thr := paddedNoBound_code_polytime pad K st
  let query : List α → List Bool := fun x => (paddedGapGame pad K st k (f x)).code
  let pairer : List (Option (α ⊕ Bool)) → List (Option (Bool ⊕ Bool)) := fun s =>
    ((thr ∘ f) ∘ fst) s |>.map (some ∘ Sum.inl) |>.append (none :: (snd s).map (some ∘ Sum.inr))
  have hpairer : PolyTimeComputable pairer := by
    have h1 : PolyTimeComputable ((thr ∘ f) ∘ fst) :=
      polyTimeComputable_comp fst (thr ∘ f) hfst (polyTimeComputable_comp f thr hfpoly hthr)
    exact polyTimeComputable_tagged_pair ((thr ∘ f) ∘ fst) snd h1 hsnd
  let decode : List (Option (α ⊕ Bool)) → List Bool := cmp ∘ pairer
  refine ⟨query, decode, ?_, polyTimeComputable_comp pairer cmp hpairer hcmp, ?_⟩
  · exact polyTimeComputable_comp f (fun w => (paddedGapGame pad K st k w).code) hfpoly
      (paddedGapGame_code_polytime pad K st k)
  intro x
  obtain ⟨hPv, hPn, hPs, hPiff⟩ := normInstance_spec (f x)
  set P := normInstance (f x) with hPdef
  set a := paddedNoBound P pad K st with hadef
  set M := paddedPieceFactor P pad K with hMdef
  set r := paddedGapRows P pad K st k with hrdef
  have hG0 : paddedGapGame pad K st k (f x) = paddedReservoirGame P pad K st r := rfl
  refine ⟨⟨paddedGapGame pad K st k (f x), paddedReservoirBoard_legal P pad K st r (by omega), rfl⟩,
    ?_⟩
  rintro y ⟨G, v, -, hq, hy, happ⟩
  have hGeq : G = paddedReservoirGame P pad K st r := (Game_code_inj hq.symm).trans hG0
  subst hGeq
  have hdec : decode (x.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)) =
      [decide (a < v)] := by
    show cmp (pairer _) = _
    simp only [pairer, Function.comp, hfst_eq, hsnd_eq, thr, hy]
    exact hcmp_eq a v
  rw [hdec]
  obtain ⟨hvatt, happ2⟩ := happ
  rw [if_neg (paddedReservoirGame_pieces_ne_nil P pad K st r)] at happ2
  set p := (paddedReservoirGame P pad K st r).pieces.length with hpdef
  have hr1 : 1 ≤ r := by
    rw [hrdef, paddedGapRows]
    have : 1 ≤ (paddedNoBound P pad K st * paddedPieceFactor P pad K + 1) ^ k :=
      Nat.one_le_pow _ _ (by omega)
    omega
  have hr_even : Even r :=
    ⟨(paddedNoBound P pad K st * paddedPieceFactor P pad K + 1) ^ k, by
      rw [hrdef, paddedGapRows]; ring⟩
  have hM1 : 1 ≤ M := by rw [hMdef, paddedPieceFactor]; omega
  have hp1 : 1 ≤ p := by
    rw [hpdef, paddedReservoirGame_pieces_length]; omega
  have hpM : p ≤ M * r := by
    rw [hpdef, hMdef]; exact paddedReservoirGame_pieces_le P pad K st r hr1
  have hgap : (a : ℝ) * (p : ℝ) ^ (1 - δ) < (r : ℝ) :=
    gap_ineq a M k p δ hδ0 hδ1 hk hM1 hp1 hpM
  have hpow : (p : ℝ) ^ (1 - ε) ≤ (p : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp1) (by linarith)
  rw [hf x, hPiff]
  constructor
  · intro hyes
    obtain ⟨w, hrw, hw⟩ := paddedReservoir_completeness R hR P hPv hPn hPs hyes pad K st r
      le_rfl (by omega) le_rfl hr_even
    have h1 : (w : ℝ) ≤ (p : ℝ) ^ (1 - ε) * (v : ℝ) := happ2 w hw
    simp only [decide_eq_true_eq, List.cons.injEq, and_true]
    by_contra hle
    push Not at hle
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
    have h2 : (r : ℝ) ≤ (w : ℝ) := Nat.cast_le.mpr hrw
    have h3 : (p : ℝ) ^ (1 - ε) * v ≤ (p : ℝ) ^ (1 - δ) * v :=
      mul_le_mul_of_nonneg_right hpow hv0
    have h4 : (p : ℝ) ^ (1 - δ) * v ≤ (p : ℝ) ^ (1 - δ) * a :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hle) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    have hcomm : (p : ℝ) ^ (1 - δ) * a = (a : ℝ) * (p : ℝ) ^ (1 - δ) := mul_comm _ _
    linarith
  · intro hdecide
    simp only [decide_eq_true_eq, List.cons.injEq, and_true] at hdecide
    by_contra hno
    have hvle : v ≤ a := paddedReservoir_soundness R hR hReason P hPv hPn hPs hno pad K st r le_rfl le_rfl le_rfl v hvatt
    omega

end TetrisHard.Rows

theorem solution
    (R : TetrisHard.Rows.Rotation) (hR : R.Admissible) (hReason : TetrisHard.Rows.Reasonable R)
    (ε : ℝ) (hε : 0 < ε) :
    (TetrisHard.Rows.rowSearch R ε).NPHard :=
  TetrisHard.Rows.cleared_rows_inapproximability_proof R hR hReason ε hε
