-- Prove2me | solution 1 for TetrisHard.Rows.cleared_rows_inapproximability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:11:37.836202+00:00
-- url     : https://prove2.me/submissions/9eef0678-1f11-4f98-b1ef-3c5719b80b4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TetrisHard_Rows_GapReduction
import Theorems.Thm_TetrisHard_Rows_three_partition_strong_np_complete
import Theorems.Thm_TetrisHard_Rows_reservoir_completeness
import Theorems.Thm_TetrisHard_Rows_reservoir_soundness
import Theorems.Thm_TetrisHard_Rows_gapGame_code_polytime
import Theorems.Thm_TetrisHard_Rows_noBound_code_polytime
import Theorems.Thm_TetrisHard_Rows_unary_lt_decider
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairFst
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairSnd
import Theorems.Thm_CookPvsNP_polyTimeComputable_tagged_pair
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

namespace TetrisHard.Rows

/-! ### Unary codes are injective -/

theorem rep_true_false_inj : ∀ (n m : ℕ) (l l' : List Bool),
    List.replicate n true ++ false :: l = List.replicate m true ++ false :: l' →
      n = m ∧ l = l'
  | 0, 0, l, l', h => by simpa using h
  | 0, m+1, l, l', h => by simp [List.replicate_succ] at h
  | n+1, 0, l, l', h => by simp [List.replicate_succ] at h
  | n+1, m+1, l, l', h => by
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

theorem ThreePartition.code_inj {P Q : ThreePartition} (h : P.code = Q.code) : P = Q := by
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

theorem Board.rows_length_flatten (B : Board) :
    B.rows.flatten.length = B.height * B.width := by
  simp [Board.rows, List.sum_ofFn]

theorem Board.eq_of_rows {B B' : Board} (hh : B.height = B'.height) (hw : B.width = B'.width)
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

theorem Piece.code_injective : Function.Injective Piece.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [Piece.code] at h)

theorem Game.code_inj {G G' : Game} (h : G.code = G'.code) : G = G' := by
  unfold Game.code at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := unaryCode_append_inj [G.board.height, G.board.width]
    [G'.board.height, G'.board.width] _ _ rfl h
  simp only [List.cons.injEq, and_true] at h1
  obtain ⟨hh, hw⟩ := h1
  have hlen : G.board.rows.flatten.length = G'.board.rows.flatten.length := by
    rw [Board.rows_length_flatten, Board.rows_length_flatten, hh, hw]
  obtain ⟨h3, h4⟩ := List.append_inj h2 hlen
  have hB : G.board = G'.board := Board.eq_of_rows hh hw h3
  have h5 := unaryCode_inj _ _ h4
  simp only [List.cons.injEq] at h5
  have hp : G.pieces = G'.pieces :=
    (List.map_injective_iff.mpr Piece.code_injective) h5.2
  cases G; cases G'
  simp only at hB hp
  rw [hB, hp]

/-! ### Scaling and the fixed instances -/

theorem ThreePartition.scale_s (P : ThreePartition) : P.scale.s = P.s := rfl

theorem ThreePartition.scale_valid {P : ThreePartition} (hP : P.Valid) : P.scale.Valid := by
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

theorem ThreePartition.scale_hasSolution_iff (P : ThreePartition) :
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

theorem ThreePartition.scale_normalized {P : ThreePartition} (hP : P.Valid) (hs : 0 < P.s) :
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
      have : Q = Classical.choose h := ThreePartition.code_inj (hwQ.symm.trans hw)
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
  refine ⟨ThreePartition.scale_valid hv, ThreePartition.scale_normalized hv hs, hs, ?_⟩
  unfold normInstance
  rw [ThreePartition.scale_hasSolution_iff]
  exact hiff

/-! ### Piece count -/

theorem reservoirGame_pieces_length (P : ThreePartition) (st r : ℕ) :
    (reservoirGame P st r).pieces.length =
      (basePieces P).length + 1 + r * (6 * P.s + 6) / 4 := by
  simp [reservoirGame]; omega

theorem reservoirGame_pieces_le (P : ThreePartition) (st r : ℕ) (hr : 1 ≤ r) :
    (reservoirGame P st r).pieces.length ≤ pieceFactor P * r := by
  rw [reservoirGame_pieces_length]
  unfold pieceFactor
  have h1 : r * (6 * P.s + 6) / 4 ≤ r * (6 * P.s + 6) := Nat.div_le_self _ _
  nlinarith

theorem reservoirGame_pieces_ne_nil (P : ThreePartition) (st r : ℕ) :
    (reservoirGame P st r).pieces ≠ [] := by
  simp [reservoirGame]

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
  -- p^(1-δ) ≤ M * r^(1-δ)
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
  -- a * M < r^δ
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

/-! ### Legality of the constructed board -/

theorem Board.occupied_nat (B : Board) (x y : ℕ) (hx : x < B.width) (hy : y < B.height) :
    B.occupied ((x : ℤ), (y : ℤ)) = B.cell ⟨y, hy⟩ ⟨x, hx⟩ := by
  unfold Board.occupied
  rw [dif_pos (show (0:ℤ) ≤ (y:ℤ) ∧ (y:ℤ) < B.height from ⟨by positivity, by exact_mod_cast hy⟩),
    dif_pos (show (0:ℤ) ≤ (x:ℤ) ∧ (x:ℤ) < B.width from ⟨by positivity, by exact_mod_cast hx⟩)]
  simp

theorem reservoirBoard_legal (P : ThreePartition) (st r : ℕ) (hs : 0 < P.s) :
    (reservoirBoard P st r).Legal := by
  have hBh : (baseBoard P st).height = baseHeight P + 3 * P.s + st := rfl
  have hBw : (baseBoard P st).width = 6 * P.s + 3 := rfl
  have hRh : (reservoirBoard P st r).height = (baseBoard P st).height + 2 + r := rfl
  have hRw : (reservoirBoard P st r).width = 6 * P.s + 7 := rfl
  -- the cell of the reservoir board in the upper part
  have hup : ∀ (y : Fin (reservoirBoard P st r).height) (x : Fin (reservoirBoard P st r).width),
      (hy : r + 2 ≤ y.val) → (hx : x.val < 6 * P.s + 3) →
      (reservoirBoard P st r).cell y x =
        (baseBoard P st).cell ⟨y.val - r - 2, by have h1 := y.isLt; have h2 := hRh; omega⟩
          ⟨x.val, by have h2 := hBw; omega⟩ := by
    intro y x hy hx
    have e : ((y.val : ℤ) - r - 2) = ((y.val - r - 2 : ℕ) : ℤ) := by omega
    show (if y.val < r then decide (x.val = 0)
      else if y.val = r then decide (x.val ≠ 6 * P.s + 4)
      else if y.val = r + 1 then decide (x.val < 6 * P.s + 4)
      else if x.val < 6 * P.s + 3 then
        (baseBoard P st).occupied (x.val, (y.val : ℤ) - r - 2)
      else decide (y.val < r + 2 + baseHeight P)) = _
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hx, e,
      Board.occupied_nat]
  have hextra : ∀ (y : Fin (reservoirBoard P st r).height) (x : Fin (reservoirBoard P st r).width),
      r + 2 ≤ y.val → 6 * P.s + 3 ≤ x.val →
      (reservoirBoard P st r).cell y x = decide (y.val < r + 2 + baseHeight P) := by
    intro y x hy hx
    show (if y.val < r then decide (x.val = 0)
      else if y.val = r then decide (x.val ≠ 6 * P.s + 4)
      else if y.val = r + 1 then decide (x.val < 6 * P.s + 4)
      else if x.val < 6 * P.s + 3 then
        (baseBoard P st).occupied (x.val, (y.val : ℤ) - r - 2)
      else decide (y.val < r + 2 + baseHeight P)) = _
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hlow : ∀ (y : Fin (reservoirBoard P st r).height) (x : Fin (reservoirBoard P st r).width),
      y.val < r + 2 →
      (reservoirBoard P st r).cell y x =
        (if y.val < r then decide (x.val = 0)
          else if y.val = r then decide (x.val ≠ 6 * P.s + 4)
          else decide (x.val < 6 * P.s + 4)) := by
    intro y x hy
    show (if y.val < r then decide (x.val = 0)
      else if y.val = r then decide (x.val ≠ 6 * P.s + 4)
      else if y.val = r + 1 then decide (x.val < 6 * P.s + 4)
      else if x.val < 6 * P.s + 3 then
        (baseBoard P st).occupied (x.val, (y.val : ℤ) - r - 2)
      else decide (y.val < r + 2 + baseHeight P)) = _
    by_cases h1 : y.val < r
    · simp [h1]
    · by_cases h2 : y.val = r
      · simp [h2]
      · have h3 : y.val = r + 1 := by omega
        simp [h3]
  have hbaseCell : ∀ (y : Fin (baseBoard P st).height) (x : Fin (baseBoard P st).width),
      (baseBoard P st).cell y x =
        (if y.val ≥ baseHeight P then false
          else if x.val < 6 * P.s then bucketInitial x.val y.val
          else if x.val = 6 * P.s then decide (y.val + 2 < baseHeight P)
          else if x.val = 6 * P.s + 1 then decide (y.val + 1 < baseHeight P)
          else decide (y.val + 2 = baseHeight P)) := fun _ _ => rfl
  -- filled rows are exactly those below r + 2 + baseHeight
  have hfilled : ∀ y : Fin (reservoirBoard P st r).height,
      y.val < r + 2 + baseHeight P → ∃ x, (reservoirBoard P st r).cell y x = true := by
    intro y hy
    by_cases hlo : y.val < r + 2
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [hlow y _ hlo]
      split_ifs <;> simp
    · refine ⟨⟨6 * P.s + 3, by omega⟩, ?_⟩
      rw [hextra y _ (by omega) (by simp)]
      simpa using hy
  have hempty : ∀ (y : Fin (reservoirBoard P st r).height) (x : Fin (reservoirBoard P st r).width),
      r + 2 + baseHeight P ≤ y.val → (reservoirBoard P st r).cell y x = false := by
    intro y x hy
    by_cases hx : x.val < 6 * P.s + 3
    · rw [hup y x (by omega) hx, hbaseCell]
      rw [if_pos (by simp; omega)]
    · rw [hextra y x (by omega) (by omega)]
      simp; omega
  refine ⟨by rw [hRh]; omega, by rw [hRw]; omega, ?_, ?_⟩
  · intro y
    by_cases hlo : y.val < r + 2
    · by_cases h1 : y.val < r
      · refine ⟨⟨1, by rw [hRw]; omega⟩, ?_⟩
        rw [hlow y _ hlo]; simp [h1]
      · refine ⟨⟨6 * P.s + 4, by rw [hRw]; omega⟩, ?_⟩
        rw [hlow y _ hlo]
        by_cases h2 : y.val = r
        · simp [h2]
        · simp [h1, h2]
    · refine ⟨⟨2, by rw [hRw]; omega⟩, ?_⟩
      rw [hup y _ (by omega) (show (2:ℕ) < 6 * P.s + 3 by omega), hbaseCell]
      have h26 : 2 < 6 * P.s := by omega
      by_cases hH : y.val - r - 2 ≥ baseHeight P
      · rw [if_pos hH]
      · rw [if_neg hH, if_pos h26]; simp [bucketInitial]
  · intro y ⟨y', x, hyy, hx⟩
    apply hfilled
    by_contra hc
    have := hempty y' x (by omega)
    rw [this] at hx
    exact absurd hx (by simp)

end TetrisHard.Rows

/-! ### Main theorem -/

open TetrisHard.Rows CookPvsNP in
theorem solution
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
  set st : ℕ := stagingAllowance R with hstdef
  obtain ⟨fst, hfst, hfst_eq⟩ := polyTimeComputable_pairFst α Bool
  obtain ⟨snd, hsnd, hsnd_eq⟩ := polyTimeComputable_pairSnd α Bool
  obtain ⟨cmp, hcmp, hcmp_eq⟩ := unary_lt_decider
  let thr : List Bool → List Bool := fun w => unaryCode [noBound (normInstance w) st]
  have hthr : PolyTimeComputable thr := noBound_code_polytime st
  let query : List α → List Bool := fun x => (gapGame st k (f x)).code
  let pairer : List (Option (α ⊕ Bool)) → List (Option (Bool ⊕ Bool)) := fun s =>
    ((thr ∘ f) ∘ fst) s |>.map (some ∘ Sum.inl) |>.append (none :: (snd s).map (some ∘ Sum.inr))
  have hpairer : PolyTimeComputable pairer := by
    have h1 : PolyTimeComputable ((thr ∘ f) ∘ fst) :=
      polyTimeComputable_comp fst (thr ∘ f) hfst (polyTimeComputable_comp f thr hfpoly hthr)
    exact polyTimeComputable_tagged_pair ((thr ∘ f) ∘ fst) snd h1 hsnd
  let decode : List (Option (α ⊕ Bool)) → List Bool := cmp ∘ pairer
  refine ⟨query, decode, ?_, polyTimeComputable_comp pairer cmp hpairer hcmp, ?_⟩
  · exact polyTimeComputable_comp f (fun w => (gapGame st k w).code) hfpoly
      (gapGame_code_polytime st k)
  intro x
  obtain ⟨hPv, hPn, hPs, hPiff⟩ := normInstance_spec (f x)
  set P := normInstance (f x) with hPdef
  set a := noBound P st with hadef
  set M := pieceFactor P with hMdef
  set r := gapRows P st k with hrdef
  have hG0 : gapGame st k (f x) = reservoirGame P st r := rfl
  refine ⟨⟨gapGame st k (f x), reservoirBoard_legal P st r hPs, rfl⟩, ?_⟩
  rintro y ⟨G, v, -, hq, hy, happ⟩
  have hGeq : G = reservoirGame P st r := (Game.code_inj hq.symm).trans hG0
  subst hGeq
  have hdec : decode (x.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)) =
      [decide (a < v)] := by
    show cmp (pairer _) = _
    simp only [pairer, Function.comp, hfst_eq, hsnd_eq, thr, hy]
    exact hcmp_eq a v
  rw [hdec]
  obtain ⟨hvatt, happ2⟩ := happ
  rw [if_neg (reservoirGame_pieces_ne_nil P st r)] at happ2
  set p := (reservoirGame P st r).pieces.length with hpdef
  have hr1 : 1 ≤ r := by
    rw [hrdef, gapRows]
    have : 1 ≤ (noBound P st * pieceFactor P + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have hM1 : 1 ≤ M := by rw [hMdef, pieceFactor]; omega
  have hp1 : 1 ≤ p := by
    rw [hpdef, reservoirGame_pieces_length]; omega
  have hpM : p ≤ M * r := by
    rw [hpdef, hMdef]; exact reservoirGame_pieces_le P st r hr1
  have hgap : (a : ℝ) * (p : ℝ) ^ (1 - δ) < (r : ℝ) :=
    gap_ineq a M k p δ hδ0 hδ1 hk hM1 hp1 hpM
  have hpow : (p : ℝ) ^ (1 - ε) ≤ (p : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1) (by linarith)
  rw [hf x, hPiff]
  constructor
  · intro hyes
    obtain ⟨w, hrw, hw⟩ := reservoir_completeness R hR hReason P hPv hPn hPs hyes r
      ⟨(noBound P st * pieceFactor P + 1) ^ k, by rw [hrdef, gapRows]; ring⟩
    have h1 := happ2 w hw
    simp only [decide_eq_true_eq, List.cons.injEq, and_true]
    by_contra hle
    push Not at hle
    have hv0 : (0 : ℝ) ≤ v := by positivity
    have h2 : (r : ℝ) ≤ (w : ℝ) := by exact_mod_cast hrw
    have h3 : (p : ℝ) ^ (1 - ε) * v ≤ (p : ℝ) ^ (1 - δ) * v :=
      mul_le_mul_of_nonneg_right hpow hv0
    have h4 : (p : ℝ) ^ (1 - δ) * v ≤ (p : ℝ) ^ (1 - δ) * a :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (Real.rpow_nonneg (by positivity) _)
    nlinarith
  · intro hdecide
    simp only [decide_eq_true_eq, List.cons.injEq, and_true] at hdecide
    by_contra hno
    have : v ≤ a := reservoir_soundness R hR hReason P hPv hPn hno r v hvatt
    omega
