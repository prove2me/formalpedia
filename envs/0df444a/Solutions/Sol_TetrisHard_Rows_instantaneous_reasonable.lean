-- Prove2me | solution 1 for TetrisHard.Rows.instantaneous_reasonable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:11:26.768598+00:00
-- url     : https://prove2.me/submissions/9288d8e4-0fda-496f-88b8-bc24e5fa702f

import Definitions.Def_TetrisHard_Rows_Reservoir

set_option autoImplicit false

namespace TetrisLemma510

open TetrisHard.Rows

private lemma base_mem_zero (t : Piece) : (0, 0) ∈ t.base := by
  cases t <;> decide

private lemma clockwise_zero : clockwise (0, 0) = (0, 0) := rfl

private lemma clockwise_iter_zero (n : ℕ) : clockwise^[n] (0, 0) = (0, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, clockwise_zero]

private lemma position_mem_cells (q : PieceState) : q.position ∈ q.cells := by
  unfold PieceState.cells
  refine List.mem_map.mpr ⟨(0, 0), base_mem_zero q.kind, ?_⟩
  by_cases h : q.kind = .Sq
  · simp [h]
  · simp [h, clockwise_iter_zero]

private lemma instantaneous_apply_cases (B : Board) (q : PieceState) (cw : Bool) :
    instantaneous.apply B q cw = q ∨
    instantaneous.apply B q cw =
      {q with orientation := ⟨(q.orientation.val + if cw then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩} := by
  unfold Rotation.apply instantaneous
  dsimp only
  set o' : Fin 4 := ⟨(q.orientation.val + if cw then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩
  set q0 : PieceState := { kind := q.kind, orientation := o', position := (0, 0), fixed := q.fixed }
  cases hcond : (q0.cells.all fun z =>
    if hy : 0 ≤ z.2 + 2 ∧ z.2 + 2 < 5 then
      if hx : 0 ≤ z.1 + 2 ∧ z.1 + 2 < 5 then
        !B.occupied (q.position.1 + (z.1 + 2).toNat - 2, q.position.2 + (z.2 + 2).toNat - 2)
      else false
    else false)
  · left
    simp
  · right
    cases q with
    | mk k o pos f =>
      cases pos with
      | mk px py =>
        simp

private lemma move_kind {R B q q'} (h : Move R B q q') : q'.kind = q.kind := by
  rcases h with ⟨_, _, _, hstep⟩
  rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
  · unfold Rotation.apply
    dsimp only
    split <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

private lemma occupied_of_neg_x (B : Board) (x y : ℤ) (hx : x < 0) :
    B.occupied (x, y) = true := by
  unfold Board.occupied
  split_ifs <;> first | rfl | omega

private lemma occupied_of_neg_y (B : Board) (x y : ℤ) (hy : y < 0) :
    B.occupied (x, y) = true := by
  unfold Board.occupied
  split_ifs <;> first | rfl | omega

private lemma bucketFrame_right_wall {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    (j : Fin s) (y : ℤ) (hy : y < H) :
    B.occupied (6 * (j.val : ℤ) + 5, y) = true := by
  by_cases hy0 : y < 0
  · exact occupied_of_neg_y B _ y hy0
  · have h := (hF.2.2.2 j y.toNat (by omega)).1
    have hy' : (y.toNat : ℤ) = y := by omega
    rw [hy'] at h
    exact h

private lemma bucketFrame_left_wall {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    (j : Fin s) (y : ℤ) (hy : y < H) :
    B.occupied (6 * (j.val : ℤ) - 1, y) = true := by
  by_cases hj : j.val = 0
  · apply occupied_of_neg_x
    omega
  · have h := bucketFrame_right_wall hF ⟨j.val - 1, by omega⟩ y hy
    have hx : 6 * ((j.val - 1 : ℕ) : ℤ) + 5 = 6 * (j.val : ℤ) - 1 := by omega
    rw [hx] at h
    exact h

private lemma bucketFrame_notch_wall {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    (j : Fin s) (y : ℤ) (hy : y < H) (hmod : (y + 1) % 6 ≠ 5) :
    B.occupied (6 * (j.val : ℤ) + 3, y) = true ∧
    B.occupied (6 * (j.val : ℤ) + 4, y) = true := by
  by_cases hy0 : y < 0
  · exact ⟨occupied_of_neg_y B _ y hy0, occupied_of_neg_y B _ y hy0⟩
  · have h := (hF.2.2.2 j y.toNat (by omega)).2 (by omega)
    have hy' : (y.toNat : ℤ) = y := by omega
    rw [hy'] at h
    exact h

private lemma openNotch_bounds {B : Board} {s H j : ℕ} {y : ℤ}
    (hF : BucketFrame B s H) (hN : OpenNotch B j H y) :
    4 ≤ y ∧ y + 6 ≤ H := by
  rcases hF.2.1 with ⟨T, hH⟩
  rcases hN with ⟨hy0, hyH, hmod, _, _⟩
  omega

/-! ### Part 1: `instantaneous.Admissible` -/

private lemma instantaneous_admissible : instantaneous.Admissible := by
  constructor
  · intro t o f d
    cases t <;> fin_cases o <;> cases f <;> cases d <;> decide
  · intro B q d hq
    unfold Rotation.apply instantaneous
    dsimp only
    set o' : Fin 4 := ⟨(q.orientation.val + if d then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩
    set q0 : PieceState := { kind := q.kind, orientation := o', position := (0, 0), fixed := q.fixed }
    cases hall : (q0.cells.all fun z =>
      if hy : 0 ≤ z.2 + 2 ∧ z.2 + 2 < 5 then
        if hx : 0 ≤ z.1 + 2 ∧ z.1 + 2 < 5 then
          !B.occupied (q.position.1 + (z.1 + 2).toNat - 2, q.position.2 + (z.2 + 2).toNat - 2)
        else false
      else false)
    · simpa using hq
    · simp only [↓reduceIte]
      intro z hz
      unfold PieceState.cells at hz
      rcases List.mem_map.mp hz with ⟨z0, hz0, rfl⟩
      set u : Cell := if q.kind = .Sq then z0 else clockwise^[o'.val] z0
      have hu : u ∈ q0.cells := by
        unfold PieceState.cells
        refine List.mem_map.mpr ⟨z0, hz0, ?_⟩
        simp [u, q0]
      have hcheck := List.all_eq_true.mp hall u hu
      split at hcheck
      · rename_i hy
        split at hcheck
        · rename_i hx
          have hocc : B.occupied (q.position.1 + ((u.1 + 2).toNat : ℤ) - 2,
              q.position.2 + ((u.2 + 2).toNat : ℤ) - 2) = false := by
            simpa using hcheck
          have h1 : q.position.1 + 0 + u.1 = q.position.1 + ((u.1 + 2).toNat : ℤ) - 2 := by omega
          have h2 : q.position.2 + 0 + u.2 = q.position.2 + ((u.2 + 2).toNat : ℤ) - 2 := by omega
          dsimp only
          change B.occupied (q.position.1 + 0 + u.1, q.position.2 + 0 + u.2) = false
          rw [h1, h2]
          exact hocc
        · simp at hcheck
      · simp at hcheck

/-! ### Part 2: Connectivity and Conditions 1 & 2 -/

private def Adj (z z' : Cell) : Prop :=
  |z.1 - z'.1| + |z.2 - z'.2| = 1

private def StepIn (S : Cell → Prop) (z z' : Cell) : Prop :=
  S z ∧ S z' ∧ Adj z z'

private lemma adj_clockwise {u v : Cell} (h : Adj u v) : Adj (clockwise u) (clockwise v) := by
  unfold Adj clockwise at *
  dsimp only at *
  simp only [abs_eq_max_neg] at h ⊢
  omega

private lemma adj_clockwise_iter (n : ℕ) {u v : Cell} (h : Adj u v) :
    Adj (clockwise^[n] u) (clockwise^[n] v) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact adj_clockwise ih

private lemma base_connected (t : Piece) :
    ∀ z ∈ t.base, Relation.ReflTransGen (StepIn (· ∈ t.base)) (0, 0) z := by
  cases t <;> intro z hz
  · -- Sq: [(0,0), (1,0), (0,-1), (1,-1)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact Relation.ReflTransGen.trans
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩ :
          Relation.ReflTransGen (StepIn (· ∈ Piece.base .Sq)) (0, 0) (1, 0))
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩)
  · -- LG: [(0,1), (0,0), (0,-1), (-1,-1)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact Relation.ReflTransGen.trans
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩ :
          Relation.ReflTransGen (StepIn (· ∈ Piece.base .LG)) (0, 0) (0, -1))
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩)
  · -- RG: [(0,1), (0,0), (0,-1), (1,-1)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact Relation.ReflTransGen.trans
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩ :
          Relation.ReflTransGen (StepIn (· ∈ Piece.base .RG)) (0, 0) (0, -1))
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩)
  · -- LS: [(0,1), (0,0), (-1,0), (-1,-1)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact Relation.ReflTransGen.trans
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩ :
          Relation.ReflTransGen (StepIn (· ∈ Piece.base .LS)) (0, 0) (-1, 0))
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩)
  · -- RS: [(-1,1), (-1,0), (0,0), (0,-1)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.trans
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩ :
          Relation.ReflTransGen (StepIn (· ∈ Piece.base .RS)) (0, 0) (-1, 0))
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩)
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
  · -- I: [(-1,0), (0,0), (1,0), (2,0)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact Relation.ReflTransGen.trans
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩ :
          Relation.ReflTransGen (StepIn (· ∈ Piece.base .I)) (0, 0) (1, 0))
        (.single ⟨by decide, by decide, by unfold Adj; decide⟩)
  · -- T: [(-1,0), (0,0), (1,0), (0,-1)]
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .refl
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩
    · exact .single ⟨by decide, by decide, by unfold Adj; decide⟩

private lemma stepIn_map {L : List Cell} {f : Cell → Cell}
    (hf : ∀ u v, Adj u v → Adj (f u) (f v)) {a b : Cell}
    (h : Relation.ReflTransGen (StepIn (· ∈ L)) a b) :
    Relation.ReflTransGen (StepIn (· ∈ L.map f)) (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    rcases hstep with ⟨hu, hv, hadj⟩
    exact ih.tail ⟨List.mem_map_of_mem hu, List.mem_map_of_mem hv, hf _ _ hadj⟩

private lemma piece_cells_connected (q : PieceState) :
    ∀ z ∈ q.cells, Relation.ReflTransGen (StepIn (· ∈ q.cells)) q.position z := by
  intro z hz
  let f : Cell → Cell := fun z0 =>
    let u := if q.kind = .Sq then z0 else clockwise^[q.orientation.val] z0
    (q.position.1 + u.1, q.position.2 + u.2)
  have hf_adj : ∀ u v, Adj u v → Adj (f u) (f v) := by
    intro u v huv
    dsimp only [f]
    by_cases hSq : q.kind = .Sq
    · simp only [hSq, ↓reduceIte]
      unfold Adj at huv ⊢
      dsimp only
      simp only [abs_eq_max_neg] at huv ⊢
      omega
    · simp only [hSq, ↓reduceIte]
      have hrot := adj_clockwise_iter q.orientation.val huv
      unfold Adj at hrot ⊢
      dsimp only
      simp only [abs_eq_max_neg] at hrot ⊢
      omega
  have hf0 : f (0, 0) = q.position := by
    dsimp only [f]
    by_cases hSq : q.kind = .Sq
    · simp [hSq]
    · simp [hSq, clockwise_iter_zero]
  have hcells : q.cells = q.kind.base.map f := rfl
  rw [hcells] at hz ⊢
  rcases List.mem_map.mp hz with ⟨z0, hz0, rfl⟩
  rw [← hf0]
  exact stepIn_map hf_adj (base_connected q.kind z0 hz0)

private lemma emptyAdjacent_symm {B : Board} {a b : Cell} (h : EmptyAdjacent B a b) :
    EmptyAdjacent B b a := by
  rcases h with ⟨ha, hb, hd⟩
  refine ⟨hb, ha, ?_⟩
  simp only [abs_eq_max_neg] at hd ⊢
  omega

private lemma reflTransGen_emptyAdjacent_symm {B : Board} {a b : Cell}
    (h : Relation.ReflTransGen (EmptyAdjacent B) a b) :
    Relation.ReflTransGen (EmptyAdjacent B) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact (Relation.ReflTransGen.single (emptyAdjacent_symm hstep)).trans ih

private lemma stepIn_to_emptyAdjacent {B : Board} {q : PieceState} (hC : B.Clear q) {a b : Cell}
    (h : Relation.ReflTransGen (StepIn (· ∈ q.cells)) a b) :
    Relation.ReflTransGen (EmptyAdjacent B) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    rcases hstep with ⟨hu, hv, hadj⟩
    exact ih.tail ⟨hC _ hu, hC _ hv, hadj⟩

private lemma cond1 :
    ∀ (B : Board) q q', Move instantaneous B q q' →
      ∀ z ∈ q.cells, ∀ z' ∈ q'.cells,
        Relation.ReflTransGen (EmptyAdjacent B) z z' := by
  intro B q q' hM z hz z' hz'
  rcases hM with ⟨_, hCq, hCq', hstep⟩
  have h1 : Relation.ReflTransGen (EmptyAdjacent B) z q.position :=
    reflTransGen_emptyAdjacent_symm (stepIn_to_emptyAdjacent hCq (piece_cells_connected q z hz))
  have h3 : Relation.ReflTransGen (EmptyAdjacent B) q'.position z' :=
    stepIn_to_emptyAdjacent hCq' (piece_cells_connected q' z' hz')
  have h2 : Relation.ReflTransGen (EmptyAdjacent B) q.position q'.position := by
    have hpq : B.occupied q.position = false := hCq _ (position_mem_cells q)
    have hpq' : B.occupied q'.position = false := hCq' _ (position_mem_cells q')
    rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
    · rcases instantaneous_apply_cases B q d with h | h <;> rw [h]
    · exact .single ⟨hpq, hpq', by simp [TetrisHard.Rows.translate, abs_eq_max_neg]⟩
    · exact .single ⟨hpq, hpq', by simp [TetrisHard.Rows.translate, abs_eq_max_neg]⟩
    · exact .single ⟨hpq, hpq', by simp [TetrisHard.Rows.translate, abs_eq_max_neg]⟩
    · exact .refl
  exact (h1.trans h2).trans h3

private lemma cond2 :
    ∀ (B : Board) s H, BucketFrame B s H →
      ∀ q q', Move instantaneous B q q' →
        (∀ z ∈ q.cells, z.2 < H) → (∀ z ∈ q'.cells, z.2 < H) →
        ∀ j : Fin s, InBucket j.val q → InBucket j.val q' := by
  intro B s H hF q q' hM hqH hq'H j hIn
  rcases hM with ⟨_, hCq, hCq', hstep⟩
  have hqp_mem := position_mem_cells q
  have hqp'_mem := position_mem_cells q'
  have hqp_in := hIn q.position hqp_mem
  have hqp_lt5 : q.position.1 < 6 * (j.val : ℤ) + 5 := by
    by_contra hge
    have heq : q.position.1 = 6 * (j.val : ℤ) + 5 := by omega
    have hocc := bucketFrame_right_wall hF j q.position.2 (hqH _ hqp_mem)
    have hclr := hCq q.position hqp_mem
    rw [← heq] at hocc
    simp [hocc] at hclr
  have hdx : -1 ≤ q'.position.1 - q.position.1 ∧ q'.position.1 - q.position.1 ≤ 1 := by
    rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
    · rcases instantaneous_apply_cases B q d with h | h <;> rw [h] <;> simp
    · simp [TetrisHard.Rows.translate]
    · simp [TetrisHard.Rows.translate]
    · simp [TetrisHard.Rows.translate]
    · simp
  have hqp'_bounds : 6 * (j.val : ℤ) ≤ q'.position.1 ∧ q'.position.1 < 6 * (j.val : ℤ) + 5 := by
    have hneL : q'.position.1 ≠ 6 * (j.val : ℤ) - 1 := by
      intro heq
      have hocc := bucketFrame_left_wall hF j q'.position.2 (hq'H _ hqp'_mem)
      have hclr := hCq' q'.position hqp'_mem
      rw [← heq] at hocc
      simp [hocc] at hclr
    have hneR : q'.position.1 ≠ 6 * (j.val : ℤ) + 5 := by
      intro heq
      have hocc := bucketFrame_right_wall hF j q'.position.2 (hq'H _ hqp'_mem)
      have hclr := hCq' q'.position hqp'_mem
      rw [← heq] at hocc
      simp [hocc] at hclr
    omega
  intro z' hz'
  have hconn := piece_cells_connected q' z' hz'
  suffices h : 6 * (j.val : ℤ) ≤ z'.1 ∧ z'.1 < 6 * (j.val : ℤ) + 5 by omega
  induction hconn with
  | refl => exact hqp'_bounds
  | @tail u v _ hst ih =>
    rcases hst with ⟨hu, hv, hadj⟩
    have ihu := ih hu
    unfold Adj at hadj
    simp only [abs_eq_max_neg] at hadj
    have hneL : v.1 ≠ 6 * (j.val : ℤ) - 1 := by
      intro heq
      have hocc := bucketFrame_left_wall hF j v.2 (hq'H v hv)
      have hclr := hCq' v hv
      rw [← heq] at hocc
      simp [hocc] at hclr
    have hneR : v.1 ≠ 6 * (j.val : ℤ) + 5 := by
      intro heq
      have hocc := bucketFrame_right_wall hF j v.2 (hq'H v hv)
      have hclr := hCq' v hv
      rw [← heq] at hocc
      simp [hocc] at hclr
    omega

/-! ### Part 3: Condition 3 (`.LG` in spurned notch) -/

private lemma lg_notch_unique {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    (j : Fin s) (y : ℤ) (hN : OpenNotch B j.val H y)
    {q : PieceState} (hk : q.kind = .LG) (hC : B.Clear q)
    (h3 : (6 * (j.val : ℤ) + 3, y) ∈ q.cells)
    (h4 : (6 * (j.val : ℤ) + 4, y) ∈ q.cells) :
    q.orientation = 1 ∧ q.position = (6 * (j.val : ℤ) + 3, y) := by
  have ⟨hy4, hyH6⟩ := openNotch_bounds hF hN
  have hR : B.occupied (6 * (j.val : ℤ) + 5, y) = true :=
    bucketFrame_right_wall hF j y (by omega)
  have hU34 := bucketFrame_notch_wall hF j (y + 1) (by omega) (by rcases hN with ⟨_, _, hm, _, _⟩; omega)
  have hD34 := bucketFrame_notch_wall hF j (y - 1) (by omega) (by rcases hN with ⟨_, _, hm, _, _⟩; omega)
  cases q with
  | mk k o pos f =>
    subst hk
    cases pos with
    | mk px py =>
      fin_cases o
      · -- o = 0: [(px, py+1), (px, py), (px, py-1), (px-1, py-1)]
        simp [PieceState.cells, Piece.base] at h3 h4
        have hpos : px = 6 * (j.val : ℤ) + 4 ∧ py = y + 1 := by omega
        rcases hpos with ⟨rfl, rfl⟩
        have hmem : (6 * (j.val : ℤ) + 4, y + 1) ∈
            ({kind := .LG, orientation := 0, position := (6 * (j.val : ℤ) + 4, y + 1), fixed := f} : PieceState).cells := by
          simp [PieceState.cells, Piece.base]
        have := hC _ hmem
        simp [hU34.2] at this
      · -- o = 1: [(px+1, py), (px, py), (px-1, py), (px-1, py+1)]
        simp [PieceState.cells, Piece.base, clockwise] at h3 h4
        have hcases : (px = 6 * (j.val : ℤ) + 3 ∧ py = y) ∨ (px = 6 * (j.val : ℤ) + 4 ∧ py = y) := by omega
        rcases hcases with ⟨hpx, hpy⟩ | ⟨hpx, hpy⟩
        · subst hpx; subst hpy; exact ⟨rfl, rfl⟩
        · subst hpx; subst hpy
          have hmem : (6 * (j.val : ℤ) + 5, py) ∈
              ({kind := .LG, orientation := 1, position := (6 * (j.val : ℤ) + 4, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base, clockwise]; omega
          have := hC _ hmem
          simp [hR] at this
      · -- o = 2: [(px, py-1), (px, py), (px, py+1), (px+1, py+1)]
        simp [PieceState.cells, Piece.base, clockwise] at h3 h4
        have hpos : px = 6 * (j.val : ℤ) + 3 ∧ py = y - 1 := by omega
        rcases hpos with ⟨rfl, rfl⟩
        have hmem : (6 * (j.val : ℤ) + 3, y - 1) ∈
            ({kind := .LG, orientation := 2, position := (6 * (j.val : ℤ) + 3, y - 1), fixed := f} : PieceState).cells := by
          simp [PieceState.cells, Piece.base, clockwise]
        have := hC _ hmem
        simp [hD34.1] at this
      · -- o = 3: [(px-1, py), (px, py), (px+1, py), (px+1, py-1)]
        simp [PieceState.cells, Piece.base, clockwise] at h3 h4
        have hcases : (px = 6 * (j.val : ℤ) + 3 ∧ py = y) ∨ (px = 6 * (j.val : ℤ) + 4 ∧ py = y) := by omega
        rcases hcases with ⟨hpx, hpy⟩ | ⟨hpx, hpy⟩
        · subst hpx; subst hpy
          have hmem : (6 * (j.val : ℤ) + 4, py - 1) ∈
              ({kind := .LG, orientation := 3, position := (6 * (j.val : ℤ) + 3, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base, clockwise]; omega
          have := hC _ hmem
          simp [hD34.2] at this
        · subst hpx; subst hpy
          have hmem : (6 * (j.val : ℤ) + 5, py) ∈
              ({kind := .LG, orientation := 3, position := (6 * (j.val : ℤ) + 4, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base, clockwise]; omega
          have := hC _ hmem
          simp [hR] at this

private lemma cond3 :
    ∀ (B : Board) s H, BucketFrame B s H → ∀ (j : Fin s) y q,
      OpenNotch B j.val H y → bucketCell B j.val 1 y = true →
      Reachable instantaneous B H .LG q →
      ¬ ((6 * (j.val : ℤ) + 3, y) ∈ q.cells ∧ (6 * (j.val : ℤ) + 4, y) ∈ q.cells) := by
  intro B s H hF j y q hN h1 hReach
  rcases hReach with ⟨hSpawnH, _, hPath⟩
  have ⟨hy4, hyH6⟩ := openNotch_bounds hF hN
  have hR : B.occupied (6 * (j.val : ℤ) + 5, y) = true :=
    bucketFrame_right_wall hF j y (by omega)
  have hU34 := bucketFrame_notch_wall hF j (y + 1) (by omega) (by rcases hN with ⟨_, _, hm, _, _⟩; omega)
  have hInv : q.kind = .LG ∧
      ¬ ((6 * (j.val : ℤ) + 3, y) ∈ q.cells ∧ (6 * (j.val : ℤ) + 4, y) ∈ q.cells) := by
    induction hPath with
    | refl =>
      refine ⟨rfl, fun ⟨h3, _⟩ => ?_⟩
      have := hSpawnH _ h3
      omega
    | @tail q q' _ hM ih =>
      rcases ih with ⟨hkq, hih⟩
      have hk' : q'.kind = .LG := (move_kind hM).trans hkq
      refine ⟨hk', fun ⟨h3, h4⟩ => ?_⟩
      rcases hM with ⟨_, hCq, hCq', hstep⟩
      have ⟨ho', hpos'⟩ := lg_notch_unique hF j y hN hk' hCq' h3 h4
      rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
      · rcases instantaneous_apply_cases B q d with heq | heq
        · rw [heq] at h3 h4
          exact hih ⟨h3, h4⟩
        · rw [heq] at ho' hpos'
          dsimp only at ho' hpos'
          cases q with
          | mk k o pos f =>
            dsimp only at hkq hpos' ho'
            subst hkq; subst hpos'
            have ho_cases : o = 0 ∨ o = 2 := by
              fin_cases o <;> cases d <;> simp at ho' ⊢
            rcases ho_cases with rfl | rfl
            · have hmem : (6 * (j.val : ℤ) + 3, y + 1) ∈
                  ({kind := .LG, orientation := 0, position := (6 * (j.val : ℤ) + 3, y), fixed := f} : PieceState).cells := by
                simp [PieceState.cells, Piece.base]
              have := hCq _ hmem
              simp [hU34.1] at this
            · have hmem : (6 * (j.val : ℤ) + 3, y + 1) ∈
                  ({kind := .LG, orientation := 2, position := (6 * (j.val : ℤ) + 3, y), fixed := f} : PieceState).cells := by
                simp [PieceState.cells, Piece.base, clockwise]
              have := hCq _ hmem
              simp [hU34.1] at this
      · -- translate (-1) 0
        cases q with
        | mk k o pos f =>
          dsimp only [TetrisHard.Rows.translate] at hkq ho' hpos'
          subst hkq; subst ho'
          cases pos with
          | mk px py =>
            have hpx : px = 6 * (j.val : ℤ) + 4 := by
              have := congrArg Prod.fst hpos'; dsimp at this; omega
            have hpy : py = y := by
              have := congrArg Prod.snd hpos'; dsimp at this; omega
            subst hpx; subst hpy
            have hmem : (6 * (j.val : ℤ) + 5, py) ∈
                ({kind := .LG, orientation := 1, position := (6 * (j.val : ℤ) + 4, py), fixed := f} : PieceState).cells := by
              simp [PieceState.cells, Piece.base, clockwise]; omega
            have := hCq _ hmem
            simp [hR] at this
      · -- translate 1 0
        cases q with
        | mk k o pos f =>
          dsimp only [TetrisHard.Rows.translate] at hkq ho' hpos'
          subst hkq; subst ho'
          cases pos with
          | mk px py =>
            have hpx : px = 6 * (j.val : ℤ) + 2 := by
              have := congrArg Prod.fst hpos'; dsimp at this; omega
            have hpy : py = y := by
              have := congrArg Prod.snd hpos'; dsimp at this; omega
            subst hpx; subst hpy
            have hmem : (6 * (j.val : ℤ) + 1, py) ∈
                ({kind := .LG, orientation := 1, position := (6 * (j.val : ℤ) + 2, py), fixed := f} : PieceState).cells := by
              simp [PieceState.cells, Piece.base, clockwise]; omega
            have := hCq _ hmem
            unfold bucketCell at h1
            simp [h1] at this
      · -- translate 0 (-1)
        cases q with
        | mk k o pos f =>
          dsimp only [TetrisHard.Rows.translate] at hkq ho' hpos'
          subst hkq; subst ho'
          cases pos with
          | mk px py =>
            have hpx : px = 6 * (j.val : ℤ) + 3 := by
              have := congrArg Prod.fst hpos'; dsimp at this; omega
            have hpy : py = y + 1 := by
              have := congrArg Prod.snd hpos'; dsimp at this; omega
            subst hpx; subst hpy
            have hmem : (6 * (j.val : ℤ) + 3, y + 1) ∈
                ({kind := .LG, orientation := 1, position := (6 * (j.val : ℤ) + 3, y + 1), fixed := f} : PieceState).cells := by
              simp [PieceState.cells, Piece.base, clockwise]
            have := hCq _ hmem
            simp [hU34.1] at this
      · -- fix
        exact hih ⟨h3, h4⟩
  exact hInv.2

/-! ### Part 4: Condition 5 (`.I` in notch with `(1, y-1)` and `(2, y-1)` filled) -/

private lemma i_horiz_positions {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    (j : Fin s) (y : ℤ) (hyH : y < H)
    {q : PieceState} (hk : q.kind = .I) (hC : B.Clear q)
    (ho : q.orientation = 0 ∨ q.orientation = 2)
    (hpy : q.position.2 = y)
    (h3 : (6 * (j.val : ℤ) + 3, y) ∈ q.cells) :
    (q.orientation = 0 ∧ (q.position.1 = 6 * (j.val : ℤ) + 1 ∨ q.position.1 = 6 * (j.val : ℤ) + 2)) ∨
    (q.orientation = 2 ∧ (q.position.1 = 6 * (j.val : ℤ) + 2 ∨ q.position.1 = 6 * (j.val : ℤ) + 3)) := by
  have hR : B.occupied (6 * (j.val : ℤ) + 5, y) = true := bucketFrame_right_wall hF j y hyH
  cases q with
  | mk k o pos f =>
    subst hk
    cases pos with
    | mk px py =>
      dsimp only at ho hpy
      subst hpy
      rcases ho with rfl | rfl
      · left
        refine ⟨rfl, ?_⟩
        simp [PieceState.cells, Piece.base] at h3
        have hcases : px = 6 * (j.val : ℤ) + 1 ∨ px = 6 * (j.val : ℤ) + 2 ∨
            px = 6 * (j.val : ℤ) + 3 ∨ px = 6 * (j.val : ℤ) + 4 := by omega
        rcases hcases with h | h | hpx | hpx
        · exact Or.inl h
        · exact Or.inr h
        · subst hpx
          have hmem : (6 * (j.val : ℤ) + 5, py) ∈
              ({kind := .I, orientation := 0, position := (6 * (j.val : ℤ) + 3, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base]; omega
          have := hC _ hmem; simp [hR] at this
        · subst hpx
          have hmem : (6 * (j.val : ℤ) + 5, py) ∈
              ({kind := .I, orientation := 0, position := (6 * (j.val : ℤ) + 4, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base]; omega
          have := hC _ hmem; simp [hR] at this
      · right
        refine ⟨rfl, ?_⟩
        simp [PieceState.cells, Piece.base, clockwise] at h3
        have hcases : px = 6 * (j.val : ℤ) + 2 ∨ px = 6 * (j.val : ℤ) + 3 ∨
            px = 6 * (j.val : ℤ) + 4 ∨ px = 6 * (j.val : ℤ) + 5 := by omega
        rcases hcases with h | h | hpx | hpx
        · exact Or.inl h
        · exact Or.inr h
        · subst hpx
          have hmem : (6 * (j.val : ℤ) + 5, py) ∈
              ({kind := .I, orientation := 2, position := (6 * (j.val : ℤ) + 4, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base, clockwise]; omega
          have := hC _ hmem; simp [hR] at this
        · subst hpx
          have hmem : (6 * (j.val : ℤ) + 5, py) ∈
              ({kind := .I, orientation := 2, position := (6 * (j.val : ℤ) + 5, py), fixed := f} : PieceState).cells := by
            simp [PieceState.cells, Piece.base, clockwise]
          have := hC _ hmem; simp [hR] at this

private lemma cond5 :
    ∀ (B : Board) s H, BucketFrame B s H → ∀ (j : Fin s) y q,
      OpenNotch B j.val H y → bucketCell B j.val 1 (y - 1) = true →
      bucketCell B j.val 2 (y - 1) = true → Reachable instantaneous B H .I q →
      ¬ ((6 * (j.val : ℤ) + 3, y) ∈ q.cells ∧ (6 * (j.val : ℤ) + 4, y) ∈ q.cells) := by
  intro B s H hF j y q hN h1 h2 hReach
  rcases hReach with ⟨hSpawnH, _, hPath⟩
  have ⟨hy4, hyH6⟩ := openNotch_bounds hF hN
  have hL : B.occupied (6 * (j.val : ℤ) - 1, y) = true := bucketFrame_left_wall hF j y (by omega)
  have hR : B.occupied (6 * (j.val : ℤ) + 5, y) = true := bucketFrame_right_wall hF j y (by omega)
  have hU34 := bucketFrame_notch_wall hF j (y + 1) (by omega) (by rcases hN with ⟨_, _, hm, _, _⟩; omega)
  have hD34 := bucketFrame_notch_wall hF j (y - 1) (by omega) (by rcases hN with ⟨_, _, hm, _, _⟩; omega)
  have hInv : q.kind = .I ∧
      ¬ ((q.orientation = 0 ∨ q.orientation = 2) ∧ q.position.2 = y ∧
         (6 * (j.val : ℤ) + 3, y) ∈ q.cells) := by
    induction hPath with
    | refl =>
      refine ⟨rfl, fun ⟨_, _, h3⟩ => ?_⟩
      have := hSpawnH _ h3
      omega
    | @tail q q' _ hM ih =>
      rcases ih with ⟨hkq, hih⟩
      have hk' : q'.kind = .I := (move_kind hM).trans hkq
      refine ⟨hk', fun ⟨ho', hpy', h3'⟩ => ?_⟩
      rcases hM with ⟨_, hCq, hCq', hstep⟩
      have hpos' := i_horiz_positions hF j y (by omega) hk' hCq' ho' hpy' h3'
      rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
      · rcases instantaneous_apply_cases B q d with heq | heq
        · rw [heq] at ho' hpy' h3'
          exact hih ⟨ho', hpy', h3'⟩
        · rw [heq] at ho' hpy' hpos'
          dsimp only at ho' hpy' hpos'
          cases q with
          | mk k o pos f =>
            dsimp only at hkq ho' hpy' hpos'
            subst hkq
            cases pos with
            | mk px py =>
              dsimp only at hpy' hpos'
              subst hpy'
              have ho_vert : o = 1 ∨ o = 3 := by
                fin_cases o <;> cases d <;> simp at ho' ⊢
              have hpx_range : px = 6 * (j.val : ℤ) + 1 ∨ px = 6 * (j.val : ℤ) + 2 ∨ px = 6 * (j.val : ℤ) + 3 := by
                rcases hpos' with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> omega
              have hmem_below : (px, py - 1) ∈
                  ({kind := .I, orientation := o, position := (px, py), fixed := f} : PieceState).cells := by
                rcases ho_vert with rfl | rfl <;> simp [PieceState.cells, Piece.base, clockwise] <;> omega
              have hclr := hCq _ hmem_below
              rcases hpx_range with rfl | rfl | rfl
              · unfold bucketCell at h1; simp [h1] at hclr
              · unfold bucketCell at h2; simp [h2] at hclr
              · simp [hD34.1] at hclr
      · -- translate (-1) 0
        cases q with
        | mk k o pos f =>
          dsimp only [TetrisHard.Rows.translate] at hkq hpy' hpos'
          subst hkq
          cases pos with
          | mk px py =>
            dsimp only at hpy' hpos'
            have hpy : py = y := by omega
            subst hpy
            rcases hpos' with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
            · have hpx : px = 6 * (j.val : ℤ) + 2 := by omega
              subst hpx
              refine hih ⟨Or.inl rfl, rfl, ?_⟩
              simp [PieceState.cells, Piece.base]; omega
            · have hpx : px = 6 * (j.val : ℤ) + 3 := by omega
              subst hpx
              have hmem : (6 * (j.val : ℤ) + 5, py) ∈
                  ({kind := .I, orientation := 0, position := (6 * (j.val : ℤ) + 3, py), fixed := f} : PieceState).cells := by
                simp [PieceState.cells, Piece.base]; omega
              have := hCq _ hmem; simp [hR] at this
            · have hpx : px = 6 * (j.val : ℤ) + 3 := by omega
              subst hpx
              refine hih ⟨Or.inr rfl, rfl, ?_⟩
              simp [PieceState.cells, Piece.base, clockwise]
            · have hpx : px = 6 * (j.val : ℤ) + 4 := by omega
              subst hpx
              have hmem : (6 * (j.val : ℤ) + 5, py) ∈
                  ({kind := .I, orientation := 2, position := (6 * (j.val : ℤ) + 4, py), fixed := f} : PieceState).cells := by
                simp [PieceState.cells, Piece.base, clockwise]; omega
              have := hCq _ hmem; simp [hR] at this
      · -- translate 1 0
        cases q with
        | mk k o pos f =>
          dsimp only [TetrisHard.Rows.translate] at hkq hpy' hpos'
          subst hkq
          cases pos with
          | mk px py =>
            dsimp only at hpy' hpos'
            have hpy : py = y := by omega
            subst hpy
            rcases hpos' with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
            · have hpx : px = 6 * (j.val : ℤ) := by omega
              subst hpx
              have hmem : (6 * (j.val : ℤ) - 1, py) ∈
                  ({kind := .I, orientation := 0, position := (6 * (j.val : ℤ), py), fixed := f} : PieceState).cells := by
                simp [PieceState.cells, Piece.base]; omega
              have := hCq _ hmem; simp [hL] at this
            · have hpx : px = 6 * (j.val : ℤ) + 1 := by omega
              subst hpx
              refine hih ⟨Or.inl rfl, rfl, ?_⟩
              simp [PieceState.cells, Piece.base]; omega
            · have hpx : px = 6 * (j.val : ℤ) + 1 := by omega
              subst hpx
              have hmem : (6 * (j.val : ℤ) - 1, py) ∈
                  ({kind := .I, orientation := 2, position := (6 * (j.val : ℤ) + 1, py), fixed := f} : PieceState).cells := by
                simp [PieceState.cells, Piece.base, clockwise]; omega
              have := hCq _ hmem; simp [hL] at this
            · have hpx : px = 6 * (j.val : ℤ) + 2 := by omega
              subst hpx
              refine hih ⟨Or.inr rfl, rfl, ?_⟩
              simp [PieceState.cells, Piece.base, clockwise]; omega
      · -- translate 0 (-1)
        cases q with
        | mk k o pos f =>
          dsimp only [TetrisHard.Rows.translate] at hkq hpy' hpos'
          subst hkq
          cases pos with
          | mk px py =>
            dsimp only at hpy' hpos'
            have hpy : py = y + 1 := by omega
            subst hpy
            have hmem : (6 * (j.val : ℤ) + 3, y + 1) ∈
                ({kind := .I, orientation := o, position := (px, y + 1), fixed := f} : PieceState).cells := by
              rcases hpos' with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ <;>
                · rw [add_zero] at h; rw [h]; simp [PieceState.cells, Piece.base, clockwise]; try omega
            have := hCq _ hmem
            simp [hU34.1] at this
      · -- fix
        exact hih ⟨ho', hpy', h3'⟩
  intro ⟨h3, h4⟩
  rcases hInv with ⟨hk, hnot⟩
  cases q with
  | mk k o pos f =>
    dsimp only at hk hnot
    subst hk
    cases pos with
    | mk px py =>
      fin_cases o
      · simp [PieceState.cells, Piece.base] at h3 h4
        exact hnot ⟨Or.inl rfl, by omega, by simp [PieceState.cells, Piece.base]; omega⟩
      · simp [PieceState.cells, Piece.base, clockwise] at h3 h4
        omega
      · simp [PieceState.cells, Piece.base, clockwise] at h3 h4
        exact hnot ⟨Or.inr rfl, by omega, by simp [PieceState.cells, Piece.base, clockwise]; omega⟩
      · simp [PieceState.cells, Piece.base, clockwise] at h3 h4
        omega

/-! ### Part 5: Condition 4 (Balcony restriction for `t ≠ .I`) -/

private lemma nonI_offset_bounds {t : Piece} (ht : t ≠ .I) (o : Fin 4)
    {z : Cell} (hz : z ∈ t.base) :
    let u := if t = .Sq then z else clockwise^[o.val] z;
    -1 ≤ u.1 ∧ u.1 ≤ 1 ∧ -1 ≤ u.2 ∧ u.2 ≤ 1 := by
  have hbase : -1 ≤ z.1 ∧ z.1 ≤ 1 ∧ -1 ≤ z.2 ∧ z.2 ≤ 1 := by
    cases t <;> try exact absurd rfl ht
    all_goals
      simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> omega
  have hrot : ∀ n : ℕ, -1 ≤ (clockwise^[n] z).1 ∧ (clockwise^[n] z).1 ≤ 1 ∧
      -1 ≤ (clockwise^[n] z).2 ∧ (clockwise^[n] z).2 ≤ 1 := by
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hcw : (clockwise (clockwise^[n] z)).1 = (clockwise^[n] z).2 ∧
          (clockwise (clockwise^[n] z)).2 = -(clockwise^[n] z).1 := ⟨rfl, rfl⟩
      omega
  dsimp only
  split_ifs
  · exact hbase
  · exact hrot o.val

private lemma nonI_cell_dist {q : PieceState} (ht : q.kind ≠ .I) {z : Cell} (hz : z ∈ q.cells) :
    -1 ≤ z.1 - q.position.1 ∧ z.1 - q.position.1 ≤ 1 ∧
    -1 ≤ z.2 - q.position.2 ∧ z.2 - q.position.2 ≤ 1 := by
  unfold PieceState.cells at hz
  rcases List.mem_map.mp hz with ⟨z0, hz0, rfl⟩
  rcases nonI_offset_bounds ht q.orientation hz0 with ⟨h1, h2, h3, h4⟩
  dsimp only at h1 h2 h3 h4 ⊢
  omega

private def GoodBalcony (X h : ℤ) (i : Fin 3) (q : PieceState) : Prop :=
  ∀ z ∈ q.cells, X ≤ z.1 → z.1 < X + 5 → z.2 ≤ h →
    z.1 = X + (i.val : ℤ) ∧ (z.2 = h ∨ z.2 = h - 1)

private def relCells (t : Piece) (o : Fin 4) (pos : Cell) : List Cell :=
  t.base.map fun z =>
    let u := if t = .Sq then z else clockwise^[o.val] z
    (pos.1 + u.1, pos.2 + u.2)

private def mustOcc (i : Fin 3) (nm : Fin 6) (z : Cell) : Bool :=
  (decide (z.2 ≤ 0) && (decide (z.1 = -1) || decide (z.1 = 5))) ||
  (decide (z.2 = 0) && decide (0 ≤ z.1 ∧ z.1 < 3) && decide (z.1 ≠ (i.val : ℤ))) ||
  (decide (z.1 = 3 ∨ z.1 = 4) &&
    ((decide (z.2 ≤ 0) && decide ((z.2 + (nm.val : ℤ)) % 6 ≠ 5)) ||
     (decide (nm.val = 5) && decide (z.2 = 1))))

private def relClear (i : Fin 3) (nm : Fin 6) (cs : List Cell) : Bool :=
  cs.all fun z => !mustOcc i nm z

private def relGood (i : Fin 3) (cs : List Cell) : Bool :=
  cs.all fun z =>
    if 0 ≤ z.1 ∧ z.1 < 5 ∧ z.2 ≤ 0 then
      decide (z.1 = (i.val : ℤ) ∧ (z.2 = 0 ∨ z.2 = -1))
    else true

private def balconyMoveOk (t : Piece) (o : Fin 4) (i : Fin 3) (nm : Fin 6) (pos : Cell) : Bool :=
  let cs := relCells t o pos
  if !relClear i nm cs || !relGood i cs then true
  else
    let nexts : List (Fin 4 × Cell) := [
      (o, (pos.1 - 1, pos.2)),
      (o, (pos.1 + 1, pos.2)),
      (o, (pos.1, pos.2 - 1)),
      (⟨(o.val + 1) % 4, Nat.mod_lt _ (by decide)⟩, pos),
      (⟨(o.val + 3) % 4, Nat.mod_lt _ (by decide)⟩, pos)
    ]
    nexts.all fun (o', pos') =>
      let cs' := relCells t o' pos'
      !relClear i nm cs' || relGood i cs'

private def nonIPieces : List Piece := [.Sq, .LG, .RG, .LS, .RS, .T]

private def allFin4 : List (Fin 4) := [0, 1, 2, 3]
private def allFin3 : List (Fin 3) := [0, 1, 2]
private def allFin6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

private def checkPos (i : Fin 3) : List Cell :=
  [((i.val : ℤ) - 1, 1), ((i.val : ℤ), 1), ((i.val : ℤ) + 1, 1),
   ((i.val : ℤ), 0), ((i.val : ℤ), -1), (2, 1)]

private lemma balconyMoveOk_piece (t : Piece) (ht : t ≠ .I) :
    ∀ o : Fin 4, ∀ i : Fin 3, ∀ nm : Fin 6, ∀ pos ∈ checkPos i,
      balconyMoveOk t o i nm pos = true := by
  have hSq : allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk .Sq o i nm pos)))) = true := by decide
  have hLG : allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk .LG o i nm pos)))) = true := by decide
  have hRG : allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk .RG o i nm pos)))) = true := by decide
  have hLS : allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk .LS o i nm pos)))) = true := by decide
  have hRS : allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk .RS o i nm pos)))) = true := by decide
  have hT : allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk .T o i nm pos)))) = true := by decide
  have extract : ∀ t', allFin4.all (fun o => allFin3.all (fun i => allFin6.all (fun nm =>
      (checkPos i).all (fun pos => balconyMoveOk t' o i nm pos)))) = true →
      ∀ o : Fin 4, ∀ i : Fin 3, ∀ nm : Fin 6, ∀ pos ∈ checkPos i,
        balconyMoveOk t' o i nm pos = true := by
    intro t' h o i nm pos hpos
    have ho : o ∈ allFin4 := by fin_cases o <;> decide
    have hi : i ∈ allFin3 := by fin_cases i <;> decide
    have hnm : nm ∈ allFin6 := by fin_cases nm <;> decide
    exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp h o ho) i hi) nm hnm) pos hpos
  cases t
  · exact extract .Sq hSq
  · exact extract .LG hLG
  · exact extract .RG hRG
  · exact extract .LS hLS
  · exact extract .RS hRS
  · exact absurd rfl ht
  · exact extract .T hT

private lemma mustOcc_sound {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    {j : Fin s} {h : ℤ} {i : Fin 3} (hBal : Balcony B j.val H h i) (hhH : h < H)
    (nm : Fin 6) (hnm : (nm.val : ℤ) = (h + 1) % 6) (z : Cell)
    (hm : mustOcc i nm z = true) :
    B.occupied (6 * (j.val : ℤ) + z.1, h + z.2) = true := by
  unfold mustOcc at hm
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hm
  rcases hm with (⟨hz2, hz1 | hz1⟩ | ⟨⟨hz2, hz1l, hz1r⟩, hne⟩) | ⟨hz1, ⟨hz2, hmod⟩ | ⟨hnm5, hz2⟩⟩
  · rw [hz1]
    have := bucketFrame_left_wall hF j (h + z.2) (by omega)
    simpa [sub_eq_add_neg] using this
  · rw [hz1]
    exact bucketFrame_right_wall hF j (h + z.2) (by omega)
  · have hbal := hBal.2.2 ⟨z.1.toNat, by omega⟩
    unfold bucketCell at hbal
    have hz1' : (z.1.toNat : ℤ) = z.1 := by omega
    have hneq : (⟨z.1.toNat, by omega⟩ : Fin 3) ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      dsimp at this
      omega
    rw [hz1'] at hbal
    rw [hz2, add_zero]
    simpa [hneq] using hbal
  · have hnw := bucketFrame_notch_wall hF j (h + z.2) (by omega) (by omega)
    rcases hz1 with hz1 | hz1 <;> rw [hz1]
    · exact hnw.1
    · exact hnw.2
  · rcases hF.2.1 with ⟨T, hH⟩
    have hh0 := hBal.1
    have hnw := bucketFrame_notch_wall hF j (h + 1) (by omega) (by omega)
    rw [hz2]
    rcases hz1 with hz1 | hz1 <;> rw [hz1]
    · exact hnw.1
    · exact hnw.2

private lemma relCells_mem_iff (X h : ℤ) (q : PieceState) (z : Cell) :
    z ∈ relCells q.kind q.orientation (q.position.1 - X, q.position.2 - h) ↔
    (X + z.1, h + z.2) ∈ q.cells := by
  unfold relCells PieceState.cells
  constructor
  · intro hz
    rcases List.mem_map.mp hz with ⟨z0, hz0, heq⟩
    refine List.mem_map.mpr ⟨z0, hz0, ?_⟩
    cases heq
    ext <;> dsimp <;> omega
  · intro hz
    rcases List.mem_map.mp hz with ⟨z0, hz0, heq⟩
    refine List.mem_map.mpr ⟨z0, hz0, ?_⟩
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp at h1 h2
    ext <;> dsimp <;> omega

private lemma clear_to_relClear {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    {j : Fin s} {h : ℤ} {i : Fin 3} (hBal : Balcony B j.val H h i) (hhH : h < H)
    (nm : Fin 6) (hnm : (nm.val : ℤ) = (h + 1) % 6)
    {q : PieceState} (hC : B.Clear q) :
    relClear i nm (relCells q.kind q.orientation (q.position.1 - 6 * (j.val : ℤ), q.position.2 - h)) = true := by
  unfold relClear
  rw [List.all_eq_true]
  intro z hz
  rw [relCells_mem_iff] at hz
  have hclr := hC _ hz
  cases hm : mustOcc i nm z
  · rfl
  · have hocc := mustOcc_sound hF hBal hhH nm hnm z hm
    simp [hocc] at hclr

private lemma goodBalcony_iff_relGood (X h : ℤ) (i : Fin 3) (q : PieceState) :
    GoodBalcony X h i q ↔
    relGood i (relCells q.kind q.orientation (q.position.1 - X, q.position.2 - h)) = true := by
  unfold GoodBalcony relGood
  rw [List.all_eq_true]
  constructor
  · intro hG z hz
    rw [relCells_mem_iff] at hz
    split_ifs with hcond
    · have ⟨hx, hy⟩ := hG _ hz (by omega) (by omega) (by omega)
      simp only [decide_eq_true_eq]
      omega
    · rfl
  · intro hR z hz hx1 hx2 hy
    have hz' : (z.1 - X, z.2 - h) ∈
        relCells q.kind q.orientation (q.position.1 - X, q.position.2 - h) := by
      rw [relCells_mem_iff]
      simpa [add_sub_cancel] using hz
    have hcheck := hR _ hz'
    have hcond : 0 ≤ z.1 - X ∧ z.1 - X < 5 ∧ z.2 - h ≤ 0 := by omega
    rw [if_pos hcond] at hcheck
    simp only [decide_eq_true_eq] at hcheck
    omega

private lemma balcony_step_from_checkPos {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    {j : Fin s} {h : ℤ} {i : Fin 3} (hBal : Balcony B j.val H h i) (hhH : h < H)
    {q q' : PieceState} (ht : q.kind ≠ .I) (hM : Move instantaneous B q q')
    (hG : GoodBalcony (6 * (j.val : ℤ)) h i q)
    (hpos : (q.position.1 - 6 * (j.val : ℤ), q.position.2 - h) ∈ checkPos i) :
    GoodBalcony (6 * (j.val : ℤ)) h i q' := by
  set X : ℤ := 6 * (j.val : ℤ)
  set nm : Fin 6 := ⟨((h + 1) % 6).toNat, by omega⟩
  have hnm : (nm.val : ℤ) = (h + 1) % 6 := by
    dsimp only [nm]; omega
  rcases hM with ⟨_, hCq, hCq', hstep⟩
  have hok := balconyMoveOk_piece q.kind ht q.orientation i nm
    (q.position.1 - X, q.position.2 - h) hpos
  have hrc : relClear i nm (relCells q.kind q.orientation (q.position.1 - X, q.position.2 - h)) = true :=
    clear_to_relClear hF hBal hhH nm hnm hCq
  have hrg := (goodBalcony_iff_relGood X h i q).mp hG
  unfold balconyMoveOk at hok
  simp only [hrc, hrg, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hok
  rw [List.all_eq_true] at hok
  have hrc' : relClear i nm (relCells q'.kind q'.orientation (q'.position.1 - X, q'.position.2 - h)) = true :=
    clear_to_relClear hF hBal hhH nm hnm hCq'
  rw [goodBalcony_iff_relGood X h i q']
  rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
  · rcases instantaneous_apply_cases B q d with heq | heq
    · rw [heq]; exact hrg
    · rw [heq] at hrc' ⊢
      cases d
      · have hres := hok (⟨(q.orientation.val + 3) % 4, Nat.mod_lt _ (by decide)⟩,
            (q.position.1 - X, q.position.2 - h)) (by simp)
        simp only [Bool.false_eq_true, ↓reduceIte] at hrc' ⊢
        simpa [hrc'] using hres
      · have hres := hok (⟨(q.orientation.val + 1) % 4, Nat.mod_lt _ (by decide)⟩,
            (q.position.1 - X, q.position.2 - h)) (by simp)
        simp only [↓reduceIte] at hrc' ⊢
        simpa [hrc'] using hres
  · have hres := hok (q.orientation, (q.position.1 - X - 1, q.position.2 - h)) (by simp)
    have hsub : q.position.1 + -1 - X = q.position.1 - X - 1 := by omega
    have hsub2 : q.position.2 + 0 - h = q.position.2 - h := by omega
    simp only [TetrisHard.Rows.translate, hsub, hsub2] at hrc' ⊢
    simpa [hrc'] using hres
  · have hres := hok (q.orientation, (q.position.1 - X + 1, q.position.2 - h)) (by simp)
    have hsub : q.position.1 + 1 - X = q.position.1 - X + 1 := by omega
    have hsub2 : q.position.2 + 0 - h = q.position.2 - h := by omega
    simp only [TetrisHard.Rows.translate, hsub, hsub2] at hrc' ⊢
    simpa [hrc'] using hres
  · have hres := hok (q.orientation, (q.position.1 - X, q.position.2 - h - 1)) (by simp)
    have hsub : q.position.1 + 0 - X = q.position.1 - X := by omega
    have hsub2 : q.position.2 + -1 - h = q.position.2 - h - 1 := by omega
    simp only [TetrisHard.Rows.translate, hsub, hsub2] at hrc' ⊢
    simpa [hrc'] using hres
  · exact hrg

private lemma balcony_step {B : Board} {s H : ℕ} (hF : BucketFrame B s H)
    {j : Fin s} {h : ℤ} {i : Fin 3} (hBal : Balcony B j.val H h i) (hhH : h < H)
    {q q' : PieceState} (ht : q.kind ≠ .I) (hM : Move instantaneous B q q')
    (hG : GoodBalcony (6 * (j.val : ℤ)) h i q) :
    GoodBalcony (6 * (j.val : ℤ)) h i q' := by
  set X : ℤ := 6 * (j.val : ℤ)
  -- Case 1: (X + i, h) ∈ q.cells -> q.position is in checkPos i
  by_cases hInH : (X + (i.val : ℤ), h) ∈ q.cells
  · apply balcony_step_from_checkPos hF hBal hhH ht hM hG
    have hdist := nonI_cell_dist ht hInH
    have hqp_mem := position_mem_cells q
    rcases hM with ⟨_, hCq, _, _⟩
    have hqp_clr := hCq _ hqp_mem
    have hdy_cases : q.position.2 - h = 1 ∨ q.position.2 - h = 0 ∨ q.position.2 - h = -1 := by omega
    have hdx_cases : q.position.1 - X = (i.val : ℤ) - 1 ∨
        q.position.1 - X = (i.val : ℤ) ∨ q.position.1 - X = (i.val : ℤ) + 1 := by omega
    rcases hdy_cases with hdy | hdy | hdy
    · rcases hdx_cases with hdx | hdx | hdx <;> simp [checkPos, ← hdx, hdy, X]
    · rcases hdx_cases with hdx | hdx | hdx
      · exfalso
        by_cases hi0 : i.val = 0
        · have hocc := bucketFrame_left_wall hF j q.position.2 (by omega)
          have h1 : q.position.1 = 6 * (j.val : ℤ) - 1 := by omega
          rw [← h1] at hocc; simp [hocc] at hqp_clr
        · have ⟨hx, _⟩ := hG _ hqp_mem (by omega) (by omega) (by omega)
          omega
      · simp [checkPos, ← hdx, hdy, X]
      · exfalso
        have ⟨hx, _⟩ := hG _ hqp_mem (by omega) (by omega) (by omega)
        omega
    · rcases hdx_cases with hdx | hdx | hdx
      · exfalso
        by_cases hi0 : i.val = 0
        · have hocc := bucketFrame_left_wall hF j q.position.2 (by omega)
          have h1 : q.position.1 = 6 * (j.val : ℤ) - 1 := by omega
          rw [← h1] at hocc; simp [hocc] at hqp_clr
        · have ⟨hx, _⟩ := hG _ hqp_mem (by omega) (by omega) (by omega)
          omega
      · simp [checkPos, ← hdx, hdy, X]
      · exfalso
        have ⟨hx, _⟩ := hG _ hqp_mem (by omega) (by omega) (by omega)
        omega
  -- Case 2: (X + i, h) ∉ q.cells -> q has NO cells in [X, X+5) × (-∞, h] at all!
  · have hNoLow : ∀ z ∈ q.cells, X ≤ z.1 → z.1 < X + 5 → z.2 ≤ h → False := by
      intro z hz hx1 hx2 hy
      have ⟨hzi, hzy⟩ := hG z hz hx1 hx2 hy
      rcases hzy with hzy | hzy
      · exact hInH (by have heq : z = (X + (i.val : ℤ), h) := Prod.ext hzi hzy; rwa [← heq])
      · -- z = (X + i, h - 1) ∈ q.cells; by connectivity to q.position, z must have a neighbor in q.cells
        have hconn := piece_cells_connected q z hz
        rcases hM with ⟨_, hCq, _, _⟩
        -- Since q.cells has 4 cells, either z = q.position or z has a neighbor in q.cells
        -- Actually, every cell in q.cells has a neighbor in q.cells!
        have hhasNb : ∃ w ∈ q.cells, Adj w z := by
          have hstep_rev := reflTransGen_emptyAdjacent_symm
            (stepIn_to_emptyAdjacent hCq hconn)
          cases hconn with
          | refl =>
            -- z = q.position; pick any other cell in q.cells? Wait: (0,0) has a neighbor in t.base!
            have hnb0 : ∃ u ∈ q.kind.base, Adj (0, 0) u := by
              cases q.kind <;> first
                | exact ⟨(1, 0), by decide, by unfold Adj; decide⟩
                | exact ⟨(0, 1), by decide, by unfold Adj; decide⟩
                | exact ⟨(-1, 0), by decide, by unfold Adj; decide⟩
            rcases hnb0 with ⟨u, hu, hadj0⟩
            let w : Cell :=
              let v := if q.kind = .Sq then u else clockwise^[q.orientation.val] u
              (q.position.1 + v.1, q.position.2 + v.2)
            refine ⟨w, ?_, ?_⟩
            · unfold PieceState.cells
              exact List.mem_map.mpr ⟨u, hu, rfl⟩
            · dsimp only [w]
              by_cases hSq : q.kind = .Sq
              · simp only [hSq, ↓reduceIte]
                unfold Adj at hadj0 ⊢
                dsimp only at hadj0 ⊢
                simp only [abs_eq_max_neg] at hadj0 ⊢
                omega
              · simp only [hSq, ↓reduceIte]
                have hrot := adj_clockwise_iter q.orientation.val hadj0
                rw [clockwise_iter_zero] at hrot
                unfold Adj at hrot ⊢
                dsimp only at hrot ⊢
                simp only [abs_eq_max_neg] at hrot ⊢
                omega
          | @tail u _ _ hst =>
            exact ⟨u, hst.1, hst.2.2⟩
        rcases hhasNb with ⟨w, hw, hadj⟩
        unfold Adj at hadj
        simp only [abs_eq_max_neg] at hadj
        -- w is adjacent to (X + i, h - 1)
        by_cases hwx : w.1 < X
        · -- then w.1 = X - 1 and w.2 = h - 1, wall!
          have hocc := bucketFrame_left_wall hF j w.2 (by omega)
          have hclr := hCq w hw
          have hw1 : w.1 = 6 * (j.val : ℤ) - 1 := by omega
          rw [← hw1] at hocc; simp [hocc] at hclr
        · have ⟨hwi, hwy⟩ := hG w hw (by omega) (by omega) (by omega)
          rcases hwy with hwy | hwy
          · exact hInH (by
              have heq : w = (X + (i.val : ℤ), h) := Prod.ext hwi hwy
              rwa [← heq])
          · omega
    -- Now q has NO cells in [X, X+5) × (-∞, h]!
    have hk' : q'.kind ≠ .I := by rw [move_kind hM]; exact ht
    have ⟨_, hCq, hCq', hstep⟩ := hM
    rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
    · -- rotation: either q' = q, or q.position = (X + 2, h + 1) (which is in checkPos i!), or impossible
      rcases instantaneous_apply_cases B q d with heq | heq
      · rw [heq]; exact hG
      · by_cases hpos21 : (q.position.1 - X, q.position.2 - h) = (2, 1)
        · apply balcony_step_from_checkPos hF hBal hhH ht hM hG
          rw [hpos21]; simp [checkPos]
        · intro z' hz' hx1 hx2 hy
          have hdist := nonI_cell_dist hk' hz'
          have hqp_eq : (instantaneous.apply B q d).position = q.position := by
            rw [heq]
          rw [hqp_eq] at hdist
          have hqp_mem := position_mem_cells q
          have hqp_clr := hCq _ hqp_mem
          -- q.position.2 ≤ h + 1; if q.position.2 ≤ h, then q.position.1 ∉ [X, X+5), so wall!
          by_cases hqpy : q.position.2 ≤ h
          · by_cases hqpx1 : q.position.1 < X
            · have hocc := bucketFrame_left_wall hF j q.position.2 (by omega)
              have h1 : q.position.1 = 6 * (j.val : ℤ) - 1 := by omega
              rw [← h1] at hocc; simp [hocc] at hqp_clr
            · by_cases hqpx2 : q.position.1 < X + 5
              · exact absurd hqp_mem (fun hm => hNoLow _ hm (by omega) hqpx2 hqpy)
              · have hocc := bucketFrame_right_wall hF j q.position.2 (by omega)
                have h1 : q.position.1 = 6 * (j.val : ℤ) + 5 := by omega
                rw [← h1] at hocc; simp [hocc] at hqp_clr
          · -- q.position.2 = h + 1, so z'.2 = h
            have hqpy1 : q.position.2 = h + 1 := by omega
            have hz'y : z'.2 = h := by omega
            by_cases hz'x3 : z'.1 < X + 3
            · -- z'.1 ∈ {X, X+1, X+2}; if z'.1 ≠ X + i, Balcony says occupied!
              by_cases hz'i : z'.1 = X + (i.val : ℤ)
              · exact ⟨hz'i, Or.inl hz'y⟩
              · exfalso
                have hbal := hBal.2.2 ⟨(z'.1 - X).toNat, by omega⟩
                unfold bucketCell at hbal
                have hneq : (⟨(z'.1 - X).toNat, by omega⟩ : Fin 3) ≠ i := by
                  intro he; have := congrArg Fin.val he; dsimp at this; omega
                have h1 : 6 * (j.val : ℤ) + ((z'.1 - X).toNat : ℤ) = z'.1 := by omega
                rw [h1] at hbal
                have hclr := hCq' z' hz'
                have hz'eq : z' = (z'.1, h) := Prod.ext rfl hz'y
                rw [hz'eq] at hclr
                simp [hneq] at hbal
                simp [hbal] at hclr
            · -- z'.1 ∈ {X + 3, X + 4} and z'.2 = h
              exfalso
              have hclr' := hCq' z' hz'
              by_cases hmod : (h + 1) % 6 = 5
              · -- then h + 1 < H and (X + 3, h + 1), (X + 4, h + 1), (X + 5, h + 1) are all occupied!
                rcases hF.2.1 with ⟨T, hH⟩
                have hh0 := hBal.1
                have hU34 := bucketFrame_notch_wall hF j (h + 1) (by omega) (by omega)
                have hU5 := bucketFrame_right_wall hF j (h + 1) (by omega)
                have hqpx_cases : q.position.1 = X + 2 ∨ q.position.1 = X + 3 ∨
                    q.position.1 = X + 4 ∨ q.position.1 = X + 5 := by omega
                rcases hqpx_cases with h2 | h3 | h4 | h5
                · exact hpos21 (by ext <;> dsimp <;> omega)
                · have heqp : q.position = (6 * (j.val : ℤ) + 3, h + 1) := Prod.ext h3 hqpy1
                  rw [heqp] at hqp_clr; simp [hU34.1] at hqp_clr
                · have heqp : q.position = (6 * (j.val : ℤ) + 4, h + 1) := Prod.ext h4 hqpy1
                  rw [heqp] at hqp_clr; simp [hU34.2] at hqp_clr
                · have heqp : q.position = (6 * (j.val : ℤ) + 5, h + 1) := Prod.ext h5 hqpy1
                  rw [heqp] at hqp_clr; simp [hU5] at hqp_clr
              · have hnw := bucketFrame_notch_wall hF j h hhH hmod
                have hz'34 : z'.1 = X + 3 ∨ z'.1 = X + 4 := by omega
                rcases hz'34 with h3 | h4
                · have heqz : z' = (6 * (j.val : ℤ) + 3, h) := Prod.ext h3 hz'y
                  rw [heqz] at hclr'; simp [hnw.1] at hclr'
                · have heqz : z' = (6 * (j.val : ℤ) + 4, h) := Prod.ext h4 hz'y
                  rw [heqz] at hclr'; simp [hnw.2] at hclr'
    · -- translate (-1) 0
      intro z' hz' hx1 hx2 hy
      exfalso
      unfold TetrisHard.Rows.translate PieceState.cells at hz'
      rcases List.mem_map.mp hz' with ⟨z0, hz0, heq⟩
      have hmem : (z'.1 + 1, z'.2) ∈ q.cells := by
        unfold PieceState.cells
        refine List.mem_map.mpr ⟨z0, hz0, ?_⟩
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp at h1 h2
        ext <;> dsimp <;> omega
      by_cases hlt : z'.1 + 1 < X + 5
      · exact hNoLow _ hmem (by omega) hlt hy
      · have hocc := bucketFrame_right_wall hF j z'.2 (by omega)
        have hclr := hCq _ hmem
        have h1 : z'.1 + 1 = 6 * (j.val : ℤ) + 5 := by omega
        rw [h1] at hclr; simp [hocc] at hclr
    · -- translate 1 0
      intro z' hz' hx1 hx2 hy
      exfalso
      unfold TetrisHard.Rows.translate PieceState.cells at hz'
      rcases List.mem_map.mp hz' with ⟨z0, hz0, heq⟩
      have hmem : (z'.1 - 1, z'.2) ∈ q.cells := by
        unfold PieceState.cells
        refine List.mem_map.mpr ⟨z0, hz0, ?_⟩
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp at h1 h2
        ext <;> dsimp <;> omega
      by_cases hge : X ≤ z'.1 - 1
      · exact hNoLow _ hmem hge (by omega) hy
      · have hocc := bucketFrame_left_wall hF j z'.2 (by omega)
        have hclr := hCq _ hmem
        have h1 : z'.1 - 1 = 6 * (j.val : ℤ) - 1 := by omega
        rw [h1] at hclr; simp [hocc] at hclr
    · -- translate 0 (-1)
      intro z' hz' hx1 hx2 hy
      unfold TetrisHard.Rows.translate PieceState.cells at hz'
      rcases List.mem_map.mp hz' with ⟨z0, hz0, heq⟩
      have hmem : (z'.1, z'.2 + 1) ∈ q.cells := by
        unfold PieceState.cells
        refine List.mem_map.mpr ⟨z0, hz0, ?_⟩
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp at h1 h2
        ext <;> dsimp <;> omega
      by_cases hyh : z'.2 + 1 ≤ h
      · exact absurd hmem (fun hm => hNoLow _ hm hx1 hx2 hyh)
      · have hz'y : z'.2 = h := by omega
        by_cases hz'x3 : z'.1 < X + 3
        · by_cases hz'i : z'.1 = X + (i.val : ℤ)
          · exact ⟨hz'i, Or.inl hz'y⟩
          · exfalso
            have hbal := hBal.2.2 ⟨(z'.1 - X).toNat, by omega⟩
            unfold bucketCell at hbal
            have hneq : (⟨(z'.1 - X).toNat, by omega⟩ : Fin 3) ≠ i := by
              intro he; have := congrArg Fin.val he; dsimp at this; omega
            have h1 : 6 * (j.val : ℤ) + ((z'.1 - X).toNat : ℤ) = z'.1 := by omega
            rw [h1] at hbal
            have hclr := hCq' z' (by unfold TetrisHard.Rows.translate PieceState.cells; exact List.mem_map.mpr ⟨z0, hz0, heq⟩)
            have hz'eq : z' = (z'.1, h) := Prod.ext rfl hz'y
            rw [hz'eq] at hclr
            simp [hneq] at hbal
            simp [hbal] at hclr
        · exfalso
          have hclr' := hCq' z' (by unfold TetrisHard.Rows.translate PieceState.cells; exact List.mem_map.mpr ⟨z0, hz0, heq⟩)
          have hclr := hCq _ hmem
          by_cases hmod : (h + 1) % 6 = 5
          · rcases hF.2.1 with ⟨T, hH⟩
            have hh0 := hBal.1
            have hU34 := bucketFrame_notch_wall hF j (h + 1) (by omega) (by omega)
            have hz'34 : z'.1 = X + 3 ∨ z'.1 = X + 4 := by omega
            rcases hz'34 with h3 | h4
            · rw [h3, hz'y] at hclr; simp [X, hU34.1] at hclr
            · rw [h4, hz'y] at hclr; simp [X, hU34.2] at hclr
          · have hnw := bucketFrame_notch_wall hF j h hhH hmod
            have hz'34 : z'.1 = X + 3 ∨ z'.1 = X + 4 := by omega
            rcases hz'34 with h3 | h4
            · have heqz : z' = (6 * (j.val : ℤ) + 3, h) := Prod.ext h3 hz'y
              rw [heqz] at hclr'; simp [hnw.1] at hclr'
            · have heqz : z' = (6 * (j.val : ℤ) + 4, h) := Prod.ext h4 hz'y
              rw [heqz] at hclr'; simp [hnw.2] at hclr'
    · -- fix
      exact hG

private lemma cond4 :
    ∀ (B : Board) s H, BucketFrame B s H → ∀ (j : Fin s) h i t q,
      Balcony B j.val H h i → h < H → t ≠ .I → Reachable instantaneous B H t q →
      ∀ z ∈ q.cells, 6 * (j.val : ℤ) ≤ z.1 → z.1 < 6 * (j.val : ℤ) + 5 → z.2 ≤ h →
        z.1 = 6 * (j.val : ℤ) + i.val ∧ (z.2 = h ∨ z.2 = h - 1) := by
  intro B s H hF j h i t q hBal hhH ht hReach
  rcases hReach with ⟨hSpawnH, _, hPath⟩
  have hInv : q.kind = t ∧ GoodBalcony (6 * (j.val : ℤ)) h i q := by
    induction hPath with
    | refl =>
      refine ⟨rfl, fun z hz _ _ hy => ?_⟩
      have := hSpawnH z hz
      omega
    | @tail q q' _ hM ih =>
      have hk' : q'.kind = t := (move_kind hM).trans ih.1
      refine ⟨hk', balcony_step hF hBal hhH (by rw [ih.1]; exact ht) hM ih.2⟩
  exact hInv.2

theorem main_result : instantaneous.Admissible ∧ Reasonable instantaneous :=
  ⟨instantaneous_admissible, cond1, cond2, cond3, cond4, cond5⟩

end TetrisLemma510

open TetrisHard.Rows in
theorem solution : instantaneous.Admissible ∧ Reasonable instantaneous :=
  TetrisLemma510.main_result

#print axioms solution
