-- Prove2me | solution 1 for TetrisHard.Rows.unapproachable_unfillable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:18:38.532202+00:00
-- url     : https://prove2.me/submissions/a890a96b-dc21-4337-a8f1-dc76735106a9

import Definitions.Def_TetrisHard_Rows_Reservoir

set_option autoImplicit false

namespace TetrisHard.Rows.Lemma58

open TetrisHard.Rows

/-! ### Basic board, trajectory, and frame lemmas -/

private lemma occupied_insert_of_occupied {B : Board} {q : PieceState} {z : Cell}
    (h : B.occupied z = true) : (B.insert q).occupied z = true := by
  unfold Board.occupied at h ⊢
  unfold Board.insert
  dsimp only at *
  split_ifs at h ⊢
  · simp [h]
  · rfl
  · rfl

private lemma occupied_insert_of_mem {B : Board} {q : PieceState} {z : Cell}
    (hy0 : 0 ≤ z.2) (hy1 : z.2 < B.height) (hx0 : 0 ≤ z.1) (hx1 : z.1 < B.width)
    (hz : z ∈ q.cells) : (B.insert q).occupied z = true := by
  unfold Board.occupied Board.insert
  dsimp only
  rw [dif_pos ⟨hy0, hy1⟩, dif_pos ⟨hx0, hx1⟩]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  right
  have h1 : ((z.1.toNat : ℤ), (z.2.toNat : ℤ)) = z := by
    ext <;> simp [hx0, hy0]
  rw [h1]
  exact hz

private lemma occupied_insert_of_not_mem {B : Board} {q : PieceState} {z : Cell}
    (h : B.occupied z = false) (hz : z ∉ q.cells) : (B.insert q).occupied z = false := by
  unfold Board.occupied at h ⊢
  unfold Board.insert
  dsimp only at *
  split_ifs at h ⊢ with hy hx
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨h, ?_⟩
  have h1 : ((z.1.toNat : ℤ), (z.2.toNat : ℤ)) = z := by
    ext <;> simp [hx.1, hy.1]
  rw [h1]
  exact hz

private lemma bucketCell_insert_of_true {B : Board} {q : PieceState} {j : ℕ} {x y : ℤ}
    (h : bucketCell B j x y = true) : bucketCell (B.insert q) j x y = true :=
  occupied_insert_of_occupied h

private lemma bucketCell_insert_of_not_mem {B : Board} {q : PieceState} {j : ℕ} {x y : ℤ}
    (h : bucketCell B j x y = false) (hz : (6 * (j : ℤ) + x, y) ∉ q.cells) :
    bucketCell (B.insert q) j x y = false :=
  occupied_insert_of_not_mem h hz

private lemma bucketCell_insert_of_mem {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    {j : Fin s} {q : PieceState} {x y : ℤ}
    (hx0 : 0 ≤ x) (hx1 : x < 6) (hy0 : 0 ≤ y) (hy1 : y < H)
    (hz : (6 * (j.val : ℤ) + x, y) ∈ q.cells) :
    bucketCell (B.insert q) j.val x y = true := by
  apply occupied_insert_of_mem hy0 _ _ _ hz
  · have := hframe.2.2.1; omega
  · omega
  · have := hframe.1; have := j.isLt; omega

private lemma bucketFrame_insert {B : Board} {s H : ℕ} {q : PieceState}
    (hframe : BucketFrame B s H) : BucketFrame (B.insert q) s H := by
  rcases hframe with ⟨hw, hH, hh, hcells⟩
  refine ⟨hw, hH, hh, fun j y hy => ?_⟩
  rcases hcells j y hy with ⟨h5, h34⟩
  refine ⟨occupied_insert_of_occupied h5, fun hmod => ?_⟩
  rcases h34 hmod with ⟨h3, h4⟩
  exact ⟨occupied_insert_of_occupied h3, occupied_insert_of_occupied h4⟩

private lemma trajectory_clear {R : Rotation} {B : Board} {t : Piece} {q : PieceState}
    (ht : Trajectory R B t q) : B.Clear q := by
  rcases ht with ⟨hspawn, hpath, _⟩
  induction hpath with
  | refl => exact hspawn
  | tail _ hstep _ => exact hstep.2.2.1

private lemma spawn_cells_ge_H {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (t : Piece) :
    ∀ z ∈ (spawn B t).cells, (H : ℤ) ≤ z.2 := by
  have hh : H + 3 ≤ B.height := hframe.2.2.1
  intro z hz
  cases t <;> simp [spawn, PieceState.cells, Piece.base] at hz <;>
    rcases hz with rfl | rfl | rfl | rfl <;> omega

private lemma trajectory_reachable {R : Rotation} {B : Board} {s H : ℕ} {t : Piece} {q : PieceState}
    (hframe : BucketFrame B s H) (ht : Trajectory R B t q) : Reachable R B H t q :=
  ⟨spawn_cells_ge_H hframe t, ht.1, ht.2.1⟩

private lemma bucketCell_left_wall {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {y : ℤ} (hy0 : 0 ≤ y) (hy1 : y < H) :
    bucketCell B j.val (-1) y = true := by
  unfold bucketCell
  by_cases hj : j.val = 0
  · rw [hj]
    unfold Board.occupied
    have hneg : ¬ (0 ≤ (6 * ((0 : ℕ) : ℤ) + -1) ∧ (6 * ((0 : ℕ) : ℤ) + -1) < B.width) := by omega
    split_ifs <;> rfl
  · let j' : Fin s := ⟨j.val - 1, by omega⟩
    have h := (hframe.2.2.2 j' y.toNat (by omega)).1
    have heq : (6 * (j'.val : ℤ) + 5, (y.toNat : ℤ)) = (6 * (j.val : ℤ) + -1, y) := by
      ext
      · simp [j']; omega
      · exact Int.toNat_of_nonneg hy0
    rwa [← heq]

private lemma bucketCell_right_wall {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {y : ℤ} (hy0 : 0 ≤ y) (hy1 : y < H) :
    bucketCell B j.val 5 y = true := by
  unfold bucketCell
  have h := (hframe.2.2.2 j y.toNat (by omega)).1
  have heq : (6 * (j.val : ℤ) + 5, (y.toNat : ℤ)) = (6 * (j.val : ℤ) + 5, y) := by
    ext
    · rfl
    · exact Int.toNat_of_nonneg hy0
  rwa [← heq]

private lemma not_bucketFull_of_false {B : Board} {j H : ℕ} (hfull : BucketFull B j H)
    {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x < 6) (hy0 : 0 ≤ y) (hy1 : y < H)
    (hf : bucketCell B j x y = false) : False := by
  have h := hfull x.toNat (Finset.mem_range.mpr (by omega)) y.toNat (Finset.mem_range.mpr (by omega))
  unfold bucketCell at hf
  rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] at h
  rw [h] at hf
  cases hf

/-! ### Finite piece-geometry lemmas -/

private def offsets (t : Piece) (o : Fin 4) : List Cell :=
  t.base.map fun z => if t = .Sq then z else clockwise^[o.val] z

private def shifted (t : Piece) (o : Fin 4) (u : Cell) : List Cell :=
  (offsets t o).map fun v => (v.1 - u.1, v.2 - u.2)

private lemma mem_cells_iff {q : PieceState} {z : Cell} :
    z ∈ q.cells ↔ ∃ u ∈ offsets q.kind q.orientation,
      z = (q.position.1 + u.1, q.position.2 + u.2) := by
  constructor
  · intro hz
    rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact ⟨if q.kind = .Sq then w else clockwise^[q.orientation.val] w,
      List.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rcases List.mem_map.mp hu with ⟨w, hw, rfl⟩
    exact List.mem_map.mpr ⟨w, hw, rfl⟩

private lemma shifted_mem_cells {q : PieceState} {z₀ u d : Cell}
    (hz₀ : z₀ = (q.position.1 + u.1, q.position.2 + u.2))
    (hd : d ∈ shifted q.kind q.orientation u) :
    (z₀.1 + d.1, z₀.2 + d.2) ∈ q.cells := by
  rcases List.mem_map.mp hd with ⟨v, hv, rfl⟩
  rw [mem_cells_iff]
  refine ⟨v, hv, ?_⟩
  rcases hz₀ with rfl
  ext <;> dsimp <;> omega

private lemma mem_shifted_of_mem_cells {q : PieceState} {z₀ u d : Cell}
    (hz₀ : z₀ = (q.position.1 + u.1, q.position.2 + u.2))
    (hmem : (z₀.1 + d.1, z₀.2 + d.2) ∈ q.cells) :
    d ∈ shifted q.kind q.orientation u := by
  rw [mem_cells_iff] at hmem
  rcases hmem with ⟨v, hv, heq⟩
  apply List.mem_map.mpr
  refine ⟨v, hv, ?_⟩
  rcases hz₀ with rfl
  have h1 : q.position.1 + u.1 + d.1 = q.position.1 + v.1 := congrArg Prod.fst heq
  have h2 : q.position.2 + u.2 + d.2 = q.position.2 + v.2 := congrArg Prod.snd heq
  ext <;> dsimp <;> omega

private lemma offsets_nonempty (t : Piece) (o : Fin 4) : ∃ u, u ∈ offsets t o := by
  cases t <;> simp [offsets, Piece.base]

private lemma cells_nonempty (q : PieceState) : ∃ z, z ∈ q.cells := by
  rcases offsets_nonempty q.kind q.orientation with ⟨u, hu⟩
  exact ⟨(q.position.1 + u.1, q.position.2 + u.2), mem_cells_iff.mpr ⟨u, hu, rfl⟩⟩

-- G1: Every cell of any piece has an orthogonal neighbor in the same piece.
private lemma geom_G1_aux (t : Piece) (o : Fin 4) :
    ∀ u ∈ offsets t o,
      (1, 0) ∈ shifted t o u ∨ (-1, 0) ∈ shifted t o u ∨
      (0, 1) ∈ shifted t o u ∨ (0, -1) ∈ shifted t o u := by
  cases t <;> fin_cases o <;> decide

private lemma geom_G1 {q : PieceState} {z : Cell} (hz : z ∈ q.cells) :
    (z.1 + 1, z.2) ∈ q.cells ∨ (z.1 - 1, z.2) ∈ q.cells ∨
    (z.1, z.2 + 1) ∈ q.cells ∨ (z.1, z.2 - 1) ∈ q.cells := by
  rcases mem_cells_iff.mp hz with ⟨u, hu, hz_eq⟩
  rcases geom_G1_aux q.kind q.orientation u hu with h | h | h | h
  · left; simpa using shifted_mem_cells hz_eq h
  · right; left; simpa [sub_eq_add_neg] using shifted_mem_cells hz_eq h
  · right; right; left; simpa using shifted_mem_cells hz_eq h
  · right; right; right; simpa [sub_eq_add_neg] using shifted_mem_cells hz_eq h

-- G2: Covering (4, r) when (4,r+1), (4,r-1), (5,r), (3,r+1), (3,r-1) are occupied.
private lemma geom_G2_aux (t : Piece) (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (o : Fin 4) :
    ∀ u ∈ offsets t o,
      (0, 1) ∈ shifted t o u ∨ (0, -1) ∈ shifted t o u ∨
      (1, 0) ∈ shifted t o u ∨ (-1, 1) ∈ shifted t o u ∨ (-1, -1) ∈ shifted t o u ∨
      (((!decide ((-2, -1) ∈ shifted t o u)) = true ∧ (!decide ((-4, -2) ∈ shifted t o u)) = true) ∧
       ((t = .I ∧ (-3, 0) ∈ shifted t o u ∧ (-2, 0) ∈ shifted t o u ∧ (-1, 0) ∈ shifted t o u) ∨
        (t = .LG ∧ (-2, 0) ∈ shifted t o u ∧ (-1, 0) ∈ shifted t o u))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> fin_cases o <;> decide

private lemma geom_G2 {B : Board} {j : ℕ} {r : ℤ} {q : PieceState}
    (hk : q.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (hclear : B.Clear q)
    (h4u : bucketCell B j 4 (r + 1) = true) (h4d : bucketCell B j 4 (r - 1) = true)
    (h5 : bucketCell B j 5 r = true)
    (h3u : bucketCell B j 3 (r + 1) = true) (h3d : bucketCell B j 3 (r - 1) = true)
    (hmem : (6 * (j : ℤ) + 4, r) ∈ q.cells) :
    ((6 * (j : ℤ) + 2, r - 1) ∉ q.cells ∧ (6 * (j : ℤ) + 0, r - 2) ∉ q.cells) ∧
    ((q.kind = .I ∧ (6 * (j : ℤ) + 1, r) ∈ q.cells ∧ (6 * (j : ℤ) + 2, r) ∈ q.cells ∧
        (6 * (j : ℤ) + 3, r) ∈ q.cells) ∨
     (q.kind = .LG ∧ (6 * (j : ℤ) + 2, r) ∈ q.cells ∧ (6 * (j : ℤ) + 3, r) ∈ q.cells)) := by
  rcases mem_cells_iff.mp hmem with ⟨u, hu, heq⟩
  have hnot : ∀ d : Cell, B.occupied (6 * (j : ℤ) + 4 + d.1, r + d.2) = true →
      d ∉ shifted q.kind q.orientation u := by
    intro d hocc hd
    have hc := hclear _ (shifted_mem_cells heq hd)
    dsimp at hc
    rw [hocc] at hc
    cases hc
  rcases geom_G2_aux q.kind hk q.orientation u hu with h | h | h | h | h | ⟨⟨hn1, hn2⟩, hres⟩
  · exact absurd h (hnot (0, 1) (by simpa [bucketCell, add_assoc] using h4u))
  · exact absurd h (hnot (0, -1) (by simpa [bucketCell, sub_eq_add_neg, add_assoc] using h4d))
  · exact absurd h (hnot (1, 0) (by simpa [bucketCell, add_assoc] using h5))
  · exact absurd h (hnot (-1, 1) (by
      have : (6 * (j : ℤ) + 4 + -1, r + 1) = (6 * (j : ℤ) + 3, r + 1) := by ext <;> omega
      rw [this]; exact h3u))
  · exact absurd h (hnot (-1, -1) (by
      have : (6 * (j : ℤ) + 4 + -1, r + -1) = (6 * (j : ℤ) + 3, r - 1) := by ext <;> omega
      rw [this]; exact h3d))
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hn1 hn2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hm
      apply hn1
      apply mem_shifted_of_mem_cells heq
      convert hm using 1; ext <;> omega
    · intro hm
      apply hn2
      apply mem_shifted_of_mem_cells heq
      convert hm using 1; ext <;> omega
    · rcases hres with ⟨hI, h1, h2, h3⟩ | ⟨hL, h2, h3⟩
      · left
        refine ⟨hI, ?_, ?_, ?_⟩
        · convert shifted_mem_cells heq h1 using 1; ext <;> omega
        · convert shifted_mem_cells heq h2 using 1; ext <;> omega
        · convert shifted_mem_cells heq h3 using 1; ext <;> omega
      · right
        refine ⟨hL, ?_, ?_⟩
        · convert shifted_mem_cells heq h2 using 1; ext <;> omega
        · convert shifted_mem_cells heq h3 using 1; ext <;> omega

-- G3: An .I piece in bucket j cannot cover (2, r-1) when (2,r), (2,r-2), (3,r-1) are occupied.
private lemma geom_G3_aux :
    ∀ o : Fin 4, ∀ u ∈ offsets .I o,
      (0, 1) ∈ shifted .I o u ∨ (0, -1) ∈ shifted .I o u ∨
      (1, 0) ∈ shifted .I o u ∨ ∃ d ∈ shifted .I o u, d.1 < -2 := by
  decide

private lemma geom_G3 {B : Board} {j : ℕ} {r : ℤ} {q : PieceState}
    (hk : q.kind = .I) (hin : InBucket j q) (hclear : B.Clear q)
    (h2u : bucketCell B j 2 r = true) (h2d : bucketCell B j 2 (r - 2) = true)
    (h3 : bucketCell B j 3 (r - 1) = true) :
    (6 * (j : ℤ) + 2, r - 1) ∉ q.cells := by
  intro hmem
  rcases mem_cells_iff.mp hmem with ⟨u, hu, heq⟩
  rw [hk] at hu
  rcases geom_G3_aux q.orientation u hu with h | h | h | ⟨d, hd, hlt⟩
  · have hc := hclear _ (shifted_mem_cells heq (by rwa [hk]))
    have : (6 * (j : ℤ) + 2 + 0, r - 1 + 1) = (6 * (j : ℤ) + 2, r) := by ext <;> omega
    rw [this] at hc; unfold bucketCell at h2u; rw [h2u] at hc; cases hc
  · have hc := hclear _ (shifted_mem_cells heq (by rwa [hk]))
    have : (6 * (j : ℤ) + 2 + 0, r - 1 + -1) = (6 * (j : ℤ) + 2, r - 2) := by ext <;> omega
    rw [this] at hc; unfold bucketCell at h2d; rw [h2d] at hc; cases hc
  · have hc := hclear _ (shifted_mem_cells heq (by rwa [hk]))
    have : (6 * (j : ℤ) + 2 + 1, r - 1 + 0) = (6 * (j : ℤ) + 3, r - 1) := by ext <;> omega
    rw [this] at hc; unfold bucketCell at h3; rw [h3] at hc; cases hc
  · have hb := hin _ (shifted_mem_cells heq (by rwa [hk]))
    dsimp at hb; omega

-- G4: Covering (2, r-1) without (2, r) when (2,r-2), (1,r-2), (3,r-1) are occupied.
private lemma geom_G4_aux (t : Piece) (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (o : Fin 4) :
    ∀ u ∈ offsets t o,
      (∃ d ∈ shifted t o u, d.1 < -2 ∨ 3 < d.1) ∨
      (0, -1) ∈ shifted t o u ∨ (-1, -1) ∈ shifted t o u ∨
      (1, 0) ∈ shifted t o u ∨ (0, 1) ∈ shifted t o u ∨
      ((!decide ((-2, -1) ∈ shifted t o u)) = true ∧
       (((-1, 1) ∈ shifted t o u ∧ (-2, 1) ∈ shifted t o u) ∨
        ((-2, 0) ∈ shifted t o u ∧ (-2, 1) ∈ shifted t o u))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> fin_cases o <;> decide

private lemma geom_G4 {B : Board} {j : ℕ} {r : ℤ} {q : PieceState}
    (hk : q.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece))
    (hin : InBucket j q) (hclear : B.Clear q)
    (h2d : bucketCell B j 2 (r - 2) = true) (h1d : bucketCell B j 1 (r - 2) = true)
    (h3 : bucketCell B j 3 (r - 1) = true)
    (hmem : (6 * (j : ℤ) + 2, r - 1) ∈ q.cells)
    (hno2r : (6 * (j : ℤ) + 2, r) ∉ q.cells) :
    (6 * (j : ℤ) + 0, r - 2) ∉ q.cells ∧
    (((6 * (j : ℤ) + 1, r) ∈ q.cells ∧ (6 * (j : ℤ) + 0, r) ∈ q.cells) ∨
     ((6 * (j : ℤ) + 0, r - 1) ∈ q.cells ∧ (6 * (j : ℤ) + 0, r) ∈ q.cells)) := by
  rcases mem_cells_iff.mp hmem with ⟨u, hu, heq⟩
  have hnot : ∀ d : Cell, B.occupied (6 * (j : ℤ) + 2 + d.1, r - 1 + d.2) = true →
      d ∉ shifted q.kind q.orientation u := by
    intro d hocc hd
    have hc := hclear _ (shifted_mem_cells heq hd)
    dsimp at hc; rw [hocc] at hc; cases hc
  rcases geom_G4_aux q.kind hk q.orientation u hu with
    ⟨d, hd, hbad⟩ | h | h | h | h | ⟨hn, hres⟩
  · have hb := hin _ (shifted_mem_cells heq hd); dsimp at hb; omega
  · exact absurd h (hnot (0, -1) (by
      have : (6 * (j : ℤ) + 2 + 0, r - 1 + -1) = (6 * (j : ℤ) + 2, r - 2) := by ext <;> omega
      rw [this]; exact h2d))
  · exact absurd h (hnot (-1, -1) (by
      have : (6 * (j : ℤ) + 2 + -1, r - 1 + -1) = (6 * (j : ℤ) + 1, r - 2) := by ext <;> omega
      rw [this]; exact h1d))
  · exact absurd h (hnot (1, 0) (by
      have : (6 * (j : ℤ) + 2 + 1, r - 1 + 0) = (6 * (j : ℤ) + 3, r - 1) := by ext <;> omega
      rw [this]; exact h3))
  · exfalso; apply hno2r; convert shifted_mem_cells heq h using 1; ext <;> omega
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hn
    refine ⟨?_, ?_⟩
    · intro hm
      apply hn
      apply mem_shifted_of_mem_cells heq
      convert hm using 1; ext <;> omega
    · rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨by convert shifted_mem_cells heq h1 using 1; ext <;> omega,
               by convert shifted_mem_cells heq h2 using 1; ext <;> omega⟩
      · right
        exact ⟨by convert shifted_mem_cells heq h1 using 1; ext <;> omega,
               by convert shifted_mem_cells heq h2 using 1; ext <;> omega⟩

-- G5: Covering (0, r-2) when (1, r-2) and (0, r-3) are occupied.
private lemma geom_G5_aux (t : Piece) (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (o : Fin 4) :
    ∀ u ∈ offsets t o,
      (∃ d ∈ shifted t o u, d.1 < 0) ∨
      (1, 0) ∈ shifted t o u ∨ (0, -1) ∈ shifted t o u ∨
      (0, 2) ∈ shifted t o u ∨ ((1, 2) ∈ shifted t o u ∧ (0, 1) ∈ shifted t o u) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> fin_cases o <;> decide

private lemma geom_G5 {B : Board} {j : ℕ} {r : ℤ} {q : PieceState}
    (hk : q.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece))
    (hin : InBucket j q) (hclear : B.Clear q)
    (h1 : bucketCell B j 1 (r - 2) = true) (h0 : bucketCell B j 0 (r - 3) = true)
    (hmem : (6 * (j : ℤ) + 0, r - 2) ∈ q.cells) :
    (6 * (j : ℤ) + 0, r) ∈ q.cells ∨
    ((6 * (j : ℤ) + 1, r) ∈ q.cells ∧ (6 * (j : ℤ) + 0, r - 1) ∈ q.cells) := by
  rcases mem_cells_iff.mp hmem with ⟨u, hu, heq⟩
  have hnot : ∀ d : Cell, B.occupied (6 * (j : ℤ) + 0 + d.1, r - 2 + d.2) = true →
      d ∉ shifted q.kind q.orientation u := by
    intro d hocc hd
    have hc := hclear _ (shifted_mem_cells heq hd)
    dsimp at hc; rw [hocc] at hc; cases hc
  rcases geom_G5_aux q.kind hk q.orientation u hu with
    ⟨d, hd, hbad⟩ | h | h | h | ⟨h1', h2'⟩
  · have hb := hin _ (shifted_mem_cells heq hd); dsimp at hb; omega
  · exact absurd h (hnot (1, 0) (by
      have : (6 * (j : ℤ) + 0 + 1, r - 2 + 0) = (6 * (j : ℤ) + 1, r - 2) := by ext <;> omega
      rw [this]; exact h1))
  · exact absurd h (hnot (0, -1) (by
      have : (6 * (j : ℤ) + 0 + 0, r - 2 + -1) = (6 * (j : ℤ) + 0, r - 3) := by ext <;> omega
      rw [this]; exact h0))
  · left; convert shifted_mem_cells heq h using 1; ext <;> omega
  · right
    exact ⟨by convert shifted_mem_cells heq h1' using 1; ext <;> omega,
           by convert shifted_mem_cells heq h2' using 1; ext <;> omega⟩

/-! ### Permanently unfillable configurations -/

-- Bad State 1: An empty cell surrounded on all 4 sides.
private lemma unfillable_of_surrounded {R : Rotation} {B : Board} {j H : ℕ} {x y : ℤ}
    (hx0 : 0 ≤ x) (hx1 : x < 6) (hy0 : 0 ≤ y) (hy1 : y < H)
    (hf : bucketCell B j x y = false)
    (hr : bucketCell B j (x + 1) y = true) (hl : bucketCell B j (x - 1) y = true)
    (hu : bucketCell B j x (y + 1) = true) (hd : bucketCell B j x (y - 1) = true) :
    Unfillable R B j H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull hx0 hx1 hy0 hy1 hf
  | @step B B' q _ _ htraj _ ih =>
    have hclear := trajectory_clear htraj
    have hnotmem : (6 * (j : ℤ) + x, y) ∉ q.cells := by
      intro hmem
      rcases geom_G1 hmem with h | h | h | h
      · have hc := hclear _ h
        have : (6 * (j : ℤ) + x + 1, y) = (6 * (j : ℤ) + (x + 1), y) := by ext <;> omega
        rw [this] at hc; unfold bucketCell at hr; rw [hr] at hc; cases hc
      · have hc := hclear _ h
        have : (6 * (j : ℤ) + x - 1, y) = (6 * (j : ℤ) + (x - 1), y) := by ext <;> omega
        rw [this] at hc; unfold bucketCell at hl; rw [hl] at hc; cases hc
      · have hc := hclear _ h; unfold bucketCell at hu; rw [hu] at hc; cases hc
      · have hc := hclear _ h; unfold bucketCell at hd; rw [hd] at hc; cases hc
    exact ih (bucketCell_insert_of_not_mem hf hnotmem)
      (bucketCell_insert_of_true hr) (bucketCell_insert_of_true hl)
      (bucketCell_insert_of_true hu) (bucketCell_insert_of_true hd) hfull

-- Bad State 2: Row r is completely full in bucket j, with an empty cell below row r.
private lemma emptyAdjacent_symm {B : Board} {z z' : Cell}
    (h : EmptyAdjacent B z z') : EmptyAdjacent B z' z := by
  rcases h with ⟨h1, h2, h3⟩
  refine ⟨h2, h1, ?_⟩
  rw [abs_sub_comm z'.1 z.1, abs_sub_comm z'.2 z.2]
  exact h3

private lemma reflTransGen_emptyAdjacent_symm {B : Board} {z z' : Cell}
    (h : Relation.ReflTransGen (EmptyAdjacent B) z z') :
    Relation.ReflTransGen (EmptyAdjacent B) z' z := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (emptyAdjacent_symm hstep) ih

private lemma reachable_emptyAdjacent {R : Rotation} (hReason : Reasonable R)
    {B : Board} {q₁ q₂ : PieceState}
    (hpath : Relation.ReflTransGen (Move R B) q₁ q₂) :
    ∀ z₂ ∈ q₂.cells, ∃ z₁ ∈ q₁.cells, Relation.ReflTransGen (EmptyAdjacent B) z₁ z₂ := by
  induction hpath with
  | refl =>
    intro z hz
    exact ⟨z, hz, .refl⟩
  | @tail q₂ q₃ _ hstep ih =>
    intro z₃ hz₃
    rcases cells_nonempty q₂ with ⟨z₂, hz₂⟩
    rcases ih z₂ hz₂ with ⟨z₁, hz₁, h12⟩
    exact ⟨z₁, hz₁, h12.trans (hReason.1 B q₂ q₃ hstep z₂ hz₂ z₃ hz₃)⟩

private lemma emptyAdjacent_stay_in_box {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {r : ℤ} (hrH : r < H)
    (h0 : bucketCell B j.val 0 r = true) (h1 : bucketCell B j.val 1 r = true)
    (h2 : bucketCell B j.val 2 r = true) (h3 : bucketCell B j.val 3 r = true)
    (h4 : bucketCell B j.val 4 r = true)
    {z z' : Cell} (hz : 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ z.2 ∧ z.2 < r)
    (hadj : EmptyAdjacent B z z') :
    6 * (j.val : ℤ) ≤ z'.1 ∧ z'.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ z'.2 ∧ z'.2 < r := by
  rcases hadj with ⟨_, hz'f, hdist⟩
  have hstep : (z'.1 = z.1 + 1 ∧ z'.2 = z.2) ∨ (z'.1 = z.1 - 1 ∧ z'.2 = z.2) ∨
      (z'.1 = z.1 ∧ z'.2 = z.2 + 1) ∨ (z'.1 = z.1 ∧ z'.2 = z.2 - 1) := by
    rcases abs_cases (z.1 - z'.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (z.2 - z'.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · by_cases h5 : z'.1 = 6 * (j.val : ℤ) + 5
    · have hw := bucketCell_right_wall hframe j (by omega) (by omega : z'.2 < H)
      unfold bucketCell at hw
      have heq : (6 * (j.val : ℤ) + 5, z'.2) = z' := by ext <;> omega
      rw [heq] at hw; rw [hw] at hz'f; cases hz'f
    · omega
  · by_cases hm1 : z'.1 = 6 * (j.val : ℤ) - 1
    · have hw := bucketCell_left_wall hframe j (by omega) (by omega : z'.2 < H)
      unfold bucketCell at hw
      have heq : (6 * (j.val : ℤ) + -1, z'.2) = z' := by ext <;> omega
      rw [heq] at hw; rw [hw] at hz'f; cases hz'f
    · omega
  · by_cases htop : z'.2 = r
    · have hdx : z'.1 - 6 * (j.val : ℤ) = 0 ∨ z'.1 - 6 * (j.val : ℤ) = 1 ∨
          z'.1 - 6 * (j.val : ℤ) = 2 ∨ z'.1 - 6 * (j.val : ℤ) = 3 ∨
          z'.1 - 6 * (j.val : ℤ) = 4 := by omega
      rcases hdx with h | h | h | h | h
      · have heq : (6 * (j.val : ℤ) + 0, r) = z' := by ext <;> omega
        unfold bucketCell at h0; rw [heq] at h0; rw [h0] at hz'f; cases hz'f
      · have heq : (6 * (j.val : ℤ) + 1, r) = z' := by ext <;> omega
        unfold bucketCell at h1; rw [heq] at h1; rw [h1] at hz'f; cases hz'f
      · have heq : (6 * (j.val : ℤ) + 2, r) = z' := by ext <;> omega
        unfold bucketCell at h2; rw [heq] at h2; rw [h2] at hz'f; cases hz'f
      · have heq : (6 * (j.val : ℤ) + 3, r) = z' := by ext <;> omega
        unfold bucketCell at h3; rw [heq] at h3; rw [h3] at hz'f; cases hz'f
      · have heq : (6 * (j.val : ℤ) + 4, r) = z' := by ext <;> omega
        unfold bucketCell at h4; rw [heq] at h4; rw [h4] at hz'f; cases hz'f
    · omega
  · by_cases hbot : z'.2 = -1
    · unfold Board.occupied at hz'f
      have : ¬ (0 ≤ z'.2 ∧ z'.2 < B.height) := by omega
      simp [this] at hz'f
    · omega

private lemma emptyAdjacent_path_stay_in_box {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {r : ℤ} (hrH : r < H)
    (h0 : bucketCell B j.val 0 r = true) (h1 : bucketCell B j.val 1 r = true)
    (h2 : bucketCell B j.val 2 r = true) (h3 : bucketCell B j.val 3 r = true)
    (h4 : bucketCell B j.val 4 r = true)
    {z z' : Cell} (hz : 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ z.2 ∧ z.2 < r)
    (hpath : Relation.ReflTransGen (EmptyAdjacent B) z z') :
    6 * (j.val : ℤ) ≤ z'.1 ∧ z'.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ z'.2 ∧ z'.2 < r := by
  induction hpath with
  | refl => exact hz
  | tail _ hstep ih => exact emptyAdjacent_stay_in_box hframe j hrH h0 h1 h2 h3 h4 ih hstep

private lemma unfillable_of_closed_row {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r x₀ y₀ : ℤ} (hrH : r < H)
    (hx0 : 0 ≤ x₀) (hx1 : x₀ < 5) (hy0 : 0 ≤ y₀) (hy1 : y₀ < r)
    (h0 : bucketCell B j.val 0 r = true) (h1 : bucketCell B j.val 1 r = true)
    (h2 : bucketCell B j.val 2 r = true) (h3 : bucketCell B j.val 3 r = true)
    (h4 : bucketCell B j.val 4 r = true)
    (hf : bucketCell B j.val x₀ y₀ = false) :
    Unfillable R B j.val H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull hx0 (by omega) hy0 (by omega) hf
  | @step B B' q _ _ htraj _ ih =>
    have hnotmem : (6 * (j.val : ℤ) + x₀, y₀) ∉ q.cells := by
      intro hmem
      rcases reachable_emptyAdjacent hReason htraj.2.1 _ hmem with ⟨z_s, hz_s, hpath⟩
      have hsym := reflTransGen_emptyAdjacent_symm hpath
      have hbox := emptyAdjacent_path_stay_in_box hframe j hrH h0 h1 h2 h3 h4
        (by omega) hsym
      have hge := spawn_cells_ge_H hframe q.kind z_s hz_s
      omega
    exact ih (bucketFrame_insert hframe)
      (bucketCell_insert_of_true h0) (bucketCell_insert_of_true h1)
      (bucketCell_insert_of_true h2) (bucketCell_insert_of_true h3)
      (bucketCell_insert_of_true h4)
      (bucketCell_insert_of_not_mem hf hnotmem) hfull

-- Bad State 3: Balcony (or closed row) at r with (2, r-1) empty.
private lemma unfillable_of_balcony {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r : ℤ} (hr2 : 2 ≤ r) (hrH : r < H)
    (h1r : bucketCell B j.val 1 r = true) (h2r : bucketCell B j.val 2 r = true)
    (h3r : bucketCell B j.val 3 r = true) (h4r : bucketCell B j.val 4 r = true)
    (h2d : bucketCell B j.val 2 (r - 2) = true) (h3d : bucketCell B j.val 3 (r - 1) = true)
    (hf : bucketCell B j.val 2 (r - 1) = false) :
    Unfillable R B j.val H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull (by omega) (by omega) (by omega) (by omega) hf
  | @step B B' q _ hin htraj hrest ih =>
    cases h0r : bucketCell B j.val 0 r with
    | true =>
      exact unfillable_of_closed_row hReason hframe j hrH
        (by omega : (0 : ℤ) ≤ 2) (by omega : (2 : ℤ) < 5) (by omega : 0 ≤ r - 1) (by omega)
        h0r h1r h2r h3r h4r hf ⟨B', .step ‹_› hin htraj hrest, hfull⟩
    | false =>
      have hclear := trajectory_clear htraj
      have hnotmem : (6 * (j.val : ℤ) + 2, r - 1) ∉ q.cells := by
        by_cases hI : q.kind = .I
        · exact geom_G3 hI hin hclear h2r h2d h3d
        · intro hmem
          have hbal : Balcony B j.val H r 0 := by
            refine ⟨by omega, hrH, fun x => ?_⟩
            fin_cases x
            · simpa using h0r
            · simpa using h1r
            · simpa using h2r
          have hreach := trajectory_reachable hframe htraj
          have hcond := hReason.2.2.2.1 B s H hframe j r 0 q.kind q hbal hrH hI hreach
            (6 * (j.val : ℤ) + 2, r - 1) hmem (by omega) (by omega) (by omega)
          dsimp at hcond
          omega
      exact ih (bucketFrame_insert hframe)
        (bucketCell_insert_of_true h1r) (bucketCell_insert_of_true h2r)
        (bucketCell_insert_of_true h3r) (bucketCell_insert_of_true h4r)
        (bucketCell_insert_of_true h2d) (bucketCell_insert_of_true h3d)
        (bucketCell_insert_of_not_mem hf hnotmem) hfull

-- Bad State 0: Notch at r blocked by (2, r) occupied.
private lemma unfillable_of_blocked_notch {R : Rotation}
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r : ℤ} (hr1 : 1 ≤ r) (hrH : r + 1 < H)
    (h4u : bucketCell B j.val 4 (r + 1) = true) (h4d : bucketCell B j.val 4 (r - 1) = true)
    (h3u : bucketCell B j.val 3 (r + 1) = true) (h3d : bucketCell B j.val 3 (r - 1) = true)
    (h2r : bucketCell B j.val 2 r = true)
    (hf : bucketCell B j.val 4 r = false) :
    Unfillable R B j.val H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull (by omega) (by omega) (by omega) (by omega) hf
  | @step B B' q hk _ htraj _ ih =>
    have hclear := trajectory_clear htraj
    have h5 := bucketCell_right_wall hframe j (y := r) (by omega) (by omega)
    have hnotmem : (6 * (j.val : ℤ) + 4, r) ∉ q.cells := by
      intro hmem
      have hG2 := geom_G2 hk hclear h4u h4d h5 h3u h3d hmem
      have h2mem : (6 * (j.val : ℤ) + 2, r) ∈ q.cells := by
        rcases hG2.2 with ⟨_, _, h2, _⟩ | ⟨_, h2, _⟩ <;> exact h2
      have hc := hclear _ h2mem
      unfold bucketCell at h2r; rw [h2r] at hc; cases hc
    exact ih (bucketFrame_insert hframe)
      (bucketCell_insert_of_true h4u) (bucketCell_insert_of_true h4d)
      (bucketCell_insert_of_true h3u) (bucketCell_insert_of_true h3d)
      (bucketCell_insert_of_true h2r) (bucketCell_insert_of_not_mem hf hnotmem) hfull

-- Bad State 4: Spurned notch at r.
private lemma unfillable_of_spurned_notch {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r : ℤ} (hr1 : 1 ≤ r) (hrH : r + 1 < H) (hmod : (r + 1) % 6 = 5)
    (h4u : bucketCell B j.val 4 (r + 1) = true) (h4d : bucketCell B j.val 4 (r - 1) = true)
    (h3u : bucketCell B j.val 3 (r + 1) = true) (h3d : bucketCell B j.val 3 (r - 1) = true)
    (h1r : bucketCell B j.val 1 r = true)
    (hf : bucketCell B j.val 4 r = false) :
    Unfillable R B j.val H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull (by omega) (by omega) (by omega) (by omega) hf
  | @step B B' q hk _ htraj _ ih =>
    have hclear := trajectory_clear htraj
    have h5 := bucketCell_right_wall hframe j (y := r) (by omega) (by omega)
    have hnotmem : (6 * (j.val : ℤ) + 4, r) ∉ q.cells := by
      intro hmem
      have hG2 := geom_G2 hk hclear h4u h4d h5 h3u h3d hmem
      rcases hG2.2 with ⟨_, h1mem, _, _⟩ | ⟨hLG, _, h3mem⟩
      · have hc := hclear _ h1mem
        unfold bucketCell at h1r; rw [h1r] at hc; cases hc
      · have h3f : bucketCell B j.val 3 r = false := hclear _ h3mem
        have hopen : OpenNotch B j.val H r := ⟨by omega, by omega, hmod, h3f, hf⟩
        have hreach : Reachable R B H .LG q := by
          rw [← hLG]; exact trajectory_reachable hframe htraj
        exact hReason.2.2.1 B s H hframe j r q hopen h1r hreach ⟨h3mem, hmem⟩
    exact ih (bucketFrame_insert hframe)
      (bucketCell_insert_of_true h4u) (bucketCell_insert_of_true h4d)
      (bucketCell_insert_of_true h3u) (bucketCell_insert_of_true h3d)
      (bucketCell_insert_of_true h1r) (bucketCell_insert_of_not_mem hf hnotmem) hfull

-- Bad State 5: Overhang at (2, r), (3, r), (4, r) with (2, r-1) empty.
private lemma unfillable_of_overhang {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r : ℤ} (hr3 : 3 ≤ r) (hrH : r < H)
    (h2r : bucketCell B j.val 2 r = true) (h3r : bucketCell B j.val 3 r = true)
    (h4r : bucketCell B j.val 4 r = true)
    (h2d : bucketCell B j.val 2 (r - 2) = true) (h1d : bucketCell B j.val 1 (r - 2) = true)
    (h3d : bucketCell B j.val 3 (r - 1) = true) (h0dd : bucketCell B j.val 0 (r - 3) = true)
    (hf : bucketCell B j.val 2 (r - 1) = false)
    (hdisj : bucketCell B j.val 0 (r - 2) = false ∨ bucketCell B j.val 0 r = true ∨
      (bucketCell B j.val 1 r = true ∧ bucketCell B j.val 0 (r - 1) = true)) :
    Unfillable R B j.val H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull (by omega) (by omega) (by omega) (by omega) hf
  | @step B B' q hk hin htraj hrest ih =>
    have hclear := trajectory_clear htraj
    by_cases hm : (6 * (j.val : ℤ) + 2, r - 1) ∈ q.cells
    · have hno2r : (6 * (j.val : ℤ) + 2, r) ∉ q.cells := by
        intro hmem
        have hc := hclear _ hmem; unfold bucketCell at h2r; rw [h2r] at hc; cases hc
      rcases geom_G4 hk hin hclear h2d h1d h3d hm hno2r with
        ⟨hno0d, ⟨h1rmem, h0rmem⟩ | ⟨h0dmem, h0rmem⟩⟩
      · have h0rf : bucketCell B j.val 0 r = false := hclear _ h0rmem
        have h1rf : bucketCell B j.val 1 r = false := hclear _ h1rmem
        have h0df : bucketCell B j.val 0 (r - 2) = false := by
          rcases hdisj with h | h | ⟨h, _⟩
          · exact h
          · rw [h0rf] at h; cases h
          · rw [h1rf] at h; cases h
        exact unfillable_of_closed_row hReason (bucketFrame_insert hframe) j hrH
          (by omega : (0 : ℤ) ≤ 0) (by omega : (0 : ℤ) < 5) (by omega : 0 ≤ r - 2) (by omega)
          (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) hrH h0rmem)
          (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) hrH h1rmem)
          (bucketCell_insert_of_true h2r) (bucketCell_insert_of_true h3r)
          (bucketCell_insert_of_true h4r)
          (bucketCell_insert_of_not_mem h0df hno0d) ⟨B', hrest, hfull⟩
      · have h0rf : bucketCell B j.val 0 r = false := hclear _ h0rmem
        have h0dmf : bucketCell B j.val 0 (r - 1) = false := hclear _ h0dmem
        have h0df : bucketCell B j.val 0 (r - 2) = false := by
          rcases hdisj with h | h | ⟨_, h⟩
          · exact h
          · rw [h0rf] at h; cases h
          · rw [h0dmf] at h; cases h
        have hleft := bucketCell_left_wall (bucketFrame_insert (q := q) hframe) j (y := r - 2) (by omega) (by omega : r - 2 < H)
        exact unfillable_of_surrounded (by omega) (by omega) (by omega) (by omega : r - 2 < H)
          (bucketCell_insert_of_not_mem h0df hno0d)
          (by simpa using bucketCell_insert_of_true h1d)
          (by simpa using hleft)
          (by
            have h' := bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h0dmem
            convert h' using 2; omega)
          (by
            have h' := bucketCell_insert_of_true (q := q) h0dd
            convert h' using 2; omega)
          ⟨B', hrest, hfull⟩
    · have hdisj' : bucketCell (B.insert q) j.val 0 (r - 2) = false ∨
          bucketCell (B.insert q) j.val 0 r = true ∨
          (bucketCell (B.insert q) j.val 1 r = true ∧ bucketCell (B.insert q) j.val 0 (r - 1) = true) := by
        rcases hdisj with h0df | h0rt | ⟨h1rt, h0dm⟩
        · by_cases hm0 : (6 * (j.val : ℤ) + 0, r - 2) ∈ q.cells
          · rcases geom_G5 hk hin hclear h1d h0dd hm0 with h0rmem | ⟨h1rmem, h0dmem⟩
            · right; left
              exact bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) hrH h0rmem
            · right; right
              exact ⟨bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) hrH h1rmem,
                     bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h0dmem⟩
          · left; exact bucketCell_insert_of_not_mem h0df hm0
        · right; left; exact bucketCell_insert_of_true h0rt
        · right; right; exact ⟨bucketCell_insert_of_true h1rt, bucketCell_insert_of_true h0dm⟩
      exact ih (bucketFrame_insert hframe)
        (bucketCell_insert_of_true h2r) (bucketCell_insert_of_true h3r)
        (bucketCell_insert_of_true h4r) (bucketCell_insert_of_true h2d)
        (bucketCell_insert_of_true h1d) (bucketCell_insert_of_true h3d)
        (bucketCell_insert_of_true h0dd) (bucketCell_insert_of_not_mem hf hm) hdisj' hfull

-- Main invariant for Unapproachable.
private lemma unfillable_of_unapproachable_inv {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r : ℤ} (hr3 : 3 ≤ r) (hrH : r + 1 < H) (hmod : (r + 1) % 6 = 5)
    (h4u : bucketCell B j.val 4 (r + 1) = true) (h3u : bucketCell B j.val 3 (r + 1) = true)
    (h4d : bucketCell B j.val 4 (r - 1) = true) (h3d : bucketCell B j.val 3 (r - 1) = true)
    (h2d : bucketCell B j.val 2 (r - 2) = true) (h1d : bucketCell B j.val 1 (r - 2) = true)
    (h0dd : bucketCell B j.val 0 (r - 3) = true)
    (h4f : bucketCell B j.val 4 r = false)
    (h2df : bucketCell B j.val 2 (r - 1) = false)
    (hdisj : bucketCell B j.val 0 (r - 2) = false ∨ bucketCell B j.val 0 r = true) :
    Unfillable R B j.val H := by
  rintro ⟨B', hplay, hfull⟩
  induction hplay with
  | nil B => exact not_bucketFull_of_false hfull (by omega) (by omega) (by omega) (by omega) h4f
  | @step B B' q hk hin htraj hrest ih =>
    cases h1r : bucketCell B j.val 1 r with
    | true =>
      exact unfillable_of_spurned_notch hReason hframe j (by omega) hrH hmod
        h4u h4d h3u h3d h1r h4f ⟨B', .step hk hin htraj hrest, hfull⟩
    | false =>
      have hclear := trajectory_clear htraj
      have h5 := bucketCell_right_wall hframe j (y := r) (by omega) (by omega)
      by_cases hm4 : (6 * (j.val : ℤ) + 4, r) ∈ q.cells
      · rcases geom_G2 hk hclear h4u h4d h5 h3u h3d hm4 with
          ⟨⟨hno2d, hno0d⟩, ⟨_, h1mem, h2mem, h3mem⟩ | ⟨_, h2mem, h3mem⟩⟩
        · exact unfillable_of_balcony hReason (bucketFrame_insert hframe) j (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h1mem)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h2mem)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h3mem)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) hm4)
            (bucketCell_insert_of_true h2d) (bucketCell_insert_of_true h3d)
            (bucketCell_insert_of_not_mem h2df hno2d) ⟨B', hrest, hfull⟩
        · have hdisj' : bucketCell (B.insert q) j.val 0 (r - 2) = false ∨
              bucketCell (B.insert q) j.val 0 r = true ∨
              (bucketCell (B.insert q) j.val 1 r = true ∧ bucketCell (B.insert q) j.val 0 (r - 1) = true) := by
            rcases hdisj with h0df | h0rt
            · left; exact bucketCell_insert_of_not_mem h0df hno0d
            · right; left; exact bucketCell_insert_of_true h0rt
          exact unfillable_of_overhang hReason (bucketFrame_insert hframe) j hr3 (by omega)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h2mem)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h3mem)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) hm4)
            (bucketCell_insert_of_true h2d) (bucketCell_insert_of_true h1d)
            (bucketCell_insert_of_true h3d) (bucketCell_insert_of_true h0dd)
            (bucketCell_insert_of_not_mem h2df hno2d) hdisj' ⟨B', hrest, hfull⟩
      · by_cases hm1 : (6 * (j.val : ℤ) + 1, r) ∈ q.cells
        · exact unfillable_of_spurned_notch hReason (bucketFrame_insert hframe) j (by omega) hrH hmod
            (bucketCell_insert_of_true h4u) (bucketCell_insert_of_true h4d)
            (bucketCell_insert_of_true h3u) (bucketCell_insert_of_true h3d)
            (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) hm1)
            (bucketCell_insert_of_not_mem h4f hm4) ⟨B', hrest, hfull⟩
        · by_cases hm2d : (6 * (j.val : ℤ) + 2, r - 1) ∈ q.cells
          · by_cases hm2r : (6 * (j.val : ℤ) + 2, r) ∈ q.cells
            · exact unfillable_of_blocked_notch (bucketFrame_insert hframe) j (by omega) hrH
                (bucketCell_insert_of_true h4u) (bucketCell_insert_of_true h4d)
                (bucketCell_insert_of_true h3u) (bucketCell_insert_of_true h3d)
                (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) hm2r)
                (bucketCell_insert_of_not_mem h4f hm4) ⟨B', hrest, hfull⟩
            · rcases geom_G4 hk hin hclear h2d h1d h3d hm2d hm2r with
                ⟨hno0d, ⟨h1rmem, _⟩ | ⟨h0dmem, h0rmem⟩⟩
              · exact absurd h1rmem hm1
              · have h0rf : bucketCell B j.val 0 r = false := hclear _ h0rmem
                have h0df : bucketCell B j.val 0 (r - 2) = false := by
                  rcases hdisj with h | h
                  · exact h
                  · rw [h0rf] at h; cases h
                have hleft := bucketCell_left_wall (bucketFrame_insert (q := q) hframe) j (y := r - 2) (by omega) (by omega : r - 2 < H)
                exact unfillable_of_surrounded (by omega) (by omega) (by omega) (by omega : r - 2 < H)
                  (bucketCell_insert_of_not_mem h0df hno0d)
                  (by simpa using bucketCell_insert_of_true h1d)
                  (by simpa using hleft)
                  (by
                    have h' := bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h0dmem
                    convert h' using 2; omega)
                  (by
                    have h' := bucketCell_insert_of_true (q := q) h0dd
                    convert h' using 2; omega)
                  ⟨B', hrest, hfull⟩
          · have hdisj' : bucketCell (B.insert q) j.val 0 (r - 2) = false ∨
                bucketCell (B.insert q) j.val 0 r = true := by
              rcases hdisj with h0df | h0rt
              · by_cases hm0 : (6 * (j.val : ℤ) + 0, r - 2) ∈ q.cells
                · rcases geom_G5 hk hin hclear h1d h0dd hm0 with h0rmem | ⟨h1rmem, _⟩
                  · right
                    exact bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) h0rmem
                  · exact absurd h1rmem hm1
                · left; exact bucketCell_insert_of_not_mem h0df hm0
              · right; exact bucketCell_insert_of_true h0rt
            exact ih (bucketFrame_insert hframe)
              (bucketCell_insert_of_true h4u) (bucketCell_insert_of_true h3u)
              (bucketCell_insert_of_true h4d) (bucketCell_insert_of_true h3d)
              (bucketCell_insert_of_true h2d) (bucketCell_insert_of_true h1d)
              (bucketCell_insert_of_true h0dd)
              (bucketCell_insert_of_not_mem h4f hm4)
              (bucketCell_insert_of_not_mem h2df hm2d) hdisj' hfull

end TetrisHard.Rows.Lemma58

open TetrisHard.Rows in
theorem solution
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (B : Board) (s H : ℕ) (hframe : BucketFrame B s H) (j : Fin s)
    (hshape : Unapproachable B j.val H) :
    Unfillable R B j.val H := by
  let _ := hR
  rcases hshape with ⟨n, hn3, hnH, hnmod, hpat⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  have hn5 : 5 ≤ n := by omega
  have hnH5 : n + 5 ≤ H := by omega
  have hHB : H + 3 ≤ B.height := hframe.2.2.1
  let r : ℤ := (n : ℤ) - 1
  have hr3 : 3 ≤ r := by omega
  have hrH : r + 1 < H := by omega
  have hrmod : (r + 1) % 6 = 5 := by omega
  have eval_pat : ∀ (x y : ℕ) (hx : x < 6) (hy : y < B.height),
      bucketCell B j.val (x : ℤ) (y : ℤ) =
        ((decide (y < H ∧ (x = 5 ∨ (3 ≤ x ∧ (y + 1) % 6 ≠ 5)))) ||
          decide (x < 5 ∧ (if x = 0 then y + 3 < n else y + 2 < n))) :=
    fun x y hx hy => hpat ⟨x, hx⟩ ⟨y, hy⟩
  have h4u : bucketCell B j.val 4 (r + 1) = true := by
    have h := eval_pat 4 n (by omega) (by omega)
    have hr1 : r + 1 = (n : ℤ) := by omega
    rw [hr1]; simpa [show n < H by omega, show (n + 1) % 6 ≠ 5 by omega] using h
  have h3u : bucketCell B j.val 3 (r + 1) = true := by
    have h := eval_pat 3 n (by omega) (by omega)
    have hr1 : r + 1 = (n : ℤ) := by omega
    rw [hr1]; simpa [show n < H by omega, show (n + 1) % 6 ≠ 5 by omega] using h
  have h4d : bucketCell B j.val 4 (r - 1) = true := by
    have h := eval_pat 4 (n - 2) (by omega) (by omega)
    have hr1 : r - 1 = ((n - 2 : ℕ) : ℤ) := by omega
    rw [hr1]; simpa [show n - 2 < H by omega, show (n - 2 + 1) % 6 ≠ 5 by omega] using h
  have h3d : bucketCell B j.val 3 (r - 1) = true := by
    have h := eval_pat 3 (n - 2) (by omega) (by omega)
    have hr1 : r - 1 = ((n - 2 : ℕ) : ℤ) := by omega
    rw [hr1]; simpa [show n - 2 < H by omega, show (n - 2 + 1) % 6 ≠ 5 by omega] using h
  have h2d : bucketCell B j.val 2 (r - 2) = true := by
    have h := eval_pat 2 (n - 3) (by omega) (by omega)
    have hr1 : r - 2 = ((n - 3 : ℕ) : ℤ) := by omega
    rw [hr1]; simpa [show n - 3 + 2 < n by omega] using h
  have h1d : bucketCell B j.val 1 (r - 2) = true := by
    have h := eval_pat 1 (n - 3) (by omega) (by omega)
    have hr1 : r - 2 = ((n - 3 : ℕ) : ℤ) := by omega
    rw [hr1]; simpa [show n - 3 + 2 < n by omega] using h
  have h0dd : bucketCell B j.val 0 (r - 3) = true := by
    have h := eval_pat 0 (n - 4) (by omega) (by omega)
    have hr1 : r - 3 = ((n - 4 : ℕ) : ℤ) := by omega
    rw [hr1]; simpa [show n - 4 + 3 < n by omega] using h
  have h4f : bucketCell B j.val 4 r = false := by
    have h := eval_pat 4 (n - 1) (by omega) (by omega)
    have hr1 : r = ((n - 1 : ℕ) : ℤ) := by omega
    rw [hr1]
    have hmod1 : (n - 1 + 1) % 6 = 5 := by omega
    have hlt1 : ¬ (n - 1 + 2 < n) := by omega
    simpa [hmod1, hlt1] using h
  have h2df : bucketCell B j.val 2 (r - 1) = false := by
    have h := eval_pat 2 (n - 2) (by omega) (by omega)
    have hr1 : r - 1 = ((n - 2 : ℕ) : ℤ) := by omega
    rw [hr1]
    have hlt1 : ¬ (n - 2 + 2 < n) := by omega
    simpa [hlt1] using h
  have h0df : bucketCell B j.val 0 (r - 2) = false := by
    have h := eval_pat 0 (n - 3) (by omega) (by omega)
    have hr1 : r - 2 = ((n - 3 : ℕ) : ℤ) := by omega
    rw [hr1]
    have hlt1 : ¬ (n - 3 + 3 < n) := by omega
    simpa [hlt1] using h
  exact Lemma58.unfillable_of_unapproachable_inv hReason hframe j hr3 hrH hrmod
    h4u h3u h4d h3d h2d h1d h0dd h4f h2df (Or.inl h0df)

