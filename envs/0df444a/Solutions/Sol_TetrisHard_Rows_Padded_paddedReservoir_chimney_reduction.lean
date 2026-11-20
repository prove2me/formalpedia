-- Prove2me | solution 1 for TetrisHard.Rows.Padded.paddedReservoir_chimney_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:29:53.586298+00:00
-- url     : https://prove2.me/submissions/ed27c4f3-cff9-49f9-8b99-33c016a41803

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetrisHard.Rows

inductive AnyPlayNoRG (R : Rotation) : Board → Board → Prop
  | nil (B) : AnyPlayNoRG R B B
  | step {B B' q} : q.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece) →
      Trajectory R B q.kind q → AnyPlayNoRG R (B.insert q) B' → AnyPlayNoRG R B B'

/-! ### Basic Board & Connectivity Helpers -/

lemma occupied_insert_of_occupied {B : Board} {q : PieceState} {z : Cell}
    (h : B.occupied z = true) : (B.insert q).occupied z = true := by
  unfold Board.occupied at h ⊢
  unfold Board.insert
  dsimp only at *
  split_ifs at h ⊢
  · simp [h]
  · rfl
  · rfl

lemma occupied_insert_of_not_mem {B : Board} {q : PieceState} {z : Cell}
    (h : B.occupied z = false) (hz : z ∉ q.cells) : (B.insert q).occupied z = false := by
  unfold Board.occupied at h ⊢
  unfold Board.insert
  dsimp only at *
  split_ifs at h ⊢ with hy hx
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨h, ?_⟩
  have h1 : ((z.1.toNat : ℤ), (z.2.toNat : ℤ)) = z := by ext <;> simp [hx.1, hy.1]
  rw [h1]
  exact hz

lemma occupied_insert_of_mem {B : Board} {q : PieceState} {z : Cell}
    (hy0 : 0 ≤ z.2) (hy1 : z.2 < B.height) (hx0 : 0 ≤ z.1) (hx1 : z.1 < B.width)
    (hz : z ∈ q.cells) : (B.insert q).occupied z = true := by
  unfold Board.occupied Board.insert
  dsimp only
  rw [dif_pos ⟨hy0, hy1⟩, dif_pos ⟨hx0, hx1⟩]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  right
  have h1 : ((z.1.toNat : ℤ), (z.2.toNat : ℤ)) = z := by ext <;> simp [hx0, hy0]
  rw [h1]
  exact hz

lemma bucketCell_insert_of_true {B : Board} {q : PieceState} {j : ℕ} {x y : ℤ}
    (h : bucketCell B j x y = true) : bucketCell (B.insert q) j x y = true :=
  occupied_insert_of_occupied h

lemma bucketCell_insert_of_not_mem {B : Board} {q : PieceState} {j : ℕ} {x y : ℤ}
    (h : bucketCell B j x y = false) (hz : (6 * (j : ℤ) + x, y) ∉ q.cells) :
    bucketCell (B.insert q) j x y = false :=
  occupied_insert_of_not_mem h hz

lemma bucketCell_insert_of_mem {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    {j : Fin s} {q : PieceState} {x y : ℤ}
    (hx0 : 0 ≤ x) (hx1 : x < 6) (hy0 : 0 ≤ y) (hy1 : y < H)
    (hz : (6 * (j.val : ℤ) + x, y) ∈ q.cells) :
    bucketCell (B.insert q) j.val x y = true := by
  apply occupied_insert_of_mem hy0 _ _ _ hz
  · have := hframe.2.2.1; omega
  · omega
  · have := hframe.1; have := j.isLt; omega

lemma bucketFrame_insert {B : Board} {s H : ℕ} {q : PieceState}
    (hframe : BucketFrame B s H) : BucketFrame (B.insert q) s H := by
  rcases hframe with ⟨hw, hH, hh, hcells⟩
  refine ⟨hw, hH, hh, fun j y hy => ?_⟩
  rcases hcells j y hy with ⟨h5, h34⟩
  refine ⟨occupied_insert_of_occupied h5, fun hmod => ?_⟩
  rcases h34 hmod with ⟨h3, h4⟩
  exact ⟨occupied_insert_of_occupied h3, occupied_insert_of_occupied h4⟩

lemma bucketCell_left_wall_B {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {y : ℤ} (hy0 : 0 ≤ y) (hy1 : y < H) :
    bucketCell B j.val (-1) y = true := by
  unfold bucketCell
  by_cases hj : j.val = 0
  · rw [hj]; unfold Board.occupied
    have hneg : ¬ (0 ≤ (6 * ((0 : ℕ) : ℤ) + -1) ∧ (6 * ((0 : ℕ) : ℤ) + -1) < B.width) := by omega
    split_ifs <;> rfl
  · let j' : Fin s := ⟨j.val - 1, by omega⟩
    have h := (hframe.2.2.2 j' y.toNat (by omega)).1
    have heq : (6 * (j'.val : ℤ) + 5, (y.toNat : ℤ)) = (6 * (j.val : ℤ) + -1, y) := by
      ext
      · simp [j']; omega
      · exact Int.toNat_of_nonneg hy0
    rwa [← heq]

lemma bucketCell_right_wall_B {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {y : ℤ} (hy0 : 0 ≤ y) (hy1 : y < H) :
    bucketCell B j.val 5 y = true := by
  unfold bucketCell
  have h := (hframe.2.2.2 j y.toNat (by omega)).1
  have heq : (6 * (j.val : ℤ) + 5, (y.toNat : ℤ)) = (6 * (j.val : ℤ) + 5, y) := by
    ext
    · rfl
    · exact Int.toNat_of_nonneg hy0
  rwa [← heq]

lemma cells_nonempty_B (q : PieceState) : ∃ z, z ∈ q.cells := by
  cases h : q.kind <;> simp [PieceState.cells, h, Piece.base]

lemma i_cells_cases {q : PieceState} (hk : q.kind = .I) :
    (∃ x₀ y₀ : ℤ, q.cells.toFinset = {(x₀, y₀), (x₀ + 1, y₀), (x₀ + 2, y₀), (x₀ + 3, y₀)}) ∨
    (∃ x₀ y₀ : ℤ, q.cells.toFinset = {(x₀, y₀), (x₀, y₀ + 1), (x₀, y₀ + 2), (x₀, y₀ + 3)}) := by
  cases q with
  | mk k o pos f =>
    dsimp only at hk; subst hk
    cases pos with
    | mk px py =>
      fin_cases o
      · left; refine ⟨px - 1, py, ?_⟩
        ext c; simp [PieceState.cells, Piece.base]; constructor <;> rintro (rfl | rfl | rfl | rfl) <;>
          first | left; ext <;> omega | right; left; ext <;> omega |
                  right; right; left; ext <;> omega | right; right; right; ext <;> omega
      · right; refine ⟨px, py - 2, ?_⟩
        ext c; simp [PieceState.cells, Piece.base, clockwise]; constructor <;>
          rintro (rfl | rfl | rfl | rfl) <;>
          first | left; ext <;> omega | right; left; ext <;> omega |
                  right; right; left; ext <;> omega | right; right; right; ext <;> omega
      · left; refine ⟨px - 2, py, ?_⟩
        ext c; simp [PieceState.cells, Piece.base, clockwise]; constructor <;>
          rintro (rfl | rfl | rfl | rfl) <;>
          first | left; ext <;> omega | right; left; ext <;> omega |
                  right; right; left; ext <;> omega | right; right; right; ext <;> omega
      · right; refine ⟨px, py - 1, ?_⟩
        ext c; simp [PieceState.cells, Piece.base, clockwise]; constructor <;>
          rintro (rfl | rfl | rfl | rfl) <;>
          first | left; ext <;> omega | right; left; ext <;> omega |
                  right; right; left; ext <;> omega | right; right; right; ext <;> omega

/-! ### Balcony Persistence Helper -/

end TetrisHard.Rows

namespace TetrisHard.Rows.Padded
open TetrisHard.Rows

lemma apply_dy_le (R : Rotation) (B : Board) (q : PieceState) (cw : Bool) :
    ((R.apply B q cw).position.2 - q.position.2).natAbs ≤ maxJump R := by
  classical
  unfold Rotation.apply maxJump
  set patch : Fin (2 * R.radius + 1) → Fin (2 * R.radius + 1) → Bool :=
    fun y x => B.occupied
      (q.position.1 + (x.val : ℤ) - R.radius, q.position.2 + (y.val : ℤ) - R.radius)
  have hmem : (q.kind, q.orientation, q.fixed, cw, patch) ∈ Finset.univ := Finset.mem_univ _
  have hsup := Finset.le_sup (f := fun (x : Piece × Fin 4 × Bool × Bool ×
      (Fin (2 * R.radius + 1) → Fin (2 * R.radius + 1) → Bool)) =>
    match R.rule x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 with
    | none => 0
    | some d => d.2.natAbs) hmem
  cases h : R.rule q.kind q.orientation q.fixed cw patch with
  | none =>
    simp [h]
  | some d =>
    simp only [h] at hsup ⊢
    have heq : q.position.2 + d.2 - q.position.2 = d.2 := by ring
    rw [heq]
    exact hsup

lemma move_dy_le (R : Rotation) (B : Board) (q q' : PieceState) (h : Move R B q q') :
    (q'.position.2 - q.position.2).natAbs ≤ maxJump R + 1 := by
  rcases h with ⟨_, _, _, hstep⟩
  rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩
  · exact le_trans (apply_dy_le R B q d) (Nat.le_succ _)
  · simp [translate]
  · simp [translate]
  · simp [translate]
  · simp


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

/-! ### Square Parity + Chimney Barrier Theorem -/

/-- Number of rows at index `≥ cut` with an odd number of occupied cells. -/
def oddRowsAbove (cut : ℕ) (B : Board) : ℕ :=
  ((Finset.univ : Finset (Fin B.height)).filter fun y =>
    cut ≤ y.val ∧ Odd ((Finset.univ : Finset (Fin B.width)).filter fun x => B.cell y x = true).card).card

/-- Chimney barrier invariant: odd width, `cut = r + h` with `h > maxJump R + 2`,
every row `< cut` has a false cell (so cannot be cleared), and every row in `[r, cut)`
has at most one false cell (so no `.Sq` piece can touch it). -/
def ChimneyInvariant (B : Board) (r cut : ℕ) : Prop :=
  Odd B.width ∧
  r ≤ cut ∧
  cut + 2 ≤ B.height ∧
  (∀ y : Fin B.height, y.val < cut → ∃ x : Fin B.width, B.cell y x = false) ∧
  (∀ y : Fin B.height, r ≤ y.val → y.val < cut →
    ∀ x1 x2 : Fin B.width, B.cell y x1 = false → B.cell y x2 = false → x1 = x2)

lemma sq_clear_not_in_chimney {B : Board} {r cut : ℕ}
    (hinv : ChimneyInvariant B r cut) {q : PieceState}
    (hk : q.kind = .Sq) (hclear : B.Clear q) :
    (q.position.2 < r ∨ (cut : ℤ) ≤ q.position.2) ∧
    (q.position.2 - 1 < r ∨ (cut : ℤ) ≤ q.position.2 - 1) := by
  have hcells : q.cells = [(q.position.1, q.position.2), (q.position.1 + 1, q.position.2),
      (q.position.1, q.position.2 - 1), (q.position.1 + 1, q.position.2 - 1)] := by
    simp [PieceState.cells, hk, Piece.base, sub_eq_add_neg]
  have h0 : B.occupied (q.position.1, q.position.2) = false := hclear _ (by simp [hcells])
  have h1 : B.occupied (q.position.1 + 1, q.position.2) = false := hclear _ (by simp [hcells])
  have h2 : B.occupied (q.position.1, q.position.2 - 1) = false := hclear _ (by simp [hcells])
  have h3 : B.occupied (q.position.1 + 1, q.position.2 - 1) = false := hclear _ (by simp [hcells])
  have not_in : ∀ (x y : ℤ), B.occupied (x, y) = false → B.occupied (x + 1, y) = false →
      y < r ∨ (cut : ℤ) ≤ y := by
    intro x y ha hb
    by_contra h
    push Not at h
    rcases h with ⟨hry, hyc⟩
    have hy0 : 0 ≤ y := by omega
    have hyH : y < B.height := by have := hinv.2.2.1; omega
    simp only [Board.occupied, hy0, hyH, and_self, ↓reduceDIte] at ha hb
    split_ifs at ha with hxa
    · split_ifs at hb with hxb
      · have hyt1 : r ≤ y.toNat := by omega
        have hyt2 : y.toNat < cut := by omega
        have heq := hinv.2.2.2.2 ⟨y.toNat, by omega⟩ hyt1 hyt2
          ⟨x.toNat, by omega⟩ ⟨(x + 1).toNat, by omega⟩ ha hb
        have : x.toNat = (x + 1).toNat := congrArg Fin.val heq
        omega
  exact ⟨not_in q.position.1 q.position.2 h0 h1,
    not_in q.position.1 (q.position.2 - 1) h2 h3⟩

lemma sq_trajectory_above_cut {R : Rotation} {B : Board} {r cut : ℕ}
    (hinv : ChimneyInvariant B r cut) (hgap : maxJump R + 2 < cut - r)
    {q : PieceState} (htraj : Trajectory R B .Sq q) :
    q.kind = .Sq ∧ (cut : ℤ) + 1 ≤ q.position.2 ∧ ∀ z ∈ q.cells, (cut : ℤ) ≤ z.2 := by
  obtain ⟨hclear0, hreach, _⟩ := htraj
  have hkind_inv : ∀ q1 q2, Move R B q1 q2 → q1.kind = .Sq → q2.kind = .Sq := by
    intro q1 q2 hm hk
    rcases hm with ⟨_, _, _, ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩⟩
    · simp only [Rotation.apply]
      split <;> exact hk
    · exact hk
    · exact hk
    · exact hk
    · exact hk
  have hreach_prop : ∀ q', Relation.ReflTransGen (Move R B) (spawn B .Sq) q' →
      q'.kind = .Sq ∧ (cut : ℤ) + 1 ≤ q'.position.2 := by
    intro q' hr
    induction hr with
    | refl =>
      refine ⟨rfl, ?_⟩
      have hH := hinv.2.2.1
      simp only [spawn, Piece.base, List.map, List.foldl]
      omega
    | tail _ hstep ih =>
      rename_i q1 q2 _
      have hk2 : q2.kind = .Sq := hkind_inv q1 q2 hstep ih.1
      have hcl2 : B.Clear q2 := hstep.2.2.1
      have hdy := move_dy_le R B q1 q2 hstep
      have hnot := sq_clear_not_in_chimney hinv hk2 hcl2
      have hge1 : (r : ℤ) ≤ q2.position.2 := by
        have := hinv.2.1
        omega
      have hge2 : (cut : ℤ) ≤ q2.position.2 := by omega
      have hge3 : (cut : ℤ) ≤ q2.position.2 - 1 := by
        have := hinv.2.1
        omega
      exact ⟨hk2, by omega⟩
  obtain ⟨hk, hpos⟩ := hreach_prop q hreach
  refine ⟨hk, hpos, ?_⟩
  intro z hz
  simp only [PieceState.cells, hk, Piece.base, List.map, List.mem_cons, List.not_mem_nil,
    or_false, ↓reduceIte] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> omega

/-- Number of rows at index `≥ cut` with an odd number of `true` cells. -/
def oddRowsAboveL (cut : ℕ) (B : Board) : ℕ :=
  ((B.rows.drop cut).filter fun row => (row.count true) % 2 == 1).length

lemma row_all_id_iff (B : Board) (y : Fin B.height) :
    (List.ofFn fun x : Fin B.width => B.cell y x).all id = true ↔
      ∀ x : Fin B.width, B.cell y x = true := by
  simp [List.all_eq_true, List.mem_ofFn]

lemma row_all_id_count {row : List Bool} (h : row.all id = true) :
    row.count true = row.length := by
  induction row with
  | nil => simp
  | cons b l ih =>
    simp only [List.all_cons, id_eq, Bool.and_eq_true] at h
    simp [h.1, ih h.2]

lemma list_filter_odd_split (L : List (List Bool)) (w : ℕ) (hw : Odd w)
    (hlen : ∀ r ∈ L, r.length = w) :
    (L.filter fun r => (r.count true) % 2 == 1).length =
      ((L.filter fun r => !(r.all id)).filter fun r => (r.count true) % 2 == 1).length +
      (L.filter fun r => r.all id).length := by
  induction L with
  | nil => simp
  | cons r l ih =>
    have ihr := ih (fun r' hr' => hlen r' (List.mem_cons_of_mem _ hr'))
    have hrl : r.length = w := hlen r (List.mem_cons_self ..)
    cases hall : r.all id
    · simp only [List.filter_cons, hall, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      by_cases hodd : (r.count true % 2 == 1) = true
      · simp [hodd, ihr]; omega
      · simp [hodd, ihr]
    · have hcnt : r.count true = w := by rw [row_all_id_count hall, hrl]
      have hodd : (r.count true % 2 == 1) = true := by
        rw [hcnt]; rcases hw with ⟨k, rfl⟩; simp
      simp [hall, hodd, ihr]; omega

lemma sq_insert_count_parity (B : Board) (q : PieceState) (hk : q.kind = .Sq)
    (hclear : B.Clear q) (y : Fin B.height) :
    ((List.ofFn fun x : Fin B.width => (B.insert q).cell y x).count true) % 2 =
      ((List.ofFn fun x : Fin B.width => B.cell y x).count true) % 2 := by
  have hcells : q.cells = [(q.position.1, q.position.2), (q.position.1 + 1, q.position.2),
      (q.position.1, q.position.2 - 1), (q.position.1 + 1, q.position.2 - 1)] := by
    simp [PieceState.cells, hk, Piece.base, sub_eq_add_neg]
  by_cases hy : (y.val : ℤ) = q.position.2 ∨ (y.val : ℤ) = q.position.2 - 1
  · -- Row y contains exactly two cells of q: (x0, y) and (x0 + 1, y), both false in B
    have h0 : B.occupied (q.position.1, y.val) = false := by
      rcases hy with hy | hy <;> rw [hy]
      · exact hclear _ (by simp [hcells])
      · exact hclear _ (by simp [hcells])
    have h1 : B.occupied (q.position.1 + 1, y.val) = false := by
      rcases hy with hy | hy <;> rw [hy]
      · exact hclear _ (by simp [hcells])
      · exact hclear _ (by simp [hcells])
    have hy0 : (0 : ℤ) ≤ y.val := Int.natCast_nonneg _
    have hyH : (y.val : ℤ) < B.height := Int.ofNat_lt.mpr y.isLt
    simp only [Board.occupied, hy0, hyH, and_self, ↓reduceDIte] at h0 h1
    split_ifs at h0 with hx0
    split_ifs at h1 with hx1
    set x0 : Fin B.width := ⟨q.position.1.toNat, by omega⟩
    set x1 : Fin B.width := ⟨(q.position.1 + 1).toNat, by omega⟩
    have hne : x0 ≠ x1 := by intro h; have := congrArg Fin.val h; simp [x0, x1] at this; omega
    have hcell_eq : ∀ x : Fin B.width,
        (B.insert q).cell y x = (B.cell y x || decide (x = x0 ∨ x = x1)) := by
      intro x
      simp only [Board.insert, hcells, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · left; ext; simp [x0]; omega
        · right; ext; simp [x1]; omega
        · left; ext; simp [x0]; omega
        · right; ext; simp [x1]; omega
      · rintro (rfl | rfl)
        · rcases hy with hy | hy
          · left; exact ⟨by simp [x0]; omega, hy⟩
          · right; right; left; exact ⟨by simp [x0]; omega, hy⟩
        · rcases hy with hy | hy
          · right; left; exact ⟨by simp [x1]; omega, hy⟩
          · right; right; right; exact ⟨by simp [x1]; omega, hy⟩
    have hcnt_fin : ∀ f : Fin B.width → Bool,
        (List.ofFn f).count true = (Finset.univ.filter fun x => f x = true).card := by
      intro f
      rw [List.count_eq_countP]
      have : (List.ofFn f).countP (· == true) =
          (List.finRange B.width).countP (fun x => f x == true) := by
        rw [List.ofFn_eq_map, List.countP_map]; rfl
      rw [this, List.countP_eq_length_filter]
      have hnodup : ((List.finRange B.width).filter fun x => f x == true).Nodup :=
        (List.nodup_finRange _).filter _
      rw [← List.toFinset_card_of_nodup hnodup]
      congr 1; ext x; simp
    let f1 : Fin B.width → Bool := fun x => (B.insert q).cell y x
    let f0 : Fin B.width → Bool := fun x => B.cell y x
    change (List.ofFn f1).count true % 2 = (List.ofFn f0).count true % 2
    rw [hcnt_fin f1, hcnt_fin f0]
    have hset : (Finset.univ.filter fun x : Fin B.width => f1 x = true) =
        insert x0 (insert x1 (Finset.univ.filter fun x : Fin B.width => f0 x = true)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, f1, f0, hcell_eq,
        Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hx0_not : x0 ∉ Finset.univ.filter (fun x : Fin B.width => f0 x = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f0, Bool.not_eq_true]
      have hy_eq : (⟨(y.val : ℤ).toNat, by omega⟩ : Fin B.height) = y := by ext; simp
      rw [← hy_eq]; exact h0
    have hx1_not : x1 ∉ Finset.univ.filter (fun x : Fin B.width => f0 x = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f0, Bool.not_eq_true]
      have hy_eq : (⟨(y.val : ℤ).toNat, by omega⟩ : Fin B.height) = y := by ext; simp
      rw [← hy_eq]; exact h1
    rw [hset, Finset.card_insert_of_notMem (by simp [hne, hx0_not]),
      Finset.card_insert_of_notMem hx1_not]
    omega
  · -- Row y contains NO cell of q
    have hsame : ∀ x : Fin B.width, (B.insert q).cell y x = B.cell y x := by
      intro x
      simp only [Board.insert, hcells, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      have : ¬ ((x.val : ℤ) = q.position.1 ∧ (y.val : ℤ) = q.position.2 ∨
          (x.val : ℤ) = q.position.1 + 1 ∧ (y.val : ℤ) = q.position.2 ∨
          (x.val : ℤ) = q.position.1 ∧ (y.val : ℤ) = q.position.2 - 1 ∨
          (x.val : ℤ) = q.position.1 + 1 ∧ (y.val : ℤ) = q.position.2 - 1) := by
        push Not at hy
        rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> omega
      simp [this]
    simp [hsame]

lemma sq_step_invariant {R : Rotation} {B : Board} {r cut : ℕ}
    (hinv : ChimneyInvariant B r cut) (hgap : maxJump R + 2 < cut - r)
    {q : PieceState} (htraj : Trajectory R B .Sq q) :
    ChimneyInvariant (B.settle q) r cut ∧
    oddRowsAboveL cut (B.settle q) + B.gain q = oddRowsAboveL cut B := by
  obtain ⟨hk, hpos, hcells_ge⟩ := sq_trajectory_above_cut hinv hgap htraj
  have hclear : B.Clear q := by
    have hreach := htraj.2.1
    cases hreach with
    | refl => exact htraj.1
    | tail _ hstep => exact hstep.2.2.1
  set B1 := B.insert q
  have hB1_below : ∀ y : Fin B.height, y.val < cut → ∀ x : Fin B.width, B1.cell y x = B.cell y x := by
    intro y hy x
    simp only [B1, Board.insert]
    have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by
      intro hmem
      have := hcells_ge _ hmem
      omega
    simp [hnot]
  have hB1_rows_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
  have hcut_le : cut ≤ B.height := by have := hinv.2.2.1; omega
  have htake_not_full : ∀ row ∈ B1.rows.take cut, row.all id = false := by
    intro row hmem
    rw [List.mem_iff_getElem] at hmem
    rcases hmem with ⟨i, hi, rfl⟩
    simp only [List.length_take, hB1_rows_len] at hi
    have hi_cut : i < cut := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hi_H : i < B.height := lt_of_lt_of_le hi (Nat.min_le_right _ _)
    rw [List.getElem_take]
    simp only [Board.rows, List.getElem_ofFn]
    obtain ⟨x, hx⟩ := hinv.2.2.2.1 ⟨i, hi_H⟩ hi_cut
    rw [Bool.eq_false_iff]
    intro hall
    have h1 := (row_all_id_iff B1 ⟨i, hi_H⟩).mp hall x
    have h2 : B1.cell ⟨i, hi_H⟩ x = B.cell ⟨i, hi_H⟩ x := hB1_below ⟨i, hi_H⟩ hi_cut x
    rw [h2, hx] at h1
    simp at h1
  have hrows_split : B1.rows = B1.rows.take cut ++ B1.rows.drop cut := (List.take_append_drop cut B1.rows).symm
  have htake_filter_false : (B1.rows.take cut).filter (fun row => row.all id) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row hmem
    simp [htake_not_full row hmem]
  have htake_filter_true : (B1.rows.take cut).filter (fun row => !(row.all id)) = B1.rows.take cut := by
    rw [List.filter_eq_self]
    intro row hmem
    simp [htake_not_full row hmem]
  have hgain_eq : B.gain q = ((B1.rows.drop cut).filter fun row => row.all id).length := by
    unfold Board.gain Board.fullCount
    change (B1.rows.filter fun row => row.all id).length = _
    conv_lhs => rw [hrows_split]
    rw [List.filter_append, htake_filter_false, List.nil_append]
  set surv := B1.rows.filter fun row => !(row.all id)
  have hsurv_eq : surv = B1.rows.take cut ++ (B1.rows.drop cut).filter fun row => !(row.all id) := by
    change B1.rows.filter (fun row => !(row.all id)) = _
    conv_lhs => rw [hrows_split]
    rw [List.filter_append, htake_filter_true]
  have htake_len : (B1.rows.take cut).length = cut := by simp [hB1_rows_len, hcut_le]
  have hsettle_below : ∀ y : Fin (B.settle q).height, y.val < cut →
      ∀ x : Fin (B.settle q).width, (B.settle q).cell y x = B.cell ⟨y.val, y.isLt⟩ ⟨x.val, x.isLt⟩ := by
    intro y hy x
    change (surv.getD y.val []).getD x.val false = _
    rw [hsurv_eq]
    have hy1 : y.val < (B1.rows.take cut).length := by omega
    have hget1 : (B1.rows.take cut ++ (B1.rows.drop cut).filter fun row => !(row.all id)).getD y.val [] =
        (B1.rows.take cut)[y.val] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hy1,
        List.getElem?_eq_getElem hy1, Option.getD_some]
    rw [hget1, List.getElem_take]
    have hx1 : x.val < B1.width := x.isLt
    simp only [Board.rows, List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx1,
      ↓reduceDIte, Option.getD_some]
    exact hB1_below ⟨y.val, y.isLt⟩ hy ⟨x.val, x.isLt⟩
  have hinv' : ChimneyInvariant (B.settle q) r cut := by
    refine ⟨hinv.1, hinv.2.1, hinv.2.2.1, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx⟩ := hinv.2.2.2.1 ⟨y.val, y.isLt⟩ hy
      exact ⟨⟨x.val, x.isLt⟩, by rw [hsettle_below y hy]; exact hx⟩
    · intro y hry hyc x1 x2 h1 h2
      rw [hsettle_below y hyc] at h1 h2
      have heq := hinv.2.2.2.2 ⟨y.val, y.isLt⟩ hry hyc ⟨x1.val, x1.isLt⟩ ⟨x2.val, x2.isLt⟩ h1 h2
      ext; exact congrArg Fin.val heq
  refine ⟨hinv', ?_⟩
  -- Compare oddRowsAboveL cut (B.settle q) with oddRowsAboveL cut B1 = oddRowsAboveL cut B
  have hB1_odd : oddRowsAboveL cut B1 = oddRowsAboveL cut B := by
    unfold oddRowsAboveL
    have hmap : ∀ (M : Board), (M.rows.drop cut).map (fun row => (row.count true) % 2 == 1) =
        (List.finRange M.height |>.drop cut).map fun y =>
          ((List.ofFn fun x : Fin M.width => M.cell y x).count true) % 2 == 1 := by
      intro M
      simp only [Board.rows, List.ofFn_eq_map, ← List.map_drop, List.map_map]
      rfl
    have hlen_filter : ∀ (L : List (List Bool)) (p : List Bool → Bool),
        (L.filter p).length = (L.map p).count true := by
      intro L p
      induction L with
      | nil => simp
      | cons a l ih =>
        cases h : p a <;> simp [h, ih]
    rw [hlen_filter, hlen_filter, hmap B1, hmap B]
    congr 1
    apply List.map_congr_left
    intro y _
    exact congrArg (· == 1) (sq_insert_count_parity B q hk hclear y)
  rw [← hB1_odd, hgain_eq]
  -- Now relate oddRowsAboveL cut (B.settle q) to ((B1.rows.drop cut).filter (fun r => !(r.all id)))
  set S := (B1.rows.drop cut).filter fun row => !(row.all id)
  have hS_len : S.length ≤ B.height - cut := by
    calc S.length ≤ (B1.rows.drop cut).length := List.length_filter_le _ _
      _ = B.height - cut := by simp [hB1_rows_len]
  have hsettle_rows_len : (B.settle q).rows.length = B.height := by
    simp [Board.rows, Board.settle, Board.compress, Board.insert]
  have hsettle_rows_drop : (B.settle q).rows.drop cut =
      S ++ List.replicate ((B.height - cut) - S.length) (List.replicate B.width false) := by
    apply List.ext_getElem
    · simp only [List.length_drop, hsettle_rows_len, List.length_append, List.length_replicate]
      omega
    · intro i hi1 hi2
      simp only [List.length_drop, hsettle_rows_len] at hi1
      have hcuti : cut + i < B.height := by omega
      rw [List.getElem_drop]
      have hlhs : (B.settle q).rows[cut + i] =
          List.ofFn (fun x : Fin (B.settle q).width => (B.settle q).cell ⟨cut + i, hcuti⟩ x) := by
        simp [Board.rows]
      rw [hlhs]
      by_cases hiS : i < S.length
      · rw [List.getElem_append_left hiS]
        have hSlen : S[i].length = B.width := by
          have hmem : S[i] ∈ B1.rows.drop cut := (List.mem_filter.mp (List.getElem_mem hiS)).1
          have hmem' := List.mem_of_mem_drop hmem
          simp only [Board.rows, List.mem_ofFn] at hmem'
          rcases hmem' with ⟨y, hy⟩
          rw [← hy]; simp; rfl
        apply List.ext_getElem
        · simp [hSlen]; rfl
        · intro j hj1 hj2
          simp only [List.getElem_ofFn]
          change (surv.getD (cut + i) []).getD j false = S[i][j]
          have hget : surv.getD (cut + i) [] = S[i] := by
            rw [hsurv_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              htake_len, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hiS, Option.getD_some]
          rw [hget, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]
      · rw [List.getElem_append_right (Nat.not_lt.mp hiS), List.getElem_replicate]
        apply List.ext_getElem
        · simp; rfl
        · intro j hj1 hj2
          simp only [List.getElem_ofFn, List.getElem_replicate]
          change (surv.getD (cut + i) []).getD j false = false
          have hget : surv.getD (cut + i) [] = [] := by
            rw [hsurv_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              htake_len, Nat.add_sub_cancel_left, List.getElem?_eq_none (Nat.not_lt.mp hiS),
              Option.getD_none]
          rw [hget]; simp
  have hrep_filter : ∀ k, (List.replicate k (List.replicate B.width false) |>.filter
      fun row => (row.count true) % 2 == 1) = [] := by
    intro k
    rw [List.filter_eq_nil_iff]
    intro row hmem
    rw [List.mem_replicate] at hmem
    rcases hmem with ⟨_, rfl⟩
    simp [List.count_replicate]
  unfold oddRowsAboveL
  rw [hsettle_rows_drop, List.filter_append, hrep_filter, List.append_nil]
  have hsplit := list_filter_odd_split (B1.rows.drop cut) B.width hinv.1 (by
    intro row hmem
    have hmem' := List.mem_of_mem_drop hmem
    simp only [Board.rows, List.mem_ofFn] at hmem'
    rcases hmem' with ⟨y, hy⟩
    rw [← hy]; simp; rfl)
  change (S.filter fun r => r.count true % 2 == 1).length + _ = _
  rw [hsplit]

/-- Any sequence of `.Sq` pieces played on a board satisfying `ChimneyInvariant B r cut`
(with `maxJump R + 2 < cut - r`) clears at most `oddRowsAboveL cut B ≤ B.height - cut` rows! -/
theorem sq_play_bound {R : Rotation} {B : Board} {r cut : ℕ}
    (hinv : ChimneyInvariant B r cut) (hgap : maxJump R + 2 < cut - r)
    {N : ℕ} {qs : List PieceState} {B' : Board} {v : ℕ}
    (hplay : Play R B (List.replicate N .Sq) qs B' v) :
    v ≤ B.height - cut := by
  have hmain : ∀ {B0 B1 : Board} {ts : List Piece} {qs : List PieceState} {v : ℕ},
      Play R B0 ts qs B1 v →
      (∀ t ∈ ts, t = .Sq) →
      ChimneyInvariant B0 r cut →
      v + oddRowsAboveL cut B1 = oddRowsAboveL cut B0 := by
    intro B0 B1 ts qs v hp hts hi
    induction hp with
    | stop _ _ => simp
    | step htraj hrest ih =>
      rename_i Bcur t ts' q qs' Bfin v'
      have ht : t = .Sq := hts t (List.mem_cons_self ..)
      subst ht
      obtain ⟨hi', hstep⟩ := sq_step_invariant hi hgap htraj
      have hih := ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) hi'
      omega
  have h1 := hmain hplay (fun t ht => (List.mem_replicate.mp ht).2) hinv
  have h2 : oddRowsAboveL cut B ≤ B.height - cut := by
    unfold oddRowsAboveL
    calc ((B.rows.drop cut).filter _).length
        ≤ (B.rows.drop cut).length := List.length_filter_le _ _
      _ = B.height - cut := by simp [Board.rows]
  omega

/-! ### Lock-Isolation Lemma (no piece enters `y < cut` while a sealing row survives) -/

/-- A board `B` is sealed at height `cut` (`cut = r + 4 * K + 2`) with `nSeal` surviving
sealing rows above `cut` if:
1. Every empty cell in row `cut - 1` has `x ≥ splitX`.
2. Every row `y` with `cut ≤ y < cut + nSeal` has `B.cell y x = true` for all `x ≥ splitX`. -/
def SealedAt (B : Board) (cut splitX nSeal : ℕ) : Prop :=
  1 ≤ cut ∧
  cut + nSeal ≤ B.height ∧
  (∀ y : Fin B.height, y.val = cut - 1 →
    ∀ x : Fin B.width, x.val < splitX → B.cell y x = true) ∧
  (∀ y : Fin B.height, cut ≤ y.val → y.val < cut + nSeal →
    ∀ x : Fin B.width, splitX ≤ x.val → B.cell y x = true)

lemma emptyAdjacent_no_cross_seal {B : Board} {cut splitX nSeal : ℕ}
    (hseal : SealedAt B cut splitX nSeal) (hpos : 1 ≤ nSeal)
    {z z' : Cell} (hadj : EmptyAdjacent B z z') (hz : (cut : ℤ) ≤ z.2) :
    (cut : ℤ) ≤ z'.2 := by
  rcases hadj with ⟨hzocc, hz'occ, hstep⟩
  by_contra hlt
  push Not at hlt
  have h1s : |z.1 - z'.1| + |z.2 - z'.2| = 1 := hstep
  have ha1 : 0 ≤ |z.1 - z'.1| := abs_nonneg _
  have ha2 : z.2 - z'.2 ≤ |z.2 - z'.2| := le_abs_self _
  have hz'2 : z'.2 = (cut : ℤ) - 1 := by omega
  have hz2 : z.2 = (cut : ℤ) := by omega
  have habs1 : |z.1 - z'.1| = 0 := by
    have : |z.2 - z'.2| = 1 := by rw [hz2, hz'2]; norm_num
    omega
  have hxeq : z.1 = z'.1 := sub_eq_zero.mp (abs_eq_zero.mp habs1)
  have hcutH : cut < B.height := by have := hseal.2.1; omega
  have h0 : (0 : ℤ) ≤ z'.2 := by have := hseal.1; omega
  have h1 : z'.2 < B.height := by omega
  simp only [Board.occupied, h0, h1, and_self, ↓reduceDIte] at hz'occ
  split_ifs at hz'occ with hx'
  have hxge : splitX ≤ z'.1.toNat := by
    by_contra hxlt
    push Not at hxlt
    have htrue := hseal.2.2.1 ⟨z'.2.toNat, by omega⟩ (by dsimp; omega) ⟨z'.1.toNat, by omega⟩ hxlt
    rw [htrue] at hz'occ
    simp at hz'occ
  have hz0 : (0 : ℤ) ≤ z.2 := by omega
  have hz1 : z.2 < B.height := by omega
  simp only [Board.occupied, hz0, hz1, and_self, ↓reduceDIte] at hzocc
  have hxz : 0 ≤ z.1 ∧ z.1 < B.width := by omega
  simp only [hxz, and_self, ↓reduceDIte] at hzocc
  have htrue := hseal.2.2.2 ⟨z.2.toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    ⟨z.1.toNat, by omega⟩ (by dsimp; omega)
  rw [htrue] at hzocc
  simp at hzocc

lemma trajectory_above_seal {R : Rotation} (hReason : Reasonable R)
    {B : Board} {cut splitX nSeal : ℕ} (hseal : SealedAt B cut splitX nSeal) (hpos : 1 ≤ nSeal)
    (hspawn_ge : ∀ t : Piece, ∀ z ∈ (spawn B t).cells, (cut : ℤ) ≤ z.2)
    {t : Piece} {q : PieceState} (htraj : Trajectory R B t q) :
    ∀ z ∈ q.cells, (cut : ℤ) ≤ z.2 := by
  have hcomp : ∀ z z', Relation.ReflTransGen (EmptyAdjacent B) z z' →
      (cut : ℤ) ≤ z.2 → (cut : ℤ) ≤ z'.2 := by
    intro z z' hrt hz
    induction hrt with
    | refl => exact hz
    | tail _ hstep ih => exact emptyAdjacent_no_cross_seal hseal hpos hstep ih
  have hreach : ∀ q', Relation.ReflTransGen (Move R B) (spawn B t) q' →
      ∀ z ∈ q'.cells, (cut : ℤ) ≤ z.2 := by
    intro q' hr
    induction hr with
    | refl => exact hspawn_ge t
    | tail _ hstep ih =>
      rename_i q1 q2 _
      intro z' hz'
      have hne : q1.cells ≠ [] := by
        cases h : q1.kind <;> simp [PieceState.cells, h, Piece.base]
      obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil q1.cells hne
      exact hcomp z z' (hReason.1 B q1 q2 hstep z hz z' hz') (ih z hz)
  exact hreach q htraj.2.1


/-! ### Part A: Outer Shell, Parity/Seal Invariant, `BucketFrame` Transfer, Area Accounting -/

/-- Prefix pieces of `paddedReservoirGame` before the `.Sq` reservoir pieces. -/
def prefixPieces (P : ThreePartition) (pad K : ℕ) : List Piece :=
  basePieces P ++ List.replicate (3 * pad) .I ++ List.replicate K .I ++ [.RG]

/-- Reservoir `.Sq` pieces of `paddedReservoirGame`. -/
def sqPieces (P : ThreePartition) (pad r : ℕ) : List Piece :=
  List.replicate (r * (6 * (P.s + pad) + 2) / 4) .Sq

/-- Bound on rows cleared in a "no" instance of `paddedReservoirGame`, independent of `r`. -/
lemma prefixPieces_length (P : ThreePartition) (pad K : ℕ) :
    (prefixPieces P pad K).length = (basePieces P).length + 3 * pad + K + 1 := by
  simp [prefixPieces]; omega

lemma paddedReservoirGame_pieces_eq (P : ThreePartition) (pad K st r : ℕ) :
    (paddedReservoirGame P pad K st r).pieces =
      prefixPieces P pad K ++ sqPieces P pad r := by
  simp [paddedReservoirGame, prefixPieces, sqPieces]

/-! ### Play Splitting -/

lemma play_append_split {R : Rotation} {B Bfin : Board} {ts1 ts2 : List Piece}
    {qs : List PieceState} {v : ℕ}
    (hplay : Play R B (ts1 ++ ts2) qs Bfin v) :
    ∃ qs1 qs2 Bmid v1 v2,
      qs = qs1 ++ qs2 ∧
      v = v1 + v2 ∧
      Play R B ts1 qs1 Bmid v1 ∧
      Play R Bmid ts2 qs2 Bfin v2 ∧
      (qs2 ≠ [] → qs1.length = ts1.length) := by
  induction ts1 generalizing B qs v with
  | nil =>
    exact ⟨[], qs, B, 0, v, rfl, (Nat.zero_add v).symm, Play.stop B [], hplay, fun _ => rfl⟩
  | cons t ts1' ih =>
    simp only [List.cons_append] at hplay
    cases hplay with
    | stop =>
      exact ⟨[], [], _, 0, 0, rfl, rfl, Play.stop _ (t :: ts1'), Play.stop _ ts2,
        fun h => absurd rfl h⟩
    | step htraj hrest =>
      rename_i q qs' v'
      obtain ⟨qs1, qs2, Bmid, v1, v2, hqs, hv, hp1, hp2, hlen⟩ := ih hrest
      refine ⟨q :: qs1, qs2, Bmid, B.gain q + v1, v2, by simp [hqs], by omega,
        Play.step htraj hp1, hp2, ?_⟩
      intro hne
      simp [hlen hne]

/-! ### Parity Bound for General Pieces Above a Cut -/

lemma piece_cells_length (q : PieceState) : q.cells.length = 4 := by
  cases h : q.kind <;> simp [PieceState.cells, h, Piece.base]

lemma list_count_map_le_add {α : Type} (L : List α) (f g : α → Bool) :
    (L.map f).count true ≤ (L.map g).count true + (L.filter fun a => f a != g a).length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    cases hf : f a <;> cases hg : g a <;> simp [hf, hg] <;> omega

lemma insert_oddRowsAboveL_le (B : Board) (q : PieceState) (cut : ℕ) :
    oddRowsAboveL cut (B.insert q) ≤ oddRowsAboveL cut B + 4 := by
  unfold oddRowsAboveL
  have hlen_filter : ∀ (L : List (List Bool)) (p : List Bool → Bool),
      (L.filter p).length = (L.map p).count true := by
    intro L p
    induction L with
    | nil => simp
    | cons a l ih => cases h : p a <;> simp [h, ih]
  have hmap : ∀ (M : Board), (M.rows.drop cut).map (fun row => (row.count true) % 2 == 1) =
      (List.finRange M.height |>.drop cut).map fun y =>
        ((List.ofFn fun x : Fin M.width => M.cell y x).count true) % 2 == 1 := by
    intro M
    simp only [Board.rows, List.ofFn_eq_map, ← List.map_drop, List.map_map]
    rfl
  rw [hlen_filter, hlen_filter, hmap (B.insert q), hmap B]
  set f : Fin B.height → Bool := fun y =>
    ((List.ofFn fun x : Fin B.width => (B.insert q).cell y x).count true) % 2 == 1
  set g : Fin B.height → Bool := fun y =>
    ((List.ofFn fun x : Fin B.width => B.cell y x).count true) % 2 == 1
  change (((List.finRange B.height).drop cut).map f).count true ≤
    (((List.finRange B.height).drop cut).map g).count true + 4
  have hle := list_count_map_le_add ((List.finRange B.height).drop cut) f g
  suffices hdiff : (((List.finRange B.height).drop cut).filter fun y => f y != g y).length ≤ 4 by
    omega
  -- Every y with f y ≠ g y must have (y.val : ℤ) ∈ q.cells.map Prod.snd
  have hsub : ∀ y ∈ ((List.finRange B.height).drop cut).filter (fun y => f y != g y),
      (y.val : ℤ) ∈ q.cells.map Prod.snd := by
    intro y hy
    have hfg : f y ≠ g y := by
      have h1 := (List.mem_filter.mp hy).2
      simpa using h1
    by_contra hnot
    apply hfg
    have hsame : ∀ x : Fin B.width, (B.insert q).cell y x = B.cell y x := by
      intro x
      simp only [Board.insert]
      have hnotmem : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by
        intro hm
        exact hnot (List.mem_map.mpr ⟨_, hm, rfl⟩)
      simp [hnotmem]
    simp [f, g, hsame]
  have hnodup : (((List.finRange B.height).drop cut).filter (fun y => f y != g y)).Nodup :=
    ((List.nodup_finRange B.height).drop).filter _
  have hnodup_map : ((((List.finRange B.height).drop cut).filter (fun y => f y != g y)).map
      fun y : Fin B.height => (y.val : ℤ)).Nodup := by
    apply hnodup.map
    intro a b hab
    exact Fin.ext (Int.ofNat.inj hab)
  have hcard : ((((List.finRange B.height).drop cut).filter (fun y => f y != g y)).map
      fun y : Fin B.height => (y.val : ℤ)).toFinset.card ≤ (q.cells.map Prod.snd).toFinset.card := by
    apply Finset.card_le_card
    intro z hz
    rw [List.mem_toFinset] at hz ⊢
    rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact hsub y hy
  rw [List.toFinset_card_of_nodup hnodup_map, List.length_map] at hcard
  have hqcard : (q.cells.map Prod.snd).toFinset.card ≤ 4 := by
    calc (q.cells.map Prod.snd).toFinset.card
        ≤ (q.cells.map Prod.snd).length := List.toFinset_card_le _
      _ = q.cells.length := List.length_map ..
      _ = 4 := piece_cells_length q
  omega

lemma settle_below_and_oddRows {B : Board} {cut : ℕ} {q : PieceState}
    (hodd : Odd B.width)
    (hcut_le : cut ≤ B.height)
    (hbelow_false : ∀ y : Fin B.height, y.val < cut → ∃ x : Fin B.width, B.cell y x = false)
    (hcells_ge : ∀ z ∈ q.cells, (cut : ℤ) ≤ z.2) :
    (∀ y : Fin (B.settle q).height, y.val < cut →
      ∀ x : Fin (B.settle q).width, (B.settle q).cell y x = B.cell ⟨y.val, y.isLt⟩ ⟨x.val, x.isLt⟩) ∧
    oddRowsAboveL cut (B.settle q) + B.gain q = oddRowsAboveL cut (B.insert q) ∧
    B.gain q = (((B.insert q).rows.drop cut).filter fun row => row.all id).length := by
  have hsettleH : (B.settle q).height = B.height := rfl
  have hsettleW : (B.settle q).width = B.width := rfl
  set B1 := B.insert q
  have hB1_below : ∀ y : Fin B.height, y.val < cut → ∀ x : Fin B.width, B1.cell y x = B.cell y x := by
    intro y hy x
    simp only [B1, Board.insert]
    have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by
      intro hmem; have := hcells_ge _ hmem; omega
    simp [hnot]
  have hB1_rows_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
  have htake_not_full : ∀ row ∈ B1.rows.take cut, row.all id = false := by
    intro row hmem
    rw [List.mem_iff_getElem] at hmem
    rcases hmem with ⟨i, hi, rfl⟩
    simp only [List.length_take, hB1_rows_len] at hi
    have hi_cut : i < cut := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hi_H : i < B.height := lt_of_lt_of_le hi (Nat.min_le_right _ _)
    rw [List.getElem_take]
    simp only [Board.rows, List.getElem_ofFn]
    obtain ⟨x, hx⟩ := hbelow_false ⟨i, hi_H⟩ hi_cut
    rw [Bool.eq_false_iff]
    intro hall
    have h1 := (row_all_id_iff B1 ⟨i, hi_H⟩).mp hall x
    have h2 : B1.cell ⟨i, hi_H⟩ x = B.cell ⟨i, hi_H⟩ x := hB1_below ⟨i, hi_H⟩ hi_cut x
    rw [h2, hx] at h1
    simp at h1
  have hrows_split : B1.rows = B1.rows.take cut ++ B1.rows.drop cut :=
    (List.take_append_drop cut B1.rows).symm
  have htake_filter_false : (B1.rows.take cut).filter (fun row => row.all id) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row hmem; simp [htake_not_full row hmem]
  have htake_filter_true : (B1.rows.take cut).filter (fun row => !(row.all id)) = B1.rows.take cut := by
    rw [List.filter_eq_self]
    intro row hmem; simp [htake_not_full row hmem]
  have hgain_eq : B.gain q = ((B1.rows.drop cut).filter fun row => row.all id).length := by
    unfold Board.gain Board.fullCount
    change (B1.rows.filter fun row => row.all id).length = _
    conv_lhs => rw [hrows_split]
    rw [List.filter_append, htake_filter_false, List.nil_append]
  set surv := B1.rows.filter fun row => !(row.all id)
  have hsurv_eq : surv = B1.rows.take cut ++ (B1.rows.drop cut).filter fun row => !(row.all id) := by
    change B1.rows.filter (fun row => !(row.all id)) = _
    conv_lhs => rw [hrows_split]
    rw [List.filter_append, htake_filter_true]
  have htake_len : (B1.rows.take cut).length = cut := by simp [hB1_rows_len, hcut_le]
  have hsettle_below : ∀ y : Fin (B.settle q).height, y.val < cut →
      ∀ x : Fin (B.settle q).width, (B.settle q).cell y x = B.cell ⟨y.val, y.isLt⟩ ⟨x.val, x.isLt⟩ := by
    intro y hy x
    change (surv.getD y.val []).getD x.val false = _
    rw [hsurv_eq]
    have hy1 : y.val < (B1.rows.take cut).length := by omega
    have hget1 : (B1.rows.take cut ++ (B1.rows.drop cut).filter fun row => !(row.all id)).getD y.val [] =
        (B1.rows.take cut)[y.val] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hy1,
        List.getElem?_eq_getElem hy1, Option.getD_some]
    rw [hget1, List.getElem_take]
    have hx1 : x.val < B1.width := x.isLt
    simp only [Board.rows, List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx1,
      ↓reduceDIte, Option.getD_some]
    exact hB1_below ⟨y.val, y.isLt⟩ hy ⟨x.val, x.isLt⟩
  refine ⟨hsettle_below, ?_, hgain_eq⟩
  set S := (B1.rows.drop cut).filter fun row => !(row.all id)
  have hS_len : S.length ≤ B.height - cut := by
    calc S.length ≤ (B1.rows.drop cut).length := List.length_filter_le _ _
      _ = B.height - cut := by simp [hB1_rows_len]
  have hsettle_rows_len : (B.settle q).rows.length = B.height := by
    simp [Board.rows, Board.settle, Board.compress, Board.insert]
  have hsettle_rows_drop : (B.settle q).rows.drop cut =
      S ++ List.replicate ((B.height - cut) - S.length) (List.replicate B.width false) := by
    apply List.ext_getElem
    · simp only [List.length_drop, hsettle_rows_len, List.length_append, List.length_replicate]
      omega
    · intro i hi1 hi2
      simp only [List.length_drop, hsettle_rows_len] at hi1
      have hcuti : cut + i < B.height := by omega
      rw [List.getElem_drop]
      have hlhs : (B.settle q).rows[cut + i] =
          List.ofFn (fun x : Fin (B.settle q).width => (B.settle q).cell ⟨cut + i, hcuti⟩ x) := by
        simp [Board.rows]
      rw [hlhs]
      by_cases hiS : i < S.length
      · rw [List.getElem_append_left hiS]
        have hSlen : S[i].length = B.width := by
          have hmem : S[i] ∈ B1.rows.drop cut := (List.mem_filter.mp (List.getElem_mem hiS)).1
          have hmem' := List.mem_of_mem_drop hmem
          simp only [Board.rows, List.mem_ofFn] at hmem'
          rcases hmem' with ⟨y, hy⟩
          rw [← hy]; simp; rfl
        apply List.ext_getElem
        · simp [hSlen]; rfl
        · intro j hj1 hj2
          simp only [List.getElem_ofFn]
          change (surv.getD (cut + i) []).getD j false = S[i][j]
          have hget : surv.getD (cut + i) [] = S[i] := by
            rw [hsurv_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              htake_len, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hiS, Option.getD_some]
          rw [hget, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]
      · rw [List.getElem_append_right (Nat.not_lt.mp hiS), List.getElem_replicate]
        apply List.ext_getElem
        · simp; rfl
        · intro j hj1 hj2
          simp only [List.getElem_ofFn, List.getElem_replicate]
          change (surv.getD (cut + i) []).getD j false = false
          have hget : surv.getD (cut + i) [] = [] := by
            rw [hsurv_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              htake_len, Nat.add_sub_cancel_left, List.getElem?_eq_none (Nat.not_lt.mp hiS),
              Option.getD_none]
          rw [hget]; simp
  have hrep_filter : ∀ k, (List.replicate k (List.replicate B.width false) |>.filter
      fun row => (row.count true) % 2 == 1) = [] := by
    intro k
    rw [List.filter_eq_nil_iff]
    intro row hmem
    rw [List.mem_replicate] at hmem
    rcases hmem with ⟨_, rfl⟩
    simp [List.count_replicate]
  unfold oddRowsAboveL
  rw [hsettle_rows_drop, hgain_eq, List.filter_append, hrep_filter, List.append_nil]
  have hsplit := list_filter_odd_split (B1.rows.drop cut) B.width hodd (by
    intro row hmem
    have hmem' := List.mem_of_mem_drop hmem
    simp only [Board.rows, List.mem_ofFn] at hmem'
    rcases hmem' with ⟨y, hy⟩
    rw [← hy]; simp; rfl)
  change (S.filter fun r => r.count true % 2 == 1).length + _ = _
  rw [hsplit]

/-! ### Chimney-Seal Invariant (Tracks Surviving Chimney + Upper Rows Above `r + 2`) -/

/-- Invariant tracking `nChimney` surviving chimney rows at `[cut0, cut0 + nChimney)`
and `nUpper` surviving upper sealing rows at `[cut0 + nChimney, cut0 + nChimney + nUpper)`.
- Every row `< cut0` has a `false` cell; row `cut0 - 1` has `true` for all `x < splitX`.
- Every chimney row has `cell y x = decide (x ≠ splitX - 1)` (only 1 empty cell, and `true` for `x ≥ splitX`).
- Every upper row has `true` for all `x ≥ upperSplitX` (where `upperSplitX ≤ splitX - 1`). -/
def ChimneySealInv (B : Board) (cut0 splitX upperSplitX nChimney nUpper : ℕ) : Prop :=
  Odd B.width ∧
  1 ≤ cut0 ∧
  upperSplitX + 1 ≤ splitX ∧
  splitX < B.width ∧
  cut0 + nChimney + nUpper + 3 ≤ B.height ∧
  (∀ y : Fin B.height, y.val < cut0 → ∃ x : Fin B.width, B.cell y x = false) ∧
  (∀ y : Fin B.height, y.val = cut0 - 1 →
    ∀ x : Fin B.width, x.val < splitX → B.cell y x = true) ∧
  (∀ y : Fin B.height, cut0 ≤ y.val → y.val < cut0 + nChimney →
    ∀ x : Fin B.width, B.cell y x = decide (x.val ≠ splitX - 1)) ∧
  (∀ y : Fin B.height, cut0 + nChimney ≤ y.val → y.val < cut0 + nChimney + nUpper →
    ∀ x : Fin B.width, upperSplitX ≤ x.val → B.cell y x = true)

lemma chimneySealInv_sealed_cut0 {B : Board} {cut0 splitX upperSplitX nChimney nUpper : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nChimney nUpper) :
    SealedAt B cut0 splitX (nChimney + nUpper) := by
  rcases hinv with ⟨_, h1, hus, _, hH, _, hrow, hchim, hup⟩
  refine ⟨h1, by omega, hrow, ?_⟩
  intro y hy1 hy2 x hx
  by_cases hc : y.val < cut0 + nChimney
  · rw [hchim y hy1 hc x]; simp; omega
  · exact hup y (by omega) (by omega) x (by omega)

lemma chimneySealInv_sealed_upper {B : Board} {cut0 splitX upperSplitX nChimney nUpper : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nChimney nUpper) (hchim_pos : 1 ≤ nChimney) :
    SealedAt B (cut0 + nChimney) upperSplitX nUpper := by
  rcases hinv with ⟨_, h1, hus, _, hH, _, _, hchim, hup⟩
  refine ⟨by omega, by omega, ?_, hup⟩
  intro y hy x hx
  rw [hchim y (by omega) (by omega) x]
  simp; omega

lemma spawn_cells_ge_of_height {B : Board} {cut : ℕ} (h : cut + 3 ≤ B.height) (t : Piece) :
    ∀ z ∈ (spawn B t).cells, (cut : ℤ) ≤ z.2 := by
  intro z hz
  cases t <;> simp [spawn, PieceState.cells, Piece.base] at hz <;>
    rcases hz with rfl | rfl | rfl | rfl <;> omega

lemma chimneySealInv_init (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hst : 3 ≤ st) :
    ChimneySealInv (paddedReservoirBoard P pad K st r)
      (r + 2) (6 * (P.s + pad)) (6 * P.s + 3) (4 * K) (12 * pad + baseHeight P) := by
  refine ⟨?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨3 * (P.s + pad) + 1, by simp [paddedReservoirBoard]; ring⟩
  · simp [paddedReservoirBoard]
  · simp [paddedReservoirBoard, baseBoard]; omega
  · intro y hy
    by_cases h1 : y.val < r
    · refine ⟨⟨1, by simp [paddedReservoirBoard]⟩, ?_⟩
      simp [paddedReservoirBoard, h1]
    · by_cases h2 : y.val = r
      · refine ⟨⟨6 * (P.s + pad), by simp [paddedReservoirBoard]⟩, ?_⟩
        simp [paddedReservoirBoard, h2]
      · have h3 : y.val = r + 1 := by omega
        refine ⟨⟨6 * (P.s + pad), by simp [paddedReservoirBoard]⟩, ?_⟩
        simp [paddedReservoirBoard, h3]
  · intro y hy x hx
    have hy3 : y.val = r + 1 := by omega
    simp [paddedReservoirBoard, hy3, hx]
  · intro y hy1 hy2 x
    have h1 : ¬ y.val < r := by omega
    have h2 : ¬ y.val = r := by omega
    have h3 : ¬ y.val = r + 1 := by omega
    have h4 : y.val < r + 2 + 4 * K := by omega
    simp [paddedReservoirBoard, h1, h2, h3, h4]
  · intro y hy1 hy2 x hx
    have h1 : ¬ y.val < r := by omega
    have h2 : ¬ y.val = r := by omega
    have h3 : ¬ y.val = r + 1 := by omega
    have h4 : ¬ y.val < r + 2 + 4 * K := by omega
    by_cases h5 : y.val < r + 2 + 4 * K + 12 * pad
    · simp only [paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte, decide_eq_true_eq]
      omega
    · have hx' : ¬ x.val < 6 * P.s + 3 := by omega
      have h6 : y.val < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
      simp [paddedReservoirBoard, h1, h2, h3, h4, h5, hx', h6]

lemma oddRowsAboveL_init_le (P : ThreePartition) (pad K st r : ℕ) (hpad : 1 ≤ pad) :
    oddRowsAboveL (r + 2) (paddedReservoirBoard P pad K st r) ≤ baseHeight P := by
  set B0 := paddedReservoirBoard P pad K st r
  unfold oddRowsAboveL
  have hlen_filter : ∀ {α : Type} (L : List α) (p : α → Bool),
      (L.filter p).length = (L.map p).count true := by
    intro α L p; induction L with
    | nil => simp
    | cons a l ih => cases h : p a <;> simp [h, ih]
  rw [hlen_filter]
  have hmap : (B0.rows.drop (r + 2)).map (fun row => (row.count true) % 2 == 1) =
      ((List.finRange B0.height).drop (r + 2)).map fun y =>
        ((List.ofFn fun x : Fin B0.width => B0.cell y x).count true) % 2 == 1 := by
    simp only [Board.rows, List.ofFn_eq_map, ← List.map_drop, List.map_map]; rfl
  rw [hmap]
  set p : Fin B0.height → Bool := fun y =>
    ((List.ofFn fun x : Fin B0.width => B0.cell y x).count true) % 2 == 1
  rw [← hlen_filter]
  have hsub : ∀ y ∈ ((List.finRange B0.height).drop (r + 2)).filter p,
      r + 2 + 4 * K + 12 * pad ≤ y.val ∧ y.val < r + 2 + 4 * K + 12 * pad + baseHeight P := by
    intro y hy
    have hpy : p y = true := (List.mem_filter.mp hy).2
    have hmem : y ∈ (List.finRange B0.height).drop (r + 2) := (List.mem_filter.mp hy).1
    have hy_ge : r + 2 ≤ y.val := by
      rw [List.mem_iff_getElem] at hmem
      rcases hmem with ⟨i, hi, rfl⟩
      simp only [List.getElem_drop, List.getElem_finRange, Fin.val_cast]
      omega
    have hcnt_fin : ∀ f : Fin B0.width → Bool,
        (List.ofFn f).count true = (Finset.univ.filter fun x => f x = true).card := by
      intro f
      rw [List.count_eq_countP]
      have : (List.ofFn f).countP (· == true) =
          (List.finRange B0.width).countP (fun x => f x == true) := by
        rw [List.ofFn_eq_map, List.countP_map]; rfl
      rw [this, List.countP_eq_length_filter]
      have hnodup : ((List.finRange B0.width).filter fun x => f x == true).Nodup :=
        (List.nodup_finRange _).filter _
      rw [← List.toFinset_card_of_nodup hnodup]
      congr 1; ext x; simp
    have hnot1 : ¬ y.val < r + 2 + 4 * K + 12 * pad := by
      intro hlt
      have h1 : ¬ y.val < r := by omega
      have h2 : ¬ y.val = r := by omega
      have h3 : ¬ y.val = r + 1 := by omega
      have hcnt : (List.ofFn fun x : Fin B0.width => B0.cell y x).count true = B0.width - 1 := by
        rw [hcnt_fin]
        by_cases h4 : y.val < r + 2 + 4 * K
        · set x0 : Fin B0.width := ⟨6 * (P.s + pad) - 1, by simp [B0, paddedReservoirBoard]; omega⟩
          have hset : (Finset.univ.filter fun x : Fin B0.width => B0.cell y x = true) =
              Finset.univ.erase x0 := by
            ext x
            rw [Finset.mem_filter, Finset.mem_erase]
            simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, ↓reduceIte, decide_eq_true_eq, x0]
            exact ⟨fun h => ⟨fun heq => h.2 (congrArg Fin.val heq), Finset.mem_univ _⟩,
              fun h => ⟨Finset.mem_univ _, fun hv => h.1 (Fin.ext hv)⟩⟩
          rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
        · set x0 : Fin B0.width := ⟨6 * P.s + 2, by simp [B0, paddedReservoirBoard]⟩
          have hset : (Finset.univ.filter fun x : Fin B0.width => B0.cell y x = true) =
              Finset.univ.erase x0 := by
            ext x
            rw [Finset.mem_filter, Finset.mem_erase]
            simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, hlt, ↓reduceIte, decide_eq_true_eq, x0]
            exact ⟨fun h => ⟨fun heq => h.2 (congrArg Fin.val heq), Finset.mem_univ _⟩,
              fun h => ⟨Finset.mem_univ _, fun hv => h.1 (Fin.ext hv)⟩⟩
          rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
      simp only [p, hcnt, beq_iff_eq] at hpy
      have hw : B0.width = 6 * (P.s + pad) + 3 := rfl
      omega
    have hnot2 : ¬ r + 2 + 4 * K + 12 * pad + baseHeight P ≤ y.val := by
      intro hge
      have h1 : ¬ y.val < r := by omega
      have h2 : ¬ y.val = r := by omega
      have h3 : ¬ y.val = r + 1 := by omega
      have h4 : ¬ y.val < r + 2 + 4 * K := by omega
      have h5 : ¬ y.val < r + 2 + 4 * K + 12 * pad := by omega
      have h6 : ¬ y.val < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
      have hall_f : ∀ x : Fin B0.width, B0.cell y x = false := by
        intro x
        simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte]
        split_ifs with hx
        · have hy_sub : baseHeight P ≤ (y.val : ℤ) - (r + 2 + 4 * K + 12 * pad) := by omega
          have hy_lt : (y.val : ℤ) - (r + 2 + 4 * K + 12 * pad) < (baseBoard P st).height := by
            have := y.isLt; simp [B0, paddedReservoirBoard] at this; omega
          unfold Board.occupied
          rw [dif_pos (by omega), dif_pos (by simp [baseBoard]; omega)]
          have hge_nat : baseHeight P ≤ ((y.val : ℤ) - (r + 2 + 4 * K + 12 * pad)).toNat := by omega
          simp [baseBoard, hge_nat]
        · simp [h6]
      have hcnt : (List.ofFn fun x : Fin B0.width => B0.cell y x).count true = 0 := by
        rw [hcnt_fin]
        simp [hall_f]
      simp [p, hcnt] at hpy
    omega
  have hnodup : (((List.finRange B0.height).drop (r + 2)).filter p).Nodup :=
    ((List.nodup_finRange B0.height).drop).filter _
  have hnodup_map : ((((List.finRange B0.height).drop (r + 2)).filter p).map Fin.val).Nodup :=
    hnodup.map Fin.val_injective
  have hcard : ((((List.finRange B0.height).drop (r + 2)).filter p).map Fin.val).toFinset.card ≤
      (Finset.Ico (r + 2 + 4 * K + 12 * pad) (r + 2 + 4 * K + 12 * pad + baseHeight P)).card := by
    apply Finset.card_le_card
    intro n hn
    rw [List.mem_toFinset] at hn
    rcases List.mem_map.mp hn with ⟨y, hy, rfl⟩
    exact Finset.mem_Ico.mpr (hsub y hy)
  rw [List.toFinset_card_of_nodup hnodup_map, List.length_map, Nat.card_Ico] at hcard
  omega

/-- Helper: extracting a surviving row from `B.settle q`. -/
lemma settle_rows_drop_eq {B : Board} {cut : ℕ} {q : PieceState}
    (hcut_le : cut ≤ B.height)
    (hbelow_false : ∀ y : Fin B.height, y.val < cut → ∃ x : Fin B.width, B.cell y x = false)
    (hcells_ge : ∀ z ∈ q.cells, (cut : ℤ) ≤ z.2) :
    let B1 := B.insert q
    let S := (B1.rows.drop cut).filter fun row => !(row.all id)
    ∀ i : ℕ, (hi : i < S.length) →
      ∀ x : Fin B.width,
        (B.settle q).cell ⟨cut + i, by
          have hsettleH : (B.settle q).height = B.height := rfl
          have hS : S.length ≤ B.height - cut := by
            calc S.length ≤ (B1.rows.drop cut).length := List.length_filter_le _ _
              _ = B.height - cut := by simp [Board.rows, B1, Board.insert]
          omega⟩ ⟨x.val, x.isLt⟩ = S[i].getD x.val false := by
  intro B1 S i hi x
  have hB1_below : ∀ y : Fin B.height, y.val < cut → ∀ x : Fin B.width, B1.cell y x = B.cell y x := by
    intro y hy x
    simp only [B1, Board.insert]
    have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by
      intro hmem; have := hcells_ge _ hmem; omega
    simp [hnot]
  have hB1_rows_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
  have htake_not_full : ∀ row ∈ B1.rows.take cut, row.all id = false := by
    intro row hmem
    rw [List.mem_iff_getElem] at hmem
    rcases hmem with ⟨j, hj, rfl⟩
    simp only [List.length_take, hB1_rows_len] at hj
    have hj_cut : j < cut := lt_of_lt_of_le hj (Nat.min_le_left _ _)
    have hj_H : j < B.height := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    rw [List.getElem_take]
    simp only [Board.rows, List.getElem_ofFn]
    obtain ⟨x0, hx0⟩ := hbelow_false ⟨j, hj_H⟩ hj_cut
    rw [Bool.eq_false_iff]
    intro hall
    have h1 := (row_all_id_iff B1 ⟨j, hj_H⟩).mp hall x0
    have h2 : B1.cell ⟨j, hj_H⟩ x0 = B.cell ⟨j, hj_H⟩ x0 := hB1_below ⟨j, hj_H⟩ hj_cut x0
    rw [h2, hx0] at h1
    simp at h1
  have hrows_split : B1.rows = B1.rows.take cut ++ B1.rows.drop cut :=
    (List.take_append_drop cut B1.rows).symm
  have htake_filter_true : (B1.rows.take cut).filter (fun row => !(row.all id)) = B1.rows.take cut := by
    rw [List.filter_eq_self]
    intro row hmem; simp [htake_not_full row hmem]
  have hsurv_eq : B1.rows.filter (fun row => !(row.all id)) = B1.rows.take cut ++ S := by
    conv_lhs => rw [hrows_split]
    rw [List.filter_append, htake_filter_true]
  have htake_len : (B1.rows.take cut).length = cut := by simp [hB1_rows_len, hcut_le]
  change ((B1.rows.filter fun row => !(row.all id)).getD (cut + i) []).getD x.val false = _
  rw [hsurv_eq]
  have hget : (B1.rows.take cut ++ S).getD (cut + i) [] = S[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      htake_len, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hget]

/-- Deterministic update of `(nChimney, nUpper)` after settling piece `q`. -/
def nextChimneyUpper (B : Board) (cut0 nC nU : ℕ) (q : PieceState) : ℕ × ℕ :=
  let B1 := B.insert q
  if 1 ≤ nU ∧ 1 ≤ nC then
    (nC, (((B1.rows.drop (cut0 + nC)).take nU).filter fun row => !(row.all id)).length)
  else if nU = 0 then
    ((((B1.rows.drop cut0).take nC).filter fun row => !(row.all id)).length, 0)
  else
    (0, (((B1.rows.drop cut0).take nU).filter fun row => !(row.all id)).length)

/-- Track `(nChimney, nUpper)` along a list of piece placements `qs`. -/
def trackChimneyUpper : Board → ℕ → ℕ → ℕ → List PieceState → ℕ × ℕ
  | _, _, nC, nU, [] => (nC, nU)
  | B, cut0, nC, nU, q :: qs =>
    let p := nextChimneyUpper B cut0 nC nU q
    trackChimneyUpper (B.settle q) cut0 p.1 p.2 qs

/-- General step lemma for `ChimneySealInv`: while `1 ≤ nChimney + nUpper`, a piece `q`
cannot cross `cut0`, preserves `ChimneySealInv` with `nextChimneyUpper`,
and satisfies `oddRowsAboveL cut0 (B.settle q) + B.gain q ≤ oddRowsAboveL cut0 B + 4`. -/
lemma chimneySealInv_step {R : Rotation} (hReason : Reasonable R)
    {B : Board} {cut0 splitX upperSplitX nChimney nUpper : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nChimney nUpper)
    (hpos : 1 ≤ nChimney + nUpper)
    {t : Piece} {q : PieceState} (htraj : Trajectory R B t q) :
    let p := nextChimneyUpper B cut0 nChimney nUpper q
    p.1 ≤ nChimney ∧
    p.2 ≤ nUpper ∧
    (1 ≤ nUpper → 1 ≤ nChimney → p.1 = nChimney) ∧
    ChimneySealInv (B.settle q) cut0 splitX upperSplitX p.1 p.2 ∧
    oddRowsAboveL cut0 (B.settle q) + B.gain q ≤ oddRowsAboveL cut0 B + 4 := by
  intro p
  have hseal0 := chimneySealInv_sealed_cut0 hinv
  have hspawn0 := spawn_cells_ge_of_height (B := B) (cut := cut0) (by have := hinv.2.2.2.2.1; omega)
  have hcells0 : ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 :=
    trajectory_above_seal hReason hseal0 hpos hspawn0 htraj
  have hodd := hinv.1
  have hcut_le : cut0 ≤ B.height := by have := hinv.2.2.2.2.1; omega
  have hbelow_f := hinv.2.2.2.2.2.1
  obtain ⟨hsettle_below, hodd_eq, _⟩ := settle_below_and_oddRows hodd hcut_le hbelow_f hcells0
  have hodd_le : oddRowsAboveL cut0 (B.settle q) + B.gain q ≤ oddRowsAboveL cut0 B + 4 := by
    rw [hodd_eq]; exact insert_oddRowsAboveL_le B q cut0
  have hsettleH : (B.settle q).height = B.height := rfl
  have hsettleW : (B.settle q).width = B.width := rfl
  set B1 := B.insert q
  have hB1_rows_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
  by_cases hup_pos : 1 ≤ nUpper ∧ 1 ≤ nChimney
  · -- Upper seal holds at `cut0 + nChimney`, so all `nChimney` chimney rows are untouched!
    have hp_eq : p = (nChimney, (((B1.rows.drop (cut0 + nChimney)).take nUpper).filter fun row => !(row.all id)).length) := by
      simp [p, nextChimneyUpper, hup_pos, B1]
    rw [hp_eq]
    dsimp only
    have hsealU := chimneySealInv_sealed_upper hinv hup_pos.2
    have hspawnU := spawn_cells_ge_of_height (B := B) (cut := cut0 + nChimney)
      (by have := hinv.2.2.2.2.1; omega)
    have hcellsU : ∀ z ∈ q.cells, ((cut0 + nChimney : ℕ) : ℤ) ≤ z.2 :=
      trajectory_above_seal hReason hsealU hup_pos.1 hspawnU htraj
    have hbelow_fU : ∀ y : Fin B.height, y.val < cut0 + nChimney → ∃ x : Fin B.width, B.cell y x = false := by
      intro y hy
      by_cases hy0 : y.val < cut0
      · exact hbelow_f y hy0
      · refine ⟨⟨splitX - 1, by have := hinv.2.2.2.1; omega⟩, ?_⟩
        rw [hinv.2.2.2.2.2.2.2.1 y (by omega) hy]; simp
    obtain ⟨hsettle_belowU, _, _⟩ := settle_below_and_oddRows hodd
      (by have := hinv.2.2.2.2.1; omega) hbelow_fU hcellsU
    set Urows := (B1.rows.drop (cut0 + nChimney)).take nUpper
    set nUpper' := (Urows.filter fun row => !(row.all id)).length
    have hnUpper'_le : nUpper' ≤ nUpper := by
      calc nUpper' ≤ Urows.length := List.length_filter_le _ _
        _ ≤ nUpper := List.length_take_le _ _
    refine ⟨le_rfl, hnUpper'_le, fun _ _ => rfl, ?_, hodd_le⟩
    refine ⟨hodd, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, by have := hinv.2.2.2.2.1; omega, ?_, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx⟩ := hbelow_f ⟨y.val, y.isLt⟩ hy
      exact ⟨⟨x.val, x.isLt⟩, by rw [hsettle_below y hy]; exact hx⟩
    · intro y hy x hx
      rw [hsettle_below y (by have := hinv.2.1; omega)]
      exact hinv.2.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy ⟨x.val, x.isLt⟩ hx
    · intro y hy1 hy2 x
      rw [hsettle_belowU y hy2]
      exact hinv.2.2.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy1 hy2 ⟨x.val, x.isLt⟩
    · intro y hy1 hy2 x hx
      set i := y.val - (cut0 + nChimney)
      have hi_lt : i < nUpper' := by omega
      have hS_split : (B1.rows.drop (cut0 + nChimney)).filter (fun row => !(row.all id)) =
          Urows.filter (fun row => !(row.all id)) ++
          ((B1.rows.drop (cut0 + nChimney)).drop nUpper).filter (fun row => !(row.all id)) := by
        conv_lhs => rw [← List.take_append_drop nUpper (B1.rows.drop (cut0 + nChimney))]
        rw [List.filter_append]
      have hi_S : i < ((B1.rows.drop (cut0 + nChimney)).filter (fun row => !(row.all id))).length := by
        rw [hS_split, List.length_append]; omega
      have hcell := settle_rows_drop_eq (cut := cut0 + nChimney) (q := q)
        (by have := hinv.2.2.2.2.1; omega) hbelow_fU hcellsU i hi_S ⟨x.val, x.isLt⟩
      have hy_eq : (⟨cut0 + nChimney + i, by omega⟩ : Fin (B.settle q).height) = y := by
        ext; dsimp [i]; omega
      rw [hy_eq] at hcell
      rw [hcell]
      set row := ((B1.rows.drop (cut0 + nChimney)).filter (fun row => !(row.all id)))[i]
      have hrow_mem : row ∈ Urows := by
        have h1 : row = (Urows.filter (fun row => !(row.all id)))[i]'(hi_lt) := by
          simp only [row, hS_split, List.getElem_append_left hi_lt]
        rw [h1]
        exact (List.mem_filter.mp (List.getElem_mem hi_lt)).1
      rw [List.mem_iff_getElem] at hrow_mem
      rcases hrow_mem with ⟨k, hk, hrow_eq⟩
      simp only [Urows, List.length_take, List.length_drop, hB1_rows_len] at hk
      have hk_up : k < nUpper := lt_of_lt_of_le hk (Nat.min_le_left _ _)
      have hk_H : cut0 + nChimney + k < B.height := by have := hinv.2.2.2.2.1; omega
      have hrow_val : row = List.ofFn (fun x' : Fin B1.width => B1.cell ⟨cut0 + nChimney + k, hk_H⟩ x') := by
        rw [← hrow_eq]
        simp only [Urows, List.getElem_take, List.getElem_drop, Board.rows, List.getElem_ofFn]
      rw [hrow_val]
      have hx_lt : x.val < B1.width := x.isLt
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx_lt, ↓reduceDIte, Option.getD_some]
      have hB_true := hinv.2.2.2.2.2.2.2.2 ⟨cut0 + nChimney + k, hk_H⟩ (by dsimp; omega) (by dsimp; omega) ⟨x.val, x.isLt⟩ hx
      simp [B1, Board.insert, hB_true]
  · -- Either `nUpper = 0` or `nChimney = 0`
    by_cases hnU : nUpper = 0
    · subst hnU
      have hp_eq : p = ((((B1.rows.drop cut0).take nChimney).filter fun row => !(row.all id)).length, 0) := by
        simp [p, nextChimneyUpper, B1]
      rw [hp_eq]
      dsimp only
      set Crows := (B1.rows.drop cut0).take nChimney
      set nChimney' := (Crows.filter fun row => !(row.all id)).length
      have hnC_le : nChimney' ≤ nChimney := by
        calc nChimney' ≤ Crows.length := List.length_filter_le _ _
          _ ≤ nChimney := List.length_take_le _ _
      refine ⟨hnC_le, le_rfl, fun h _ => by omega, ?_, hodd_le⟩
      refine ⟨hodd, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, by have := hinv.2.2.2.2.1; omega, ?_, ?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx⟩ := hbelow_f ⟨y.val, y.isLt⟩ hy
        exact ⟨⟨x.val, x.isLt⟩, by rw [hsettle_below y hy]; exact hx⟩
      · intro y hy x hx
        rw [hsettle_below y (by have := hinv.2.1; omega)]
        exact hinv.2.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy ⟨x.val, x.isLt⟩ hx
      · intro y hy1 hy2 x
        set i := y.val - cut0
        have hi_lt : i < nChimney' := by omega
        have hS_split : (B1.rows.drop cut0).filter (fun row => !(row.all id)) =
            Crows.filter (fun row => !(row.all id)) ++
            ((B1.rows.drop cut0).drop nChimney).filter (fun row => !(row.all id)) := by
          conv_lhs => rw [← List.take_append_drop nChimney (B1.rows.drop cut0)]
          rw [List.filter_append]
        have hi_S : i < ((B1.rows.drop cut0).filter (fun row => !(row.all id))).length := by
          rw [hS_split, List.length_append]; omega
        have hcell := settle_rows_drop_eq (cut := cut0) (q := q) hcut_le hbelow_f hcells0 i hi_S ⟨x.val, x.isLt⟩
        have hy_eq : (⟨cut0 + i, by omega⟩ : Fin (B.settle q).height) = y := by
          ext; dsimp [i]; omega
        rw [hy_eq] at hcell
        rw [hcell]
        set row := ((B1.rows.drop cut0).filter (fun row => !(row.all id)))[i]
        have hrow_filt : row ∈ Crows.filter (fun row => !(row.all id)) := by
          have h1 : row = (Crows.filter (fun row => !(row.all id)))[i]'(hi_lt) := by
            simp only [row, hS_split, List.getElem_append_left hi_lt]
          rw [h1]; exact List.getElem_mem hi_lt
        have hrow_mem : row ∈ Crows := (List.mem_filter.mp hrow_filt).1
        have hrow_not_full : row.all id = false := by
          have h2 := (List.mem_filter.mp hrow_filt).2
          simpa using h2
        rw [List.mem_iff_getElem] at hrow_mem
        rcases hrow_mem with ⟨k, hk, hrow_eq⟩
        simp only [Crows, List.length_take, List.length_drop, hB1_rows_len] at hk
        have hk_c : k < nChimney := lt_of_lt_of_le hk (Nat.min_le_left _ _)
        have hk_H : cut0 + k < B.height := by have := hinv.2.2.2.2.1; omega
        have hrow_val : row = List.ofFn (fun x' : Fin B1.width => B1.cell ⟨cut0 + k, hk_H⟩ x') := by
          rw [← hrow_eq]
          simp only [Crows, List.getElem_take, List.getElem_drop, Board.rows, List.getElem_ofFn]
        rw [hrow_val]
        have hx_lt : x.val < B1.width := x.isLt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx_lt, ↓reduceDIte, Option.getD_some]
        by_cases hxeq : x.val = splitX - 1
        · simp only [hxeq, ne_eq, not_true_eq_false, decide_false]
          -- If B1.cell (cut0 + k) (splitX - 1) were true, the entire row would be full!
          by_contra htrue
          have hbt : B1.cell ⟨cut0 + k, hk_H⟩ ⟨splitX - 1, by omega⟩ = true :=
            Bool.eq_true_of_not_eq_false htrue
          have hall : ∀ x' : Fin B1.width, B1.cell ⟨cut0 + k, hk_H⟩ x' = true := by
            intro x'
            by_cases hx' : x'.val = splitX - 1
            · have : x' = ⟨splitX - 1, by omega⟩ := by ext; exact hx'
              rw [this]; exact hbt
            · have hB := hinv.2.2.2.2.2.2.2.1 ⟨cut0 + k, hk_H⟩ (by dsimp; omega) (by dsimp; omega) ⟨x'.val, x'.isLt⟩
              have hBt : B.cell ⟨cut0 + k, hk_H⟩ ⟨x'.val, x'.isLt⟩ = true := by rw [hB]; simp [hx']
              change (B.cell ⟨cut0 + k, hk_H⟩ ⟨x'.val, x'.isLt⟩ || _) = true
              rw [hBt]; rfl
          have hfull := (row_all_id_iff B1 ⟨cut0 + k, hk_H⟩).mpr hall
          rw [← hrow_val, hrow_not_full] at hfull
          simp at hfull
        · have hB := hinv.2.2.2.2.2.2.2.1 ⟨cut0 + k, hk_H⟩ (by dsimp; omega) (by dsimp; omega) ⟨x.val, x.isLt⟩
          have hBt : B.cell ⟨cut0 + k, hk_H⟩ ⟨x.val, x.isLt⟩ = true := by rw [hB]; simp [hxeq]
          simp only [hxeq, ne_eq, not_false_eq_true, decide_true]
          change (B.cell ⟨cut0 + k, hk_H⟩ ⟨x.val, x.isLt⟩ || _) = true
          rw [hBt]; rfl
      · intro y hy1 hy2; omega
    · -- `nChimney = 0` and `1 ≤ nUpper`
      have hnC : nChimney = 0 := by omega
      subst hnC
      have hp_eq : p = (0, (((B1.rows.drop cut0).take nUpper).filter fun row => !(row.all id)).length) := by
        simp [p, nextChimneyUpper, hnU, B1]
      rw [hp_eq]
      dsimp only
      set Urows := (B1.rows.drop cut0).take nUpper
      set nUpper' := (Urows.filter fun row => !(row.all id)).length
      have hnU_le : nUpper' ≤ nUpper := by
        calc nUpper' ≤ Urows.length := List.length_filter_le _ _
          _ ≤ nUpper := List.length_take_le _ _
      refine ⟨le_rfl, hnU_le, fun _ h => by omega, ?_, hodd_le⟩
      refine ⟨hodd, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, by have := hinv.2.2.2.2.1; omega, ?_, ?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx⟩ := hbelow_f ⟨y.val, y.isLt⟩ hy
        exact ⟨⟨x.val, x.isLt⟩, by rw [hsettle_below y hy]; exact hx⟩
      · intro y hy x hx
        rw [hsettle_below y (by have := hinv.2.1; omega)]
        exact hinv.2.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy ⟨x.val, x.isLt⟩ hx
      · intro y hy1 hy2; omega
      · intro y hy1 hy2 x hx
        set i := y.val - cut0
        have hi_lt : i < nUpper' := by omega
        have hS_split : (B1.rows.drop cut0).filter (fun row => !(row.all id)) =
            Urows.filter (fun row => !(row.all id)) ++
            ((B1.rows.drop cut0).drop nUpper).filter (fun row => !(row.all id)) := by
          conv_lhs => rw [← List.take_append_drop nUpper (B1.rows.drop cut0)]
          rw [List.filter_append]
        have hi_S : i < ((B1.rows.drop cut0).filter (fun row => !(row.all id))).length := by
          rw [hS_split, List.length_append]; omega
        have hcell := settle_rows_drop_eq (cut := cut0) (q := q) hcut_le hbelow_f hcells0 i hi_S ⟨x.val, x.isLt⟩
        have hy_eq : (⟨cut0 + i, by omega⟩ : Fin (B.settle q).height) = y := by
          ext; dsimp [i]; omega
        rw [hy_eq] at hcell
        rw [hcell]
        set row := ((B1.rows.drop cut0).filter (fun row => !(row.all id)))[i]
        have hrow_mem : row ∈ Urows := by
          have h1 : row = (Urows.filter (fun row => !(row.all id)))[i]'(hi_lt) := by
            simp only [row, hS_split, List.getElem_append_left hi_lt]
          rw [h1]; exact (List.mem_filter.mp (List.getElem_mem hi_lt)).1
        rw [List.mem_iff_getElem] at hrow_mem
        rcases hrow_mem with ⟨k, hk, hrow_eq⟩
        simp only [Urows, List.length_take, List.length_drop, hB1_rows_len] at hk
        have hk_up : k < nUpper := lt_of_lt_of_le hk (Nat.min_le_left _ _)
        have hk_H : cut0 + k < B.height := by have := hinv.2.2.2.2.1; omega
        have hrow_val : row = List.ofFn (fun x' : Fin B1.width => B1.cell ⟨cut0 + k, hk_H⟩ x') := by
          rw [← hrow_eq]
          simp only [Urows, List.getElem_take, List.getElem_drop, Board.rows, List.getElem_ofFn]
        rw [hrow_val]
        have hx_lt : x.val < B1.width := x.isLt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hx_lt, ↓reduceDIte, Option.getD_some]
        have hB_true := hinv.2.2.2.2.2.2.2.2 ⟨cut0 + k, hk_H⟩ (by dsimp; omega) (by dsimp; omega) ⟨x.val, x.isLt⟩ hx
        simp [B1, Board.insert, hB_true]

/-- A `.Sq` piece played on a board satisfying `ChimneySealInv` with `1 ≤ nChimney`
cannot touch any row `< cut0 + nChimney`, preserves `nChimney`, and satisfies
`oddRowsAboveL cut0 (B.settle q) + B.gain q = oddRowsAboveL cut0 B`. -/
lemma chimneySealInv_sq_step {R : Rotation} (hReason : Reasonable R)
    {B : Board} {cut0 splitX upperSplitX nChimney nUpper : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nChimney nUpper)
    (hchim_pos : 1 ≤ nChimney)
    {q : PieceState} (htraj : Trajectory R B .Sq q) :
    ChimneySealInv (B.settle q) cut0 splitX upperSplitX nChimney 0 ∧
    oddRowsAboveL cut0 (B.settle q) + B.gain q = oddRowsAboveL cut0 B := by
  have hseal0 := chimneySealInv_sealed_cut0 hinv
  have hspawn0 := spawn_cells_ge_of_height (B := B) (cut := cut0) (by have := hinv.2.2.2.2.1; omega)
  have hcells0 : ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 :=
    trajectory_above_seal hReason hseal0 (by omega) hspawn0 htraj
  have hk : q.kind = .Sq := by
    have hinv_k : ∀ q1 q2, Move R B q1 q2 → q1.kind = .Sq → q2.kind = .Sq := by
      intro q1 q2 hm hk1
      rcases hm with ⟨_, _, _, ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩⟩
      · simp only [Rotation.apply]; split <;> exact hk1
      · exact hk1
      · exact hk1
      · exact hk1
      · exact hk1
    have hkind : ∀ q', Relation.ReflTransGen (Move R B) (spawn B .Sq) q' → q'.kind = .Sq := by
      intro q' hr
      induction hr with
      | refl => rfl
      | tail _ hstep ih => exact hinv_k _ _ hstep ih
    exact hkind q htraj.2.1
  have hclear : B.Clear q := by
    cases htraj.2.1 with
    | refl => exact htraj.1
    | tail _ hstep => exact hstep.2.2.1
  have hcells_sq : q.cells = [(q.position.1, q.position.2), (q.position.1 + 1, q.position.2),
      (q.position.1, q.position.2 - 1), (q.position.1 + 1, q.position.2 - 1)] := by
    simp [PieceState.cells, hk, Piece.base, sub_eq_add_neg]
  have hnot_chim : ∀ y : ℤ, B.occupied (q.position.1, y) = false →
      B.occupied (q.position.1 + 1, y) = false → (cut0 : ℤ) ≤ y → ((cut0 + nChimney : ℕ) : ℤ) ≤ y := by
    intro y ha hb hy_ge
    by_contra hlt
    push Not at hlt
    have hy0 : 0 ≤ y := by omega
    have hyH : y < B.height := by have := hinv.2.2.2.2.1; omega
    simp only [Board.occupied, hy0, hyH, and_self, ↓reduceDIte] at ha hb
    split_ifs at ha with hxa
    split_ifs at hb with hxb
    have hca := hinv.2.2.2.2.2.2.2.1 ⟨y.toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega)
      ⟨q.position.1.toNat, by omega⟩
    have hcb := hinv.2.2.2.2.2.2.2.1 ⟨y.toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega)
      ⟨(q.position.1 + 1).toNat, by omega⟩
    rw [hca] at ha; rw [hcb] at hb
    simp at ha hb; omega
  have hcells_ge_chim : ∀ z ∈ q.cells, ((cut0 + nChimney : ℕ) : ℤ) ≤ z.2 := by
    have h1 := hnot_chim q.position.2 (hclear _ (by simp [hcells_sq]))
      (hclear _ (by simp [hcells_sq])) (hcells0 (q.position.1, q.position.2) (by simp [hcells_sq]))
    have h2 := hnot_chim (q.position.2 - 1) (hclear _ (by simp [hcells_sq]))
      (hclear _ (by simp [hcells_sq])) (hcells0 (q.position.1, q.position.2 - 1) (by simp [hcells_sq]))
    intro z hz
    rw [hcells_sq] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> omega
  have hbelow_fU : ∀ y : Fin B.height, y.val < cut0 + nChimney → ∃ x : Fin B.width, B.cell y x = false := by
    intro y hy
    by_cases hy0 : y.val < cut0
    · exact hinv.2.2.2.2.2.1 y hy0
    · refine ⟨⟨splitX - 1, by have := hinv.2.2.2.1; omega⟩, ?_⟩
      rw [hinv.2.2.2.2.2.2.2.1 y (by omega) hy]; simp
  obtain ⟨hsettle_belowU, _, _⟩ := settle_below_and_oddRows hinv.1
    (by have := hinv.2.2.2.2.1; omega) hbelow_fU hcells_ge_chim
  obtain ⟨hsettle_below0, hodd_eq, _⟩ := settle_below_and_oddRows hinv.1
    (by have := hinv.2.2.2.2.1; omega) hinv.2.2.2.2.2.1 hcells0
  -- Parity of every row is preserved by `.Sq`
  have hB1_odd : oddRowsAboveL cut0 (B.insert q) = oddRowsAboveL cut0 B := by
    unfold oddRowsAboveL
    have hmap : ∀ (M : Board), (M.rows.drop cut0).map (fun row => (row.count true) % 2 == 1) =
        (List.finRange M.height |>.drop cut0).map fun y =>
          ((List.ofFn fun x : Fin M.width => M.cell y x).count true) % 2 == 1 := by
      intro M; simp only [Board.rows, List.ofFn_eq_map, ← List.map_drop, List.map_map]; rfl
    have hlen_filter : ∀ (L : List (List Bool)) (p : List Bool → Bool),
        (L.filter p).length = (L.map p).count true := by
      intro L p; induction L with
      | nil => simp
      | cons a l ih => cases h : p a <;> simp [h, ih]
    rw [hlen_filter, hlen_filter, hmap (B.insert q), hmap B]
    congr 1
    apply List.map_congr_left
    intro y _
    exact congrArg (· == 1) (sq_insert_count_parity B q hk hclear y)
  have hsettleH : (B.settle q).height = B.height := rfl
  refine ⟨?_, by rw [hodd_eq, hB1_odd]⟩
  refine ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, by have := hinv.2.2.2.2.1; omega, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hinv.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy
    exact ⟨⟨x.val, x.isLt⟩, by rw [hsettle_below0 y hy]; exact hx⟩
  · intro y hy x hx
    rw [hsettle_below0 y (by have := hinv.2.1; omega)]
    exact hinv.2.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy ⟨x.val, x.isLt⟩ hx
  · intro y hy1 hy2 x
    rw [hsettle_belowU y hy2]
    exact hinv.2.2.2.2.2.2.2.1 ⟨y.val, y.isLt⟩ hy1 hy2 ⟨x.val, x.isLt⟩
  · intro y hy1 hy2; omega

/-- Any `.Sq` play on a board with `ChimneySealInv` and `1 ≤ nChimney` clears at most
`oddRowsAboveL cut0 B` rows. -/
lemma chimneySealInv_sq_play_bound {R : Rotation} (hReason : Reasonable R)
    {B B' : Board} {cut0 splitX upperSplitX nChimney nUpper N v : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nChimney nUpper)
    (hchim_pos : 1 ≤ nChimney)
    {qs : List PieceState}
    (hplay : Play R B (List.replicate N .Sq) qs B' v) :
    v ≤ oddRowsAboveL cut0 B := by
  have hmain : ∀ {B0 B1 : Board} {ts : List Piece} {qs : List PieceState} {v : ℕ} {nU : ℕ},
      Play R B0 ts qs B1 v →
      (∀ t ∈ ts, t = .Sq) →
      ChimneySealInv B0 cut0 splitX upperSplitX nChimney nU →
      v + oddRowsAboveL cut0 B1 = oddRowsAboveL cut0 B0 := by
    intro B0 B1 ts qs v nU hp hts hi
    induction hp generalizing nU with
    | stop _ _ => simp
    | step htraj hrest ih =>
      rename_i Bcur t ts' q qs' Bfin v'
      have ht : t = .Sq := hts t (List.mem_cons_self ..)
      subst ht
      obtain ⟨hi', hstep⟩ := chimneySealInv_sq_step hReason hi hchim_pos htraj
      have hih := ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) hi'
      omega
  have h1 := hmain hplay (fun t ht => (List.mem_replicate.mp ht).2) hinv
  omega

/-- Tracking `ChimneySealInv` across a prefix play: if `trackChimneyUpper` never reaches `0`,
then at the end `1 ≤ nC` and `v + oddRowsAboveL cut0 Bmid ≤ oddRowsAboveL cut0 B0 + 4 * ts.length`. -/
lemma chimneySealInv_prefix_play {R : Rotation} (hReason : Reasonable R)
    {B0 Bmid : Board} {cut0 splitX upperSplitX nC0 nU0 : ℕ}
    (hinv0 : ChimneySealInv B0 cut0 splitX upperSplitX nC0 nU0)
    (hC0_pos : 1 ≤ nC0)
    {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hplay : Play R B0 ts qs Bmid v)
    (hne0 : ∀ {B1 : Board} {ts1 : List Piece} {qs1 : List PieceState} {v1 : ℕ},
      Play R B0 ts1 qs1 B1 v1 →
      (∃ ts2, ts = ts1 ++ ts2) →
      1 ≤ (trackChimneyUpper B0 cut0 nC0 nU0 qs1).1 + (trackChimneyUpper B0 cut0 nC0 nU0 qs1).2) :
    let p := trackChimneyUpper B0 cut0 nC0 nU0 qs
    1 ≤ p.1 ∧
    ChimneySealInv Bmid cut0 splitX upperSplitX p.1 p.2 ∧
    v + oddRowsAboveL cut0 Bmid ≤ oddRowsAboveL cut0 B0 + 4 * ts.length := by
  have hgen : ∀ {Bcur Bfin : Board} {ts_cur : List Piece} {qs_cur : List PieceState}
      {v_cur nC_cur nU_cur : ℕ},
      Play R Bcur ts_cur qs_cur Bfin v_cur →
      ChimneySealInv Bcur cut0 splitX upperSplitX nC_cur nU_cur →
      1 ≤ nC_cur →
      (∀ (qs_p : List PieceState) (B1 : Board) (v1 k : ℕ),
        k ≤ ts_cur.length →
        Play R Bcur (ts_cur.take k) qs_p B1 v1 →
        1 ≤ (trackChimneyUpper Bcur cut0 nC_cur nU_cur qs_p).1 +
          (trackChimneyUpper Bcur cut0 nC_cur nU_cur qs_p).2) →
      let p := trackChimneyUpper Bcur cut0 nC_cur nU_cur qs_cur
      1 ≤ p.1 ∧
      ChimneySealInv Bfin cut0 splitX upperSplitX p.1 p.2 ∧
      v_cur + oddRowsAboveL cut0 Bfin ≤ oddRowsAboveL cut0 Bcur + 4 * ts_cur.length := by
    intro Bcur Bfin ts_cur qs_cur v_cur nC_cur nU_cur hp
    induction hp generalizing nC_cur nU_cur with
    | stop B ts' =>
      intro hi hC _
      exact ⟨hC, hi, by simp [trackChimneyUpper]⟩
    | step htraj hrest ih =>
      rename_i B1 t ts' q qs' Bfin v'
      intro hi hC hno0
      obtain ⟨_, _, hkeep, hi1, hodd1⟩ :=
        chimneySealInv_step hReason hi (by omega) htraj
      set p1 := nextChimneyUpper B1 cut0 nC_cur nU_cur q
      have hpos1 : 1 ≤ p1.1 + p1.2 := by
        have h1 : Play R B1 ((t :: ts').take 1) [q] (B1.settle q) (B1.gain q + 0) :=
          Play.step htraj (Play.stop _ _)
        simpa [trackChimneyUpper, p1] using hno0 [q] (B1.settle q) (B1.gain q + 0) 1 (by simp) h1
      have hC1 : 1 ≤ p1.1 := by
        by_cases hU0 : p1.2 = 0
        · omega
        · have hU_orig : 1 ≤ nU_cur := by
            have := (chimneySealInv_step hReason hi (by omega) htraj).2.1
            omega
          rw [hkeep hU_orig hC]; exact hC
      have hno0' : ∀ (qs_p : List PieceState) (B2 : Board) (v2 k : ℕ),
          k ≤ ts'.length →
          Play R (B1.settle q) (ts'.take k) qs_p B2 v2 →
          1 ≤ (trackChimneyUpper (B1.settle q) cut0 p1.1 p1.2 qs_p).1 +
            (trackChimneyUpper (B1.settle q) cut0 p1.1 p1.2 qs_p).2 := by
        intro qs_p B2 v2 k hk hp2
        have h1 : Play R B1 ((t :: ts').take (k + 1)) (q :: qs_p) B2 (B1.gain q + v2) :=
          Play.step htraj hp2
        simpa [trackChimneyUpper, p1] using hno0 (q :: qs_p) B2 (B1.gain q + v2) (k + 1) (by simp; omega) h1
      obtain ⟨hCf, hif, hoddf⟩ := ih hi1 hC1 hno0'
      refine ⟨hCf, hif, ?_⟩
      simp only [List.length_cons]
      omega
  exact hgen hplay hinv0 hC0_pos (fun qs_p B1 v1 k _ hp1 =>
    hne0 hp1 ⟨ts.drop k, (List.take_append_drop k ts).symm⟩)

/-- **Outer Shell Theorem:** If no prefix of `prefixPieces P pad K` can reduce
`trackChimneyUpper` to `0`, then `paddedReservoir_soundness` holds! -/
theorem soundness_of_no_clear_all_chimney
    (R : Rotation) (hReason : Reasonable R)
    (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hK : 1 ≤ K) (hst : 3 ≤ st)
    (hno_clear : ∀ {B1 : Board} {ts1 : List Piece} {qs1 : List PieceState} {v1 : ℕ},
      Play R (paddedReservoirBoard P pad K st r) ts1 qs1 B1 v1 →
      (∃ ts2, prefixPieces P pad K = ts1 ++ ts2) →
      1 ≤ (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).1 +
      (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).2) :
    ∀ v, Attainable R (paddedReservoirGame P pad K st r) v →
      v ≤ paddedNoBound P pad K st := by
  intro v ⟨qs, Bfin, hplay⟩
  rw [paddedReservoirGame_pieces_eq] at hplay
  obtain ⟨qs_pre, qs_sq, Bmid, v_pre, v_sq, _, rfl, hp_pre, hp_sq, _⟩ := play_append_split hplay
  have hinv0 := chimneySealInv_init P pad K st r hpad hst
  obtain ⟨hC_pos, hinv_mid, hodd_pre⟩ :=
    chimneySealInv_prefix_play hReason hinv0 (by omega) hp_pre hno_clear
  have hv_sq : v_sq ≤ oddRowsAboveL (r + 2) Bmid :=
    chimneySealInv_sq_play_bound hReason hinv_mid hC_pos hp_sq
  have hodd0 := oddRowsAboveL_init_le P pad K st r hpad
  have hplen := prefixPieces_length P pad K
  have hbase_le : baseHeight P ≤ (baseBoard P st).height := by simp [baseBoard]; omega
  unfold paddedNoBound
  omega

/-! ### Upper Board Extraction (`dropRows`) and `BucketFrame` Transfer -/

/-- Shift a `PieceState` vertically down by `cut`. -/
def shiftDown (cut : ℕ) (q : PieceState) : PieceState :=
  { q with position := (q.position.1, q.position.2 - cut) }

lemma shiftDown_cells (cut : ℕ) (q : PieceState) :
    (shiftDown cut q).cells = q.cells.map (fun z => (z.1, z.2 - (cut : ℤ))) := by
  simp only [shiftDown, PieceState.cells, List.map_map]
  apply List.map_congr_left
  intro z _
  ext
  · rfl
  · dsimp; exact sub_add_eq_add_sub _ _ _

lemma dropRows_occupied_ge (B : Board) (cut : ℕ) (hcut : cut ≤ B.height) (z : Cell)
    (hz : (cut : ℤ) ≤ z.2) :
    (dropRows B cut).occupied (z.1, z.2 - cut) = B.occupied z := by
  unfold Board.occupied dropRows
  dsimp only
  by_cases hy : z.2 < B.height
  · have hy1 : 0 ≤ z.2 - cut ∧ z.2 - cut < (B.height - cut : ℕ) := by omega
    have hy2 : 0 ≤ z.2 ∧ z.2 < B.height := by omega
    rw [dif_pos hy1, dif_pos hy2]
    split_ifs with hx
    · congr 1
      ext; dsimp; omega
    · rfl
  · have hy1 : ¬ (0 ≤ z.2 - cut ∧ z.2 - cut < (B.height - cut : ℕ)) := by omega
    have hy2 : ¬ (0 ≤ z.2 ∧ z.2 < B.height) := by omega
    rw [dif_neg hy1, dif_neg hy2]

lemma dropRows_clear_iff {B : Board} {cut : ℕ} (hcut : cut ≤ B.height) {q : PieceState}
    (hge : ∀ z ∈ q.cells, (cut : ℤ) ≤ z.2) :
    (dropRows B cut).Clear (shiftDown cut q) ↔ B.Clear q := by
  unfold Board.Clear
  rw [shiftDown_cells]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h z hz
    rw [← dropRows_occupied_ge B cut hcut z (hge z hz)]
    exact h z hz
  · intro h z hz
    rw [dropRows_occupied_ge B cut hcut z (hge z hz)]
    exact h z hz

lemma dropRows_apply_eq {R : Rotation} {B : Board} {cut : ℕ} (hcut : cut ≤ B.height)
    {q : PieceState} (hpos : (cut : ℤ) + R.radius ≤ q.position.2) (cw : Bool) :
    R.apply (dropRows B cut) (shiftDown cut q) cw = shiftDown cut (R.apply B q cw) := by
  unfold Rotation.apply
  have hpatch : (fun y x : Fin (2 * R.radius + 1) =>
      (dropRows B cut).occupied ((shiftDown cut q).position.1 + (x.val : ℤ) - R.radius,
        (shiftDown cut q).position.2 + (y.val : ℤ) - R.radius)) =
      (fun y x : Fin (2 * R.radius + 1) =>
        B.occupied (q.position.1 + (x.val : ℤ) - R.radius,
          q.position.2 + (y.val : ℤ) - R.radius)) := by
    funext y x
    have h1 : (shiftDown cut q).position.1 + (x.val : ℤ) - R.radius =
        q.position.1 + (x.val : ℤ) - R.radius := rfl
    have h2 : (shiftDown cut q).position.2 + (y.val : ℤ) - R.radius =
        (q.position.2 + (y.val : ℤ) - R.radius) - cut := by dsimp [shiftDown]; omega
    rw [h1, h2]
    exact dropRows_occupied_ge B cut hcut
      (q.position.1 + (x.val : ℤ) - R.radius, q.position.2 + (y.val : ℤ) - R.radius)
      (by dsimp; omega)
  dsimp only
  rw [hpatch]
  simp only [shiftDown]
  cases R.rule q.kind q.orientation q.fixed cw _ with
  | none => rfl
  | some d =>
    simp only [PieceState.mk.injEq, Prod.mk.injEq, true_and, and_true]
    ring

lemma position_mem_cells_A (q : PieceState) : q.position ∈ q.cells := by
  have h0 : (0, 0) ∈ q.kind.base := by cases q.kind <;> decide
  have hcw : ∀ n : ℕ, clockwise^[n] (0, 0) = (0, 0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
  unfold PieceState.cells
  refine List.mem_map.mpr ⟨(0, 0), h0, ?_⟩
  by_cases h : q.kind = .Sq <;> simp [h, hcw]

lemma dropRows_spawn_eq (B : Board) (cut : ℕ) (hcut : cut ≤ B.height) (t : Piece) :
    spawn (dropRows B cut) t = shiftDown cut (spawn B t) := by
  unfold spawn shiftDown dropRows
  dsimp only
  simp only [PieceState.mk.injEq, Prod.mk.injEq, true_and, and_true]
  omega

lemma dropRows_insert_eq (B : Board) (cut : ℕ) (q : PieceState) :
    dropRows (B.insert q) cut = (dropRows B cut).insert (shiftDown cut q) := by
  unfold dropRows Board.insert
  dsimp only
  congr 1
  funext y x
  congr 1
  apply decide_eq_decide.mpr
  rw [shiftDown_cells]
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨((x.val : ℤ), ((cut + y.val : ℕ) : ℤ)), h, rfl, by omega⟩
  · rintro ⟨z, hz, hx, hy⟩
    have hz_eq : z = ((x.val : ℤ), ((cut + y.val : ℕ) : ℤ)) := by ext <;> omega
    rwa [← hz_eq]

/-- Transfer a `Move` on `B` to `dropRows B cut` when both states lie at `y ≥ cut + R.radius`. -/
lemma move_dropRows_transfer {R : Rotation} {B : Board} {cut : ℕ} (hcut : cut ≤ B.height)
    {q q' : PieceState} (hm : Move R B q q')
    (hge : ∀ z ∈ q.cells, (cut : ℤ) + R.radius ≤ z.2)
    (hge' : ∀ z ∈ q'.cells, (cut : ℤ) + R.radius ≤ z.2)
    (hge_down : ∀ z ∈ (translate q 0 (-1)).cells, (cut : ℤ) ≤ z.2) :
    Move R (dropRows B cut) (shiftDown cut q) (shiftDown cut q') := by
  rcases hm with ⟨hf, hcl, hcl', hstep⟩
  have hge0 : ∀ z ∈ q.cells, (cut : ℤ) ≤ z.2 := fun z hz => by have := hge z hz; omega
  have hge0' : ∀ z ∈ q'.cells, (cut : ℤ) ≤ z.2 := fun z hz => by have := hge' z hz; omega
  refine ⟨hf, (dropRows_clear_iff hcut hge0).mpr hcl, (dropRows_clear_iff hcut hge0').mpr hcl', ?_⟩
  rcases hstep with ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, hnot⟩
  · left
    refine ⟨d, ?_⟩
    exact (dropRows_apply_eq hcut (hge q.position (position_mem_cells_A q)) d).symm
  · right; left; simp [shiftDown, translate]
  · right; right; left; simp [shiftDown, translate]
  · right; right; right; left; simp [shiftDown, translate]; omega
  · right; right; right; right
    refine ⟨rfl, ?_⟩
    have htr : translate (shiftDown cut q) 0 (-1) = shiftDown cut (translate q 0 (-1)) := by
      simp [shiftDown, translate]; omega
    rw [htr, dropRows_clear_iff hcut hge_down]
    exact hnot

/-- `dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K)` satisfies
`BucketFrame _ (P.s + pad) (12 * pad + baseHeight P)`. -/
lemma dropRows_init_bucketFrame (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hst : 3 ≤ st) :
    BucketFrame (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
      (P.s + pad) (12 * pad + baseHeight P) := by
  set B0 := paddedReservoirBoard P pad K st r
  set cut := r + 2 + 4 * K
  refine ⟨rfl, ⟨P.target + 2 * pad, by unfold baseHeight; omega⟩, ?_, ?_⟩
  · simp [dropRows, B0, paddedReservoirBoard, baseBoard]; omega
  · intro j y hy
    have hcut_le : cut ≤ B0.height := by simp [cut, B0, paddedReservoirBoard, baseBoard]; omega
    have hdrop_h : (dropRows B0 cut).height = B0.height - cut := rfl
    have hy_lt : y < B0.height - cut := by
      simp [cut, B0, paddedReservoirBoard, baseBoard]; omega
    have hocc : ∀ x : ℕ, (hx : x < B0.width) →
        (dropRows B0 cut).occupied (x, y) = B0.cell ⟨cut + y, by omega⟩ ⟨x, hx⟩ := by
      intro x hx
      unfold Board.occupied dropRows
      dsimp only
      have h1 : (0 : ℤ) ≤ y ∧ (y : ℤ) < (B0.height - cut : ℕ) := by omega
      have h2 : (0 : ℤ) ≤ x ∧ (x : ℤ) < B0.width := by omega
      rw [dif_pos h1, dif_pos h2]
      simp
    have h1 : ¬ (cut + y < r) := by omega
    have h2 : ¬ (cut + y = r) := by omega
    have h3 : ¬ (cut + y = r + 1) := by omega
    have h4 : ¬ (cut + y < r + 2 + 4 * K) := by omega
    have hjlt : j.val < P.s + pad := j.isLt
    have hx5 : 6 * j.val + 5 < B0.width := by simp [B0, paddedReservoirBoard]; omega
    have hx3 : 6 * j.val + 3 < B0.width := by omega
    have hx4 : 6 * j.val + 4 < B0.width := by omega
    have hcast5 : 6 * (j.val : ℤ) + 5 = ((6 * j.val + 5 : ℕ) : ℤ) := by omega
    have hcast3 : 6 * (j.val : ℤ) + 3 = ((6 * j.val + 3 : ℕ) : ℤ) := by omega
    have hcast4 : 6 * (j.val : ℤ) + 4 = ((6 * j.val + 4 : ℕ) : ℤ) := by omega
    rw [hcast5, hcast3, hcast4, hocc _ hx5, hocc _ hx3, hocc _ hx4]
    by_cases h5 : cut + y < r + 2 + 4 * K + 12 * pad
    · refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        (simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte, decide_eq_true_eq]; omega)
    · have h6 : cut + y < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
      by_cases hj : j.val < P.s
      · have hx5s : 6 * j.val + 5 < 6 * P.s + 3 := by omega
        have hx3s : 6 * j.val + 3 < 6 * P.s + 3 := by omega
        have hx4s : 6 * j.val + 4 < 6 * P.s + 3 := by omega
        have hy_sub : ((cut + y : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) =
            ((y - 12 * pad : ℕ) : ℤ) := by omega
        have hy_base : y - 12 * pad < baseHeight P := by omega
        have hy_baseH : y - 12 * pad < (baseBoard P st).height := by simp [baseBoard]; omega
        have heval : ∀ (x : ℕ), (hx : x < 6 * P.s) →
            B0.cell ⟨cut + y, by omega⟩ ⟨x, by simp [B0, paddedReservoirBoard]; omega⟩ =
              bucketInitial x (y - 12 * pad) := by
          intro x hx
          simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show x < 6 * P.s + 3 by omega,
            ↓reduceIte]
          rw [hy_sub]
          unfold Board.occupied
          have h1' : (0 : ℤ) ≤ (y - 12 * pad : ℕ) ∧ ((y - 12 * pad : ℕ) : ℤ) < (baseBoard P st).height := by omega
          have h2' : (0 : ℤ) ≤ (x : ℕ) ∧ ((x : ℕ) : ℤ) < (baseBoard P st).width := by simp [baseBoard]; omega
          rw [dif_pos h1', dif_pos h2']
          simp [baseBoard, show ¬ (y - 12 * pad ≥ baseHeight P) by omega, hx]
        refine ⟨?_, fun hmod => ⟨?_, ?_⟩⟩
        · rw [heval (6 * j.val + 5) (by omega)]
          simp [bucketInitial]
        · rw [heval (6 * j.val + 3) (by omega)]
          have hmod' : (y - 12 * pad + 1) % 6 ≠ 5 := by omega
          simp [bucketInitial, hmod']
        · rw [heval (6 * j.val + 4) (by omega)]
          have hmod' : (y - 12 * pad + 1) % 6 ≠ 5 := by omega
          simp [bucketInitial, hmod']
      · refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
        · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5,
            show ¬ (6 * j.val + 5 < 6 * P.s + 3) by omega, ↓reduceIte, decide_eq_true_eq]
          exact h6
        · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5,
            show ¬ (6 * j.val + 3 < 6 * P.s + 3) by omega, ↓reduceIte, decide_eq_true_eq]
          exact h6
        · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5,
            show ¬ (6 * j.val + 4 < 6 * P.s + 3) by omega, ↓reduceIte, decide_eq_true_eq]
          exact h6

/-- Initially in `dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K)`,
every bucket `j < P.s` is `Unprepped` at height `h = 12 * pad + 4` with `gap = 2`. -/
lemma dropRows_init_unprepped (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (j : Fin P.s) :
    Unprepped (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
      j.val (12 * pad + baseHeight P) := by
  set B0 := paddedReservoirBoard P pad K st r
  set cut := r + 2 + 4 * K
  set H' := 12 * pad + baseHeight P
  refine ⟨12 * pad + 4, 2, by omega, ?_, by omega, Or.inr rfl, ?_⟩
  · simp [dropRows, cut, B0, paddedReservoirBoard, baseBoard, baseHeight]; omega
  · intro x y
    unfold bucketCell
    have hxj : 6 * j.val + x.val < B0.width := by
      have := j.isLt; have := x.isLt; simp [B0, paddedReservoirBoard]; omega
    have hy_lt : y.val < B0.height - cut := y.isLt
    have hcastx : 6 * (j.val : ℤ) + (x.val : ℤ) = ((6 * j.val + x.val : ℕ) : ℤ) := by omega
    rw [hcastx]
    have hocc : (dropRows B0 cut).occupied (((6 * j.val + x.val : ℕ) : ℤ), (y.val : ℤ)) =
        B0.cell ⟨cut + y.val, by omega⟩ ⟨6 * j.val + x.val, hxj⟩ := by
      unfold Board.occupied dropRows
      dsimp only
      rw [dif_pos (by omega), dif_pos (by omega)]
      simp only [Int.toNat_natCast]
    rw [hocc]
    have h1 : ¬ (cut + y.val < r) := by omega
    have h2 : ¬ (cut + y.val = r) := by omega
    have h3 : ¬ (cut + y.val = r + 1) := by omega
    have h4 : ¬ (cut + y.val < r + 2 + 4 * K) := by omega
    by_cases h5 : cut + y.val < r + 2 + 4 * K + 12 * pad
    · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte]
      have hne : 6 * j.val + x.val ≠ 6 * P.s + 2 := by have := j.isLt; have := x.isLt; omega
      have hylt : y.val < 12 * pad + 4 := by omega
      have hnot4 : ¬ (12 * pad + 4 ≤ y.val + 4) := by omega
      have hyltH : y.val < H' := by omega
      by_cases hx5 : x.val = 5
      · simp [hx5, hyltH]; omega
      · have hxlt5 : x.val < 5 := by have := x.isLt; omega
        simp [hne, hylt, hnot4, hxlt5]
    · have hxs : 6 * j.val + x.val < 6 * P.s := by have := j.isLt; have := x.isLt; omega
      have hxs3 : 6 * j.val + x.val < 6 * P.s + 3 := by omega
      simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, hxs3, ↓reduceIte]
      have hy_sub : ((cut + y.val : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) =
          ((y.val - 12 * pad : ℕ) : ℤ) := by omega
      rw [hy_sub]
      unfold Board.occupied
      have h1' : (0 : ℤ) ≤ (y.val - 12 * pad : ℕ) ∧
          ((y.val - 12 * pad : ℕ) : ℤ) < (baseBoard P st).height := by
        simp [B0, paddedReservoirBoard, cut] at hy_lt; omega
      have h2' : (0 : ℤ) ≤ (6 * j.val + x.val : ℕ) ∧
          ((6 * j.val + x.val : ℕ) : ℤ) < (baseBoard P st).width := by simp [baseBoard]; omega
      rw [dif_pos h1', dif_pos h2']
      simp only [baseBoard, Int.toNat_natCast]
      by_cases hyH : y.val - 12 * pad ≥ baseHeight P
      · simp only [hyH, ↓reduceIte]
        have hnotH : ¬ (y.val < H') := by omega
        have hnot4 : ¬ (y.val < 12 * pad + 4) := by unfold baseHeight at hyH; omega
        simp [hnotH, hnot4]
      · simp only [hyH, hxs, ↓reduceIte, bucketInitial]
        have hmodx : (6 * j.val + x.val) % 6 = x.val := by have := x.isLt; omega
        have hmody : (y.val - 12 * pad + 1) % 6 = (y.val + 1) % 6 := by omega
        have hyltH : y.val < H' := by omega
        rw [hmodx, hmody]
        have hxlt := x.isLt
        interval_cases hxv : x.val <;> simp [hyltH] <;> omega

/-! ### Exact Empty-Cell Area Accounting Above `r + 2` -/

/-- Number of `false` cells in a board `B` in rows `[yStart, yEnd)`. -/
def emptyCellsInRange (B : Board) (yStart yEnd : ℕ) : ℕ :=
  ∑ y ∈ Finset.Ico yStart yEnd,
    if hy : y < B.height then
      ((Finset.univ : Finset (Fin B.width)).filter fun x => B.cell ⟨y, hy⟩ x = false).card
    else 0

lemma basePieces_length_eq (P : ThreePartition) (hP : P.Valid) (hEven : Even P.target) :
    4 * (basePieces P).length =
      P.s * (20 * P.target + 64) + (6 * P.target + 24) := by
  have hnum : (numberPieces P).length = 5 * P.s * P.target + 15 * P.s := by
    unfold numberPieces
    rw [List.length_flatMap, List.map_ofFn, List.sum_ofFn]
    have hblk : ∀ a : ℕ, (integerBlock a).length = 5 * a + 5 := by
      intro a
      simp [integerBlock, initiator, filler, terminator]
      omega
    simp_rw [hblk]
    simp only [Function.comp_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.1, Finset.sum_const, Finset.card_fin]
    ring
  rcases hEven with ⟨m, hm⟩
  simp only [basePieces, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  rw [hnum, hm]
  have hdiv : 3 * (m + m) / 2 = 3 * m := by omega
  rw [hdiv]
  ring

/-- Exact count of empty cells in `paddedReservoirBoard P pad K st r` in rows
`[r + 2, r + 2 + 4 * K + 12 * pad + baseHeight P)`: equals `4 * ((basePieces P).length + 3 * pad + K)`. -/
lemma emptyCells_init_above_chimney (P : ThreePartition) (hP : P.Valid) (hEven : Even P.target)
    (pad K st r : ℕ) (hpad : 1 ≤ pad) :
    emptyCellsInRange (paddedReservoirBoard P pad K st r)
      (r + 2) (r + 2 + 4 * K + 12 * pad + baseHeight P) =
      4 * ((basePieces P).length + 3 * pad + K) := by
  set B0 := paddedReservoirBoard P pad K st r
  set y0 := r + 2
  set y1 := r + 2 + 4 * K
  set y2 := r + 2 + 4 * K + 12 * pad
  set y3 := r + 2 + 4 * K + 12 * pad + baseHeight P
  have hsplit1 : Finset.Ico y0 y3 = Finset.Ico y0 y1 ∪ Finset.Ico y1 y3 :=
    (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have hsplit2 : Finset.Ico y1 y3 = Finset.Ico y1 y2 ∪ Finset.Ico y2 y3 :=
    (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  unfold emptyCellsInRange
  rw [hsplit1, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive y0 y1 y3),
    hsplit2, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive y1 y2 y3)]
  -- Part 1: Chimney rows `[y0, y1)` have 1 empty cell per row -> `4 * K`
  have hpart1 : (∑ y ∈ Finset.Ico y0 y1,
      if hy : y < B0.height then
        ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
      else 0) = 4 * K := by
    have hterm : ∀ y ∈ Finset.Ico y0 y1,
        (if hy : y < B0.height then
          ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
        else 0) = 1 := by
      intro y hy
      rw [Finset.mem_Ico] at hy
      have hyH : y < B0.height := by simp [B0, paddedReservoirBoard, baseBoard, baseHeight]; omega
      rw [dif_pos hyH]
      set x0 : Fin B0.width := ⟨6 * (P.s + pad) - 1, by simp [B0, paddedReservoirBoard]; omega⟩
      have hset : (Finset.univ.filter fun x : Fin B0.width => B0.cell ⟨y, hyH⟩ x = false) = {x0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, x0]
        have h1 : ¬ y < r := by omega
        have h2 : ¬ y = r := by omega
        have h3 : ¬ y = r + 1 := by omega
        have h4 : y < r + 2 + 4 * K := by omega
        simp [B0, paddedReservoirBoard, h1, h2, h3, h4]
      rw [hset, Finset.card_singleton]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
  -- Part 2: Buffer rows `[y1, y2)` have 1 empty cell per row -> `12 * pad`
  have hpart2 : (∑ y ∈ Finset.Ico y1 y2,
      if hy : y < B0.height then
        ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
      else 0) = 12 * pad := by
    have hterm : ∀ y ∈ Finset.Ico y1 y2,
        (if hy : y < B0.height then
          ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
        else 0) = 1 := by
      intro y hy
      rw [Finset.mem_Ico] at hy
      have hyH : y < B0.height := by simp [B0, paddedReservoirBoard, baseBoard, baseHeight]; omega
      rw [dif_pos hyH]
      set x0 : Fin B0.width := ⟨6 * P.s + 2, by simp [B0, paddedReservoirBoard]⟩
      have hset : (Finset.univ.filter fun x : Fin B0.width => B0.cell ⟨y, hyH⟩ x = false) = {x0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, x0]
        have h1 : ¬ y < r := by omega
        have h2 : ¬ y = r := by omega
        have h3 : ¬ y = r + 1 := by omega
        have h4 : ¬ y < r + 2 + 4 * K := by omega
        have h5 : y < r + 2 + 4 * K + 12 * pad := by omega
        simp [B0, paddedReservoirBoard, h1, h2, h3, h4, h5]
      rw [hset, Finset.card_singleton]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
  -- Part 3: `baseBoard` rows `[y2, y3)` have `P.s * (20 * P.target + 64) + (6 * P.target + 24)` empty cells
  have hpart3 : (∑ y ∈ Finset.Ico y2 y3,
      if hy : y < B0.height then
        ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
      else 0) = P.s * (20 * P.target + 64) + (6 * P.target + 24) := by
    -- Reindex `y = y2 + k` for `k ∈ Finset.range (baseHeight P)`
    have hbij : (∑ y ∈ Finset.Ico y2 y3,
        if hy : y < B0.height then
          ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
        else 0) =
        ∑ k ∈ Finset.range (baseHeight P),
          (((Finset.range (6 * P.s)).filter (fun x => bucketInitial x k = false)).card +
          ((Finset.range 3).filter (fun d =>
            (if d = 0 then decide (k + 2 < baseHeight P)
             else if d = 1 then decide (k + 1 < baseHeight P)
             else decide (k + 2 = baseHeight P)) = false)).card) := by
      have hreindex : ∑ y ∈ Finset.Ico y2 y3,
          (if hy : y < B0.height then
            ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y, hy⟩ x = false).card
          else 0) =
          ∑ k ∈ Finset.range (baseHeight P),
            (if hy : y2 + k < B0.height then
              ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y2 + k, hy⟩ x = false).card
            else 0) := by
        apply Finset.sum_nbij (fun y => y - y2)
        · intro y hy; rw [Finset.mem_Ico] at hy; rw [Finset.mem_range]; omega
        · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb; dsimp at hab; omega
        · intro k hk; simp only [Finset.mem_coe, Finset.mem_range] at hk
          exact ⟨y2 + k, by simp only [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp; omega⟩
        · intro y hy; rw [Finset.mem_Ico] at hy
          have : y2 + (y - y2) = y := by omega
          rw [this]
      rw [hreindex]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hyH : y2 + k < B0.height := by simp [y2, B0, paddedReservoirBoard, baseBoard]; omega
      rw [dif_pos hyH]
      -- Split `Fin B0.width` into `x < 6 * P.s`, `6 * P.s ≤ x < 6 * P.s + 3`, `x ≥ 6 * P.s + 3`
      have hcard_eq : ((Finset.univ : Finset (Fin B0.width)).filter fun x => B0.cell ⟨y2 + k, hyH⟩ x = false).card =
          ((Finset.range (6 * P.s + 3)).filter fun x : ℕ =>
            (baseBoard P st).occupied ((x : ℤ), (k : ℤ)) = false).card := by
        apply Finset.card_nbij Fin.val
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have h1 : ¬ y2 + k < r := by omega
          have h2 : ¬ y2 + k = r := by omega
          have h3 : ¬ y2 + k = r + 1 := by omega
          have h4 : ¬ y2 + k < r + 2 + 4 * K := by omega
          have h5 : ¬ y2 + k < r + 2 + 4 * K + 12 * pad := by omega
          have h6 : y2 + k < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
          simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte] at hx
          split_ifs at hx with hxs
          · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
            refine ⟨hxs, ?_⟩
            have hy_sub : ((y2 + k : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = (k : ℤ) := by omega
            rwa [hy_sub] at hx
          · simp [h6] at hx
        · intro a _ b _ hab; exact Fin.ext hab
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
          refine ⟨⟨x, by simp [B0, paddedReservoirBoard]; omega⟩, ?_, rfl⟩
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          have h1 : ¬ y2 + k < r := by omega
          have h2 : ¬ y2 + k = r := by omega
          have h3 : ¬ y2 + k = r + 1 := by omega
          have h4 : ¬ y2 + k < r + 2 + 4 * K := by omega
          have h5 : ¬ y2 + k < r + 2 + 4 * K + 12 * pad := by omega
          simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, hx.1, ↓reduceIte]
          have hy_sub : ((y2 + k : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = (k : ℤ) := by omega
          rw [hy_sub]
          exact hx.2
      rw [hcard_eq]
      have hrange_split : Finset.range (6 * P.s + 3) =
          Finset.range (6 * P.s) ∪ Finset.Ico (6 * P.s) (6 * P.s + 3) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (6 * P.s)) (Finset.Ico (6 * P.s) (6 * P.s + 3)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
      rw [hrange_split, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
      have hocc_base : ∀ x : ℕ, x < 6 * P.s + 3 →
          (baseBoard P st).occupied (x, k) =
            (if x < 6 * P.s then bucketInitial x k
             else if x = 6 * P.s then decide (k + 2 < baseHeight P)
             else if x = 6 * P.s + 1 then decide (k + 1 < baseHeight P)
             else decide (k + 2 = baseHeight P)) := by
        intro x hx
        unfold Board.occupied
        have h1' : (0 : ℤ) ≤ k ∧ (k : ℤ) < (baseBoard P st).height := by simp [baseBoard]; omega
        have h2' : (0 : ℤ) ≤ x ∧ (x : ℤ) < (baseBoard P st).width := by simp [baseBoard]; omega
        rw [dif_pos h1', dif_pos h2']
        simp [baseBoard, show ¬ (k ≥ baseHeight P) by omega]
      congr 1
      · congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro ⟨hx1, hx2⟩
          rw [hocc_base x (by omega), if_pos hx1] at hx2
          exact ⟨hx1, hx2⟩
        · intro ⟨hx1, hx2⟩
          refine ⟨hx1, ?_⟩
          rw [hocc_base x (by omega), if_pos hx1]
          exact hx2
      · apply Finset.card_nbij (fun x => x - 6 * P.s)
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          have hnot : ¬ x < 6 * P.s := by omega
          have h1 := hx.2
          rw [hocc_base x (by omega), if_neg hnot] at h1
          have hd : x - 6 * P.s = 0 ∨ x - 6 * P.s = 1 ∨ x - 6 * P.s = 2 := by omega
          rcases hd with h | h | h
          · rw [h]; simpa [show x = 6 * P.s by omega] using h1
          · rw [h]; simpa [show x ≠ 6 * P.s by omega, show x = 6 * P.s + 1 by omega] using h1
          · rw [h]; simpa [show x ≠ 6 * P.s by omega, show x ≠ 6 * P.s + 1 by omega] using h1
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha hb
          dsimp at hab; omega
        · intro d hd
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd
          refine ⟨6 * P.s + d, ?_, by dsimp; omega⟩
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
          refine ⟨by omega, ?_⟩
          rw [hocc_base (6 * P.s + d) (by omega), if_neg (by omega)]
          have hd_lt : d < 3 := hd.1
          have h1 := hd.2
          interval_cases d <;> simp at h1 ⊢ <;> exact h1
    rw [hbij, Finset.sum_add_distrib]
    -- Compute bucket sum and lock sum
    have hbucket_row : ∀ k : ℕ,
        ((Finset.range (6 * P.s)).filter (fun x => bucketInitial x k = false)).card =
          P.s * ((if k < 4 then 1 else 3) + (if (k + 1) % 6 = 5 then 2 else 0)) := by
      intro k
      have hpart : ∀ n : ℕ,
          ((Finset.range (6 * n)).filter (fun x => bucketInitial x k = false)).card =
            n * ((if k < 4 then 1 else 3) + (if (k + 1) % 6 = 5 then 2 else 0)) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hsp : Finset.range (6 * (n + 1)) =
              Finset.range (6 * n) ∪ Finset.Ico (6 * n) (6 * n + 6) := by
            ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
          have hdj : Disjoint (Finset.range (6 * n)) (Finset.Ico (6 * n) (6 * n + 6)) := by
            rw [Finset.disjoint_left]; intro x h1 h2
            rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
          rw [hsp, Finset.filter_union,
            Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdj), ih]
          have h6 : ((Finset.Ico (6 * n) (6 * n + 6)).filter (fun x => bucketInitial x k = false)).card =
              (if k < 4 then 1 else 3) + (if (k + 1) % 6 = 5 then 2 else 0) := by
            have hshift : ((Finset.Ico (6 * n) (6 * n + 6)).filter (fun x => bucketInitial x k = false)).card =
                ((Finset.range 6).filter (fun d => bucketInitial d k = false)).card := by
              apply Finset.card_nbij (fun x => x - 6 * n)
              · intro x hx
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hx
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
                refine ⟨by omega, ?_⟩
                have hmod : (x - 6 * n) % 6 = x % 6 := by omega
                simpa [bucketInitial, hmod] using hx.2
              · intro a ha b hb hab
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha hb
                dsimp at hab; omega
              · intro d hd
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd
                refine ⟨6 * n + d, ?_, by dsimp; omega⟩
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
                refine ⟨by omega, ?_⟩
                have hmod : (6 * n + d) % 6 = d % 6 := by omega
                simpa [bucketInitial, hmod] using hd.2
            rw [hshift]
            have hfin6 : Finset.range 6 = {0, 1, 2, 3, 4, 5} := by decide
            rw [hfin6]
            by_cases hk4 : k < 4 <;> by_cases hk5 : (k + 1) % 6 = 5 <;>
              (simp [bucketInitial, hk4, hk5]; decide)
          rw [h6]; ring
      exact hpart P.s
    have hbucket_sum : (∑ k ∈ Finset.range (baseHeight P),
        ((Finset.range (6 * P.s)).filter (fun x => bucketInitial x k = false)).card) =
        P.s * (20 * P.target + 64) := by
      simp_rw [hbucket_row, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      have h1 : (∑ k ∈ Finset.range (baseHeight P), if k < 4 then 1 else 3) =
          18 * P.target + 58 := by
        have hsp : Finset.range (baseHeight P) = Finset.range 4 ∪ Finset.Ico 4 (baseHeight P) := by
          ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico, baseHeight]; omega
        have hdj : Disjoint (Finset.range 4) (Finset.Ico 4 (baseHeight P)) := by
          rw [Finset.disjoint_left]; intro k h1 h2
          rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
        rw [hsp, Finset.sum_union hdj]
        have ha : (∑ k ∈ Finset.range 4, if k < 4 then 1 else 3) = 4 := by decide
        have hb : (∑ k ∈ Finset.Ico 4 (baseHeight P), if k < 4 then 1 else 3) =
            3 * (baseHeight P - 4) := by
          have ht3 : ∀ k ∈ Finset.Ico 4 (baseHeight P), (if k < 4 then 1 else 3) = 3 := by
            intro k hk; rw [Finset.mem_Ico] at hk; simp [show ¬ k < 4 by omega]
          rw [Finset.sum_congr rfl ht3, Finset.sum_const, Nat.card_Ico, smul_eq_mul]; ring
        rw [ha, hb]; unfold baseHeight; omega
      have h2 : (∑ k ∈ Finset.range (baseHeight P), if (k + 1) % 6 = 5 then 2 else 0) =
          2 * P.target + 6 := by
        have hmod6 : ∀ m : ℕ, (∑ k ∈ Finset.range (6 * m), if (k + 1) % 6 = 5 then 2 else 0) = 2 * m := by
          intro m; induction m with
          | zero => simp
          | succ m ih =>
            have hsp : Finset.range (6 * (m + 1)) =
                Finset.range (6 * m) ∪ Finset.Ico (6 * m) (6 * m + 6) := by
              ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
            have hdj : Disjoint (Finset.range (6 * m)) (Finset.Ico (6 * m) (6 * m + 6)) := by
              rw [Finset.disjoint_left]; intro x h1 h2
              rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
            rw [hsp, Finset.sum_union hdj, ih]
            have h6 : (∑ k ∈ Finset.Ico (6 * m) (6 * m + 6), if (k + 1) % 6 = 5 then 2 else 0) = 2 := by
              have hshift : (∑ k ∈ Finset.Ico (6 * m) (6 * m + 6), if (k + 1) % 6 = 5 then 2 else 0) =
                  ∑ d ∈ Finset.range 6, if (d + 1) % 6 = 5 then 2 else 0 := by
                apply Finset.sum_nbij (fun k => k - 6 * m)
                · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
                · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb; dsimp at hab; omega
                · intro d hd; simp only [Finset.mem_coe, Finset.mem_range] at hd
                  exact ⟨6 * m + d, by simp only [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp; omega⟩
                · intro k hk; rw [Finset.mem_Ico] at hk
                  have : (k + 1) % 6 = (k - 6 * m + 1) % 6 := by omega
                  rw [this]
              rw [hshift]; decide
            rw [h6]; omega
        have hsp : Finset.range (baseHeight P) =
            Finset.range (6 * (P.target + 3)) ∪ Finset.Ico (6 * (P.target + 3)) (baseHeight P) := by
          ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico, baseHeight]; omega
        have hdj : Disjoint (Finset.range (6 * (P.target + 3)))
            (Finset.Ico (6 * (P.target + 3)) (baseHeight P)) := by
          rw [Finset.disjoint_left]; intro k h1 h2
          rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
        rw [hsp, Finset.sum_union hdj, hmod6 (P.target + 3)]
        have htail : (∑ k ∈ Finset.Ico (6 * (P.target + 3)) (baseHeight P),
            if (k + 1) % 6 = 5 then 2 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk; rw [Finset.mem_Ico] at hk; unfold baseHeight at hk
          simp [show (k + 1) % 6 ≠ 5 by omega]
        rw [htail]; omega
      omega
    have hlock_sum : (∑ k ∈ Finset.range (baseHeight P),
        ((Finset.range 3).filter (fun d =>
          (if d = 0 then decide (k + 2 < baseHeight P)
           else if d = 1 then decide (k + 1 < baseHeight P)
           else decide (k + 2 = baseHeight P)) = false)).card) = 6 * P.target + 24 := by
      have hterm : ∀ k ∈ Finset.range (baseHeight P),
          ((Finset.range 3).filter (fun d =>
            (if d = 0 then decide (k + 2 < baseHeight P)
             else if d = 1 then decide (k + 1 < baseHeight P)
             else decide (k + 2 = baseHeight P)) = false)).card =
            if k + 2 < baseHeight P then 1
            else if k + 2 = baseHeight P then 1
            else 3 := by
        intro k hk
        rw [Finset.mem_range] at hk
        have h3 : Finset.range 3 = {0, 1, 2} := by decide
        rw [h3]
        by_cases h1 : k + 2 < baseHeight P
        · have h2 : k + 1 < baseHeight P := by omega
          have h3' : k + 2 ≠ baseHeight P := by omega
          simp [h1, h2, h3']; decide
        · by_cases h2 : k + 2 = baseHeight P
          · have h3' : k + 1 < baseHeight P := by omega
            simp [h2, h3']; decide
          · have h3' : ¬ k + 1 < baseHeight P := by omega
            simp [h1, h2, h3']
      rw [Finset.sum_congr rfl hterm]
      have hsp1 : Finset.range (baseHeight P) =
          Finset.range (baseHeight P - 1) ∪ {baseHeight P - 1} := by
        ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, baseHeight]; omega
      have hdj1 : Disjoint (Finset.range (baseHeight P - 1)) {baseHeight P - 1} := by
        rw [Finset.disjoint_singleton_right, Finset.mem_range]; omega
      rw [hsp1, Finset.sum_union hdj1, Finset.sum_singleton]
      have htop : (if baseHeight P - 1 + 2 < baseHeight P then 1
          else if baseHeight P - 1 + 2 = baseHeight P then 1 else 3) = 3 := by
        unfold baseHeight; split_ifs <;> omega
      rw [htop]
      have hbot : (∑ k ∈ Finset.range (baseHeight P - 1),
          if k + 2 < baseHeight P then 1 else if k + 2 = baseHeight P then 1 else 3) =
          baseHeight P - 1 := by
        have ht1 : ∀ k ∈ Finset.range (baseHeight P - 1),
            (if k + 2 < baseHeight P then 1 else if k + 2 = baseHeight P then 1 else 3) = 1 := by
          intro k hk; rw [Finset.mem_range] at hk
          by_cases h1 : k + 2 < baseHeight P <;> simp [h1]
          omega
        rw [Finset.sum_congr rfl ht1, Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
      rw [hbot]; unfold baseHeight; omega
    rw [hbucket_sum, hlock_sum]
  rw [hpart1, hpart2, hpart3]
  have hbp := basePieces_length_eq P hP hEven
  omega

end TetrisHard.Rows.Padded

namespace TetrisHard.Rows.Padded.Carbon

open TetrisHard.Rows
open TetrisHard.Rows.Padded

/-! ### Part C-1: Exact Zero-Waste Reduction, Chimney Mod-4 Invariant, and Phase-1 Lifting -/

/-- For `0 < P.s` and `¬ P.HasSolution`, we must have `2 ≤ P.s`. -/
lemma two_le_s_of_not_hasSolution {P : ThreePartition} (hP : P.Valid) (hs : 0 < P.s)
    (hno : ¬ P.HasSolution) : 2 ≤ P.s := by
  by_contra hlt
  have hs1 : P.s = 1 := by omega
  apply hno
  refine ⟨fun _ => ⟨0, by omega⟩, fun j => ?_⟩
  have hj : j = ⟨0, by omega⟩ := by ext; omega
  subst hj
  have hfilt : (Finset.univ.filter fun _ : Fin (3 * P.s) => (⟨0, by omega⟩ : Fin P.s) = ⟨0, by omega⟩) =
      Finset.univ := by simp
  rw [hfilt, hP.1, hs1, one_mul]

/-- Pieces of `prefixPieces` before the final reservoir-unlocking `.RG`. -/
def mainPieces (P : ThreePartition) (pad K : ℕ) : List Piece :=
  basePieces P ++ List.replicate (3 * pad) .I ++ List.replicate K .I

/-- Bucket-filling pieces before the first lock `.RG`. -/
def phase1Pieces (P : ThreePartition) : List Piece :=
  numberPieces P ++ List.replicate P.s .I

/-- Lock, buffer, and chimney pieces in `mainPieces`. -/
def postPhase1Pieces (P : ThreePartition) (pad K : ℕ) : List Piece :=
  [.RG] ++ List.replicate (3 * P.target / 2 + 5) .I ++
    List.replicate (3 * pad) .I ++ List.replicate K .I

lemma prefixPieces_eq_main_rg (P : ThreePartition) (pad K : ℕ) :
    prefixPieces P pad K = mainPieces P pad K ++ [.RG] := by
  simp [prefixPieces, mainPieces, List.append_assoc]

lemma mainPieces_eq_phase1_post (P : ThreePartition) (pad K : ℕ) :
    mainPieces P pad K = phase1Pieces P ++ postPhase1Pieces P pad K := by
  simp [mainPieces, basePieces, phase1Pieces, postPhase1Pieces, List.append_assoc]

lemma mainPieces_length (P : ThreePartition) (pad K : ℕ) :
    (mainPieces P pad K).length = (basePieces P).length + 3 * pad + K := by
  simp [mainPieces]
  omega

lemma phase1Pieces_mem_allowed {P : ThreePartition} {t : Piece} (ht : t ∈ phase1Pieces P) :
    t ∈ ([.LG, .LS, .Sq, .I] : List Piece) := by
  simp only [phase1Pieces, List.mem_append, List.mem_replicate] at ht
  rcases ht with hnum | ⟨_, rfl⟩
  · unfold numberPieces at hnum
    rw [List.mem_flatMap] at hnum
    rcases hnum with ⟨a, _, ha⟩
    simp only [integerBlock, initiator, filler, terminator, List.mem_append,
      List.mem_flatten] at ha
    rcases ha with (h | ⟨l, hl, hxl⟩) | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide
    · rw [List.mem_replicate] at hl
      rcases hl with ⟨_, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxl
      rcases hxl with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide
  · decide

lemma phase1Pieces_four_mul_length (P : ThreePartition) (hP : P.Valid) :
    4 * (phase1Pieces P).length = P.s * (20 * P.target + 64) := by
  have hnum : (numberPieces P).length = 5 * P.s * P.target + 15 * P.s := by
    unfold numberPieces
    rw [List.length_flatMap, List.map_ofFn, List.sum_ofFn]
    have hblk : ∀ a : ℕ, (integerBlock a).length = 5 * a + 5 := by
      intro a; simp [integerBlock, initiator, filler, terminator]; omega
    simp_rw [hblk]
    simp only [Function.comp_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.1, Finset.sum_const, Finset.card_fin]
    ring
  simp only [phase1Pieces, List.length_append, List.length_replicate, hnum]
  ring

/-! ### Basic Piece Geometry, `Nodup`, Connectivity, and `Trajectory` Extraction -/

def offsetsC (t : Piece) (o : Fin 4) : List Cell :=
  t.base.map fun z => if t = .Sq then z else clockwise^[o.val] z

lemma offsetsC_nodup (t : Piece) (o : Fin 4) : (offsetsC t o).Nodup := by
  cases t <;> fin_cases o <;> decide

lemma piece_cells_eq_map_offsetsC (q : PieceState) :
    q.cells = (offsetsC q.kind q.orientation).map
      (fun u => (q.position.1 + u.1, q.position.2 + u.2)) := by
  simp [PieceState.cells, offsetsC, List.map_map]

lemma piece_cells_nodup (q : PieceState) : q.cells.Nodup := by
  rw [piece_cells_eq_map_offsetsC]
  apply (offsetsC_nodup q.kind q.orientation).map
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  ext <;> omega

lemma piece_cells_toFinset_card (q : PieceState) : q.cells.toFinset.card = 4 := by
  rw [List.toFinset_card_of_nodup (piece_cells_nodup q), piece_cells_length]

lemma move_kind_eq {R : Rotation} {B : Board} {q1 q2 : PieceState} (hm : Move R B q1 q2) :
    q2.kind = q1.kind := by
  rcases hm with ⟨_, _, _, ⟨d, rfl⟩ | rfl | rfl | rfl | ⟨rfl, _⟩⟩
  · unfold Rotation.apply; dsimp only; split <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

lemma trajectory_kind_eq {R : Rotation} {B : Board} {t : Piece} {q : PieceState}
    (htraj : Trajectory R B t q) : q.kind = t := by
  have hgen : ∀ q', Relation.ReflTransGen (Move R B) (spawn B t) q' → q'.kind = t := by
    intro q' hp
    induction hp with
    | refl => rfl
    | tail _ hstep ih => exact (move_kind_eq hstep).trans ih
  exact hgen q htraj.2.1

lemma trajectory_clear_and_blocked {R : Rotation} {B : Board} {t : Piece} {q : PieceState}
    (htraj : Trajectory R B t q) : B.Clear q ∧ ¬ B.Clear (translate q 0 (-1)) := by
  rcases htraj with ⟨_, hpath, hfix⟩
  cases hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    simp [spawn] at hfix
  | head hstep hrest =>
    -- Instead use tail case analysis on the original hpath
    have htail : ∀ q0, q0.fixed = false → Relation.ReflTransGen (Move R B) q0 q →
        q.fixed = true → B.Clear q ∧ ¬ B.Clear (translate q 0 (-1)) := by
      intro q0 h0 hp hf
      cases hp with
      | refl => rw [h0] at hf; cases hf
      | @tail q_prev _ _ hm =>
        rcases hm with ⟨hpf, _, hclq, ⟨d, heq⟩ | heq | heq | heq | ⟨heq, hnb⟩⟩
        · exfalso
          have hfeq : (R.apply B q_prev d).fixed = q_prev.fixed := by
            unfold Rotation.apply; dsimp only; split <;> rfl
          rw [heq, hfeq, hpf] at hf; cases hf
        · rw [heq] at hf; simp [translate, hpf] at hf
        · rw [heq] at hf; simp [translate, hpf] at hf
        · rw [heq] at hf; simp [translate, hpf] at hf
        · refine ⟨hclq, ?_⟩
          have hcells : (translate q 0 (-1)).cells = (translate q_prev 0 (-1)).cells := by
            rw [heq]; rfl
          unfold Board.Clear at hnb ⊢
          rwa [hcells]
    exact htail _ hstep.1 (Relation.ReflTransGen.head hstep hrest) hfix

private def AdjCell (z z' : Cell) : Prop :=
  |z.1 - z'.1| + |z.2 - z'.2| = 1

private def StepInList (L : List Cell) (z z' : Cell) : Prop :=
  z ∈ L ∧ z' ∈ L ∧ AdjCell z z'

private lemma adjCell_clockwise {u v : Cell} (h : AdjCell u v) :
    AdjCell (clockwise u) (clockwise v) := by
  unfold AdjCell clockwise at *
  dsimp only at *
  rcases abs_cases (u.1 - v.1) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases (u.2 - v.2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases (u.2 - v.2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases abs_cases (-u.1 - -v.1) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

private lemma adjCell_clockwise_iter (n : ℕ) {u v : Cell} (h : AdjCell u v) :
    AdjCell (clockwise^[n] u) (clockwise^[n] v) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact adjCell_clockwise ih

private lemma base_connected_C (t : Piece) :
    ∀ z ∈ t.base, Relation.ReflTransGen (StepInList t.base) (0, 0) z := by
  cases t <;> intro z hz <;> (
    simp only [Piece.base, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl)
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩ :
      Relation.ReflTransGen (StepInList (Piece.base .Sq)) (0, 0) (1, 0)).trans
      (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩)
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩ :
      Relation.ReflTransGen (StepInList (Piece.base .LG)) (0, 0) (0, -1)).trans
      (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩)
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩ :
      Relation.ReflTransGen (StepInList (Piece.base .RG)) (0, 0) (0, -1)).trans
      (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩)
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩ :
      Relation.ReflTransGen (StepInList (Piece.base .LS)) (0, 0) (-1, 0)).trans
      (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩)
  · exact (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩ :
      Relation.ReflTransGen (StepInList (Piece.base .RS)) (0, 0) (-1, 0)).trans
      (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩)
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩ :
      Relation.ReflTransGen (StepInList (Piece.base .I)) (0, 0) (1, 0)).trans
      (.single ⟨by decide, by decide, by unfold AdjCell; decide⟩)
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .refl
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩
  · exact .single ⟨by decide, by decide, by unfold AdjCell; decide⟩

lemma piece_cells_connected_C (q : PieceState) :
    ∀ z ∈ q.cells, Relation.ReflTransGen (StepInList q.cells) q.position z := by
  intro z hz
  let f : Cell → Cell := fun z0 =>
    let u := if q.kind = .Sq then z0 else clockwise^[q.orientation.val] z0
    (q.position.1 + u.1, q.position.2 + u.2)
  have hf_adj : ∀ u v, AdjCell u v → AdjCell (f u) (f v) := by
    intro u v huv
    dsimp only [f]
    by_cases hSq : q.kind = .Sq
    · simp only [hSq, ↓reduceIte]; unfold AdjCell at huv ⊢; dsimp only
      have h1 : q.position.1 + u.1 - (q.position.1 + v.1) = u.1 - v.1 := by ring
      have h2 : q.position.2 + u.2 - (q.position.2 + v.2) = u.2 - v.2 := by ring
      rwa [h1, h2]
    · simp only [hSq, ↓reduceIte]
      have hrot := adjCell_clockwise_iter q.orientation.val huv
      unfold AdjCell at hrot ⊢; dsimp only
      have h1 : q.position.1 + (clockwise^[q.orientation.val] u).1 -
          (q.position.1 + (clockwise^[q.orientation.val] v).1) =
          (clockwise^[q.orientation.val] u).1 - (clockwise^[q.orientation.val] v).1 := by ring
      have h2 : q.position.2 + (clockwise^[q.orientation.val] u).2 -
          (q.position.2 + (clockwise^[q.orientation.val] v).2) =
          (clockwise^[q.orientation.val] u).2 - (clockwise^[q.orientation.val] v).2 := by ring
      rwa [h1, h2]
  have hcw0 : ∀ n : ℕ, clockwise^[n] (0, 0) = (0, 0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
  have hf0 : f (0, 0) = q.position := by
    dsimp only [f]; by_cases hSq : q.kind = .Sq <;> simp [hSq, hcw0]
  have hcells : q.cells = q.kind.base.map f := rfl
  rw [hcells] at hz ⊢
  rcases List.mem_map.mp hz with ⟨z0, hz0, rfl⟩
  rw [← hf0]
  have hmap : ∀ {a b}, Relation.ReflTransGen (StepInList q.kind.base) a b →
      Relation.ReflTransGen (StepInList (q.kind.base.map f)) (f a) (f b) := by
    intro a b hp
    induction hp with
    | refl => exact .refl
    | tail _ hst ih =>
      exact ih.tail ⟨List.mem_map_of_mem hst.1, List.mem_map_of_mem hst.2.1, hf_adj _ _ hst.2.2⟩
  exact hmap (base_connected_C q.kind z0 hz0)

/-- If a clear piece `q` has all cells in `[0, yMax)` and `B.occupied (xL, y) = B.occupied (xR, y) = true`
for all `0 ≤ y < yMax`, and `q.position.1` is strictly between `xL` and `xR`, then ALL cells of `q`
lie strictly between `xL` and `xR`. -/
lemma clear_between_vertical_walls {B : Board} {q : PieceState} {xL xR yMax : ℤ}
    (hcl : B.Clear q)
    (hy : ∀ z ∈ q.cells, 0 ≤ z.2 ∧ z.2 < yMax)
    (hwL : ∀ y : ℤ, 0 ≤ y → y < yMax → B.occupied (xL, y) = true)
    (hwR : ∀ y : ℤ, 0 ≤ y → y < yMax → B.occupied (xR, y) = true)
    (hpos : xL < q.position.1 ∧ q.position.1 < xR) :
    ∀ z ∈ q.cells, xL < z.1 ∧ z.1 < xR := by
  intro z hz
  have hconn := piece_cells_connected_C q z hz
  induction hconn with
  | refl => exact hpos
  | @tail u v _ hst ih =>
    rcases hst with ⟨hu, hv, hadj⟩
    have ih1 : xL < u.1 := (ih hu).1
    have ih2 : u.1 < xR := (ih hu).2
    unfold AdjCell at hadj
    have hstep : |u.1 - v.1| ≤ 1 := by
      have := abs_nonneg (u.2 - v.2); omega
    have hdx : -1 ≤ u.1 - v.1 ∧ u.1 - v.1 ≤ 1 := abs_le.mp hstep
    have hvy := hy v hv
    have hneL : v.1 ≠ xL := by
      intro heq
      have hocc := hwL v.2 hvy.1 hvy.2
      have hv_eq : v = (xL, v.2) := Prod.ext heq rfl
      rw [← hv_eq, hcl v hv] at hocc; cases hocc
    have hneR : v.1 ≠ xR := by
      intro heq
      have hocc := hwR v.2 hvy.1 hvy.2
      have hv_eq : v = (xR, v.2) := Prod.ext heq rfl
      rw [← hv_eq, hcl v hv] at hocc; cases hocc
    omega

/-! ### Exact Per-Step Empty-Cell Accounting -/

lemma row_false_count_eq_C (B : Board) (y : Fin B.height) :
    ((Finset.univ : Finset (Fin B.width)).filter fun x => B.cell y x = false).card =
      (List.ofFn fun x : Fin B.width => B.cell y x).count false := by
  rw [List.count_eq_countP]
  have h1 : (List.ofFn fun x : Fin B.width => B.cell y x).countP (· == false) =
      (List.finRange B.width).countP (fun x => B.cell y x == false) := by
    rw [List.ofFn_eq_map, List.countP_map]; rfl
  rw [h1, List.countP_eq_length_filter]
  have hnodup : ((List.finRange B.width).filter fun x => B.cell y x == false).Nodup :=
    (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1; ext x; simp

/-- Number of cells of `q` whose `y`-coordinate lies in `[cut0, cut0 + n)`. -/
def insideCount (cut0 n : ℕ) (q : PieceState) : ℕ :=
  (q.cells.toFinset.filter fun z => (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + n : ℕ) : ℤ)).card

lemma insideCount_le_four (cut0 n : ℕ) (q : PieceState) : insideCount cut0 n q ≤ 4 := by
  calc insideCount cut0 n q
      ≤ q.cells.toFinset.card := Finset.card_filter_le _ _
    _ = 4 := piece_cells_toFinset_card q

lemma insideCount_eq_four_iff (cut0 n : ℕ) (q : PieceState) :
    insideCount cut0 n q = 4 ↔
      ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + n : ℕ) : ℤ) := by
  unfold insideCount
  have hcard := piece_cells_toFinset_card q
  constructor
  · intro heq z hz
    have hsub : q.cells.toFinset.filter (fun z => (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + n : ℕ) : ℤ)) =
        q.cells.toFinset :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hmem : z ∈ q.cells.toFinset := List.mem_toFinset.mpr hz
    rw [← hsub, Finset.mem_filter] at hmem
    exact hmem.2
  · intro hall
    have hsub : q.cells.toFinset.filter (fun z => (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + n : ℕ) : ℤ)) =
        q.cells.toFinset := by
      ext z; simp only [Finset.mem_filter, List.mem_toFinset, and_iff_left_iff_imp]
      exact hall z
    rw [hsub, hcard]

lemma emptyCellsInRange_insert_le_C (B : Board) (q : PieceState) (cut0 n : ℕ) :
    emptyCellsInRange B cut0 (cut0 + n) ≤
      emptyCellsInRange (B.insert q) cut0 (cut0 + n) + insideCount cut0 n q := by
  set B1 := B.insert q
  have hrow : ∀ y ∈ Finset.Ico cut0 (cut0 + n),
      (if hy : y < B.height then
        ((Finset.univ : Finset (Fin B.width)).filter fun x => B.cell ⟨y, hy⟩ x = false).card
      else 0) ≤
      (if hy : y < B1.height then
        ((Finset.univ : Finset (Fin B1.width)).filter fun x => B1.cell ⟨y, hy⟩ x = false).card
      else 0) +
      (q.cells.toFinset.filter fun z => z.2 = (y : ℤ)).card := by
    intro y _
    by_cases hy : y < B.height
    · have hy1 : y < B1.height := hy
      rw [dif_pos hy, dif_pos hy1]
      set S0 : Finset (Fin B.width) := Finset.univ.filter fun x => B.cell ⟨y, hy⟩ x = false
      set S1 : Finset (Fin B.width) := Finset.univ.filter fun x => B1.cell ⟨y, hy1⟩ ⟨x.val, x.isLt⟩ = false
      set D : Finset (Fin B.width) := S0 \ S1
      have hS1_sub : S1 ⊆ S0 := by
        intro x hx; rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        cases hB : B.cell ⟨y, hy⟩ x with
        | false => rfl
        | true =>
          have hx2 := hx.2; change (B.cell ⟨y, hy⟩ x || _) = false at hx2
          rw [hB] at hx2; simp at hx2
      have hcard_split : S0.card = S1.card + D.card := by
        have h := Finset.card_sdiff_add_card_eq_card hS1_sub
        change D.card + S1.card = S0.card at h; omega
      change S0.card ≤ S1.card + (q.cells.toFinset.filter fun z => z.2 = (y : ℤ)).card
      rw [hcard_split]
      suffices hD : D.card ≤ (q.cells.toFinset.filter fun z => z.2 = (y : ℤ)).card by omega
      apply Finset.card_le_card_of_injOn (fun x : Fin B.width => ((x.val : ℤ), (y : ℤ)))
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hx
        simp only [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset, and_true]
        have htrue : B1.cell ⟨y, hy1⟩ ⟨x.val, x.isLt⟩ = true :=
          Bool.eq_true_of_not_eq_false (fun hf => hx.2 ⟨Finset.mem_univ _, hf⟩)
        change (B.cell ⟨y, hy⟩ x || decide (((x.val : ℤ), (y : ℤ)) ∈ q.cells)) = true at htrue
        rw [hx.1.2] at htrue; simpa using htrue
      · intro a _ b _ hab
        simp only [Prod.mk.injEq] at hab; exact Fin.ext (Int.ofNat.inj hab.1)
    · have hy1 : ¬ y < B1.height := hy
      rw [dif_neg hy, dif_neg hy1]; exact Nat.zero_le _
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib] at hsum
  unfold emptyCellsInRange insideCount
  have hbi : (∑ y ∈ Finset.Ico cut0 (cut0 + n),
      (q.cells.toFinset.filter fun z => z.2 = (y : ℤ)).card) =
      (q.cells.toFinset.filter fun z => (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + n : ℕ) : ℤ)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext z
      simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun ⟨y, ⟨hy1, hy2⟩, hz, hyz⟩ => ⟨hz, by omega, by omega⟩,
             fun ⟨hz, hz1, hz2⟩ => ⟨z.2.toNat, ⟨by omega, by omega⟩, hz, by omega⟩⟩
    · intro a _ b _ hab
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro z hz1 hz2; simp only [Finset.mem_filter] at hz1 hz2
      exact hab (Int.ofNat.inj (hz1.2.symm.trans hz2.2))
  rwa [hbi] at hsum

lemma emptyCellsInRange_settle_eq_C {B : Board} {cut0 n : ℕ} {q : PieceState}
    (hcut_le : cut0 + n ≤ B.height)
    (hbelow_false : ∀ y : Fin B.height, y.val < cut0 → ∃ x : Fin B.width, B.cell y x = false)
    (hcells_ge : ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2) :
    let B1 := B.insert q
    let n' := (((B1.rows.drop cut0).take n).filter fun row => !(row.all id)).length
    emptyCellsInRange (B.settle q) cut0 (cut0 + n') = emptyCellsInRange B1 cut0 (cut0 + n) := by
  intro B1 n'
  have hB1_rows_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
  have hsum_filter_false : ∀ L : List (List Bool),
      (L.map fun row => row.count false).sum =
      ((L.filter fun row => !(row.all id)).map fun row => row.count false).sum := by
    intro L; induction L with
    | nil => simp
    | cons r l ih =>
      cases hall : r.all id
      · simp [hall, ih]
      · have h0 : r.count false = 0 := by
          rw [List.count_eq_zero]; intro hmem
          have := List.all_eq_true.mp hall false hmem; simp at this
        simp [hall, h0, ih]
  have hempty_eq_list : ∀ (M : Board) (m : ℕ), cut0 + m ≤ M.height →
      emptyCellsInRange M cut0 (cut0 + m) =
        (((M.rows.drop cut0).take m).map fun row => row.count false).sum := by
    intro M m hm; unfold emptyCellsInRange
    have hreindex : (∑ y ∈ Finset.Ico cut0 (cut0 + m),
        if hy : y < M.height then
          ((Finset.univ : Finset (Fin M.width)).filter fun x => M.cell ⟨y, hy⟩ x = false).card
        else 0) =
        ∑ i ∈ Finset.range m,
          if hi : cut0 + i < M.height then
            (List.ofFn fun x : Fin M.width => M.cell ⟨cut0 + i, hi⟩ x).count false
          else 0 := by
      apply Finset.sum_nbij (fun y => y - cut0)
      · intro y hy; rw [Finset.mem_Ico] at hy; rw [Finset.mem_range]; omega
      · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb; dsimp at hab; omega
      · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi
        exact ⟨cut0 + i, by simp only [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp; omega⟩
      · intro y hy; rw [Finset.mem_Ico] at hy
        have hyH : y < M.height := by omega
        have hyH' : cut0 + (y - cut0) < M.height := by omega
        rw [dif_pos hyH, dif_pos hyH', row_false_count_eq_C M ⟨y, hyH⟩]
        congr 1; congr 1; funext x; congr 1; ext; dsimp; omega
    rw [hreindex]
    have hL : (M.rows.drop cut0).take m =
        List.ofFn fun i : Fin m => List.ofFn fun x : Fin M.width => M.cell ⟨cut0 + i.val, by omega⟩ x := by
      apply List.ext_getElem
      · simp [Board.rows]; omega
      · intro i hi1 hi2; simp only [List.length_ofFn] at hi2
        rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn]; simp [Board.rows]
    rw [hL, List.map_ofFn, List.sum_ofFn]; symm
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    simp [hi, show cut0 + i < M.height by omega]
  have hn'_le : n' ≤ n := by
    calc n' ≤ ((B1.rows.drop cut0).take n).length := List.length_filter_le _ _
      _ ≤ n := List.length_take_le _ _
  have hsettleH : (B.settle q).height = B.height := rfl
  rw [hempty_eq_list (B.settle q) n' (by omega), hempty_eq_list B1 n hcut_le]
  rw [hsum_filter_false ((B1.rows.drop cut0).take n)]
  congr 2
  apply List.ext_getElem
  · change (((B.settle q).rows.drop cut0).take n').length = n'
    simp [Board.rows, hsettleH]; omega
  · intro i hi1 hi2
    have hi_n' : i < n' := hi2
    have hS_split : (B1.rows.drop cut0).filter (fun row => !(row.all id)) =
        ((B1.rows.drop cut0).take n).filter (fun row => !(row.all id)) ++
        ((B1.rows.drop cut0).drop n).filter (fun row => !(row.all id)) := by
      conv_lhs => rw [← List.take_append_drop n (B1.rows.drop cut0)]
      rw [List.filter_append]
    have hi_S : i < ((B1.rows.drop cut0).filter (fun row => !(row.all id))).length := by
      rw [hS_split, List.length_append]; omega
    have hrow_eq : ((B1.rows.drop cut0).filter (fun row => !(row.all id)))[i]'hi_S =
        (((B1.rows.drop cut0).take n).filter (fun row => !(row.all id)))[i]'hi_n' := by
      simp only [hS_split, List.getElem_append_left hi_n']
    have hrow_len : (((B1.rows.drop cut0).take n).filter (fun row => !(row.all id)))[i].length = B.width := by
      set row := (((B1.rows.drop cut0).take n).filter (fun row => !(row.all id)))[i]
      have hmem : row ∈ (B1.rows.drop cut0).take n := (List.mem_filter.mp (List.getElem_mem hi_n')).1
      have hmem' : row ∈ B1.rows := List.mem_of_mem_drop (List.mem_of_mem_take hmem)
      simp only [Board.rows, List.mem_ofFn] at hmem'
      rcases hmem' with ⟨y, hy⟩; rw [← hy]; simp; rfl
    rw [List.getElem_take, List.getElem_drop]
    have hlhs : (B.settle q).rows[cut0 + i]'(by simp [Board.rows, hsettleH]; omega) =
        List.ofFn (fun x : Fin (B.settle q).width => (B.settle q).cell ⟨cut0 + i, by omega⟩ x) := by
      simp [Board.rows]
    rw [hlhs]
    apply List.ext_getElem
    · simp [hrow_len]; rfl
    · intro j hj1 hj2
      simp only [List.getElem_ofFn]
      have hcell := settle_rows_drop_eq (cut := cut0) (q := q) (by omega) hbelow_false hcells_ge i hi_S
        ⟨j, by omega⟩
      have hget : (((B1.rows.drop cut0).filter fun row => !(row.all id))[i]'hi_S).getD j false =
          (((B1.rows.drop cut0).take n).filter fun row => !(row.all id))[i][j] := by
        rw [hrow_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]
      rw [← hget]; exact hcell

/-- Sum of `insideCount` along a sequence of placements `qs`. -/
def playInsideSum : Board → ℕ → ℕ → ℕ → List PieceState → ℕ
  | _, _, _, _, [] => 0
  | B, cut0, nC, nU, q :: qs =>
    if 1 ≤ nC + nU then
      let p := nextChimneyUpper B cut0 nC nU q
      insideCount cut0 (nC + nU) q + playInsideSum (B.settle q) cut0 p.1 p.2 qs
    else 0

lemma playInsideSum_le_four_mul (B : Board) (cut0 nC nU : ℕ) (qs : List PieceState) :
    playInsideSum B cut0 nC nU qs ≤ 4 * qs.length := by
  induction qs generalizing B nC nU with
  | nil => simp [playInsideSum]
  | cons q qs' ih =>
    simp only [playInsideSum, List.length_cons]
    split_ifs
    · have h1 := insideCount_le_four cut0 (nC + nU) q
      have h2 := ih (B.settle q) (nextChimneyUpper B cut0 nC nU q).1 (nextChimneyUpper B cut0 nC nU q).2
      omega
    · omega

/-- Every piece along `qs` stays strictly inside `[cut0, cut0 + nC + nU)` when `playInsideSum = 4 * qs.length`. -/
def AllPiecesInside : Board → ℕ → ℕ → ℕ → List PieceState → Prop
  | _, _, _, _, [] => True
  | B, cut0, nC, nU, q :: qs =>
    1 ≤ nC + nU ∧
    (∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + (nC + nU) : ℕ) : ℤ)) ∧
    let p := nextChimneyUpper B cut0 nC nU q
    AllPiecesInside (B.settle q) cut0 p.1 p.2 qs

lemma allPiecesInside_of_sum_eq_four_mul {B : Board} {cut0 nC nU : ℕ} {qs : List PieceState}
    (heq : playInsideSum B cut0 nC nU qs = 4 * qs.length) :
    AllPiecesInside B cut0 nC nU qs := by
  induction qs generalizing B nC nU with
  | nil => trivial
  | cons q qs' ih =>
    simp only [playInsideSum, List.length_cons] at heq
    by_cases hpos : 1 ≤ nC + nU
    · simp only [hpos, ↓reduceIte] at heq
      set p := nextChimneyUpper B cut0 nC nU q
      have h1 := insideCount_le_four cut0 (nC + nU) q
      have h2 := playInsideSum_le_four_mul (B.settle q) cut0 p.1 p.2 qs'
      have hi4 : insideCount cut0 (nC + nU) q = 4 := by omega
      have hrest : playInsideSum (B.settle q) cut0 p.1 p.2 qs' = 4 * qs'.length := by omega
      exact ⟨hpos, (insideCount_eq_four_iff cut0 (nC + nU) q).mp hi4, ih hrest⟩
    · simp only [hpos, ↓reduceIte] at heq
      omega

lemma nextChimneyUpper_sum_eq {R : Rotation} (hReason : Reasonable R)
    {B : Board} {cut0 splitX upperSplitX nC nU : ℕ}
    (hi : ChimneySealInv B cut0 splitX upperSplitX nC nU)
    (hpos : 1 ≤ nC + nU)
    {t : Piece} {q : PieceState} (htraj : Trajectory R B t q) :
    let p := nextChimneyUpper B cut0 nC nU q
    p.1 + p.2 = ((((B.insert q).rows.drop cut0).take (nC + nU)).filter fun row => !(row.all id)).length := by
  intro p
  set B1 := B.insert q
  by_cases hup : 1 ≤ nU ∧ 1 ≤ nC
  · have hp_eq : p = (nC, (((B1.rows.drop (cut0 + nC)).take nU).filter
        fun row => !(row.all id)).length) := by simp [p, nextChimneyUpper, hup, B1]
    rw [hp_eq]; dsimp only
    have hsealU := chimneySealInv_sealed_upper hi hup.2
    have hspawnU := spawn_cells_ge_of_height (B := B) (cut := cut0 + nC)
      (by have := hi.2.2.2.2.1; omega)
    have hcellsU : ∀ z ∈ q.cells, ((cut0 + nC : ℕ) : ℤ) ≤ z.2 :=
      trajectory_above_seal hReason hsealU hup.1 hspawnU htraj
    have hsplit_take : (B1.rows.drop cut0).take (nC + nU) =
        (B1.rows.drop cut0).take nC ++ (B1.rows.drop (cut0 + nC)).take nU := by
      rw [List.take_add, List.drop_drop, Nat.add_comm]
    rw [hsplit_take, List.filter_append, List.length_append]
    have hchim_all : ((B1.rows.drop cut0).take nC).filter (fun row => !(row.all id)) =
        (B1.rows.drop cut0).take nC := by
      rw [List.filter_eq_self]
      intro row hmem
      rw [List.mem_iff_getElem] at hmem
      rcases hmem with ⟨k, hk, rfl⟩
      have hB1_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
      simp only [List.length_take, List.length_drop, hB1_len] at hk
      have hk_c : k < nC := lt_of_lt_of_le hk (Nat.min_le_left _ _)
      have hk_H : cut0 + k < B.height := by omega
      rw [List.getElem_take, List.getElem_drop]
      simp only [Board.rows, List.getElem_ofFn, Bool.not_eq_true']
      rw [Bool.eq_false_iff]; intro hall
      have hx0 : splitX - 1 < B.width := by have := hi.2.2.2.1; omega
      have htrue := (row_all_id_iff B1 ⟨cut0 + k, hk_H⟩).mp hall ⟨splitX - 1, hx0⟩
      have hB_f : B.cell ⟨cut0 + k, hk_H⟩ ⟨splitX - 1, hx0⟩ = false := by
        rw [hi.2.2.2.2.2.2.2.1 ⟨cut0 + k, hk_H⟩ (by dsimp; omega) (by dsimp; omega)]; simp
      have hnotm : (((splitX - 1 : ℕ) : ℤ), ((cut0 + k : ℕ) : ℤ)) ∉ q.cells := by
        intro hm; have := hcellsU _ hm; omega
      change (B.cell ⟨cut0 + k, hk_H⟩ ⟨splitX - 1, hx0⟩ || decide _) = true at htrue
      rw [hB_f] at htrue; simp at htrue
      exact hnotm (by simpa [Nat.cast_add] using htrue)
    rw [hchim_all, List.length_take, List.length_drop]
    have hB1_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
    have := hi.2.2.2.2.1; omega
  · by_cases hnU : nU = 0
    · subst hnU; simp [p, nextChimneyUpper, B1]
    · have hnC : nC = 0 := by omega
      subst hnC; simp [p, nextChimneyUpper, hnU, B1]

lemma emptyCellsInRange_play_exact_bound {R : Rotation} (hReason : Reasonable R)
    {B0 B1 : Board} {cut0 splitX upperSplitX nC0 nU0 : ℕ}
    (hinv0 : ChimneySealInv B0 cut0 splitX upperSplitX nC0 nU0)
    {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hplay : Play R B0 ts qs B1 v) :
    let p := trackChimneyUpper B0 cut0 nC0 nU0 qs
    emptyCellsInRange B0 cut0 (cut0 + (nC0 + nU0)) ≤
      emptyCellsInRange B1 cut0 (cut0 + (p.1 + p.2)) + playInsideSum B0 cut0 nC0 nU0 qs := by
  induction hplay generalizing nC0 nU0 with
  | stop B ts' =>
    simp [trackChimneyUpper, playInsideSum]
  | step htraj hrest ih =>
    rename_i Bcur t ts' q qs' Bfin v'
    by_cases hpos : 1 ≤ nC0 + nU0
    · have hstep := chimneySealInv_step hReason hinv0 hpos htraj
      set p1 := nextChimneyUpper Bcur cut0 nC0 nU0 q
      have hih := ih hstep.2.2.2.1
      have hseal0 := chimneySealInv_sealed_cut0 hinv0
      have hspawn0 := spawn_cells_ge_of_height (B := Bcur) (cut := cut0)
        (by have := hinv0.2.2.2.2.1; omega)
      have hcells0 : ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 :=
        trajectory_above_seal hReason hseal0 hpos hspawn0 htraj
      have hcut_le : cut0 + (nC0 + nU0) ≤ Bcur.height := by have := hinv0.2.2.2.2.1; omega
      have hp1_sum := nextChimneyUpper_sum_eq hReason hinv0 hpos htraj
      dsimp only at hp1_sum
      have hsettle_eq := emptyCellsInRange_settle_eq_C (B := Bcur) (cut0 := cut0) (n := nC0 + nU0)
        (q := q) hcut_le hinv0.2.2.2.2.2.1 hcells0
      dsimp only at hsettle_eq
      rw [← hp1_sum] at hsettle_eq
      have hins_le := emptyCellsInRange_insert_le_C Bcur q cut0 (nC0 + nU0)
      simp only [trackChimneyUpper, playInsideSum, hpos, ↓reduceIte]
      dsimp only [p1] at hih hsettle_eq
      omega
    · have h0 : nC0 + nU0 = 0 := by omega
      rw [h0]; unfold emptyCellsInRange; simp

/-! ### Chimney Mod-4 Invariance Under `.I` and Non-Clearance Under `.RG` -/

lemma play_length_le {R : Rotation} {B B' : Board} {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hp : Play R B ts qs B' v) : qs.length ≤ ts.length := by
  induction hp with
  | stop => simp
  | step _ _ ih => simp; omega

lemma play_take_prefix {R : Rotation} {B B' : Board} {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hp : Play R B ts qs B' v) :
    ∀ k ≤ qs.length, ∃ Bk vk, Play R B (ts.take k) (qs.take k) Bk vk := by
  induction hp with
  | stop B ts =>
    intro k hk; have hk0 : k = 0 := by simpa using hk
    subst hk0; exact ⟨B, 0, Play.stop B []⟩
  | step htraj hrest ih =>
    intro k hk
    cases k with
    | zero => exact ⟨_, 0, Play.stop _ []⟩
    | succ k' =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hk
      obtain ⟨Bk, vk, hpk⟩ := ih k' hk
      exact ⟨Bk, _, Play.step htraj hpk⟩

lemma trackChimneyUpper_append (B : Board) (cut0 nC nU : ℕ) :
    ∀ (qs1 qs2 : List PieceState) {R ts1 B1 v1},
      Play R B ts1 qs1 B1 v1 →
      trackChimneyUpper B cut0 nC nU (qs1 ++ qs2) =
        let p := trackChimneyUpper B cut0 nC nU qs1
        trackChimneyUpper B1 cut0 p.1 p.2 qs2
  | [], qs2, _, _, _, _, Play.stop _ _ => rfl
  | q :: qs1, qs2, _, _, _, _, Play.step _ hrest => by
    simp only [List.cons_append, trackChimneyUpper]
    exact trackChimneyUpper_append _ cut0 _ _ qs1 qs2 hrest

lemma emptyCellsInRange_chimney_only {B : Board} {cut0 splitX upperSplitX nC : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nC 0) :
    emptyCellsInRange B cut0 (cut0 + nC) = nC := by
  unfold emptyCellsInRange
  have hterm : ∀ y ∈ Finset.Ico cut0 (cut0 + nC),
      (if hy : y < B.height then
        ((Finset.univ : Finset (Fin B.width)).filter fun x => B.cell ⟨y, hy⟩ x = false).card
      else 0) = 1 := by
    intro y hy; rw [Finset.mem_Ico] at hy
    have hyH : y < B.height := by have := hinv.2.2.2.2.1; omega
    rw [dif_pos hyH]
    set x0 : Fin B.width := ⟨splitX - 1, by have := hinv.2.2.2.1; omega⟩
    have hset : (Finset.univ.filter fun x : Fin B.width => B.cell ⟨y, hyH⟩ x = false) = {x0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, x0]
      rw [hinv.2.2.2.2.2.2.2.1 ⟨y, hyH⟩ hy.1 hy.2 x]
      simp
    rw [hset, Finset.card_singleton]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  omega

/-- An `.I` piece played on `ChimneySealInv B cut0 splitX upperSplitX nC 0` with `nC % 4 = 0`
preserves `nU = 0` and `nC % 4 = 0`. -/
lemma chimney_I_step_mod4 {R : Rotation} (hReason : Reasonable R)
    {B : Board} {cut0 splitX upperSplitX nC : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nC 0)
    (hmod : nC % 4 = 0)
    {q : PieceState} (htraj : Trajectory R B .I q) :
    (nextChimneyUpper B cut0 nC 0 q).2 = 0 ∧
    (nextChimneyUpper B cut0 nC 0 q).1 % 4 = 0 := by
  by_cases hnC0 : nC = 0
  · subst hnC0
    simp [nextChimneyUpper]
  · have hnC4 : 4 ≤ nC := by omega
    have hseal0 := chimneySealInv_sealed_cut0 hinv
    have hspawn0 := spawn_cells_ge_of_height (B := B) (cut := cut0) (by have := hinv.2.2.2.2.1; omega)
    have hcells0 : ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 :=
      trajectory_above_seal hReason hseal0 (by omega) hspawn0 htraj
    have hk : q.kind = .I := trajectory_kind_eq htraj
    obtain ⟨hcl, hblk⟩ := trajectory_clear_and_blocked htraj
    set B1 := B.insert q
    have hp_eq : nextChimneyUpper B cut0 nC 0 q =
        ((((B1.rows.drop cut0).take nC).filter fun row => !(row.all id)).length, 0) := by
      simp [nextChimneyUpper, B1]
    rw [hp_eq]; dsimp only; refine ⟨rfl, ?_⟩
    have hB1_len : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
    have hchim_occ : ∀ (x y : ℤ), (cut0 : ℤ) ≤ y → y < ((cut0 + nC : ℕ) : ℤ) →
        B.occupied (x, y) = false → x = ((splitX - 1 : ℕ) : ℤ) := by
      intro x y hy1 hy2 hocc
      unfold Board.occupied at hocc
      have hyB : 0 ≤ y ∧ y < B.height := by have := hinv.2.2.2.2.1; omega
      rw [dif_pos hyB] at hocc
      split_ifs at hocc with hxB
      have hc := hinv.2.2.2.2.2.2.2.1 ⟨y.toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega)
        ⟨x.toNat, by omega⟩
      rw [hc] at hocc; simp at hocc; omega
    -- Row `cut0 + i` (`i < nC`) is full in `B1` iff `((splitX - 1 : ℕ), cut0 + i) ∈ q.cells`
    have hrow_full_iff : ∀ (i : ℕ) (hi : i < nC),
        (((B1.rows.drop cut0).take nC)[i]'(by simp [hB1_len]; have := hinv.2.2.2.2.1; omega)).all id =
          decide ((((splitX - 1 : ℕ) : ℤ), ((cut0 + i : ℕ) : ℤ)) ∈ q.cells) := by
      intro i hi
      have hkH : cut0 + i < B.height := by have := hinv.2.2.2.2.1; omega
      have hget : ((B1.rows.drop cut0).take nC)[i]'(by simp [hB1_len]; omega) =
          List.ofFn (fun x : Fin B1.width => B1.cell ⟨cut0 + i, hkH⟩ x) := by
        rw [List.getElem_take, List.getElem_drop]; simp [Board.rows]
      rw [hget]
      cases hm : decide ((((splitX - 1 : ℕ) : ℤ), ((cut0 + i : ℕ) : ℤ)) ∈ q.cells)
      · rw [Bool.eq_false_iff]; intro hall
        have hx0 : splitX - 1 < B.width := by have := hinv.2.2.2.1; omega
        have ht := (row_all_id_iff B1 ⟨cut0 + i, hkH⟩).mp hall ⟨splitX - 1, hx0⟩
        have hBf : B.cell ⟨cut0 + i, hkH⟩ ⟨splitX - 1, hx0⟩ = false := by
          rw [hinv.2.2.2.2.2.2.2.1 ⟨cut0 + i, hkH⟩ (by dsimp; omega) (by dsimp; omega)]; simp
        change (B.cell ⟨cut0 + i, hkH⟩ ⟨splitX - 1, hx0⟩ || _) = true at ht
        rw [hBf] at ht; simp at ht
        simp [ht] at hm
      · rw [row_all_id_iff]
        intro x
        by_cases hx : x.val = splitX - 1
        · change (B.cell ⟨cut0 + i, hkH⟩ ⟨x.val, x.isLt⟩ || _) = true
          rw [Bool.or_eq_true]; right; simp only [decide_eq_true_eq] at hm ⊢
          rwa [hx]
        · have hBt : B.cell ⟨cut0 + i, hkH⟩ ⟨x.val, x.isLt⟩ = true := by
            rw [hinv.2.2.2.2.2.2.2.1 ⟨cut0 + i, hkH⟩ (by dsimp; omega) (by dsimp; omega)]; simp [hx]
          change (B.cell ⟨cut0 + i, hkH⟩ ⟨x.val, x.isLt⟩ || _) = true
          rw [hBt]; rfl
    rcases i_cells_cases hk with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
    · -- Horizontal `.I`: cannot touch `[cut0, cut0 + nC)`!
      have hge : ((cut0 + nC : ℕ) : ℤ) ≤ y₀ := by
        by_contra hlt; push Not at hlt
        have hm0 : (x₀, y₀) ∈ q.cells := by
          rw [← List.mem_toFinset, hfin]; simp
        have hm1 : (x₀ + 1, y₀) ∈ q.cells := by
          rw [← List.mem_toFinset, hfin]; simp
        have hy0 := hcells0 _ hm0
        have hx0 := hchim_occ x₀ y₀ hy0 hlt (hcl _ hm0)
        have hx1 := hchim_occ (x₀ + 1) y₀ hy0 hlt (hcl _ hm1)
        omega
      have hall_nfull : (((B1.rows.drop cut0).take nC).filter fun row => !(row.all id)) =
          (B1.rows.drop cut0).take nC := by
        rw [List.filter_eq_self]
        intro row hmem; rw [List.mem_iff_getElem] at hmem
        rcases hmem with ⟨i, hi, rfl⟩
        have hi_nC : i < nC := by simp [hB1_len] at hi; omega
        rw [hrow_full_iff i hi_nC]
        simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
        rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      rw [hall_nfull, List.length_take, List.length_drop, hB1_len]
      have hmin : min nC (B.height - cut0) = nC := by have := hinv.2.2.2.2.1; omega
      rw [hmin]; exact hmod
    · -- Vertical `.I`: either `y₀ ≥ cut0 + nC` (0 rows full) or `y₀ = cut0` (4 rows full)!
      by_cases hy_top : ((cut0 + nC : ℕ) : ℤ) ≤ y₀
      · have hall_nfull : (((B1.rows.drop cut0).take nC).filter fun row => !(row.all id)) =
            (B1.rows.drop cut0).take nC := by
          rw [List.filter_eq_self]
          intro row hmem; rw [List.mem_iff_getElem] at hmem
          rcases hmem with ⟨i, hi, rfl⟩
          have hi_nC : i < nC := by simp [hB1_len] at hi; omega
          rw [hrow_full_iff i hi_nC]
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
          rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        rw [hall_nfull, List.length_take, List.length_drop, hB1_len]
        have hmin : min nC (B.height - cut0) = nC := by have := hinv.2.2.2.2.1; omega
        rw [hmin]; exact hmod
      · push Not at hy_top
        have hm0 : (x₀, y₀) ∈ q.cells := by rw [← List.mem_toFinset, hfin]; simp
        have hy0_ge := hcells0 _ hm0
        have hx0_eq : x₀ = ((splitX - 1 : ℕ) : ℤ) := hchim_occ x₀ y₀ hy0_ge hy_top (hcl _ hm0)
        -- `¬ B.Clear (translate q 0 (-1))` forces `B.occupied (x₀, y₀ - 1) = true`, hence `y₀ = cut0`!
        have hy0_eq : y₀ = (cut0 : ℤ) := by
          by_contra hne
          have hy0_gt : (cut0 : ℤ) < y₀ := by omega
          apply hblk
          intro w hw
          have htr_cells : (translate q 0 (-1)).cells = q.cells.map (fun z => (z.1, z.2 - 1)) := by
            unfold translate PieceState.cells
            rw [List.map_map]
            apply List.map_congr_left
            intro a _; simp only [Function.comp_apply]; ext <;> omega
          rw [htr_cells, List.mem_map] at hw
          rcases hw with ⟨z, hz, rfl⟩
          have hz' := List.mem_toFinset.mpr hz; rw [hfin] at hz'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
          rcases hz' with rfl | rfl | rfl | rfl
          · -- `(x₀, y₀ - 1)` lies in `[cut0, cut0 + nC)` at `x = splitX - 1`, so it IS `false`!
            dsimp only
            rw [hx0_eq]; unfold Board.occupied
            have hyB : (0 : ℤ) ≤ y₀ - 1 ∧ y₀ - 1 < B.height := by have := hinv.2.2.2.2.1; omega
            have hxB : (0 : ℤ) ≤ ((splitX - 1 : ℕ) : ℤ) ∧ ((splitX - 1 : ℕ) : ℤ) < B.width := by
              have := hinv.2.2.2.1; omega
            rw [dif_pos hyB, dif_pos hxB]
            rw [hinv.2.2.2.2.2.2.2.1 ⟨(y₀ - 1).toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega)]; simp
          · dsimp only; rw [add_sub_cancel_right]
            exact hcl (x₀, y₀) (by rw [← List.mem_toFinset, hfin]; simp)
          · dsimp only; have : y₀ + 2 - 1 = y₀ + 1 := by omega
            rw [this]; exact hcl (x₀, y₀ + 1) (by rw [← List.mem_toFinset, hfin]; simp)
          · dsimp only; have : y₀ + 3 - 1 = y₀ + 2 := by omega
            rw [this]; exact hcl (x₀, y₀ + 2) (by rw [← List.mem_toFinset, hfin]; simp)
        -- With `x₀ = splitX - 1` and `y₀ = cut0`, rows `0,1,2,3` of `take nC` are full and `4..nC-1` are not full!
        set L := (B1.rows.drop cut0).take nC
        have hL_len : L.length = nC := by simp [L, hB1_len]; have := hinv.2.2.2.2.1; omega
        have hsplitL : L = L.take 4 ++ L.drop 4 := (List.take_append_drop 4 L).symm
        rw [hsplitL, List.filter_append, List.length_append]
        have hfirst4 : (L.take 4).filter (fun row => !(row.all id)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro row hmem; rw [List.mem_iff_getElem] at hmem
          rcases hmem with ⟨i, hi, rfl⟩
          simp only [List.length_take, hL_len] at hi
          have hi4 : i < 4 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
          rw [List.getElem_take, hrow_full_iff i (by omega)]
          simp only [Bool.not_eq_true', Bool.not_eq_false, decide_eq_true_eq]
          rw [← List.mem_toFinset, hfin, hx0_eq, hy0_eq]
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, true_and]
          omega
        have hrest_nC : (L.drop 4).filter (fun row => !(row.all id)) = L.drop 4 := by
          rw [List.filter_eq_self]
          intro row hmem; rw [List.mem_iff_getElem] at hmem
          rcases hmem with ⟨i, hi, rfl⟩
          simp only [List.length_drop, hL_len] at hi
          rw [List.getElem_drop, hrow_full_iff (4 + i) (by omega)]
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin, hy0_eq] at hm'
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
          rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        rw [hfirst4, hrest_nC, List.length_nil, Nat.zero_add, List.length_drop, hL_len]
        omega

private lemma rg_has_nonzero_dx : ∀ o : Fin 4, ∃ u ∈ offsetsC .RG o, u.1 ≠ 0 := by
  decide

/-- An `.RG` piece cannot clear all `nC ≥ 4` chimney rows! -/
lemma chimney_RG_not_zero {R : Rotation} (hReason : Reasonable R)
    {B : Board} {cut0 splitX upperSplitX nC : ℕ}
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nC 0)
    (hnC4 : 4 ≤ nC)
    {q : PieceState} (htraj : Trajectory R B .RG q) :
    1 ≤ (nextChimneyUpper B cut0 nC 0 q).1 := by
  have hseal0 := chimneySealInv_sealed_cut0 hinv
  have hspawn0 := spawn_cells_ge_of_height (B := B) (cut := cut0) (by have := hinv.2.2.2.2.1; omega)
  have hcells0 : ∀ z ∈ q.cells, (cut0 : ℤ) ≤ z.2 :=
    trajectory_above_seal hReason hseal0 (by omega) hspawn0 htraj
  have hk : q.kind = .RG := trajectory_kind_eq htraj
  have hcl := (trajectory_clear_and_blocked htraj).1
  obtain ⟨u, hu, hux⟩ := rg_has_nonzero_dx q.orientation
  have hpos_mem : q.position ∈ q.cells := position_mem_cells_A q
  have hu_mem : (q.position.1 + u.1, q.position.2 + u.2) ∈ q.cells := by
    rw [piece_cells_eq_map_offsetsC, hk]
    exact List.mem_map.mpr ⟨u, hu, rfl⟩
  -- At least one cell `z* ∈ q.cells` has `z*.1 ≠ splitX - 1`, hence `z*.2 ≥ cut0 + nC`!
  have hex_out : ∃ z ∈ q.cells, ((cut0 + nC : ℕ) : ℤ) ≤ z.2 := by
    have hchim_occ : ∀ z ∈ q.cells, z.2 < ((cut0 + nC : ℕ) : ℤ) → z.1 = ((splitX - 1 : ℕ) : ℤ) := by
      intro z hz hlt
      have hocc := hcl z hz
      have hy0 := hcells0 z hz
      unfold Board.occupied at hocc
      have hyB : 0 ≤ z.2 ∧ z.2 < B.height := by have := hinv.2.2.2.2.1; omega
      rw [dif_pos hyB] at hocc
      split_ifs at hocc with hxB
      have hc := hinv.2.2.2.2.2.2.2.1 ⟨z.2.toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega)
        ⟨z.1.toNat, by omega⟩
      rw [hc] at hocc; simp at hocc; omega
    by_cases h1 : q.position.2 < ((cut0 + nC : ℕ) : ℤ)
    · by_cases h2 : (q.position.1 + u.1, q.position.2 + u.2).2 < ((cut0 + nC : ℕ) : ℤ)
      · have hx1 := hchim_occ _ hpos_mem h1
        have hx2 := hchim_occ _ hu_mem h2
        dsimp at hx2; omega
      · exact ⟨_, hu_mem, by dsimp at h2 ⊢; omega⟩
    · exact ⟨_, hpos_mem, by omega⟩
  rcases hex_out with ⟨z_out, hz_out, hge_out⟩
  have hinside_le3 : insideCount cut0 nC q ≤ 3 := by
    unfold insideCount
    have hlt : (q.cells.toFinset.filter fun z => (cut0 : ℤ) ≤ z.2 ∧ z.2 < ((cut0 + nC : ℕ) : ℤ)).card <
        q.cells.toFinset.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have hmem : z_out ∈ q.cells.toFinset := List.mem_toFinset.mpr hz_out
      rw [← heq, Finset.mem_filter] at hmem
      omega
    rw [piece_cells_toFinset_card] at hlt; omega
  -- Use `emptyCellsInRange` to show `(nextChimneyUpper B cut0 nC 0 q).1 ≥ 1`!
  by_contra hlt1
  have hp0 : (nextChimneyUpper B cut0 nC 0 q).1 = 0 := by omega
  have hp2 : (nextChimneyUpper B cut0 nC 0 q).2 = 0 := by simp [nextChimneyUpper]
  have hsum := nextChimneyUpper_sum_eq hReason hinv (by omega) htraj
  simp only [hp0, hp2, Nat.add_zero] at hsum
  have hsettle := emptyCellsInRange_settle_eq_C (B := B) (cut0 := cut0) (n := nC) (q := q)
    (by have := hinv.2.2.2.2.1; omega) hinv.2.2.2.2.2.1 hcells0
  dsimp only at hsettle
  rw [← hsum] at hsettle
  have hempty0 : emptyCellsInRange (B.settle q) cut0 (cut0 + 0) = 0 := by
    unfold emptyCellsInRange; simp
  have hemptyB : emptyCellsInRange B cut0 (cut0 + nC) = nC := emptyCellsInRange_chimney_only hinv
  have hins := emptyCellsInRange_insert_le_C B q cut0 nC
  omega

/-- Direct `ChimneySealInv` propagation along a specific `Play` when every prefix keeps `1 ≤ p.1 + p.2`. -/
lemma chimneySealInv_along_play {R : Rotation} (hReason : Reasonable R)
    {B B' : Board} {cut0 splitX upperSplitX nC nU : ℕ}
    {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hp : Play R B ts qs B' v)
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nC nU)
    (hC : 1 ≤ nC)
    (hne0 : ∀ j ≤ qs.length,
      1 ≤ (trackChimneyUpper B cut0 nC nU (qs.take j)).1 +
        (trackChimneyUpper B cut0 nC nU (qs.take j)).2) :
    let p := trackChimneyUpper B cut0 nC nU qs
    1 ≤ p.1 ∧ ChimneySealInv B' cut0 splitX upperSplitX p.1 p.2 := by
  induction hp generalizing nC nU with
  | stop => exact ⟨hC, hinv⟩
  | step htraj hrest ih =>
    rename_i Bcur t ts' q qs' Bfin v'
    obtain ⟨_, h2le, hkeep, hinv1, _⟩ := chimneySealInv_step hReason hinv (by omega) htraj
    set p1 := nextChimneyUpper Bcur cut0 nC nU q
    have hp1_pos : 1 ≤ p1.1 + p1.2 := by
      simpa [trackChimneyUpper, p1] using hne0 1 (by simp)
    have hC1 : 1 ≤ p1.1 := by
      by_cases hU0 : p1.2 = 0
      · omega
      · rw [hkeep (by omega) hC]; exact hC
    have hne0' : ∀ j ≤ qs'.length,
        1 ≤ (trackChimneyUpper (Bcur.settle q) cut0 p1.1 p1.2 (qs'.take j)).1 +
          (trackChimneyUpper (Bcur.settle q) cut0 p1.1 p1.2 (qs'.take j)).2 := by
      intro j hj
      simpa [trackChimneyUpper, p1] using hne0 (j + 1) (by simp; omega)
    exact ih hinv1 hC1 hne0'

/-- While `1 ≤ nU` holds at every proper prefix of `qs`, `nC` stays equal to its initial value. -/
lemma chimneySealInv_keep_nC_while_nU_pos {R : Rotation} (hReason : Reasonable R)
    {B B' : Board} {cut0 splitX upperSplitX nC nU : ℕ}
    {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hp : Play R B ts qs B' v)
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nC nU)
    (hC : 1 ≤ nC)
    (hUpos : ∀ j < qs.length, 1 ≤ (trackChimneyUpper B cut0 nC nU (qs.take j)).2) :
    let p := trackChimneyUpper B cut0 nC nU qs
    p.1 = nC ∧ ChimneySealInv B' cut0 splitX upperSplitX nC p.2 := by
  induction hp generalizing nC nU with
  | stop => exact ⟨rfl, hinv⟩
  | step htraj hrest ih =>
    rename_i Bcur t ts' q qs' Bfin v'
    have hU0 : 1 ≤ nU := by simpa [trackChimneyUpper] using hUpos 0 (by simp)
    obtain ⟨_, _, hkeep, hinv1, _⟩ := chimneySealInv_step hReason hinv (by omega) htraj
    set p1 := nextChimneyUpper Bcur cut0 nC nU q
    have hp1_1 : p1.1 = nC := hkeep hU0 hC
    have hinv1' : ChimneySealInv (Bcur.settle q) cut0 splitX upperSplitX nC p1.2 := by
      rwa [hp1_1] at hinv1
    have hUpos' : ∀ j < qs'.length,
        1 ≤ (trackChimneyUpper (Bcur.settle q) cut0 nC p1.2 (qs'.take j)).2 := by
      intro j hj
      have h := hUpos (j + 1) (by simp; omega)
      simpa [trackChimneyUpper, p1, hp1_1] using h
    have hres := ih hinv1' hC hUpos'
    simpa [trackChimneyUpper, p1, hp1_1] using hres

lemma trackChimneyUpper_zero_zero (M : Board) (cut0 : ℕ) (L : List PieceState) :
    trackChimneyUpper M cut0 0 0 L = (0, 0) := by
  induction L generalizing M with
  | nil => rfl
  | cons q qs ih =>
    have hp : nextChimneyUpper M cut0 0 0 q = (0, 0) := by simp [nextChimneyUpper]
    simp [trackChimneyUpper, hp, ih]

/-- Playing a list of `.I` pieces on `ChimneySealInv B cut0 splitX upperSplitX nC 0` with `nC % 4 = 0`
preserves `nU = 0` and `nC % 4 = 0`. -/
lemma chimney_I_play_mod4 {R : Rotation} (hReason : Reasonable R)
    {B B' : Board} {cut0 splitX upperSplitX nC : ℕ}
    {ts : List Piece} {qs : List PieceState} {v : ℕ}
    (hp : Play R B ts qs B' v)
    (hts : ∀ t ∈ ts, t = .I)
    (hinv : ChimneySealInv B cut0 splitX upperSplitX nC 0)
    (hmod : nC % 4 = 0) :
    (trackChimneyUpper B cut0 nC 0 qs).2 = 0 ∧
    (trackChimneyUpper B cut0 nC 0 qs).1 % 4 = 0 := by
  induction hp generalizing nC with
  | stop => exact ⟨rfl, hmod⟩
  | step htraj hrest ih =>
    rename_i Bcur t ts' q qs' Bfin v'
    have ht : t = .I := hts t (List.mem_cons_self ..)
    subst ht
    by_cases hnC0 : nC = 0
    · subst hnC0
      rw [trackChimneyUpper_zero_zero]; simp
    · obtain ⟨hp2, hp1_mod⟩ := chimney_I_step_mod4 hReason hinv hmod htraj
      obtain ⟨_, _, _, hinv1, _⟩ := chimneySealInv_step hReason hinv (by omega) htraj
      set p1 := nextChimneyUpper Bcur cut0 nC 0 q
      have hp1_2 : p1.2 = 0 := hp2
      have hinv1' : ChimneySealInv (Bcur.settle q) cut0 splitX upperSplitX p1.1 0 := by
        rwa [hp1_2] at hinv1
      have hres := ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) hinv1' hp1_mod
      simpa [trackChimneyUpper, p1, hp1_2] using hres

/-- Key zero-waste theorem: if ANY prefix of `prefixPieces P pad K` reduces `trackChimneyUpper`
to `(0, 0)`, then `mainPieces P pad K` ALREADY reduces `trackChimneyUpper` to `(0, 0)` in its
full length `N_tot` with `AllPiecesInside` (ZERO wasted cells at every step!). -/
theorem mainPieces_zero_waste_of_clear_chimney {R : Rotation} (hReason : Reasonable R)
    {P : ThreePartition} (hP : P.Valid) (hEven : Even P.target)
    {pad K st r : ℕ} (hpad : 1 ≤ pad) (hK : 1 ≤ K) (hst : 3 ≤ st)
    {B1 : Board} {ts1 ts2 : List Piece} {qs1 : List PieceState} {v1 : ℕ}
    (hplay : Play R (paddedReservoirBoard P pad K st r) ts1 qs1 B1 v1)
    (hpref : prefixPieces P pad K = ts1 ++ ts2)
    (hzero : (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).1 +
      (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).2 = 0) :
    ∃ qs_main B_main v_main,
      qs_main.length = (mainPieces P pad K).length ∧
      Play R (paddedReservoirBoard P pad K st r) (mainPieces P pad K) qs_main B_main v_main ∧
      AllPiecesInside (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs_main := by
  classical
  set B0 := paddedReservoirBoard P pad K st r
  set cut0 := r + 2
  set nC0 := 4 * K
  set H' := 12 * pad + baseHeight P
  set N_tot := (mainPieces P pad K).length
  have hinv0 := chimneySealInv_init P pad K st r hpad hst
  have hex_k : ∃ k, k ≤ qs1.length ∧
      (trackChimneyUpper B0 cut0 nC0 H' (qs1.take k)).1 +
        (trackChimneyUpper B0 cut0 nC0 H' (qs1.take k)).2 = 0 :=
    ⟨qs1.length, le_rfl, by simpa using hzero⟩
  set k := Nat.find hex_k
  obtain ⟨hk_le, hk_zero⟩ := Nat.find_spec hex_k
  have hk_min : ∀ j < k, 1 ≤ (trackChimneyUpper B0 cut0 nC0 H' (qs1.take j)).1 +
      (trackChimneyUpper B0 cut0 nC0 H' (qs1.take j)).2 := by
    intro j hj
    by_contra hlt
    exact Nat.find_min hex_k hj ⟨by omega, by omega⟩
  obtain ⟨Bk, vk, hpk⟩ := play_take_prefix hplay k hk_le
  have hqs1_le_ts1 := play_length_le hplay
  have hts1_le_pref : ts1.length ≤ N_tot + 1 := by
    have := congrArg List.length hpref
    rw [prefixPieces_eq_main_rg, List.length_append, List.length_append] at this
    simp at this; omega
  have htake_pref : ts1.take k = (prefixPieces P pad K).take k := by
    rw [hpref, List.take_append_of_le_length (by omega)]
  rw [htake_pref] at hpk
  -- Show `k ≤ N_tot` (cannot be `N_tot + 1`!)
  have hk_le_N : k ≤ N_tot := by
    by_contra hgt
    have hk_eq : k = N_tot + 1 := by omega
    have hpref_len : (prefixPieces P pad K).length = N_tot + 1 := by
      rw [prefixPieces_eq_main_rg, List.length_append]; simp [N_tot]
    have htake_all : (prefixPieces P pad K).take k = mainPieces P pad K ++ [Piece.RG] := by
      rw [hk_eq, ← hpref_len, List.take_length, prefixPieces_eq_main_rg]
    rw [htake_all] at hpk
    obtain ⟨qs_m, qs_rg, B_m, v_m, v_rg, hqs_split, _, hp_m, hp_rg, _⟩ := play_append_split hpk
    have hqsk_len : (qs1.take k).length = N_tot + 1 := by rw [List.length_take]; omega
    have hqsm_le := play_length_le hp_m
    have hqsrg_le := play_length_le hp_rg
    have hlen_sum : qs_m.length + qs_rg.length = N_tot + 1 := by
      rw [← List.length_append, ← hqs_split, hqsk_len]
    have hqsm_len : qs_m.length = N_tot := by dsimp [N_tot] at *; omega
    have hqsrg_len : qs_rg.length = 1 := by simp at hqsrg_le; omega
    obtain ⟨q_RG, rfl⟩ : ∃ q_RG, qs_rg = [q_RG] := by
      cases qs_rg with
      | nil => simp at hqsrg_len
      | cons q l => simp at hqsrg_len; subst hqsrg_len; exact ⟨q, rfl⟩
    have htraj_RG : Trajectory R B_m Piece.RG q_RG := by
      cases hp_rg with
      | step ht _ => exact ht
    have hqsm_eq : qs_m = qs1.take N_tot := by
      have h1 : qs1.take (N_tot + 1) = qs_m ++ [q_RG] := by rwa [← hk_eq]
      have h2 := congrArg (List.take N_tot) h1
      rw [List.take_take, Nat.min_eq_left (by omega),
        List.take_append_of_le_length (by omega), ← hqsm_len, List.take_length, hqsm_len] at h2
      exact h2.symm
    have hne0_m : ∀ j ≤ qs_m.length,
        1 ≤ (trackChimneyUpper B0 cut0 nC0 H' (qs_m.take j)).1 +
          (trackChimneyUpper B0 cut0 nC0 H' (qs_m.take j)).2 := by
      intro j hj
      rw [hqsm_eq, List.take_take, Nat.min_eq_left (by omega)]
      exact hk_min j (by omega)
    obtain ⟨hnCm_pos, hinv_m⟩ := chimneySealInv_along_play hReason hp_m hinv0 (by omega) hne0_m
    set pm := trackChimneyUpper B0 cut0 nC0 H' qs_m
    -- At `qs1.take k = qs_m ++ [q_RG]`, `trackChimneyUpper` becomes `(0, 0)`!
    have hzero_rg : (nextChimneyUpper B_m cut0 pm.1 pm.2 q_RG).1 +
        (nextChimneyUpper B_m cut0 pm.1 pm.2 q_RG).2 = 0 := by
      have h1 := trackChimneyUpper_append B0 cut0 nC0 H' qs_m [q_RG] hp_m
      rw [← hqs_split] at h1
      rw [h1] at hk_zero
      simpa [trackChimneyUpper, pm] using hk_zero
    have hpm2_zero : pm.2 = 0 := by
      by_contra hpos2
      have hstep := chimneySealInv_step hReason hinv_m (by omega) htraj_RG
      have hkeep := hstep.2.2.1 (by omega) hnCm_pos
      dsimp [cut0] at hzero_rg hkeep
      omega
    -- Find minimal `m ≤ N_tot` where `(trackChimneyUpper B0 cut0 nC0 H' (qs_m.take m)).2 = 0`
    have hex_m : ∃ m, m ≤ N_tot ∧ (trackChimneyUpper B0 cut0 nC0 H' (qs_m.take m)).2 = 0 :=
      ⟨N_tot, le_rfl, by rw [← hqsm_len, List.take_length]; exact hpm2_zero⟩
    set m := Nat.find hex_m
    have hm_le : m ≤ N_tot := (Nat.find_spec hex_m).1
    have hm_zero : (trackChimneyUpper B0 cut0 nC0 H' (qs_m.take m)).2 = 0 := (Nat.find_spec hex_m).2
    have hm_min : ∀ j < m, 1 ≤ (trackChimneyUpper B0 cut0 nC0 H' (qs_m.take j)).2 := by
      intro j hj; by_contra hlt
      exact Nat.find_min hex_m hj ⟨by omega, by omega⟩
    have hm_pos : 1 ≤ m := by
      by_contra h0; have hm0 : m = 0 := by omega
      rw [hm0] at hm_zero; simp [trackChimneyUpper] at hm_zero
      dsimp [H'] at hm_zero; unfold baseHeight at hm_zero; omega
    -- Split `hp_m` at `m`
    have hmain_split : mainPieces P pad K = (mainPieces P pad K).take m ++ (mainPieces P pad K).drop m :=
      (List.take_append_drop m _).symm
    rw [hmain_split] at hp_m
    obtain ⟨qs_preU, qs_postU, B_U, v_U, v_postU, hqsm_sp, _, hp_preU, hp_postU, _⟩ :=
      play_append_split hp_m
    have hpre_le := play_length_le hp_preU
    have hpost_le := play_length_le hp_postU
    have htake_m_len : ((mainPieces P pad K).take m).length = m := by rw [List.length_take]; omega
    have hdrop_m_len : ((mainPieces P pad K).drop m).length = N_tot - m := by rw [List.length_drop]
    have hsum_U : qs_preU.length + qs_postU.length = N_tot := by
      rw [← List.length_append, ← hqsm_sp, hqsm_len]
    have hpreU_len : qs_preU.length = m := by omega
    have hpreU_eq : qs_preU = qs_m.take m := by
      have h2 := congrArg (List.take m) hqsm_sp
      rw [List.take_append_of_le_length (by omega), ← hpreU_len, List.take_length, hpreU_len] at h2
      exact h2.symm
    have hUpos_pre : ∀ j < qs_preU.length,
        1 ≤ (trackChimneyUpper B0 cut0 nC0 H' (qs_preU.take j)).2 := by
      intro j hj
      rw [hpreU_eq, List.take_take, Nat.min_eq_left (by omega)]
      exact hm_min j (by omega)
    obtain ⟨hpU_1, hinv_U⟩ := chimneySealInv_keep_nC_while_nU_pos hReason hp_preU hinv0 (by omega) hUpos_pre
    have hpU_2 : (trackChimneyUpper B0 cut0 nC0 H' qs_preU).2 = 0 := by rwa [hpreU_eq]
    have hinv_U0 : ChimneySealInv B_U cut0 (6 * (P.s + pad)) (6 * P.s + 3) nC0 0 := by
      rwa [hpU_2] at hinv_U
    -- Bound `m ≥ N_tot - K` via `emptyCellsInRange_play_exact_bound` on `hp_preU`
    have hbndU := emptyCellsInRange_play_exact_bound hReason hinv0 hp_preU
    dsimp only at hbndU
    rw [hpU_1, hpU_2, Nat.add_zero] at hbndU
    have hempty0 : emptyCellsInRange B0 cut0 (cut0 + (nC0 + H')) = 4 * N_tot := by
      dsimp only [N_tot]; rw [mainPieces_length]
      convert emptyCells_init_above_chimney P hP hEven pad K st r hpad using 2
      dsimp [cut0, nC0, H']; omega
    have hemptyU : emptyCellsInRange B_U cut0 (cut0 + nC0) = nC0 :=
      emptyCellsInRange_chimney_only hinv_U0
    have hsum_le4m := playInsideSum_le_four_mul B0 cut0 nC0 H' qs_preU
    dsimp only [B0, cut0, nC0, H'] at hbndU hempty0 hemptyU hsum_le4m
    simp only [Nat.add_zero] at hbndU
    rw [hempty0, hemptyU] at hbndU
    rw [hpreU_len] at hsum_le4m
    have hm_ge : N_tot - K ≤ m := by omega
    -- Every piece in `(mainPieces P pad K).drop m` is `.I`!
    have hdrop_all_I : ∀ t ∈ (mainPieces P pad K).drop m, t = Piece.I := by
      intro t ht
      have hm_split2 : mainPieces P pad K = (basePieces P ++ List.replicate (3 * pad) .I) ++ List.replicate K .I := by
        simp [mainPieces, List.append_assoc]
      have hlen_left : (basePieces P ++ List.replicate (3 * pad) Piece.I).length = N_tot - K := by
        have := mainPieces_length P pad K
        simp [N_tot]; omega
      rw [hm_split2, List.drop_append,
        List.drop_eq_nil_of_le (by rw [hlen_left]; omega), List.nil_append] at ht
      exact (List.mem_replicate.mp (List.mem_of_mem_drop ht)).2
    have hmod_post := chimney_I_play_mod4 hReason hp_postU hdrop_all_I hinv_U0 (by dsimp [nC0]; omega)
    have hpm_eq_post : pm = trackChimneyUpper B_U cut0 nC0 0 qs_postU := by
      have h1 := trackChimneyUpper_append B0 cut0 nC0 H' qs_preU qs_postU hp_preU
      rw [← hqsm_sp] at h1
      dsimp only [pm, B0, cut0, nC0, H'] at h1 hpU_1 hpU_2 ⊢
      rw [h1, hpU_1, hpU_2]
    have hpm1_mod : pm.1 % 4 = 0 := by rw [hpm_eq_post]; exact hmod_post.2
    have hpm1_ge4 : 4 ≤ pm.1 := by omega
    have hinv_m0 : ChimneySealInv B_m cut0 (6 * (P.s + pad)) (6 * P.s + 3) pm.1 0 := by
      rwa [hpm2_zero] at hinv_m
    have hrg_pos := chimney_RG_not_zero hReason hinv_m0 hpm1_ge4 htraj_RG
    rw [hpm2_zero] at hzero_rg
    omega
  -- Now `k ≤ N_tot`!
  have htake_main : (prefixPieces P pad K).take k = (mainPieces P pad K).take k := by
    rw [prefixPieces_eq_main_rg, List.take_append_of_le_length hk_le_N]
  rw [htake_main] at hpk
  have hbnd_k := emptyCellsInRange_play_exact_bound hReason hinv0 hpk
  dsimp only at hbnd_k
  have hpk_sum0 : (trackChimneyUpper B0 cut0 nC0 H' (qs1.take k)).1 +
      (trackChimneyUpper B0 cut0 nC0 H' (qs1.take k)).2 = 0 := hk_zero
  rw [hpk_sum0] at hbnd_k
  have hempty0 : emptyCellsInRange B0 cut0 (cut0 + (nC0 + H')) = 4 * N_tot := by
    dsimp only [N_tot]; rw [mainPieces_length]
    convert emptyCells_init_above_chimney P hP hEven pad K st r hpad using 2
    dsimp [cut0, nC0, H']; omega
  have hempty_end : emptyCellsInRange Bk cut0 (cut0 + 0) = 0 := by unfold emptyCellsInRange; simp
  have hqsk_len : (qs1.take k).length = k := by rw [List.length_take]; omega
  have hsum_le := playInsideSum_le_four_mul B0 cut0 nC0 H' (qs1.take k)
  dsimp only [B0, cut0, nC0, H', N_tot] at hbnd_k hempty0 hempty_end hsum_le hk_le_N ⊢
  rw [hempty0, hempty_end] at hbnd_k
  rw [hqsk_len] at hsum_le
  have hk_eq_N : k = (mainPieces P pad K).length := by omega
  have hsum_eq : playInsideSum (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
      (12 * pad + baseHeight P) (qs1.take k) = 4 * (qs1.take k).length := by omega
  have hall_in := allPiecesInside_of_sum_eq_four_mul hsum_eq
  rw [hk_eq_N, List.take_length] at hpk
  rw [hk_eq_N] at hall_in hqsk_len
  exact ⟨qs1.take (mainPieces P pad K).length, Bk, vk, hqsk_len, hpk, hall_in⟩

/-! ### Lock-Well Isolation, Zero Row Clears, and Phase-1 Lifting to `dropRows` -/

def LockWellSealed (B : Board) (s pad K H' r : ℕ) : Prop :=
  let cut := r + 2 + 4 * K
  1 ≤ pad ∧
  cut + H' + 3 ≤ B.height ∧
  6 * (s + pad) + 3 = B.width ∧
  12 * pad + 2 ≤ H' ∧
  (∀ y : Fin B.height, cut ≤ y.val → y.val < cut + 12 * pad →
    ∀ x : Fin B.width, B.cell y x = decide (x.val ≠ 6 * s + 2)) ∧
  (∀ y : ℕ, cut ≤ y → y < cut + H' - 2 →
    B.occupied ((6 * s + 1 : ℕ), (y : ℤ)) = true ∧
    B.occupied ((6 * s + 2 : ℕ), (y : ℤ)) = false ∧
    B.occupied ((6 * s + 3 : ℕ), (y : ℤ)) = true) ∧
  B.occupied ((6 * s + 2 : ℕ), ((cut + H' - 2 : ℕ) : ℤ)) = true

lemma lockWellSealed_init (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hst : 3 ≤ st) :
    LockWellSealed (paddedReservoirBoard P pad K st r) P.s pad K (12 * pad + baseHeight P) r := by
  set B0 := paddedReservoirBoard P pad K st r
  set cut := r + 2 + 4 * K
  set H' := 12 * pad + baseHeight P
  have hB0_H : cut + H' + 3 ≤ B0.height := by simp [B0, paddedReservoirBoard, baseBoard, cut, H']; omega
  refine ⟨hpad, hB0_H, rfl, by dsimp [H']; unfold baseHeight; omega, ?_, ?_, ?_⟩
  · intro y hy1 hy2 x
    have h1 : ¬ y.val < r := by omega
    have h2 : ¬ y.val = r := by omega
    have h3 : ¬ y.val = r + 1 := by omega
    have h4 : ¬ y.val < r + 2 + 4 * K := by omega
    have h5 : y.val < r + 2 + 4 * K + 12 * pad := by omega
    simp [B0, paddedReservoirBoard, h1, h2, h3, h4, h5]
  · intro y hy1 hy2
    have hyH : y < B0.height := by omega
    have h1 : ¬ y < r := by omega
    have h2 : ¬ y = r := by omega
    have h3 : ¬ y = r + 1 := by omega
    have h4 : ¬ y < r + 2 + 4 * K := by omega
    have hocc_eq : ∀ x : ℕ, (hx : x < B0.width) →
        B0.occupied ((x : ℕ), (y : ℤ)) = B0.cell ⟨y, hyH⟩ ⟨x, hx⟩ := by
      intro x hx; unfold Board.occupied
      rw [dif_pos (by omega), dif_pos (by omega)]; simp
    rw [hocc_eq (6 * P.s + 1) (by dsimp [B0, paddedReservoirBoard]; omega),
      hocc_eq (6 * P.s + 2) (by dsimp [B0, paddedReservoirBoard]; omega),
      hocc_eq (6 * P.s + 3) (by dsimp [B0, paddedReservoirBoard]; omega)]
    by_cases h5 : y < r + 2 + 4 * K + 12 * pad
    · refine ⟨?_, ?_, ?_⟩ <;>
        (simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte]; simp)
    · have h6 : y < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
      have hy_sub : (y : ℤ) - (r + 2 + 4 * K + 12 * pad) = ((y - (cut + 12 * pad) : ℕ) : ℤ) := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s + 1 < 6 * P.s + 3 by omega, ↓reduceIte]
        rw [hy_sub]; unfold Board.occupied
        rw [dif_pos (by dsimp [baseBoard]; omega), dif_pos (by dsimp [baseBoard]; omega)]
        simp only [Int.toNat_natCast, baseBoard, show ¬ (y - (cut + 12 * pad) ≥ baseHeight P) by omega,
          show ¬ (6 * P.s + 1 < 6 * P.s) by omega, show ¬ (6 * P.s + 1 = 6 * P.s) by omega,
          ↓reduceIte, decide_eq_true_eq]
        dsimp [cut, H'] at hy2; omega
      · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s + 2 < 6 * P.s + 3 by omega, ↓reduceIte]
        rw [hy_sub]; unfold Board.occupied
        rw [dif_pos (by dsimp [baseBoard]; omega), dif_pos (by dsimp [baseBoard]; omega)]
        simp only [Int.toNat_natCast, baseBoard, show ¬ (y - (cut + 12 * pad) ≥ baseHeight P) by omega,
          show ¬ (6 * P.s + 2 < 6 * P.s) by omega, show ¬ (6 * P.s + 2 = 6 * P.s) by omega,
          show ¬ (6 * P.s + 2 = 6 * P.s + 1) by omega, ↓reduceIte, decide_eq_false_iff_not]
        dsimp [cut, H'] at hy2; omega
      · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show ¬ (6 * P.s + 3 < 6 * P.s + 3) by omega,
          ↓reduceIte, decide_eq_true_eq]
        exact h6
  · have hx2 : 6 * P.s + 2 < B0.width := by dsimp [B0, paddedReservoirBoard]; omega
    have hy2_lt : cut + H' - 2 < B0.height := by omega
    have hocc2 : B0.occupied (((6 * P.s + 2 : ℕ) : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) =
        B0.cell ⟨cut + H' - 2, hy2_lt⟩ ⟨6 * P.s + 2, hx2⟩ := by
      unfold Board.occupied; dsimp only; rw [dif_pos (by omega), dif_pos (by omega)]
      congr 1
    rw [hocc2]
    have h1 : ¬ cut + H' - 2 < r := by omega
    have h2 : ¬ cut + H' - 2 = r := by omega
    have h3 : ¬ cut + H' - 2 = r + 1 := by omega
    have h4 : ¬ cut + H' - 2 < r + 2 + 4 * K := by omega
    have h5 : ¬ cut + H' - 2 < r + 2 + 4 * K + 12 * pad := by dsimp [cut, H']; unfold baseHeight; omega
    simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s + 2 < 6 * P.s + 3 by omega, ↓reduceIte]
    have hy_sub : ((cut + H' - 2 : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = ((baseHeight P - 2 : ℕ) : ℤ) := by
      dsimp [cut, H']; unfold baseHeight; omega
    rw [hy_sub]; unfold Board.occupied
    rw [dif_pos (by dsimp [baseBoard, baseHeight]; omega), dif_pos (by dsimp [baseBoard]; omega)]
    simp only [Int.toNat_natCast, baseBoard,
      show ¬ (baseHeight P - 2 ≥ baseHeight P) by unfold baseHeight; omega,
      show ¬ (6 * P.s + 2 < 6 * P.s) by omega, show ¬ (6 * P.s + 2 = 6 * P.s) by omega,
      show ¬ (6 * P.s + 2 = 6 * P.s + 1) by omega, ↓reduceIte, decide_eq_true_eq]
    unfold baseHeight; omega

lemma emptyAdjacent_above_lock_well {B : Board} {s pad K H' r : ℕ}
    (hlock : LockWellSealed B s pad K H' r) {z z' : Cell}
    (hadj : EmptyAdjacent B z z')
    (hz : ((r + 2 + 4 * K + 12 * pad : ℕ) : ℤ) ≤ z.2 ∧
      (z.2 < ((r + 2 + 4 * K + H' - 2 : ℕ) : ℤ) → z.1 ≠ 6 * (s : ℤ) + 2)) :
    ((r + 2 + 4 * K + 12 * pad : ℕ) : ℤ) ≤ z'.2 ∧
      (z'.2 < ((r + 2 + 4 * K + H' - 2 : ℕ) : ℤ) → z'.1 ≠ 6 * (s : ℤ) + 2) := by
  set cut := r + 2 + 4 * K
  rcases hlock with ⟨hpad, hH, hw, hH2, hbuf, hwell, hstop⟩
  rcases hadj with ⟨hzf, hz'f, hdist⟩
  have hstep : (z'.1 = z.1 + 1 ∧ z'.2 = z.2) ∨ (z'.1 = z.1 - 1 ∧ z'.2 = z.2) ∨
      (z'.1 = z.1 ∧ z'.2 = z.2 + 1) ∨ (z'.1 = z.1 ∧ z'.2 = z.2 - 1) := by
    rcases abs_cases (z.1 - z'.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (z.2 - z'.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  have hnot_well : z'.2 < ((cut + H' - 2 : ℕ) : ℤ) → z'.1 ≠ 6 * (s : ℤ) + 2 := by
    intro hlt hx
    have hz'ge : (cut : ℤ) ≤ z'.2 := by omega
    rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hocc := (hwell z'.2.toNat (by omega) (by omega)).1
      have heq : (((6 * s + 1 : ℕ) : ℤ), (z'.2.toNat : ℤ)) = z := by ext <;> omega
      rw [heq, hzf] at hocc; cases hocc
    · have hocc := (hwell z'.2.toNat (by omega) (by omega)).2.2
      have heq : (((6 * s + 3 : ℕ) : ℤ), (z'.2.toNat : ℤ)) = z := by ext <;> omega
      rw [heq, hzf] at hocc; cases hocc
    · exact hz.2 (by omega) (by omega)
    · by_cases htop : z.2 = ((cut + H' - 2 : ℕ) : ℤ)
      · have heq : (((6 * s + 2 : ℕ) : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) = z := by ext <;> omega
        rw [heq, hzf] at hstop; cases hstop
      · exact hz.2 (by omega) (by omega)
  refine ⟨?_, hnot_well⟩
  by_contra hlt; push Not at hlt
  have hlt2 : z'.2 < ((cut + H' - 2 : ℕ) : ℤ) := by omega
  have hne := hnot_well hlt2
  unfold Board.occupied at hz'f
  rw [dif_pos (by omega)] at hz'f
  split_ifs at hz'f with hxB
  have hb := hbuf ⟨z'.2.toNat, by omega⟩ (by dsimp; omega) (by dsimp; omega) ⟨z'.1.toNat, by omega⟩
  rw [hb] at hz'f; simp at hz'f; omega

lemma reachable_above_lock_well {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s pad K H' r : ℕ}
    (hlock : LockWellSealed B s pad K H' r) {t : Piece} {q' : PieceState}
    (hreach : Relation.ReflTransGen (Move R B) (spawn B t) q') :
    ∀ z ∈ q'.cells,
      ((r + 2 + 4 * K + 12 * pad : ℕ) : ℤ) ≤ z.2 ∧
      (z.2 < ((r + 2 + 4 * K + H' - 2 : ℕ) : ℤ) → z.1 ≠ 6 * (s : ℤ) + 2) := by
  have hcomp : ∀ z z', Relation.ReflTransGen (EmptyAdjacent B) z z' →
      (((r + 2 + 4 * K + 12 * pad : ℕ) : ℤ) ≤ z.2 ∧
        (z.2 < ((r + 2 + 4 * K + H' - 2 : ℕ) : ℤ) → z.1 ≠ 6 * (s : ℤ) + 2)) →
      (((r + 2 + 4 * K + 12 * pad : ℕ) : ℤ) ≤ z'.2 ∧
        (z'.2 < ((r + 2 + 4 * K + H' - 2 : ℕ) : ℤ) → z'.1 ≠ 6 * (s : ℤ) + 2)) := by
    intro z z' hrt hz
    induction hrt with
    | refl => exact hz
    | tail _ hstep ih => exact emptyAdjacent_above_lock_well hlock hstep ih
  induction hreach with
  | refl =>
    intro z hz
    have hge := spawn_cells_ge_of_height (B := B) (cut := r + 2 + 4 * K + H') hlock.2.1 t z hz
    have hH2 := hlock.2.2.2.1
    exact ⟨by omega, fun _ => by omega⟩
  | tail _ hstep ih =>
    rename_i q1 q2 _
    intro z' hz'
    obtain ⟨z, hz⟩ := cells_nonempty_B q1
    exact hcomp z z' (hReason.1 B q1 q2 hstep z hz z' hz') (ih z hz)

lemma trajectory_dropRows_transfer {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s pad K H' r : ℕ}
    (hlock : LockWellSealed B s pad K H' r)
    (hrad : R.radius + 1 ≤ 12 * pad)
    {t : Piece} {q : PieceState} (htraj : Trajectory R B t q) :
    Trajectory R (dropRows B (r + 2 + 4 * K)) t (shiftDown (r + 2 + 4 * K) q) := by
  set cut := r + 2 + 4 * K
  have hcut_le : cut ≤ B.height := by have := hlock.2.1; omega
  rcases htraj with ⟨hcl0, hpath, hfix⟩
  have hge_spawn : ∀ z ∈ (spawn B t).cells, (cut : ℤ) ≤ z.2 := fun z hz => by
    have := (reachable_above_lock_well hReason hlock .refl z hz).1; omega
  refine ⟨?_, ?_, hfix⟩
  · rw [dropRows_spawn_eq B cut hcut_le t]
    exact (dropRows_clear_iff hcut_le hge_spawn).mpr hcl0
  · rw [dropRows_spawn_eq B cut hcut_le t]
    have hlift : ∀ q', Relation.ReflTransGen (Move R B) (spawn B t) q' →
        Relation.ReflTransGen (Move R (dropRows B cut)) (shiftDown cut (spawn B t)) (shiftDown cut q') := by
      intro q' hp
      induction hp with
      | refl => exact .refl
      | tail hprev hstep ih =>
        rename_i q1 q2
        have hge1 : ∀ z ∈ q1.cells, (cut : ℤ) + R.radius ≤ z.2 := fun z hz => by
          have := (reachable_above_lock_well hReason hlock hprev z hz).1; omega
        have hge2 : ∀ z ∈ q2.cells, (cut : ℤ) + R.radius ≤ z.2 := fun z hz => by
          have := (reachable_above_lock_well hReason hlock (hprev.tail hstep) z hz).1; omega
        have hge_down : ∀ z ∈ (translate q1 0 (-1)).cells, (cut : ℤ) ≤ z.2 := by
          intro z hz
          unfold translate PieceState.cells at hz
          dsimp only at hz
          rw [List.mem_map] at hz
          rcases hz with ⟨w, hw, rfl⟩
          set u := if q1.kind = .Sq then w else clockwise^[q1.orientation.val] w
          have hmem : (q1.position.1 + u.1, q1.position.2 + u.2) ∈ q1.cells :=
            List.mem_map.mpr ⟨w, hw, rfl⟩
          have h1 := (reachable_above_lock_well hReason hlock hprev _ hmem).1
          dsimp only [u, cut] at h1 ⊢; omega
        exact ih.tail (move_dropRows_transfer hcut_le hstep hge1 hge2 hge_down)
    exact hlift q hpath

/-! ### `settle = insert` When Every Row Has a `false` Cell -/

lemma gain_zero_and_settle_eq_insert {B : Board} {q : PieceState}
    (hhas_false : ∀ y : Fin B.height, ∃ x : Fin B.width, (B.insert q).cell y x = false) :
    B.gain q = 0 ∧ B.settle q = B.insert q := by
  set B1 := B.insert q
  have hnot_full : ∀ row ∈ B1.rows, row.all id = false := by
    intro row hmem
    rw [List.mem_iff_getElem] at hmem
    rcases hmem with ⟨i, hi, rfl⟩
    simp only [Board.rows, List.length_ofFn] at hi
    simp only [Board.rows, List.getElem_ofFn]
    obtain ⟨x, hx⟩ := hhas_false ⟨i, hi⟩
    rw [Bool.eq_false_iff]; intro hall
    have ht := (row_all_id_iff B1 ⟨i, hi⟩).mp hall x
    exact Bool.noConfusion (hx.symm.trans ht)
  have hgain : B.gain q = 0 := by
    unfold Board.gain Board.fullCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro row hmem; simp [hnot_full row hmem]
  refine ⟨hgain, ?_⟩
  have hsurv : B1.rows.filter (fun r => !(r.all id)) = B1.rows := by
    rw [List.filter_eq_self]
    intro row hmem; simp [hnot_full row hmem]
  cases B with
  | mk H W c =>
    unfold Board.settle Board.compress
    dsimp only at B1 hsurv ⊢
    congr 1; funext y x
    change ((B1.rows.filter fun r => !(r.all id)).getD y.val []).getD x.val false = B1.cell y x
    rw [hsurv]
    have hy : y.val < B1.rows.length := by simp only [Board.rows, List.length_ofFn]; exact y.isLt
    have hx : x.val < (B1.rows[y.val]).length := by
      simp only [Board.rows, List.getElem_ofFn, List.length_ofFn]; exact x.isLt
    rw [List.getD_eq_getElem _ _ hy, List.getD_eq_getElem _ _ hx]
    simp only [Board.rows, List.getElem_ofFn]; rfl

/-! ### Non-`.RG` Pieces Cannot Fit Inside the 4-Cell Lock Cap -/

private def lockCapFit (t : Piece) (o : Fin 4) (pos : Cell) : Bool :=
  (offsetsC t o).all fun w =>
    decide ((pos.1 + w.1, pos.2 + w.2) ∈ ([(0, 0), (0, 1), (1, 1), (2, 1)] : List Cell))

private lemma no_nonRG_fits_lockCap :
    ∀ t ∈ ([.LG, .LS, .Sq, .I] : List Piece), ∀ o : Fin 4,
      ∀ pos ∈ ([(0, 0), (0, 1), (1, 1), (2, 1)] : List Cell),
        lockCapFit t o pos = false := by
  decide

/-- Full invariant maintained on `B` throughout `phase1Pieces P`. -/
def Phase1Inv (B : Board) (P : ThreePartition) (pad K r : ℕ) : Prop :=
  let cut := r + 2 + 4 * K
  let H' := 12 * pad + baseHeight P
  ChimneySealInv B (r + 2) (6 * (P.s + pad)) (6 * P.s + 3) (4 * K) H' ∧
  LockWellSealed B P.s pad K H' r ∧
  BucketFrame (dropRows B cut) (P.s + pad) H' ∧
  (∀ x y : ℕ, 6 * P.s + 3 ≤ x → x < B.width → cut ≤ y → y < cut + H' →
    B.occupied ((x : ℤ), (y : ℤ)) = true) ∧
  (∀ y : ℕ, cut ≤ y → y < cut + H' - 2 →
    B.occupied (6 * (P.s : ℤ), (y : ℤ)) = true) ∧
  B.occupied (6 * (P.s : ℤ) + 1, ((cut + H' - 2 : ℕ) : ℤ)) = true ∧
  B.occupied (6 * (P.s : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) = false ∧
  B.occupied (6 * (P.s : ℤ), ((cut + H' - 1 : ℕ) : ℤ)) = false ∧
  (∀ y : Fin B.height, cut + H' ≤ y.val → ∀ x : Fin B.width, B.cell y x = false)

lemma phase1Inv_init (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hst : 3 ≤ st) :
    Phase1Inv (paddedReservoirBoard P pad K st r) P pad K r := by
  set B0 := paddedReservoirBoard P pad K st r
  set cut := r + 2 + 4 * K
  set H' := 12 * pad + baseHeight P
  have hB0_H : cut + H' + 3 ≤ B0.height := by simp [B0, paddedReservoirBoard, baseBoard, cut, H']; omega
  have hocc_eq : ∀ (x y : ℕ) (hx : x < B0.width) (hy : y < B0.height),
      B0.occupied ((x : ℤ), (y : ℤ)) = B0.cell ⟨y, hy⟩ ⟨x, hx⟩ := by
    intro x y hx hy; unfold Board.occupied
    rw [dif_pos (by omega), dif_pos (by omega)]; simp
  refine ⟨chimneySealInv_init P pad K st r hpad hst,
    lockWellSealed_init P pad K st r hpad hst,
    dropRows_init_bucketFrame P pad K st r hpad hst,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx1 hx2 hy1 hy2
    rw [hocc_eq x y hx2 (by omega)]
    have h1 : ¬ y < r := by omega
    have h2 : ¬ y = r := by omega
    have h3 : ¬ y = r + 1 := by omega
    have h4 : ¬ y < r + 2 + 4 * K := by omega
    by_cases h5 : y < r + 2 + 4 * K + 12 * pad
    · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte, decide_eq_true_eq]; omega
    · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show ¬ x < 6 * P.s + 3 by omega,
        ↓reduceIte, decide_eq_true_eq]
      omega
  · intro y hy1 hy2
    have hx : 6 * P.s < B0.width := by dsimp [B0, paddedReservoirBoard]; omega
    have hcast : (6 * (P.s : ℤ), (y : ℤ)) = (((6 * P.s : ℕ) : ℤ), (y : ℤ)) := by ext <;> simp
    rw [hcast, hocc_eq (6 * P.s) y hx (by omega)]
    have h1 : ¬ y < r := by omega
    have h2 : ¬ y = r := by omega
    have h3 : ¬ y = r + 1 := by omega
    have h4 : ¬ y < r + 2 + 4 * K := by omega
    by_cases h5 : y < r + 2 + 4 * K + 12 * pad
    · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte, decide_eq_true_eq]; omega
    · simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s < 6 * P.s + 3 by omega, ↓reduceIte]
      have hy_sub : (y : ℤ) - (r + 2 + 4 * K + 12 * pad) = ((y - (cut + 12 * pad) : ℕ) : ℤ) := by omega
      rw [hy_sub]; unfold Board.occupied; dsimp only
      rw [dif_pos (by dsimp [baseBoard]; omega), dif_pos (by dsimp [baseBoard]; omega)]
      simp only [Int.toNat_natCast, baseBoard,
        show ¬ (y - (cut + 12 * pad) ≥ baseHeight P) by dsimp [cut] at *; omega,
        show ¬ (6 * P.s < 6 * P.s) by omega, ↓reduceIte, decide_eq_true_eq]
      dsimp [cut] at *; omega
  · have hx : 6 * P.s + 1 < B0.width := by dsimp [B0, paddedReservoirBoard]; omega
    have hcast : (6 * (P.s : ℤ) + 1, ((cut + H' - 2 : ℕ) : ℤ)) =
        (((6 * P.s + 1 : ℕ) : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) := by ext <;> simp
    rw [hcast, hocc_eq (6 * P.s + 1) (cut + H' - 2) hx (by omega)]
    have h1 : ¬ cut + H' - 2 < r := by omega
    have h2 : ¬ cut + H' - 2 = r := by omega
    have h3 : ¬ cut + H' - 2 = r + 1 := by omega
    have h4 : ¬ cut + H' - 2 < r + 2 + 4 * K := by omega
    have h5 : ¬ cut + H' - 2 < r + 2 + 4 * K + 12 * pad := by dsimp [cut, H']; unfold baseHeight; omega
    simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s + 1 < 6 * P.s + 3 by omega, ↓reduceIte]
    have hy_sub : ((cut + H' - 2 : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = ((baseHeight P - 2 : ℕ) : ℤ) := by
      dsimp [cut, H']; unfold baseHeight; omega
    rw [hy_sub]; unfold Board.occupied
    rw [dif_pos (by dsimp [baseBoard, baseHeight]; omega), dif_pos (by dsimp [baseBoard]; omega)]
    simp only [Int.toNat_natCast, baseBoard,
      show ¬ (baseHeight P - 2 ≥ baseHeight P) by unfold baseHeight; omega,
      show ¬ (6 * P.s + 1 < 6 * P.s) by omega, show ¬ (6 * P.s + 1 = 6 * P.s) by omega,
      ↓reduceIte, decide_eq_true_eq]
    unfold baseHeight; omega
  · have hx : 6 * P.s < B0.width := by dsimp [B0, paddedReservoirBoard]; omega
    have hcast : (6 * (P.s : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) =
        (((6 * P.s : ℕ) : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) := by ext <;> simp
    rw [hcast, hocc_eq (6 * P.s) (cut + H' - 2) hx (by omega)]
    have h1 : ¬ cut + H' - 2 < r := by omega
    have h2 : ¬ cut + H' - 2 = r := by omega
    have h3 : ¬ cut + H' - 2 = r + 1 := by omega
    have h4 : ¬ cut + H' - 2 < r + 2 + 4 * K := by omega
    have h5 : ¬ cut + H' - 2 < r + 2 + 4 * K + 12 * pad := by dsimp [cut, H']; unfold baseHeight; omega
    simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s < 6 * P.s + 3 by omega, ↓reduceIte]
    have hy_sub : ((cut + H' - 2 : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = ((baseHeight P - 2 : ℕ) : ℤ) := by
      dsimp [cut, H']; unfold baseHeight; omega
    rw [hy_sub]; unfold Board.occupied
    rw [dif_pos (by dsimp [baseBoard, baseHeight]; omega), dif_pos (by dsimp [baseBoard]; omega)]
    simp only [Int.toNat_natCast, baseBoard,
      show ¬ (baseHeight P - 2 ≥ baseHeight P) by unfold baseHeight; omega,
      show ¬ (6 * P.s < 6 * P.s) by omega, ↓reduceIte, decide_eq_false_iff_not]
    unfold baseHeight; omega
  · have hx : 6 * P.s < B0.width := by dsimp [B0, paddedReservoirBoard]; omega
    have hcast : (6 * (P.s : ℤ), ((cut + H' - 1 : ℕ) : ℤ)) =
        (((6 * P.s : ℕ) : ℤ), ((cut + H' - 1 : ℕ) : ℤ)) := by ext <;> simp
    rw [hcast, hocc_eq (6 * P.s) (cut + H' - 1) hx (by omega)]
    have h1 : ¬ cut + H' - 1 < r := by omega
    have h2 : ¬ cut + H' - 1 = r := by omega
    have h3 : ¬ cut + H' - 1 = r + 1 := by omega
    have h4 : ¬ cut + H' - 1 < r + 2 + 4 * K := by omega
    have h5 : ¬ cut + H' - 1 < r + 2 + 4 * K + 12 * pad := by dsimp [cut, H']; unfold baseHeight; omega
    simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, show 6 * P.s < 6 * P.s + 3 by omega, ↓reduceIte]
    have hy_sub : ((cut + H' - 1 : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = ((baseHeight P - 1 : ℕ) : ℤ) := by
      dsimp [cut, H']; unfold baseHeight; omega
    rw [hy_sub]; unfold Board.occupied
    rw [dif_pos (by dsimp [baseBoard, baseHeight]; omega), dif_pos (by dsimp [baseBoard]; omega)]
    simp only [Int.toNat_natCast, baseBoard,
      show ¬ (baseHeight P - 1 ≥ baseHeight P) by unfold baseHeight; omega,
      show ¬ (6 * P.s < 6 * P.s) by omega, ↓reduceIte, decide_eq_false_iff_not]
    unfold baseHeight; omega
  · intro y hy x
    have h1 : ¬ y.val < r := by omega
    have h2 : ¬ y.val = r := by omega
    have h3 : ¬ y.val = r + 1 := by omega
    have h4 : ¬ y.val < r + 2 + 4 * K := by omega
    have h5 : ¬ y.val < r + 2 + 4 * K + 12 * pad := by unfold baseHeight at hy; omega
    simp only [B0, paddedReservoirBoard, h1, h2, h3, h4, h5, ↓reduceIte]
    split_ifs with hxs
    · unfold Board.occupied
      have hy_lt : (y.val : ℤ) - (r + 2 + 4 * K + 12 * pad) < (baseBoard P st).height := by
        have := y.isLt; simp [B0, paddedReservoirBoard] at this; omega
      rw [dif_pos (by omega), dif_pos (by simp [baseBoard]; omega)]
      have hge : baseHeight P ≤ ((y.val : ℤ) - (r + 2 + 4 * K + 12 * pad)).toNat := by omega
      simp [baseBoard, hge]
    · simp; omega

/-- Single zero-waste step during `phase1Pieces P`: piece `q` lifts to `u = shiftDown cut q`
in some bucket `j : Fin P.s` with `0 ≤ z.2 < H'`, and `B.settle q = B.insert q` preserves `Phase1Inv`! -/
lemma phase1Inv_step {R : Rotation} (hReason : Reasonable R)
    {P : ThreePartition} (hs : 0 < P.s)
    {pad K r : ℕ} (hrad : R.radius + 1 ≤ 12 * pad) (hK : 1 ≤ K)
    {B : Board} (hinv : Phase1Inv B P pad K r)
    {t : Piece} (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece))
    {q : PieceState} (htraj : Trajectory R B t q)
    (hinside : ∀ z ∈ q.cells, ((r + 2 : ℕ) : ℤ) ≤ z.2 ∧
      z.2 < (((r + 2) + (4 * K + (12 * pad + baseHeight P)) : ℕ) : ℤ)) :
    let cut := r + 2 + 4 * K
    let H' := 12 * pad + baseHeight P
    let u := shiftDown cut q
    (∃ j : Fin P.s, InBucket j.val u) ∧
    (∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ)) ∧
    Trajectory R (dropRows B cut) t u ∧
    B.settle q = B.insert q ∧
    nextChimneyUpper B (r + 2) (4 * K) H' q = (4 * K, H') ∧
    Phase1Inv (B.insert q) P pad K r := by
  set cut := r + 2 + 4 * K
  set H' := 12 * pad + baseHeight P
  set U := dropRows B cut
  set u := shiftDown cut q
  rcases hinv with ⟨hchim, hlock, hframe, hpad_wall, h6s_low, h6s1_cap, h6s_cap2, h6s_cap1, htop_empty⟩
  have hcut_le : cut ≤ B.height := by have := hlock.2.1; omega
  have hreach_well := reachable_above_lock_well hReason hlock htraj.2.1
  have htrajU : Trajectory R U t u := trajectory_dropRows_transfer hReason hlock hrad htraj
  have hclU : U.Clear u := (trajectory_clear_and_blocked htrajU).1
  have hu_kind : u.kind = t := trajectory_kind_eq htrajU
  have hu_y : ∀ z ∈ u.cells, ((12 * pad : ℕ) : ℤ) ≤ z.2 ∧ z.2 < (H' : ℤ) ∧
      (z.2 < ((H' - 2 : ℕ) : ℤ) → z.1 ≠ 6 * (P.s : ℤ) + 2) := by
    intro z hz
    rw [shiftDown_cells, List.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw1 := hreach_well w hw
    have hw2 := hinside w hw
    have hH2 : 2 ≤ H' := by have := hlock.2.2.2.1; omega
    exact ⟨by dsimp [cut] at *; omega, by dsimp [cut, H'] at *; omega,
      fun hlt => hw1.2 (by dsimp [cut, H'] at *; omega)⟩
  have hu_y0 : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ) :=
    fun z hz => ⟨by have := (hu_y z hz).1; omega, (hu_y z hz).2.1⟩
  -- Every `z ∈ u.cells` has `0 ≤ z.1 < 6 * P.s + 3`
  have hu_x_lt : ∀ z ∈ u.cells, 0 ≤ z.1 ∧ z.1 < 6 * (P.s : ℤ) + 3 := by
    intro z hz
    have hocc := hclU z hz
    have hyz := hu_y0 z hz
    have hge_cut : (cut : ℤ) ≤ z.2 + cut := by omega
    have hoccB : B.occupied (z.1, z.2 + cut) = false := by
      have h1 := dropRows_occupied_ge B cut hcut_le (z.1, z.2 + cut) hge_cut
      dsimp only [U] at hocc; rw [add_sub_cancel_right] at h1
      exact h1.symm.trans hocc
    unfold Board.occupied at hoccB
    split_ifs at hoccB with hyB hxB
    refine ⟨hxB.1, ?_⟩
    by_contra hge
    have ht_wall := hpad_wall z.1.toNat (z.2 + cut).toNat (by omega) (by omega) (by omega) (by omega)
    have hcast : ((z.1.toNat : ℤ), ((z.2 + cut).toNat : ℤ)) = (z.1, z.2 + cut) := by ext <;> omega
    rw [hcast] at ht_wall
    unfold Board.occupied at ht_wall
    rw [dif_pos hyB, dif_pos hxB] at ht_wall
    rw [ht_wall] at hoccB; cases hoccB
  -- Rule out `6 * P.s ≤ u.position.1` using `no_nonRG_fits_lockCap`!
  have hpos_mem : u.position ∈ u.cells := position_mem_cells_A u
  have hpos_lt_6s : u.position.1 < 6 * (P.s : ℤ) := by
    by_contra hge; push Not at hge
    have hpos_lt3 := (hu_x_lt _ hpos_mem).2
    -- Left wall `6 * P.s - 1` and right wall `6 * P.s + 3` are `true` in `U` for all `0 ≤ y < H'`!
    have hwL : ∀ y : ℤ, 0 ≤ y → y < (H' : ℤ) → U.occupied (6 * (P.s : ℤ) - 1, y) = true := by
      intro y hy0 hy1
      let j_last : Fin (P.s + pad) := ⟨P.s - 1, by omega⟩
      have hrw := bucketCell_right_wall_B hframe j_last hy0 hy1
      unfold bucketCell at hrw
      have hxeq : 6 * (j_last.val : ℤ) + 5 = 6 * (P.s : ℤ) - 1 := by dsimp [j_last]; omega
      rwa [hxeq] at hrw
    have hwR : ∀ y : ℤ, 0 ≤ y → y < (H' : ℤ) → U.occupied (6 * (P.s : ℤ) + 3, y) = true := by
      intro y hy0 hy1
      have h1 := dropRows_occupied_ge B cut hcut_le (6 * (P.s : ℤ) + 3, y + cut) (by omega)
      rw [add_sub_cancel_right] at h1; dsimp [U]; rw [h1]
      have h2 := hpad_wall (6 * P.s + 3) (y + cut).toNat (by omega)
        (by have := hlock.2.2.1; have := hlock.1; omega) (by omega) (by omega)
      convert h2 using 2; ext <;> omega
    have hall_lock := clear_between_vertical_walls hclU hu_y0 hwL hwR ⟨by omega, hpos_lt3⟩
    -- Every `z ∈ u.cells` lies in `{(6s + dx, H' - 2 + dy) | (dx, dy) ∈ [(0,0), (0,1), (1,1), (2,1)]}`!
    have hall_cap : ∀ z ∈ u.cells,
        (z.1 - 6 * (P.s : ℤ), z.2 - ((H' - 2 : ℕ) : ℤ)) ∈
          ([(0, 0), (0, 1), (1, 1), (2, 1)] : List Cell) := by
      intro z hz
      have hzx := hall_lock z hz
      have hzy := hu_y z hz
      have hoccU := hclU z hz
      have hoccB : B.occupied (z.1, z.2 + cut) = false := by
        have h1 := dropRows_occupied_ge B cut hcut_le (z.1, z.2 + cut) (by omega)
        rw [add_sub_cancel_right] at h1; exact h1.symm.trans hoccU
      have hH2 : 2 ≤ H' := by have := hlock.2.2.2.1; omega
      by_cases hy_low : z.2 < ((H' - 2 : ℕ) : ℤ)
      · exfalso
        have hne2 := hzy.2.2 hy_low
        have hx_cases : z.1 = 6 * (P.s : ℤ) ∨ z.1 = 6 * (P.s : ℤ) + 1 := by omega
        rcases hx_cases with hx0 | hx1
        · have htB := h6s_low (z.2 + cut).toNat (by omega) (by omega)
          have heq : (6 * (P.s : ℤ), ((z.2 + cut).toNat : ℤ)) = (z.1, z.2 + cut) := by ext <;> omega
          rw [heq, hoccB] at htB; cases htB
        · have htB := (hlock.2.2.2.2.2.1 (z.2 + cut).toNat (by omega) (by omega)).1
          have heq : (((6 * P.s + 1 : ℕ) : ℤ), ((z.2 + cut).toNat : ℤ)) = (z.1, z.2 + cut) := by ext <;> omega
          rw [heq, hoccB] at htB; cases htB
      · by_cases hy_mid : z.2 = ((H' - 2 : ℕ) : ℤ)
        · have hne1 : z.1 ≠ 6 * (P.s : ℤ) + 1 := by
            intro hx1
            have heq : (z.1, z.2 + cut) = (6 * (P.s : ℤ) + 1, ((cut + H' - 2 : ℕ) : ℤ)) := by ext <;> omega
            rw [heq, h6s1_cap] at hoccB; cases hoccB
          have hne2 : z.1 ≠ 6 * (P.s : ℤ) + 2 := by
            intro hx2
            have hstop := hlock.2.2.2.2.2.2
            have heq : (((6 * P.s + 2 : ℕ) : ℤ), ((cut + H' - 2 : ℕ) : ℤ)) = (z.1, z.2 + cut) := by ext <;> omega
            rw [heq, hoccB] at hstop; cases hstop
          have hx0 : z.1 = 6 * (P.s : ℤ) := by omega
          simp [hx0, hy_mid]
        · have hy_top : z.2 = ((H' - 1 : ℕ) : ℤ) := by omega
          have hx_cases : z.1 - 6 * (P.s : ℤ) = 0 ∨ z.1 - 6 * (P.s : ℤ) = 1 ∨
              z.1 - 6 * (P.s : ℤ) = 2 := by omega
          have hdy : z.2 - ((H' - 2 : ℕ) : ℤ) = 1 := by omega
          rw [hdy]
          rcases hx_cases with h | h | h <;> simp [h]
    set relPos : Cell := (u.position.1 - 6 * (P.s : ℤ), u.position.2 - ((H' - 2 : ℕ) : ℤ))
    have hrelPos_in := hall_cap u.position hpos_mem
    have hfit_false := no_nonRG_fits_lockCap t ht u.orientation relPos hrelPos_in
    have hfit_true : lockCapFit t u.orientation relPos = true := by
      unfold lockCapFit; rw [List.all_eq_true]
      intro w hw; rw [decide_eq_true_eq]
      have hmem_u : (u.position.1 + w.1, u.position.2 + w.2) ∈ u.cells := by
        rw [piece_cells_eq_map_offsetsC, hu_kind]
        exact List.mem_map.mpr ⟨w, hw, rfl⟩
      have hc := hall_cap _ hmem_u
      convert hc using 1; ext <;> dsimp [relPos] <;> omega
    rw [hfit_true] at hfit_false; cases hfit_false
  -- Now `0 ≤ u.position.1 < 6 * P.s`, so `u` lies inside bucket `j0`!
  have hpos_ge0 := (hu_x_lt _ hpos_mem).1
  set j0_nat := u.position.1.toNat / 6
  have hj0_lt : j0_nat < P.s := by omega
  let j0 : Fin P.s := ⟨j0_nat, hj0_lt⟩
  let j0_pad : Fin (P.s + pad) := ⟨j0_nat, by omega⟩
  have hpos_not_wall : u.position.1 ≠ 6 * (j0.val : ℤ) + 5 := by
    intro heq
    have hrw := bucketCell_right_wall_B hframe j0_pad (hu_y0 _ hpos_mem).1 (hu_y0 _ hpos_mem).2
    unfold bucketCell at hrw
    have hp : (6 * (j0_pad.val : ℤ) + 5, u.position.2) = u.position := by ext; (dsimp [j0_pad, j0]; omega); rfl
    rw [hp, hclU _ hpos_mem] at hrw; cases hrw
  have hpos_j0 : 6 * (j0.val : ℤ) - 1 < u.position.1 ∧ u.position.1 < 6 * (j0.val : ℤ) + 5 := by
    simp only [j0, j0_nat] at hpos_not_wall ⊢; omega
  have hwL_j0 : ∀ y : ℤ, 0 ≤ y → y < (H' : ℤ) → U.occupied (6 * (j0.val : ℤ) - 1, y) = true := by
    intro y hy0 hy1
    have hlw := bucketCell_left_wall_B hframe j0_pad hy0 hy1
    simpa [bucketCell, j0_pad, j0, sub_eq_add_neg] using hlw
  have hwR_j0 : ∀ y : ℤ, 0 ≤ y → y < (H' : ℤ) → U.occupied (6 * (j0.val : ℤ) + 5, y) = true := by
    intro y hy0 hy1
    exact bucketCell_right_wall_B hframe j0_pad hy0 hy1
  have hin_j0_strict := clear_between_vertical_walls hclU hu_y0 hwL_j0 hwR_j0 hpos_j0
  have hin_j0 : InBucket j0.val u := fun z hz => by
    have := hin_j0_strict z hz; exact ⟨by omega, by omega⟩
  -- Every cell `w ∈ q.cells` satisfies `w.1 < 6 * P.s` and `cut + 12 * pad ≤ w.2 < cut + H'`!
  have hq_bounds : ∀ w ∈ q.cells,
      0 ≤ w.1 ∧ w.1 < 6 * (P.s : ℤ) ∧
      ((cut + 12 * pad : ℕ) : ℤ) ≤ w.2 ∧ w.2 < ((cut + H' : ℕ) : ℤ) := by
    intro w hw
    have hmem_u : (w.1, w.2 - cut) ∈ u.cells := by
      rw [shiftDown_cells]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
    have hx := hin_j0_strict _ hmem_u
    have hy := hu_y _ hmem_u
    dsimp [j0] at hx
    exact ⟨by omega, by omega, by omega, by omega⟩
  -- Every row of `B.insert q` has a `false` cell!
  have hhas_false : ∀ y : Fin B.height, ∃ x : Fin B.width, (B.insert q).cell y x = false := by
    intro y
    by_cases hy1 : y.val < r + 2
    · obtain ⟨x, hx⟩ := hchim.2.2.2.2.2.1 y hy1
      refine ⟨x, ?_⟩
      change (B.cell y x || decide _) = false
      rw [hx, Bool.false_or, decide_eq_false_iff_not]
      intro hm; have := hq_bounds _ hm; omega
    · by_cases hy2 : y.val < cut
      · refine ⟨⟨6 * (P.s + pad) - 1, by have := hchim.2.2.2.1; omega⟩, ?_⟩
        change (B.cell y _ || decide _) = false
        rw [hchim.2.2.2.2.2.2.2.1 y (by omega) hy2, decide_eq_false (by simp), Bool.false_or,
          decide_eq_false_iff_not]
        intro hm; have := hq_bounds _ hm; omega
      · by_cases hy3 : y.val < cut + H' - 2
        · have hx : 6 * P.s + 2 < B.width := by have := hlock.2.2.1; omega
          refine ⟨⟨6 * P.s + 2, hx⟩, ?_⟩
          have hocc := (hlock.2.2.2.2.2.1 y.val (by omega) hy3).2.1
          unfold Board.occupied at hocc
          rw [dif_pos (by omega), dif_pos (by omega)] at hocc
          simp only [Int.toNat_natCast] at hocc
          change (B.cell y ⟨6 * P.s + 2, hx⟩ || decide _) = false
          rw [hocc, Bool.false_or, decide_eq_false_iff_not]
          intro hm; have := hq_bounds _ hm; dsimp at this; omega
        · by_cases hy4 : y.val < cut + H'
          · have hx : 6 * P.s < B.width := by have := hlock.2.2.1; omega
            refine ⟨⟨6 * P.s, hx⟩, ?_⟩
            have hocc : B.occupied (6 * (P.s : ℤ), (y.val : ℤ)) = false := by
              by_cases hyeq : y.val = cut + H' - 2
              · rwa [hyeq]
              · have hyeq1 : y.val = cut + H' - 1 := by omega
                rwa [hyeq1]
            unfold Board.occupied at hocc
            rw [dif_pos (by omega), dif_pos (by omega)] at hocc
            have h6s_nat : (6 * (P.s : ℤ)).toNat = 6 * P.s := by omega
            simp only [Int.toNat_natCast, h6s_nat] at hocc
            change (B.cell y ⟨6 * P.s, hx⟩ || decide _) = false
            rw [hocc, Bool.false_or, decide_eq_false_iff_not]
            intro hm; have := hq_bounds _ hm; dsimp at this; omega
          · refine ⟨⟨0, by have := hlock.2.2.1; omega⟩, ?_⟩
            change (B.cell y _ || decide _) = false
            rw [htop_empty y (by omega), Bool.false_or, decide_eq_false_iff_not]
            intro hm; have := hq_bounds _ hm; dsimp at this; omega
  obtain ⟨hgain0, hsettle_eq⟩ := gain_zero_and_settle_eq_insert hhas_false
  -- `nextChimneyUpper B (r + 2) (4 * K) H' q = (4 * K, H')`
  have hnext_eq : nextChimneyUpper B (r + 2) (4 * K) H' q = (4 * K, H') := by
    have hup : 1 ≤ H' ∧ 1 ≤ 4 * K := ⟨by dsimp [H']; unfold baseHeight; omega, by omega⟩
    simp only [nextChimneyUpper, hup, and_self, ↓reduceIte, Prod.mk.injEq, true_and]
    have hfilt : (((B.insert q).rows.drop (r + 2 + 4 * K)).take H').filter (fun row => !(row.all id)) =
        (((B.insert q).rows.drop (r + 2 + 4 * K)).take H') := by
      rw [List.filter_eq_self]
      intro row hmem
      have hmem' : row ∈ (B.insert q).rows := List.mem_of_mem_drop (List.mem_of_mem_take hmem)
      rw [List.mem_iff_getElem] at hmem'
      rcases hmem' with ⟨i, hi, rfl⟩
      simp only [Board.rows, List.length_ofFn] at hi
      simp only [Board.rows, List.getElem_ofFn, Bool.not_eq_true']
      obtain ⟨x, hx⟩ := hhas_false ⟨i, hi⟩
      rw [Bool.eq_false_iff]; intro hall
      have ht1 := (row_all_id_iff (B.insert q) ⟨i, hi⟩).mp hall x
      exact Bool.noConfusion (hx.symm.trans ht1)
    rw [hfilt, List.length_take, List.length_drop]
    have hlen : (B.insert q).rows.length = B.height := by simp [Board.rows, Board.insert]
    rw [hlen]; have := hlock.2.1; omega
  refine ⟨⟨j0, hin_j0⟩, hu_y0, htrajU, hsettle_eq, hnext_eq, ?_⟩
  -- Prove `Phase1Inv (B.insert q) P pad K r`
  have hchim_step := (chimneySealInv_step hReason hchim (by unfold baseHeight; omega) htraj).2.2.2.1
  rw [hsettle_eq, hnext_eq] at hchim_step
  refine ⟨hchim_step, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hlock.1, hlock.2.1, hlock.2.2.1, hlock.2.2.2.1, ?_, ?_,
      occupied_insert_of_occupied hlock.2.2.2.2.2.2⟩
    · intro y hy1 hy2 x
      change (B.cell y x || decide _) = _
      rw [hlock.2.2.2.2.1 y hy1 hy2 x]
      have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by
        intro hm; have := hq_bounds _ hm; omega
      simp [hnot]
    · intro y hy1 hy2
      rcases hlock.2.2.2.2.2.1 y hy1 hy2 with ⟨ha, hb, hc⟩
      refine ⟨occupied_insert_of_occupied ha, occupied_insert_of_not_mem hb ?_,
        occupied_insert_of_occupied hc⟩
      intro hm; have := hq_bounds _ hm; dsimp at this; omega
  · rw [dropRows_insert_eq]; exact bucketFrame_insert hframe
  · intro x y hx1 hx2 hy1 hy2
    exact occupied_insert_of_occupied (hpad_wall x y hx1 hx2 hy1 hy2)
  · intro y hy1 hy2
    exact occupied_insert_of_occupied (h6s_low y hy1 hy2)
  · exact occupied_insert_of_occupied h6s1_cap
  · apply occupied_insert_of_not_mem h6s_cap2
    intro hm; have := hq_bounds _ hm; dsimp at this; omega
  · apply occupied_insert_of_not_mem h6s_cap1
    intro hm; have := hq_bounds _ hm; dsimp at this; omega
  · intro y hy x
    change (B.cell y x || decide _) = false
    rw [htop_empty y hy x, Bool.false_or, decide_eq_false_iff_not]
    intro hm; have := hq_bounds _ hm; omega

/-! ### `NoRGSeqPlay` and Bucket Empty-Cell Area Saturation -/

lemma noRGSeqPlay_to_anyPlayNoRG {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U ts us U') : AnyPlayNoRG R U U' := by
  induction hp with
  | nil U => exact .nil U
  | step _ ht _ _ _ htraj _ ih =>
    have hk : _ = _ := trajectory_kind_eq htraj
    exact .step (by rwa [hk]) (by rwa [hk]) ih

lemma noRGSeqPlay_append_split {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts1 ts2 : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U (ts1 ++ ts2) us U') :
    ∃ us1 us2 Umid,
      us = us1 ++ us2 ∧
      NoRGSeqPlay R s s' H' U ts1 us1 Umid ∧
      NoRGSeqPlay R s s' H' Umid ts2 us2 U' := by
  induction ts1 generalizing U us with
  | nil => exact ⟨[], us, U, rfl, .nil U, hp⟩
  | cons t ts1' ih =>
    simp only [List.cons_append] at hp
    cases hp with
    | step j ht hfr hin hy htraj hrest =>
      obtain ⟨us1, us2, Umid, rfl, hp1, hp2⟩ := ih hrest
      exact ⟨_ :: us1, us2, Umid, rfl, .step j ht hfr hin hy htraj hp1, hp2⟩

lemma emptyBucketCells_insert_same {U : Board} {s s' H' : ℕ}
    (hs_le : s ≤ s') (hframe : BucketFrame U s' H')
    {j : Fin s} {u : PieceState}
    (hcl : U.Clear u) (hin : InBucket j.val u)
    (hy : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ)) :
    emptyBucketCells (U.insert u) j.val H' + 4 = emptyBucketCells U j.val H' := by
  unfold emptyBucketCells
  set E0 := (Finset.range 6 ×ˢ Finset.range H').filter fun z : ℕ × ℕ =>
    U.occupied (6 * (j.val : ℤ) + z.1, z.2) = false
  set E1 := (Finset.range 6 ×ˢ Finset.range H').filter fun z : ℕ × ℕ =>
    (U.insert u).occupied (6 * (j.val : ℤ) + z.1, z.2) = false
  set S4 := u.cells.toFinset.image fun w : Cell => ((w.1 - 6 * (j.val : ℤ)).toNat, w.2.toNat)
  have hS4_card : S4.card = 4 := by
    rw [Finset.card_image_of_injOn, piece_cells_toFinset_card]
    intro a ha b hb hab
    rw [Finset.mem_coe, List.mem_toFinset] at ha hb
    have hax := hin a ha; have hay := hy a ha
    have hbx := hin b hb; have hby := hy b hb
    simp only [Prod.mk.injEq] at hab
    ext <;> omega
  have hmem_S4 : ∀ p : ℕ × ℕ, p.1 < 6 → p.2 < H' →
      (p ∈ S4 ↔ (6 * (j.val : ℤ) + p.1, (p.2 : ℤ)) ∈ u.cells) := by
    intro p hp1 hp2
    simp only [S4, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwx := hin w hw; have hwy := hy w hw
      have hw_eq : (6 * (j.val : ℤ) + p.1, (p.2 : ℤ)) = w := by
        have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq
        dsimp at h1 h2; ext <;> omega
      rwa [hw_eq]
    · intro hm
      refine ⟨(6 * (j.val : ℤ) + p.1, (p.2 : ℤ)), hm, ?_⟩
      dsimp; ext <;> omega
  have hS4_sub : S4 ⊆ E0 := by
    intro p hp
    simp only [S4, Finset.mem_image, List.mem_toFinset] at hp
    rcases hp with ⟨w, hw, rfl⟩
    have hwx := hin w hw; have hwy := hy w hw
    simp only [E0, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hw_eq : (6 * (j.val : ℤ) + ((w.1 - 6 * (j.val : ℤ)).toNat : ℤ), (w.2.toNat : ℤ)) = w := by
      ext <;> omega
    rw [hw_eq]; exact hcl w hw
  have hE1_eq : E1 = E0 \ S4 := by
    ext p
    simp only [E1, E0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · intro ⟨⟨hp1, hp2⟩, hf1⟩
      have hf0 : U.occupied (6 * (j.val : ℤ) + p.1, p.2) = false := by
        cases hB : U.occupied (6 * (j.val : ℤ) + p.1, p.2) with
        | false => rfl
        | true => rw [occupied_insert_of_occupied hB] at hf1; cases hf1
      refine ⟨⟨⟨hp1, hp2⟩, hf0⟩, fun hpS => ?_⟩
      have hm := (hmem_S4 p hp1 hp2).mp hpS
      let j_pad : Fin s' := ⟨j.val, by omega⟩
      have ht := bucketCell_insert_of_mem hframe (j := j_pad) (x := p.1) (y := p.2)
        (by omega) (by omega) (by omega) (by omega) hm
      unfold bucketCell at ht; dsimp [j_pad] at ht
      rw [ht] at hf1; cases hf1
    · rintro ⟨⟨⟨hp1, hp2⟩, hf0⟩, hnotS⟩
      exact ⟨⟨hp1, hp2⟩, occupied_insert_of_not_mem hf0 (mt (hmem_S4 p hp1 hp2).mpr hnotS)⟩
  change E1.card + 4 = E0.card
  rw [hE1_eq, ← hS4_card, Finset.card_sdiff_add_card_eq_card hS4_sub]

lemma emptyBucketCells_insert_other {U : Board} {H' : ℕ}
    {j k : ℕ} (hne : k ≠ j) {u : PieceState} (hin : InBucket j u) :
    emptyBucketCells (U.insert u) k H' = emptyBucketCells U k H' := by
  unfold emptyBucketCells
  congr 1; ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine and_congr_right fun ⟨hp1, _⟩ => ?_
  constructor
  · intro hf1
    cases hB : U.occupied (6 * (k : ℤ) + p.1, p.2) with
    | false => rfl
    | true => rw [occupied_insert_of_occupied hB] at hf1; cases hf1
  · intro hf0
    apply occupied_insert_of_not_mem hf0
    intro hm
    have hx := hin _ hm; dsimp at hx; omega

lemma sum_emptyBucketCells_noRGSeqPlay {R : Rotation} {s s' H' : ℕ} (hs_le : s ≤ s')
    {U U' : Board} {ts : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U ts us U') :
    (∑ j : Fin s, emptyBucketCells U' j.val H') + 4 * ts.length =
      ∑ j : Fin s, emptyBucketCells U j.val H' := by
  induction hp with
  | nil U => simp
  | @step U U' t ts' u us' j0 _ hfr hin hy htraj _ ih =>
    have hcl := (trajectory_clear_and_blocked htraj).1
    have hsame := emptyBucketCells_insert_same hs_le hfr hcl hin hy
    have hsum_step : (∑ k : Fin s, emptyBucketCells (U.insert u) k.val H') + 4 =
        ∑ k : Fin s, emptyBucketCells U k.val H' := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
      have herase : ∑ k ∈ Finset.univ.erase j0, emptyBucketCells (U.insert u) k.val H' =
          ∑ k ∈ Finset.univ.erase j0, emptyBucketCells U k.val H' := by
        apply Finset.sum_congr rfl
        intro k hk
        have hne : k.val ≠ j0.val := fun he => (Finset.mem_erase.mp hk).1 (Fin.ext he)
        exact emptyBucketCells_insert_other hne hin
      rw [herase]; omega
    simp only [List.length_cons]
    omega

lemma bucketFull_of_emptyBucketCells_zero {U : Board} {j H' : ℕ}
    (h0 : emptyBucketCells U j H' = 0) : BucketFull U j H' := by
  unfold emptyBucketCells at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  intro x hx y hy
  have h := h0 (Finset.mk_mem_product hx hy)
  exact Bool.eq_true_of_not_eq_false h

lemma sum_emptyBucketCells_init (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hst : 3 ≤ st) :
    ∑ j : Fin P.s, emptyBucketCells (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
      j.val (12 * pad + baseHeight P) = P.s * (20 * P.target + 64) := by
  set B0 := paddedReservoirBoard P pad K st r
  set cut := r + 2 + 4 * K
  set U0 := dropRows B0 cut
  set H' := 12 * pad + baseHeight P
  have hcut_le : cut ≤ B0.height := by dsimp [B0, paddedReservoirBoard, baseBoard, cut]; omega
  have hper_bucket : ∀ j : Fin P.s, emptyBucketCells U0 j.val H' = 20 * P.target + 64 := by
    intro j
    unfold emptyBucketCells
    rw [Finset.card_filter, Finset.sum_product_right]
    have hsp_H : Finset.range H' = Finset.range (12 * pad) ∪ Finset.Ico (12 * pad) H' := by
      ext y; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico, H']; omega
    have hdj_H : Disjoint (Finset.range (12 * pad)) (Finset.Ico (12 * pad) H') := by
      rw [Finset.disjoint_left]; intro y h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
    rw [hsp_H, Finset.sum_union hdj_H]
    have hbuf0 : (∑ y ∈ Finset.range (12 * pad), ∑ x ∈ Finset.range 6,
        if U0.occupied (6 * (j.val : ℤ) + (x : ℤ), (y : ℤ)) = false then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro y hy; rw [Finset.mem_range] at hy
      apply Finset.sum_eq_zero; intro x hx; rw [Finset.mem_range] at hx
      have hocc : U0.occupied (6 * (j.val : ℤ) + (x : ℤ), (y : ℤ)) = true := by
        have hxj : 6 * j.val + x < B0.width := by have := j.isLt; dsimp [B0, paddedReservoirBoard]; omega
        have hyB : cut + y < B0.height := by dsimp [B0, paddedReservoirBoard, baseBoard, cut]; omega
        have hcast : 6 * (j.val : ℤ) + (x : ℤ) = ((6 * j.val + x : ℕ) : ℤ) := by omega
        rw [hcast]
        have hcell : U0.occupied (((6 * j.val + x : ℕ) : ℤ), (y : ℤ)) = B0.cell ⟨cut + y, hyB⟩ ⟨6 * j.val + x, hxj⟩ := by
          dsimp only [U0]; unfold Board.occupied dropRows; dsimp only
          rw [dif_pos (by omega), dif_pos (by omega)]; simp only [Int.toNat_natCast]
        rw [hcell]
        have ha : ¬ cut + y < r := by omega
        have hb : ¬ cut + y = r := by omega
        have hc : ¬ cut + y = r + 1 := by omega
        have hd : ¬ cut + y < r + 2 + 4 * K := by omega
        have he : cut + y < r + 2 + 4 * K + 12 * pad := by omega
        simp only [B0, paddedReservoirBoard, ha, hb, hc, hd, he, ↓reduceIte, decide_eq_true_eq]
        have := j.isLt; omega
      simp [hocc]
    rw [hbuf0, Nat.zero_add]
    have hreindex : (∑ y ∈ Finset.Ico (12 * pad) H', ∑ x ∈ Finset.range 6,
        if U0.occupied (6 * (j.val : ℤ) + (x : ℤ), (y : ℤ)) = false then 1 else 0) =
        ∑ k ∈ Finset.range (baseHeight P),
          ((if k < 4 then 1 else 3) + (if (k + 1) % 6 = 5 then 2 else 0)) := by
      apply Finset.sum_nbij (fun y => y - 12 * pad)
      · intro y hy; rw [Finset.mem_Ico] at hy; rw [Finset.mem_range]; dsimp [H'] at hy; omega
      · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb; dsimp at hab; omega
      · intro k hk; simp only [Finset.mem_coe, Finset.mem_range] at hk
        exact ⟨12 * pad + k, by simp only [Finset.mem_coe, Finset.mem_Ico, H']; omega, by dsimp; omega⟩
      · intro y hy; rw [Finset.mem_Ico] at hy
        set k := y - 12 * pad
        have hk_lt : k < baseHeight P := by dsimp [H', k] at *; omega
        have hy_eq : y = 12 * pad + k := by omega
        have heval : ∀ x ∈ Finset.range 6,
            U0.occupied (6 * (j.val : ℤ) + (x : ℤ), (y : ℤ)) = bucketInitial x k := by
          intro x hx; rw [Finset.mem_range] at hx
          have hxj : 6 * j.val + x < B0.width := by have := j.isLt; dsimp [B0, paddedReservoirBoard]; omega
          have hyB : cut + y < B0.height := by dsimp [B0, paddedReservoirBoard, baseBoard, cut, H'] at hy ⊢; omega
          have hcast : 6 * (j.val : ℤ) + (x : ℤ) = ((6 * j.val + x : ℕ) : ℤ) := by omega
          rw [hcast]
          have hcell : U0.occupied (((6 * j.val + x : ℕ) : ℤ), (y : ℤ)) = B0.cell ⟨cut + y, hyB⟩ ⟨6 * j.val + x, hxj⟩ := by
            dsimp only [U0]; unfold Board.occupied dropRows; dsimp only
            rw [dif_pos (by omega), dif_pos (by omega)]; simp only [Int.toNat_natCast]
          rw [hcell]
          have ha : ¬ cut + y < r := by omega
          have hb : ¬ cut + y = r := by omega
          have hc : ¬ cut + y = r + 1 := by omega
          have hd : ¬ cut + y < r + 2 + 4 * K := by omega
          have he : ¬ cut + y < r + 2 + 4 * K + 12 * pad := by omega
          have hxs : 6 * j.val + x < 6 * P.s + 3 := by have := j.isLt; omega
          simp only [B0, paddedReservoirBoard, ha, hb, hc, hd, he, hxs, ↓reduceIte]
          have hy_sub : ((cut + y : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = (k : ℤ) := by
            dsimp [cut]; omega
          rw [hy_sub]; unfold Board.occupied
          rw [dif_pos (by dsimp [baseBoard]; omega), dif_pos (by have := j.isLt; dsimp [baseBoard]; omega)]
          simp only [baseBoard, show ¬ (k ≥ baseHeight P) by omega, ↓reduceIte, Int.toNat_natCast,
            show 6 * j.val + x < 6 * P.s by have := j.isLt; omega]
          have hmodx : (6 * j.val + x) % 6 = x % 6 := by omega
          simp [bucketInitial, hmodx]
        have hsum_x : (∑ x ∈ Finset.range 6,
            if U0.occupied (6 * (j.val : ℤ) + (x : ℤ), (y : ℤ)) = false then 1 else 0) =
            ∑ x ∈ Finset.range 6, if bucketInitial x k = false then 1 else 0 :=
          Finset.sum_congr rfl fun x hx => by rw [heval x hx]
        rw [hsum_x]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, bucketInitial]
        by_cases hk4 : k < 4 <;> by_cases hk5 : (k + 1) % 6 = 5 <;> simp [hk4, hk5]
    rw [hreindex, Finset.sum_add_distrib]
    have h1 : (∑ k ∈ Finset.range (baseHeight P), if k < 4 then 1 else 3) =
        18 * P.target + 58 := by
      have hsp : Finset.range (baseHeight P) = Finset.range 4 ∪ Finset.Ico 4 (baseHeight P) := by
        ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico, baseHeight]; omega
      have hdj : Disjoint (Finset.range 4) (Finset.Ico 4 (baseHeight P)) := by
        rw [Finset.disjoint_left]; intro k h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
      rw [hsp, Finset.sum_union hdj]
      have ha : (∑ k ∈ Finset.range 4, if k < 4 then 1 else 3) = 4 := by
        simp [Finset.sum_range_succ]
      have hb : (∑ k ∈ Finset.Ico 4 (baseHeight P), if k < 4 then 1 else 3) =
          3 * (baseHeight P - 4) := by
        have ht3 : ∀ k ∈ Finset.Ico 4 (baseHeight P), (if k < 4 then 1 else 3) = 3 := by
          intro k hk; rw [Finset.mem_Ico] at hk; simp [show ¬ k < 4 by omega]
        rw [Finset.sum_congr rfl ht3, Finset.sum_const, Nat.card_Ico, smul_eq_mul]; ring
      rw [ha, hb]; unfold baseHeight; omega
    have h2 : (∑ k ∈ Finset.range (baseHeight P), if (k + 1) % 6 = 5 then 2 else 0) =
        2 * P.target + 6 := by
      have hmod6 : ∀ m : ℕ, (∑ k ∈ Finset.range (6 * m), if (k + 1) % 6 = 5 then 2 else 0) = 2 * m := by
        intro m; induction m with
        | zero => simp
        | succ m ih =>
          have hsp : Finset.range (6 * (m + 1)) =
              Finset.range (6 * m) ∪ Finset.Ico (6 * m) (6 * m + 6) := by
            ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
          have hdj : Disjoint (Finset.range (6 * m)) (Finset.Ico (6 * m) (6 * m + 6)) := by
            rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
          rw [hsp, Finset.sum_union hdj, ih]
          have h6 : (∑ k ∈ Finset.Ico (6 * m) (6 * m + 6), if (k + 1) % 6 = 5 then 2 else 0) = 2 := by
            have hshift : (∑ k ∈ Finset.Ico (6 * m) (6 * m + 6), if (k + 1) % 6 = 5 then 2 else 0) =
                ∑ d ∈ Finset.range 6, if (d + 1) % 6 = 5 then 2 else 0 := by
              apply Finset.sum_nbij (fun k => k - 6 * m)
              · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
              · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb; dsimp at hab; omega
              · intro d hd; simp only [Finset.mem_coe, Finset.mem_range] at hd
                exact ⟨6 * m + d, by simp only [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp; omega⟩
              · intro k hk; rw [Finset.mem_Ico] at hk
                have : (k + 1) % 6 = (k - 6 * m + 1) % 6 := by omega
                rw [this]
            rw [hshift]; simp [Finset.sum_range_succ]
          rw [h6]; omega
      have hsp : Finset.range (baseHeight P) =
          Finset.range (6 * (P.target + 3)) ∪ Finset.Ico (6 * (P.target + 3)) (baseHeight P) := by
        ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico, baseHeight]; omega
      have hdj : Disjoint (Finset.range (6 * (P.target + 3)))
          (Finset.Ico (6 * (P.target + 3)) (baseHeight P)) := by
        rw [Finset.disjoint_left]; intro k h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
      rw [hsp, Finset.sum_union hdj, hmod6 (P.target + 3)]
      have htail : (∑ k ∈ Finset.Ico (6 * (P.target + 3)) (baseHeight P),
          if (k + 1) % 6 = 5 then 2 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk; rw [Finset.mem_Ico] at hk; unfold baseHeight at hk
        simp [show (k + 1) % 6 ≠ 5 by omega]
      rw [htail]; omega
    omega
  simp_rw [hper_bucket, Finset.sum_const, Finset.card_fin, smul_eq_mul]

/-- **Main Bridge of Part C-1**: If any prefix of `prefixPieces P pad K` clears all chimney + upper rows,
then `numberPieces P` lifts to an exact no-deletion `NoRGSeqPlay` on `U0 = dropRows B0 (r + 2 + 4 * K)`
reaching `U_num`, followed by `AnyPlayNoRG R U_num U_end` where EVERY bucket `j : Fin P.s` is `BucketFull`! -/
theorem phase1_lifts_to_bucketFull {R : Rotation} (hReason : Reasonable R)
    {P : ThreePartition} (hP : P.Valid) (hEven : Even P.target) (hs : 0 < P.s)
    {pad K st r : ℕ} (hpad : max R.radius 2 + 2 ≤ pad) (hK : 1 ≤ K) (hst : 3 ≤ st)
    {B1 : Board} {ts1 ts2 : List Piece} {qs1 : List PieceState} {v1 : ℕ}
    (hplay : Play R (paddedReservoirBoard P pad K st r) ts1 qs1 B1 v1)
    (hpref : prefixPieces P pad K = ts1 ++ ts2)
    (hzero : (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).1 +
      (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).2 = 0) :
    let cut := r + 2 + 4 * K
    let H' := 12 * pad + baseHeight P
    let U0 := dropRows (paddedReservoirBoard P pad K st r) cut
    ∃ us us_I U_num U_end,
      NoRGSeqPlay R P.s (P.s + pad) H' U0 (numberPieces P) us U_num ∧
      NoRGSeqPlay R P.s (P.s + pad) H' U_num (List.replicate P.s .I) us_I U_end ∧
      ∀ j : Fin P.s, BucketFull U_end j.val H' := by
  have hpad1 : 1 ≤ pad := by omega
  have hrad : R.radius + 1 ≤ 12 * pad := by have := le_max_left R.radius 2; omega
  obtain ⟨qs_main, B_main, v_main, hqsm_len, hp_main, hall_in⟩ :=
    mainPieces_zero_waste_of_clear_chimney hReason hP hEven hpad1 hK hst hplay hpref hzero
  rw [mainPieces_eq_phase1_post] at hp_main hqsm_len
  obtain ⟨qs_ph1, qs_post, B_ph1, v_ph1, v_post, hqs_sp, _, hp_ph1, hp_post, _⟩ :=
    play_append_split hp_main
  have hph1_le := play_length_le hp_ph1
  have hpost_le := play_length_le hp_post
  have hlen_eq : qs_ph1.length + qs_post.length =
      (phase1Pieces P).length + (postPhase1Pieces P pad K).length := by
    rw [← List.length_append, ← hqs_sp, hqsm_len, List.length_append]
  have hph1_len : qs_ph1.length = (phase1Pieces P).length := by omega
  -- Extract `AllPiecesInside` on the prefix `qs_ph1`
  have hall_ph1 : ∀ {B_cur B_fin : Board} {ts_cur : List Piece} {qs_cur qs_tail : List PieceState} {v_cur : ℕ},
      Play R B_cur ts_cur qs_cur B_fin v_cur →
      qs_cur.length = ts_cur.length →
      (∀ t ∈ ts_cur, t ∈ ([.LG, .LS, .Sq, .I] : List Piece)) →
      Phase1Inv B_cur P pad K r →
      AllPiecesInside B_cur (r + 2) (4 * K) (12 * pad + baseHeight P) (qs_cur ++ qs_tail) →
      ∃ us_cur,
        NoRGSeqPlay R P.s (P.s + pad) (12 * pad + baseHeight P)
          (dropRows B_cur (r + 2 + 4 * K)) ts_cur us_cur (dropRows B_fin (r + 2 + 4 * K)) := by
    intro B_cur B_fin ts_cur qs_cur qs_tail v_cur hp_c
    induction hp_c with
    | stop B_cur ts' =>
      intro hlen _ _ _
      simp only [List.length_nil] at hlen
      have hts : ts' = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst hts
      exact ⟨[], .nil _⟩
    | step htraj hrest ih =>
      rename_i B_cur t ts' q qs' B_fin v'
      intro hlen hmem hinv hin_all
      simp only [List.cons_append, AllPiecesInside] at hin_all
      rcases hin_all with ⟨_, hq_in, hrest_in⟩
      have ht_ok := hmem t (List.mem_cons_self ..)
      obtain ⟨⟨j0, hin_j0⟩, hu_y0, htrajU, hsettle_eq, hnext_eq, hinv_next⟩ :=
        phase1Inv_step hReason hs hrad hK hinv ht_ok htraj hq_in
      rw [hnext_eq] at hrest_in
      rw [hsettle_eq] at ih hrest hrest_in
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      obtain ⟨us', hseq'⟩ := ih hlen (fun t' ht' => hmem t' (List.mem_cons_of_mem _ ht')) hinv_next hrest_in
      rw [dropRows_insert_eq] at hseq'
      exact ⟨shiftDown (r + 2 + 4 * K) q :: us',
        .step j0 ht_ok hinv.2.2.1 hin_j0 hu_y0 htrajU hseq'⟩
  rw [hqs_sp] at hall_in
  obtain ⟨us_ph1, hseq_ph1⟩ := hall_ph1 hp_ph1 hph1_len
    (fun t ht => phase1Pieces_mem_allowed ht)
    (phase1Inv_init P pad K st r hpad1 hst) hall_in
  -- Compute emptyBucketCells at `U_end = dropRows B_ph1 (r + 2 + 4 * K)`
  set cut := r + 2 + 4 * K
  set H' := 12 * pad + baseHeight P
  set U0 := dropRows (paddedReservoirBoard P pad K st r) cut
  set U_end := dropRows B_ph1 cut
  have hsum_end := sum_emptyBucketCells_noRGSeqPlay (by omega : P.s ≤ P.s + pad) hseq_ph1
  have hsum_init := sum_emptyBucketCells_init P pad K st r hpad1 hst
  have h4len := phase1Pieces_four_mul_length P hP
  dsimp only [U0, U_end, cut, H'] at hsum_end hsum_init ⊢
  have hsum_zero : ∑ j : Fin P.s, emptyBucketCells (dropRows B_ph1 (r + 2 + 4 * K)) j.val (12 * pad + baseHeight P) = 0 := by
    omega
  have hall_full : ∀ j : Fin P.s, BucketFull U_end j.val H' := by
    intro j
    apply bucketFull_of_emptyBucketCells_zero
    exact Finset.sum_eq_zero_iff.mp hsum_zero j (Finset.mem_univ j)
  -- Split `phase1Pieces P = numberPieces P ++ List.replicate P.s .I`!
  unfold phase1Pieces at hseq_ph1
  obtain ⟨us_num, us_I, U_num, _, hseq_num, hseq_I⟩ := noRGSeqPlay_append_split hseq_ph1
  exact ⟨us_num, us_I, U_num, U_end, hseq_num, hseq_I, hall_full⟩

end TetrisHard.Rows.Padded.Carbon

namespace TetrisHard.Rows.Padded
open TetrisHard.Rows
open TetrisHard.Rows.Padded.Carbon

lemma dropRows_init_unpreppedAt (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (hst : 3 ≤ st) (j : Fin P.s) :
    UnpreppedAt (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
      j.val (12 * pad + baseHeight P) (12 * pad + 4) := by
  set B0 := paddedReservoirBoard P pad K st r
  set cut := r + 2 + 4 * K
  set U0 := dropRows B0 cut
  set H' := 12 * pad + baseHeight P
  have hfr0 := dropRows_init_bucketFrame P pad K st r hpad hst
  obtain ⟨h, gap, hh4, hhB, hmod, hgap, hpat⟩ := dropRows_init_unprepped P pad K st r hpad j
  -- Evaluate `bucketCell U0 j.val 1 (12 * pad + 3)` and `bucketCell U0 j.val 1 (12 * pad + 4)` to pin `h = 12 * pad + 4`!
  have hcell1 : ∀ k : ℕ, k < baseHeight P →
      bucketCell U0 j.val 1 ((12 * pad + k : ℕ) : ℤ) = decide (k < 4) := by
    intro k hk
    unfold bucketCell
    have hxj : 6 * j.val + 1 < B0.width := by have := j.isLt; dsimp [B0, paddedReservoirBoard]; omega
    have hyB : cut + (12 * pad + k) < B0.height := by
      dsimp [B0, paddedReservoirBoard, baseBoard, cut]; omega
    have hcast : 6 * (j.val : ℤ) + 1 = ((6 * j.val + 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    have hc : U0.occupied (((6 * j.val + 1 : ℕ) : ℤ), ((12 * pad + k : ℕ) : ℤ)) =
        B0.cell ⟨cut + (12 * pad + k), hyB⟩ ⟨6 * j.val + 1, hxj⟩ := by
      dsimp only [U0]; unfold Board.occupied dropRows; dsimp only
      rw [dif_pos (by omega), dif_pos (by omega)]; simp only [Int.toNat_natCast]
    rw [hc]
    have ha : ¬ cut + (12 * pad + k) < r := by omega
    have hb : ¬ cut + (12 * pad + k) = r := by omega
    have hc' : ¬ cut + (12 * pad + k) = r + 1 := by omega
    have hd : ¬ cut + (12 * pad + k) < r + 2 + 4 * K := by omega
    have he : ¬ cut + (12 * pad + k) < r + 2 + 4 * K + 12 * pad := by omega
    have hxs : 6 * j.val + 1 < 6 * P.s + 3 := by have := j.isLt; omega
    simp only [B0, paddedReservoirBoard, ha, hb, hc', hd, he, hxs, ↓reduceIte]
    have hy_sub : ((cut + (12 * pad + k) : ℕ) : ℤ) - (r + 2 + 4 * K + 12 * pad) = (k : ℤ) := by
      dsimp [cut]; omega
    rw [hy_sub]; unfold Board.occupied; dsimp only
    rw [dif_pos (by dsimp [baseBoard]; omega), dif_pos (by have := j.isLt; dsimp [baseBoard]; omega)]
    simp only [Int.toNat_natCast, baseBoard, show ¬ (k ≥ baseHeight P) by omega, ↓reduceIte,
      show 6 * j.val + 1 < 6 * P.s by have := j.isLt; omega, bucketInitial]
    have hmod1 : (6 * j.val + 1) % 6 = 1 := by omega
    simp [hmod1]
  have h_t := hcell1 3 (by unfold baseHeight; omega)
  have h_f := hcell1 4 (by unfold baseHeight; omega)
  have hp_t := hpat ⟨1, by decide⟩ ⟨12 * pad + 3, by have := hfr0.2.2.1; unfold baseHeight at this; omega⟩
  have hp_f := hpat ⟨1, by decide⟩ ⟨12 * pad + 4, by have := hfr0.2.2.1; unfold baseHeight at this; omega⟩
  have eq_t : decide (3 < 4) = ((decide (12 * pad + 3 < 12 * pad + baseHeight P ∧
      (1 = 5 ∨ 3 ≤ 1 ∧ (12 * pad + 3 + 1) % 6 ≠ 5))) ||
      decide (1 < 5 ∧ 12 * pad + 3 < h ∧ ¬ (1 = gap ∧ h ≤ 12 * pad + 3 + 4))) := h_t.symm.trans hp_t
  have eq_f : decide (4 < 4) = ((decide (12 * pad + 4 < 12 * pad + baseHeight P ∧
      (1 = 5 ∨ 3 ≤ 1 ∧ (12 * pad + 4 + 1) % 6 ≠ 5))) ||
      decide (1 < 5 ∧ 12 * pad + 4 < h ∧ ¬ (1 = gap ∧ h ≤ 12 * pad + 4 + 4))) := h_f.symm.trans hp_f
  have h1_ne_gap : (1 : ℕ) ≠ gap := by rcases hgap with rfl | rfl <;> decide
  simp only [show ¬ ((1 : ℕ) = 5 ∨ 3 ≤ (1 : ℕ) ∧ (12 * pad + 3 + 1) % 6 ≠ 5) by omega,
    show ¬ ((1 : ℕ) = 5 ∨ 3 ≤ (1 : ℕ) ∧ (12 * pad + 4 + 1) % 6 ≠ 5) by omega,
    and_false, decide_false, Bool.false_or, show (1 : ℕ) < 5 by decide, show (3 : ℕ) < 4 by decide,
    show ¬ ((4 : ℕ) < 4) by decide, true_and, h1_ne_gap, false_and,
    not_false_eq_true, and_true, decide_true] at eq_t eq_f
  have hgt : 12 * pad + 3 < h := of_decide_eq_true eq_t.symm
  have hngt : ¬ (12 * pad + 4 < h) := of_decide_eq_false eq_f.symm
  have h_eq : h = 12 * pad + 4 := by omega
  subst h_eq
  exact ⟨gap, by omega, by dsimp [H']; unfold baseHeight; omega, by omega, hgap, hpat⟩


end TetrisHard.Rows.Padded

theorem solution
    (R : TetrisHard.Rows.Rotation) (hR : R.Admissible) (hReason : TetrisHard.Rows.Reasonable R)
    (P : TetrisHard.Rows.ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : TetrisHard.Rows.Padded.maxJump R + 2 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st)
    (v : ℕ) (hatt : TetrisHard.Rows.Attainable R (TetrisHard.Rows.Padded.paddedReservoirGame P pad K st r) v) :
    v ≤ TetrisHard.Rows.Padded.paddedNoBound P pad K st ∨
    (TetrisHard.Rows.Padded.AllUnpreppedHeights
        (TetrisHard.Rows.Padded.dropRows (TetrisHard.Rows.Padded.paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
        P.s (12 * pad + TetrisHard.Rows.baseHeight P) (fun _ => 12 * pad + 4) ∧
     ∃ us us_I U_num U_end,
       TetrisHard.Rows.Padded.NoRGSeqPlay R P.s (P.s + pad) (12 * pad + TetrisHard.Rows.baseHeight P)
         (TetrisHard.Rows.Padded.dropRows (TetrisHard.Rows.Padded.paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
         (TetrisHard.Rows.numberPieces P) us U_num ∧
       TetrisHard.Rows.Padded.NoRGSeqPlay R P.s (P.s + pad) (12 * pad + TetrisHard.Rows.baseHeight P)
         U_num (List.replicate P.s .I) us_I U_end ∧
       ∀ j : Fin P.s, TetrisHard.Rows.BucketFull U_end j.val (12 * pad + TetrisHard.Rows.baseHeight P)) := by
  open TetrisHard.Rows TetrisHard.Rows.Padded TetrisHard.Rows.Padded.Carbon in
  let _ := hR
  have hpad1 : 1 ≤ pad := by omega
  have hK1 : 1 ≤ K := by omega
  have hst3 : 3 ≤ st := by omega
  by_cases hno_clear : ∀ {B1 : Board} {ts1 : List Piece} {qs1 : List PieceState} {v1 : ℕ},
      Play R (paddedReservoirBoard P pad K st r) ts1 qs1 B1 v1 →
      (∃ ts2, prefixPieces P pad K = ts1 ++ ts2) →
      1 ≤ (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).1 +
      (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).2
  · exact Or.inl (soundness_of_no_clear_all_chimney R hReason P pad K st r hpad1 hK1 hst3 hno_clear v hatt)
  · right
    push Not at hno_clear
    obtain ⟨B1, ts1, qs1, v1, hplay, ⟨ts2, hpref⟩, hlt⟩ := hno_clear
    have hzero : (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).1 +
      (trackChimneyUpper (paddedReservoirBoard P pad K st r) (r + 2) (4 * K)
        (12 * pad + baseHeight P) qs1).2 = 0 := by omega
    exact ⟨fun j => dropRows_init_unpreppedAt P pad K st r hpad1 hst3 j,
      phase1_lifts_to_bucketFull hReason hP hN.2.1 hs hpad hK1 hst3 hplay hpref hzero⟩
