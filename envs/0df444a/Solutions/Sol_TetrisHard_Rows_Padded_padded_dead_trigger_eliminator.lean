-- Prove2me | solution 1 for TetrisHard.Rows.Padded.padded_dead_trigger_eliminator
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:40:28.638181+00:00
-- url     : https://prove2.me/submissions/788e8124-8ef6-4de7-a4a9-e9d82942a67b

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetrisHard.Rows.Padded

open TetrisHard.Rows

/-! ### Part B: Section 5.4 Unfillable Configurations -/

/-- Arbitrary sequence of valid piece placements without row deletion (all 7 piece types,
anywhere on the board). -/
inductive AnyPlay (R : Rotation) : Board → Board → Prop
  | nil (B) : AnyPlay R B B
  | step {B B' q} : Trajectory R B q.kind q → AnyPlay R (B.insert q) B' → AnyPlay R B B'

/-- Sequence of valid piece placements without row deletion, restricted to `{.LG, .LS, .Sq, .I}`. -/
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

lemma trajectory_clear_B {R : Rotation} {B : Board} {t : Piece} {q : PieceState}
    (ht : Trajectory R B t q) : B.Clear q := by
  rcases ht with ⟨hspawn, hpath, _⟩
  induction hpath with
  | refl => exact hspawn
  | tail _ hstep _ => exact hstep.2.2.1

lemma spawn_cells_ge_H_B {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (t : Piece) :
    ∀ z ∈ (spawn B t).cells, (H : ℤ) ≤ z.2 := by
  have hh : H + 3 ≤ B.height := hframe.2.2.1
  intro z hz
  cases t <;> simp [spawn, PieceState.cells, Piece.base] at hz <;>
    rcases hz with rfl | rfl | rfl | rfl <;> omega

lemma trajectory_reachable_B {R : Rotation} {B : Board} {s H : ℕ} {t : Piece} {q : PieceState}
    (hframe : BucketFrame B s H) (ht : Trajectory R B t q) : Reachable R B H t q :=
  ⟨spawn_cells_ge_H_B hframe t, ht.1, ht.2.1⟩

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

lemma bucketCell_notch_wall_B {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {y : ℤ} (hy0 : 0 ≤ y) (hy1 : y < H) (hmod : (y + 1) % 6 ≠ 5) :
    bucketCell B j.val 3 y = true ∧ bucketCell B j.val 4 y = true := by
  unfold bucketCell
  have h := (hframe.2.2.2 j y.toNat (by omega)).2 (by omega)
  have heq : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
  rw [heq] at h
  exact h

lemma not_bucketFull_of_false_B {B : Board} {j H : ℕ} (hfull : BucketFull B j H)
    {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x < 6) (hy0 : 0 ≤ y) (hy1 : y < H)
    (hf : bucketCell B j x y = false) : False := by
  have h := hfull x.toNat (Finset.mem_range.mpr (by omega)) y.toNat (Finset.mem_range.mpr (by omega))
  unfold bucketCell at hf
  rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] at h
  rw [h] at hf
  cases hf

lemma emptyAdjacent_symm_B {B : Board} {z z' : Cell}
    (h : EmptyAdjacent B z z') : EmptyAdjacent B z' z := by
  rcases h with ⟨h1, h2, h3⟩
  refine ⟨h2, h1, ?_⟩
  rw [abs_sub_comm z'.1 z.1, abs_sub_comm z'.2 z.2]
  exact h3

lemma reflTransGen_emptyAdjacent_symm_B {B : Board} {z z' : Cell}
    (h : Relation.ReflTransGen (EmptyAdjacent B) z z') :
    Relation.ReflTransGen (EmptyAdjacent B) z' z := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (emptyAdjacent_symm_B hstep) ih

lemma emptyAdjacent_of_insert {B : Board} {q : PieceState} {z z' : Cell}
    (h : EmptyAdjacent (B.insert q) z z') : EmptyAdjacent B z z' := by
  rcases h with ⟨h1, h2, h3⟩
  have hback : ∀ c : Cell, (B.insert q).occupied c = false → B.occupied c = false := by
    intro c hc
    cases hB : B.occupied c with
    | false => rfl
    | true => rw [occupied_insert_of_occupied hB] at hc; cases hc
  exact ⟨hback z h1, hback z' h2, h3⟩

lemma reflTransGen_emptyAdjacent_of_insert {B : Board} {q : PieceState} {z z' : Cell}
    (h : Relation.ReflTransGen (EmptyAdjacent (B.insert q)) z z') :
    Relation.ReflTransGen (EmptyAdjacent B) z z' := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (emptyAdjacent_of_insert hstep)

lemma cells_nonempty_B (q : PieceState) : ∃ z, z ∈ q.cells := by
  cases h : q.kind <;> simp [PieceState.cells, h, Piece.base]

lemma reachable_emptyAdjacent_B {R : Rotation} (hReason : Reasonable R)
    {B : Board} {q₁ q₂ : PieceState}
    (hpath : Relation.ReflTransGen (Move R B) q₁ q₂) :
    ∀ z₂ ∈ q₂.cells, ∃ z₁ ∈ q₁.cells, Relation.ReflTransGen (EmptyAdjacent B) z₁ z₂ := by
  induction hpath with
  | refl => intro z hz; exact ⟨z, hz, .refl⟩
  | @tail q₂ q₃ _ hstep ih =>
    intro z₃ hz₃
    rcases cells_nonempty_B q₂ with ⟨z₂, hz₂⟩
    rcases ih z₂ hz₂ with ⟨z₁, hz₁, h12⟩
    exact ⟨z₁, hz₁, h12.trans (hReason.1 B q₂ q₃ hstep z₂ hz₂ z₃ hz₃)⟩

/-! ### Lemma B1: `HasHole` is unfillable (even under `AnyPlay`) -/

theorem anyPlay_unfillable_of_hasHole {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    (hhole : HasHole B j.val H) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rintro ⟨B', hplay, hfull⟩
  rcases hhole with ⟨x, y, hx0, hx5, hy0, hyH, hf, hno⟩
  have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
      bucketCell Bcur j.val x y = false →
      (¬ ∃ z : Cell, (H : ℤ) ≤ z.2 ∧ Bcur.occupied z = false ∧
        Relation.ReflTransGen (EmptyAdjacent Bcur) (6 * (j.val : ℤ) + x, y) z) →
      BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ hf' _ hfull'
      exact not_bucketFull_of_false_B hfull' hx0 (by omega) hy0 hyH hf'
    | @step Bcur B' q htraj _ ih =>
      intro hfr hf' hno' hfull'
      have hnotmem : (6 * (j.val : ℤ) + x, y) ∉ q.cells := by
        intro hmem
        rcases reachable_emptyAdjacent_B hReason htraj.2.1 _ hmem with ⟨zs, hzs, hpath⟩
        have hge := spawn_cells_ge_H_B hfr q.kind zs hzs
        have hocc : Bcur.occupied zs = false := htraj.1 zs hzs
        exact hno' ⟨zs, hge, hocc, reflTransGen_emptyAdjacent_symm_B hpath⟩
      have hno'' : ¬ ∃ z : Cell, (H : ℤ) ≤ z.2 ∧ (Bcur.insert q).occupied z = false ∧
          Relation.ReflTransGen (EmptyAdjacent (Bcur.insert q)) (6 * (j.val : ℤ) + x, y) z := by
        rintro ⟨z, hzH, hzocc, hpath⟩
        have hzoccB : Bcur.occupied z = false := by
          cases hB : Bcur.occupied z with
          | false => rfl
          | true => rw [occupied_insert_of_occupied hB] at hzocc; cases hzocc
        exact hno' ⟨z, hzH, hzoccB, reflTransGen_emptyAdjacent_of_insert hpath⟩
      exact ih (bucketFrame_insert hfr) (bucketCell_insert_of_not_mem hf' hnotmem) hno'' hfull'
  exact hgen hplay hframe hf hno hfull

lemma hasHole_of_surrounded_B {B : Board} {j H : ℕ} {x y : ℤ}
    (hx0 : 0 ≤ x) (hx5 : x < 5) (hy0 : 0 ≤ y) (hyH : y < H)
    (hf : bucketCell B j x y = false)
    (hR : bucketCell B j (x + 1) y = true) (hL : bucketCell B j (x - 1) y = true)
    (hU : bucketCell B j x (y + 1) = true) (hD : bucketCell B j x (y - 1) = true) :
    HasHole B j H := by
  refine ⟨x, y, hx0, hx5, hy0, hyH, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨w, hst, _⟩
  · dsimp at hzH; omega
  · rcases hst with ⟨_, hwf, hdist⟩
    dsimp only at hdist
    have hstep : (w.1 = 6 * (j : ℤ) + (x + 1) ∧ w.2 = y) ∨
        (w.1 = 6 * (j : ℤ) + (x - 1) ∧ w.2 = y) ∨
        (w.1 = 6 * (j : ℤ) + x ∧ w.2 = y + 1) ∨
        (w.1 = 6 * (j : ℤ) + x ∧ w.2 = y - 1) := by
      rcases abs_cases ((6 * (j : ℤ) + x) - w.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (y - w.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have heq : w = (6 * (j : ℤ) + (x + 1), y) := by ext <;> omega
      rw [heq] at hwf; unfold bucketCell at hR; rw [hR] at hwf; cases hwf
    · have heq : w = (6 * (j : ℤ) + (x - 1), y) := by ext <;> omega
      rw [heq] at hwf; unfold bucketCell at hL; rw [hL] at hwf; cases hwf
    · have heq : w = (6 * (j : ℤ) + x, y + 1) := by ext <;> omega
      rw [heq] at hwf; unfold bucketCell at hU; rw [hU] at hwf; cases hwf
    · have heq : w = (6 * (j : ℤ) + x, y - 1) := by ext <;> omega
      rw [heq] at hwf; unfold bucketCell at hD; rw [hD] at hwf; cases hwf

/-! ### Lemma B2: Closed row with empty cell below gives `HasHole` -/

lemma hasHole_of_closed_row {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r x₀ y₀ : ℤ} (hrH : r < H)
    (hx0 : 0 ≤ x₀) (hx1 : x₀ < 5) (hy0 : 0 ≤ y₀) (hy1 : y₀ < r)
    (h0 : bucketCell B j.val 0 r = true) (h1 : bucketCell B j.val 1 r = true)
    (h2 : bucketCell B j.val 2 r = true) (h3 : bucketCell B j.val 3 r = true)
    (h4 : bucketCell B j.val 4 r = true)
    (hf : bucketCell B j.val x₀ y₀ = false) :
    HasHole B j.val H := by
  refine ⟨x₀, y₀, hx0, hx1, hy0, by omega, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ u v : Cell,
      6 * (j.val : ℤ) ≤ u.1 ∧ u.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ u.2 ∧ u.2 < r →
      EmptyAdjacent B u v →
      6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < r := by
    intro u v hu hadj
    rcases hadj with ⟨_, hvf, hdist⟩
    have hstep : (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 - 1 ∧ v.2 = u.2) ∨
        (v.1 = u.1 ∧ v.2 = u.2 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 - 1) := by
      rcases abs_cases (u.1 - v.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (u.2 - v.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · by_cases h5 : v.1 = 6 * (j.val : ℤ) + 5
      · have hw := bucketCell_right_wall_B hframe j (y := v.2) (by omega) (by omega)
        unfold bucketCell at hw
        have heq : (6 * (j.val : ℤ) + 5, v.2) = v := by ext <;> omega
        rw [heq] at hw; rw [hw] at hvf; cases hvf
      · omega
    · by_cases hm1 : v.1 = 6 * (j.val : ℤ) - 1
      · have hw := bucketCell_left_wall_B hframe j (y := v.2) (by omega) (by omega)
        unfold bucketCell at hw
        have heq : (6 * (j.val : ℤ) + -1, v.2) = v := by ext <;> omega
        rw [heq] at hw; rw [hw] at hvf; cases hvf
      · omega
    · by_cases htop : v.2 = r
      · have hdx : v.1 - 6 * (j.val : ℤ) = 0 ∨ v.1 - 6 * (j.val : ℤ) = 1 ∨
            v.1 - 6 * (j.val : ℤ) = 2 ∨ v.1 - 6 * (j.val : ℤ) = 3 ∨
            v.1 - 6 * (j.val : ℤ) = 4 := by omega
        rcases hdx with h | h | h | h | h
        · have heq : (6 * (j.val : ℤ) + 0, r) = v := by ext <;> omega
          unfold bucketCell at h0; rw [heq] at h0; rw [h0] at hvf; cases hvf
        · have heq : (6 * (j.val : ℤ) + 1, r) = v := by ext <;> omega
          unfold bucketCell at h1; rw [heq] at h1; rw [h1] at hvf; cases hvf
        · have heq : (6 * (j.val : ℤ) + 2, r) = v := by ext <;> omega
          unfold bucketCell at h2; rw [heq] at h2; rw [h2] at hvf; cases hvf
        · have heq : (6 * (j.val : ℤ) + 3, r) = v := by ext <;> omega
          unfold bucketCell at h3; rw [heq] at h3; rw [h3] at hvf; cases hvf
        · have heq : (6 * (j.val : ℤ) + 4, r) = v := by ext <;> omega
          unfold bucketCell at h4; rw [heq] at h4; rw [h4] at hvf; cases hvf
      · omega
    · by_cases hbot : v.2 = -1
      · unfold Board.occupied at hvf
        have : ¬ (0 ≤ v.2 ∧ v.2 < B.height) := by omega
        simp [this] at hvf
      · omega
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent B) (6 * (j.val : ℤ) + x₀, y₀) v →
      6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < r := by
    intro v hp
    induction hp with
    | refl => dsimp; omega
    | tail _ hst ih => exact hstay _ _ ih hst
  have := hbox z hpath
  omega

/-- Generalization of closed row: if `(0, r-1), (1, r-1), (3, r-1), (4, r-1)` are `true` and
`(1, r), (2, r), (3, r), (4, r)` are `true` and `(2, r-1) = false`, then `HasHole B j.val H`! -/
lemma hasHole_of_stepped_seal {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r : ℤ} (hr1 : 1 ≤ r) (hrH : r < H)
    (_h1u : bucketCell B j.val 1 r = true) (h2u : bucketCell B j.val 2 r = true)
    (_h3u : bucketCell B j.val 3 r = true) (_h4u : bucketCell B j.val 4 r = true)
    (h0d : bucketCell B j.val 0 (r - 1) = true) (h1d : bucketCell B j.val 1 (r - 1) = true)
    (h3d : bucketCell B j.val 3 (r - 1) = true) (h4d : bucketCell B j.val 4 (r - 1) = true)
    (hf : bucketCell B j.val 2 (r - 1) = false) :
    HasHole B j.val H := by
  refine ⟨2, r - 1, by omega, by omega, by omega, by omega, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ u v : Cell,
      6 * (j.val : ℤ) ≤ u.1 ∧ u.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ u.2 ∧ u.2 < r ∧
        (u.2 = r - 1 → u.1 = 6 * (j.val : ℤ) + 2) →
      EmptyAdjacent B u v →
      6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < r ∧
        (v.2 = r - 1 → v.1 = 6 * (j.val : ℤ) + 2) := by
    intro u v hu hadj
    rcases hadj with ⟨_, hvf, hdist⟩
    have hstep : (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 - 1 ∧ v.2 = u.2) ∨
        (v.1 = u.1 ∧ v.2 = u.2 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 - 1) := by
      rcases abs_cases (u.1 - v.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (u.2 - v.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    have hnot_rm1 : ∀ dx : ℤ, dx ∈ ([0, 1, 3, 4] : List ℤ) →
        v ≠ (6 * (j.val : ℤ) + dx, r - 1) := by
      intro dx hdx heq
      subst heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdx
      rcases hdx with rfl | rfl | rfl | rfl
      · unfold bucketCell at h0d; rw [h0d] at hvf; cases hvf
      · unfold bucketCell at h1d; rw [h1d] at hvf; cases hvf
      · unfold bucketCell at h3d; rw [h3d] at hvf; cases hvf
      · unfold bucketCell at h4d; rw [h4d] at hvf; cases hvf
    rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · by_cases h5 : v.1 = 6 * (j.val : ℤ) + 5
      · have hw := bucketCell_right_wall_B hframe j (y := v.2) (by omega) (by omega)
        unfold bucketCell at hw
        have heq : (6 * (j.val : ℤ) + 5, v.2) = v := by ext <;> omega
        rw [heq] at hw; rw [hw] at hvf; cases hvf
      · refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        intro hvr
        have hu2 := hu.2.2.2.2 (by omega)
        exact absurd (by ext <;> omega) (hnot_rm1 3 (by decide))
    · by_cases hm1 : v.1 = 6 * (j.val : ℤ) - 1
      · have hw := bucketCell_left_wall_B hframe j (y := v.2) (by omega) (by omega)
        unfold bucketCell at hw
        have heq : (6 * (j.val : ℤ) + -1, v.2) = v := by ext <;> omega
        rw [heq] at hw; rw [hw] at hvf; cases hvf
      · refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        intro hvr
        have hu2 := hu.2.2.2.2 (by omega)
        exact absurd (by ext <;> omega) (hnot_rm1 1 (by decide))
    · by_cases htop : v.2 = r
      · have hu2 := hu.2.2.2.2 (by omega)
        have heq : (6 * (j.val : ℤ) + 2, r) = v := by ext <;> omega
        unfold bucketCell at h2u; rw [heq] at h2u; rw [h2u] at hvf; cases hvf
      · refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        intro hvr
        have hdx : v.1 - 6 * (j.val : ℤ) = 0 ∨ v.1 - 6 * (j.val : ℤ) = 1 ∨
            v.1 - 6 * (j.val : ℤ) = 2 ∨ v.1 - 6 * (j.val : ℤ) = 3 ∨
            v.1 - 6 * (j.val : ℤ) = 4 := by omega
        rcases hdx with h | h | h | h | h
        · exact absurd (by ext <;> omega) (hnot_rm1 0 (by decide))
        · exact absurd (by ext <;> omega) (hnot_rm1 1 (by decide))
        · omega
        · exact absurd (by ext <;> omega) (hnot_rm1 3 (by decide))
        · exact absurd (by ext <;> omega) (hnot_rm1 4 (by decide))
    · by_cases hbot : v.2 = -1
      · unfold Board.occupied at hvf
        have : ¬ (0 ≤ v.2 ∧ v.2 < B.height) := by omega
        simp [this] at hvf
      · refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        intro hvr; omega
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent B) (6 * (j.val : ℤ) + 2, r - 1) v →
      6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < r ∧
        (v.2 = r - 1 → v.1 = 6 * (j.val : ℤ) + 2) := by
    intro v hp
    induction hp with
    | refl => dsimp; omega
    | tail _ hst ih => exact hstay _ _ ih hst
  have := hbox z hpath
  omega

/-! ### Finite Piece-Geometry Lemmas for `.I` and General Pieces -/

private def offsetsB (t : Piece) (o : Fin 4) : List Cell :=
  t.base.map fun z => if t = .Sq then z else clockwise^[o.val] z

private def shiftedB (t : Piece) (o : Fin 4) (u : Cell) : List Cell :=
  (offsetsB t o).map fun v => (v.1 - u.1, v.2 - u.2)

private lemma mem_cells_iff_B {q : PieceState} {z : Cell} :
    z ∈ q.cells ↔ ∃ u ∈ offsetsB q.kind q.orientation,
      z = (q.position.1 + u.1, q.position.2 + u.2) := by
  constructor
  · intro hz
    rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact ⟨if q.kind = .Sq then w else clockwise^[q.orientation.val] w,
      List.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rcases List.mem_map.mp hu with ⟨w, hw, rfl⟩
    exact List.mem_map.mpr ⟨w, hw, rfl⟩

private lemma shiftedB_mem_cells {q : PieceState} {z₀ u d : Cell}
    (hz₀ : z₀ = (q.position.1 + u.1, q.position.2 + u.2))
    (hd : d ∈ shiftedB q.kind q.orientation u) :
    (z₀.1 + d.1, z₀.2 + d.2) ∈ q.cells := by
  rcases List.mem_map.mp hd with ⟨v, hv, rfl⟩
  rw [mem_cells_iff_B]
  refine ⟨v, hv, ?_⟩
  rcases hz₀ with rfl
  ext <;> dsimp <;> omega

/-- An `.I` piece covering `(4, r)` when `(4, r+1)`, `(4, r-1)`, `(5, r)` are occupied
must be horizontal and cover `(1, r)`, `(2, r)`, `(3, r)`, `(4, r)`. -/
private lemma i_notch_cover_aux :
    ∀ o : Fin 4, ∀ u ∈ offsetsB .I o,
      (0, 1) ∈ shiftedB .I o u ∨ (0, -1) ∈ shiftedB .I o u ∨ (1, 0) ∈ shiftedB .I o u ∨
      ((-3, 0) ∈ shiftedB .I o u ∧ (-2, 0) ∈ shiftedB .I o u ∧ (-1, 0) ∈ shiftedB .I o u) := by
  decide

lemma i_notch_cover {B : Board} {j : ℕ} {r : ℤ} {q : PieceState}
    (hk : q.kind = .I) (hclear : B.Clear q)
    (h4u : bucketCell B j 4 (r + 1) = true) (h4d : bucketCell B j 4 (r - 1) = true)
    (h5 : bucketCell B j 5 r = true)
    (hmem : (6 * (j : ℤ) + 4, r) ∈ q.cells) :
    (6 * (j : ℤ) + 1, r) ∈ q.cells ∧ (6 * (j : ℤ) + 2, r) ∈ q.cells ∧
    (6 * (j : ℤ) + 3, r) ∈ q.cells := by
  rcases mem_cells_iff_B.mp hmem with ⟨u, hu, heq⟩
  rw [hk] at hu
  rcases i_notch_cover_aux q.orientation u hu with h | h | h | ⟨h1, h2, h3⟩
  · have hc := hclear _ (shiftedB_mem_cells heq (by rwa [hk]))
    have : (6 * (j : ℤ) + 4 + 0, r + 1) = (6 * (j : ℤ) + 4, r + 1) := by ext <;> omega
    rw [this] at hc; unfold bucketCell at h4u; rw [h4u] at hc; cases hc
  · have hc := hclear _ (shiftedB_mem_cells heq (by rwa [hk]))
    have : (6 * (j : ℤ) + 4 + 0, r + -1) = (6 * (j : ℤ) + 4, r - 1) := by ext <;> omega
    rw [this] at hc; unfold bucketCell at h4d; rw [h4d] at hc; cases hc
  · have hc := hclear _ (shiftedB_mem_cells heq (by rwa [hk]))
    have : (6 * (j : ℤ) + 4 + 1, r + 0) = (6 * (j : ℤ) + 5, r) := by ext <;> omega
    rw [this] at hc; unfold bucketCell at h5; rw [h5] at hc; cases hc
  · refine ⟨?_, ?_, ?_⟩
    · convert shiftedB_mem_cells heq (by rwa [hk] : (-3, 0) ∈ shiftedB q.kind q.orientation u) using 1
      ext <;> omega
    · convert shiftedB_mem_cells heq (by rwa [hk] : (-2, 0) ∈ shiftedB q.kind q.orientation u) using 1
      ext <;> omega
    · convert shiftedB_mem_cells heq (by rwa [hk] : (-1, 0) ∈ shiftedB q.kind q.orientation u) using 1
      ext <;> omega

/-- An `.I` piece is either horizontal (all 4 cells in the same row `y`, consecutive `x` of length 4)
or vertical (all 4 cells in the same column `x`, consecutive `y` of length 4). -/
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

lemma balcony_insert {B : Board} {j H : ℕ} {b : ℤ} {i : Fin 3} {q : PieceState}
    (hbal : Balcony B j H b i) :
    Balcony (B.insert q) j H b i ∨
    (bucketCell (B.insert q) j 0 b = true ∧ bucketCell (B.insert q) j 1 b = true ∧
     bucketCell (B.insert q) j 2 b = true) := by
  cases h : bucketCell (B.insert q) j i.val b with
  | false =>
    left
    refine ⟨hbal.1, hbal.2.1, fun x => ?_⟩
    by_cases hx : x = i
    · subst hx; simpa using h
    · have hB := hbal.2.2 x
      simp only [hx, ne_eq, not_false_eq_true, decide_true] at hB ⊢
      exact bucketCell_insert_of_true hB
  | true =>
    right
    have h012 : ∀ x : Fin 3, bucketCell (B.insert q) j x.val b = true := by
      intro x
      by_cases hx : x = i
      · subst hx; exact h
      · have hB := hbal.2.2 x
        simp only [hx, ne_eq, not_false_eq_true, decide_true] at hB
        exact bucketCell_insert_of_true hB
    exact ⟨h012 0, h012 1, h012 2⟩

lemma closed_row_of_balcony_filled {B : Board} {s H : ℕ} (hframe : BucketFrame B s H)
    (j : Fin s) {b x₀ y₀ : ℤ} (hbH : b < H) (hx0 : 0 ≤ x₀) (hx5 : x₀ < 5)
    (hy0 : 0 ≤ y₀) (hyb : y₀ < b)
    (h0 : bucketCell B j.val 0 b = true) (h1 : bucketCell B j.val 1 b = true)
    (h2 : bucketCell B j.val 2 b = true)
    (h3 : bucketCell B j.val 3 b = true) (h4 : bucketCell B j.val 4 b = true)
    (hf : bucketCell B j.val x₀ y₀ = false) :
    HasHole B j.val H :=
  hasHole_of_closed_row hframe j hbH hx0 hx5 hy0 hyb h0 h1 h2 h3 h4 hf

/-- Helper: if `(0, b) = true, (1, b) = true, (2, b) = true` at `b < H` and some cell `(x₀, y₀)`
in `[0..4] × [0..b)` is `false`, then `HasHole B j.val H` (whether or not `b` is a notch row!). -/
lemma hasHole_of_closed_012 {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {b x₀ y₀ : ℤ} (hb0 : 0 ≤ b) (hbH : b < H) (hx0 : 0 ≤ x₀) (hx5 : x₀ < 5)
    (hy0 : 0 ≤ y₀) (hyb : y₀ < b)
    (h0 : bucketCell B j.val 0 b = true) (h1 : bucketCell B j.val 1 b = true)
    (h2 : bucketCell B j.val 2 b = true)
    (hf : bucketCell B j.val x₀ y₀ = false) :
    HasHole B j.val H := by
  by_cases hbmod : (b + 1) % 6 = 5
  · refine ⟨x₀, y₀, hx0, hx5, hy0, by omega, hf, ?_⟩
    rintro ⟨z, hzH, _, hpath⟩
    have hstay : ∀ u v : Cell,
        6 * (j.val : ℤ) ≤ u.1 ∧ u.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ u.2 ∧ u.2 < b →
        EmptyAdjacent B u v →
        6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < b := by
      intro u v hu hadj
      rcases hadj with ⟨huf, hvf, hdist⟩
      have hstep : (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 - 1 ∧ v.2 = u.2) ∨
          (v.1 = u.1 ∧ v.2 = u.2 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 - 1) := by
        rcases abs_cases (u.1 - v.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (u.2 - v.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
      rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · by_cases h5 : v.1 = 6 * (j.val : ℤ) + 5
        · have hw := bucketCell_right_wall_B hframe j (y := v.2) (by omega) (by omega)
          unfold bucketCell at hw
          have heq : (6 * (j.val : ℤ) + 5, v.2) = v := by ext <;> omega
          rw [heq] at hw; rw [hw] at hvf; cases hvf
        · omega
      · by_cases hm1 : v.1 = 6 * (j.val : ℤ) - 1
        · have hw := bucketCell_left_wall_B hframe j (y := v.2) (by omega) (by omega)
          unfold bucketCell at hw
          have heq : (6 * (j.val : ℤ) + -1, v.2) = v := by ext <;> omega
          rw [heq] at hw; rw [hw] at hvf; cases hvf
        · omega
      · by_cases htop : v.2 = b
        · have h34d := bucketCell_notch_wall_B hframe j (y := b - 1) (by omega) (by omega) (by omega)
          have hdx : v.1 - 6 * (j.val : ℤ) = 0 ∨ v.1 - 6 * (j.val : ℤ) = 1 ∨
              v.1 - 6 * (j.val : ℤ) = 2 ∨ v.1 - 6 * (j.val : ℤ) = 3 ∨
              v.1 - 6 * (j.val : ℤ) = 4 := by omega
          rcases hdx with h | h | h | h | h
          · have heq : (6 * (j.val : ℤ) + 0, b) = v := by ext <;> omega
            unfold bucketCell at h0; rw [heq] at h0; rw [h0] at hvf; cases hvf
          · have heq : (6 * (j.val : ℤ) + 1, b) = v := by ext <;> omega
            unfold bucketCell at h1; rw [heq] at h1; rw [h1] at hvf; cases hvf
          · have heq : (6 * (j.val : ℤ) + 2, b) = v := by ext <;> omega
            unfold bucketCell at h2; rw [heq] at h2; rw [h2] at hvf; cases hvf
          · have heq : (6 * (j.val : ℤ) + 3, b - 1) = u := by ext <;> omega
            unfold bucketCell at h34d; rw [heq] at h34d; rw [h34d.1] at huf; cases huf
          · have heq : (6 * (j.val : ℤ) + 4, b - 1) = u := by ext <;> omega
            unfold bucketCell at h34d; rw [heq] at h34d; rw [h34d.2] at huf; cases huf
        · omega
      · by_cases hbot : v.2 = -1
        · unfold Board.occupied at hvf
          have : ¬ (0 ≤ v.2 ∧ v.2 < B.height) := by omega
          simp [this] at hvf
        · omega
    have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent B) (6 * (j.val : ℤ) + x₀, y₀) v →
        6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < b := by
      intro v hp
      induction hp with
      | refl => dsimp; omega
      | tail _ hst ih => exact hstay _ _ ih hst
    have := hbox z hpath
    omega
  · have h34 := bucketCell_notch_wall_B hframe j hb0 hbH hbmod
    exact hasHole_of_closed_row hframe j hbH hx0 hx5 hy0 hyb h0 h1 h2 h34.1 h34.2 hf

/-! ### Lemma B3: `FlooredNotch` is unfillable (even under `AnyPlay`) -/

/-- Auxiliary: if `OpenNotch B j H y` and `Balcony B j H b i` with `y < b`, and
`(1, y-1) = true ∧ (2, y-1) = true`, then bucket `j` is unfillable under `AnyPlay`! -/
lemma anyPlay_unfillable_of_flooredNotch_12 {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {y b : ℤ} {i : Fin 3} (hyb : y < b)
    (hopen : OpenNotch B j.val H y) (hbal : Balcony B j.val H b i)
    (h1d : bucketCell B j.val 1 (y - 1) = true) (h2d : bucketCell B j.val 2 (y - 1) = true) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rintro ⟨B', hplay, hfull⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  have hy4 : 4 ≤ y := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hyH : y + 1 < H := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
      OpenNotch Bcur j.val H y → Balcony Bcur j.val H b i →
      bucketCell Bcur j.val 1 (y - 1) = true → bucketCell Bcur j.val 2 (y - 1) = true →
      BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ hopen' _ _ _ hfull'
      exact not_bucketFull_of_false_B hfull' (by omega) (by omega) (by omega) (by omega) hopen'.2.2.2.2
    | @step Bcur B' q htraj hrest ih =>
      intro hfr hopen' hbal' h1d' h2d' hfull'
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      have hnot4 : (6 * (j.val : ℤ) + 4, y) ∉ q.cells := by
        intro hmem
        by_cases hI : q.kind = .I
        · have h4u := (bucketCell_notch_wall_B hfr j (y := y + 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
          have h4d := (bucketCell_notch_wall_B hfr j (y := y - 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
          have h5 := bucketCell_right_wall_B hfr j (y := y) (by omega) (by omega)
          have hcov := i_notch_cover hI hclear h4u h4d h5 hmem
          have hreachI : Reachable R Bcur H .I q := by rw [← hI]; exact hreach
          exact hReason.2.2.2.2 Bcur s H hfr j y q hopen' h1d' h2d' hreachI ⟨hcov.2.2, hmem⟩
        · have hcond := hReason.2.2.2.1 Bcur s H hfr j b i q.kind q hbal' hbal'.2.1 hI hreach
            (6 * (j.val : ℤ) + 4, y) hmem (by omega) (by omega) (by omega)
          dsimp at hcond; have := i.isLt; omega
      by_cases hm3 : (6 * (j.val : ℤ) + 3, y) ∈ q.cells
      · have h4u := (bucketCell_notch_wall_B hfr j (y := y + 1) (by omega) (by omega)
          (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
        have h4d := (bucketCell_notch_wall_B hfr j (y := y - 1) (by omega) (by omega)
          (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
        have h5 := bucketCell_right_wall_B hfr j (y := y) (by omega) (by omega)
        have hhole := hasHole_of_surrounded_B (B := Bcur.insert q) (j := j.val) (H := H) (x := 4) (y := y)
          (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_not_mem hopen'.2.2.2.2 hnot4)
          (bucketCell_insert_of_true h5)
          (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm3)
          (bucketCell_insert_of_true h4u)
          (bucketCell_insert_of_true h4d)
        exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
      · have hopen'' : OpenNotch (Bcur.insert q) j.val H y :=
          ⟨hopen'.1, hopen'.2.1, hopen'.2.2.1,
            bucketCell_insert_of_not_mem hopen'.2.2.2.1 hm3,
            bucketCell_insert_of_not_mem hopen'.2.2.2.2 hnot4⟩
        rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
        · exact ih (bucketFrame_insert hfr) hopen'' hbal''
            (bucketCell_insert_of_true h1d') (bucketCell_insert_of_true h2d') hfull'
        · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
            hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) hyb hb0 hb1 hb2 hopen''.2.2.2.2
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
  exact hgen hplay hframe hopen hbal h1d h2d hfull

/-- `FlooredNotch` is unfillable under `AnyPlay`! -/
theorem anyPlay_unfillable_of_flooredNotch {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    (hfn : FlooredNotch B j.val H) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rcases hfn with ⟨y, hopen, ⟨b, i, hyb, hbal⟩, hcase⟩
  rcases hcase with ⟨h0d, h1d, h2f⟩ | ⟨_, h1d, h2d⟩ | ⟨_, h1d, h2d⟩
  · -- Case 1: `(0, y-1) = T, (1, y-1) = T, (2, y-1) = F`
    rintro ⟨B', hplay, hfull⟩
    rcases hframe.2.1 with ⟨T, hHT⟩
    have hy4 : 4 ≤ y := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
    have hyH : y + 1 < H := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
    have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
        OpenNotch Bcur j.val H y → Balcony Bcur j.val H b i →
        bucketCell Bcur j.val 0 (y - 1) = true → bucketCell Bcur j.val 1 (y - 1) = true →
        bucketCell Bcur j.val 2 (y - 1) = false → BucketFull B' j.val H → False := by
      intro Bcur B' hp
      induction hp with
      | nil Bcur =>
        intro _ hopen' _ _ _ _ hfull'
        exact not_bucketFull_of_false_B hfull' (by omega) (by omega) (by omega) (by omega) hopen'.2.2.2.2
      | @step Bcur B' q htraj hrest ih =>
        intro hfr hopen' hbal' h0d' h1d' h2f' hfull'
        have hclear := trajectory_clear_B htraj
        have hreach := trajectory_reachable_B hfr htraj
        by_cases hm4 : (6 * (j.val : ℤ) + 4, y) ∈ q.cells
        · have hI : q.kind = .I := by
            by_contra hne
            have hcond := hReason.2.2.2.1 Bcur s H hfr j b i q.kind q hbal' hbal'.2.1 hne hreach
              (6 * (j.val : ℤ) + 4, y) hm4 (by omega) (by omega) (by omega)
            dsimp at hcond; have := i.isLt; omega
          have h4u := (bucketCell_notch_wall_B hfr j (y := y + 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
          have h4d := (bucketCell_notch_wall_B hfr j (y := y - 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
          have h3d := (bucketCell_notch_wall_B hfr j (y := y - 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).1
          have h5 := bucketCell_right_wall_B hfr j (y := y) (by omega) (by omega)
          have hcov := i_notch_cover hI hclear h4u h4d h5 hm4
          have hno2d : (6 * (j.val : ℤ) + 2, y - 1) ∉ q.cells := by
            intro hm2d
            rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
            · have h1 := List.mem_toFinset.mpr hm4; rw [hfin] at h1
              have h2 := List.mem_toFinset.mpr hm2d; rw [hfin] at h2
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
              rcases h1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ | ⟨_, hy1⟩ | ⟨_, hy1⟩ <;>
                rcases h2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ | ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
            · have h1 := List.mem_toFinset.mpr hm4; rw [hfin] at h1
              have h2 := List.mem_toFinset.mpr hm2d; rw [hfin] at h2
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
              rcases h1 with ⟨hx1, _⟩ | ⟨hx1, _⟩ | ⟨hx1, _⟩ | ⟨hx1, _⟩ <;>
                rcases h2 with ⟨hx2, _⟩ | ⟨hx2, _⟩ | ⟨hx2, _⟩ | ⟨hx2, _⟩ <;> omega
          have hhole := hasHole_of_stepped_seal (bucketFrame_insert hfr) j (by omega) (by omega)
            (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hcov.1)
            (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hcov.2.1)
            (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hcov.2.2)
            (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm4)
            (bucketCell_insert_of_true h0d') (bucketCell_insert_of_true h1d')
            (bucketCell_insert_of_true h3d) (bucketCell_insert_of_true h4d)
            (bucketCell_insert_of_not_mem h2f' hno2d)
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
        · by_cases hm3 : (6 * (j.val : ℤ) + 3, y) ∈ q.cells
          · have h4u := (bucketCell_notch_wall_B hfr j (y := y + 1) (by omega) (by omega)
              (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
            have h4d := (bucketCell_notch_wall_B hfr j (y := y - 1) (by omega) (by omega)
              (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
            have h5 := bucketCell_right_wall_B hfr j (y := y) (by omega) (by omega)
            have hhole := hasHole_of_surrounded_B (B := Bcur.insert q) (j := j.val) (H := H) (x := 4) (y := y)
              (by omega) (by omega) (by omega) (by omega)
              (bucketCell_insert_of_not_mem hopen'.2.2.2.2 hm4)
              (bucketCell_insert_of_true h5)
              (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm3)
              (bucketCell_insert_of_true h4u)
              (bucketCell_insert_of_true h4d)
            exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
          · have hopen'' : OpenNotch (Bcur.insert q) j.val H y :=
              ⟨hopen'.1, hopen'.2.1, hopen'.2.2.1,
                bucketCell_insert_of_not_mem hopen'.2.2.2.1 hm3,
                bucketCell_insert_of_not_mem hopen'.2.2.2.2 hm4⟩
            rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
            · by_cases hm2d : (6 * (j.val : ℤ) + 2, y - 1) ∈ q.cells
              · exact anyPlay_unfillable_of_flooredNotch_12 hReason (bucketFrame_insert hfr) j
                  hyb hopen'' hbal'' (bucketCell_insert_of_true h1d')
                  (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm2d)
                  ⟨B', hrest, hfull'⟩
              · exact ih (bucketFrame_insert hfr) hopen'' hbal''
                  (bucketCell_insert_of_true h0d') (bucketCell_insert_of_true h1d')
                  (bucketCell_insert_of_not_mem h2f' hm2d) hfull'
            · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) hyb hb0 hb1 hb2 hopen''.2.2.2.2
              exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
    exact hgen hplay hframe hopen hbal h0d h1d h2f hfull
  · exact anyPlay_unfillable_of_flooredNotch_12 hReason hframe j hyb hopen hbal h1d h2d
  · exact anyPlay_unfillable_of_flooredNotch_12 hReason hframe j hyb hopen hbal h1d h2d

/-! ### Lemma B4: `BadNonNotchVeranda` is unfillable (mod-4 empty-cell count invariant!) -/

/-- Count of empty cells in column `col` of bucket `j` in rows `[bottom, bottom + length)`. -/
def verandaEmptyCount (B : Board) (j : ℕ) (col bottom : ℤ) (length : ℕ) : ℕ :=
  ((Finset.range length).filter fun k : ℕ => bucketCell B j col (bottom + (k : ℤ)) = false).card

/-- `BadNonNotchVeranda` is unfillable under `AnyPlay`! -/
theorem anyPlay_unfillable_of_badNonNotchVeranda {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    (hbad : BadNonNotchVeranda B j.val H) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rcases hbad with ⟨col, bottom, length, hver, hmod4, ⟨b, ib, hltb, hbal⟩, hnonotch⟩
  -- Generalize to any board preserving sentinels, no-notch, balcony, and `verandaEmptyCount % 4 ≠ 0`
  have hcnt0 : verandaEmptyCount B j.val col.val bottom length % 4 ≠ 0 := by
    have hall : verandaEmptyCount B j.val col.val bottom length = length := by
      unfold verandaEmptyCount
      have hfilt : ((Finset.range length).filter fun k : ℕ => bucketCell B j.val col.val (bottom + (k : ℤ)) = false) =
          Finset.range length := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
        intro hk; exact hver.2.2.2.1 (bottom + k) (by omega) (by omega)
      rw [hfilt, Finset.card_range]
    rwa [hall]
  have hgen : ∀ {Bcur B' : Board},
      AnyPlay R Bcur B' →
      BucketFrame Bcur s H →
      Balcony Bcur j.val H b ib →
      bucketCell Bcur j.val col.val (bottom - 1) = true →
      bucketCell Bcur j.val col.val (bottom + length) = true →
      (∀ y : ℤ, bottom ≤ y → y < bottom + length →
        (y + 1) % 6 ≠ 5 ∨ (bucketCell Bcur j.val 3 y = true ∧ bucketCell Bcur j.val 4 y = true)) →
      verandaEmptyCount Bcur j.val col.val bottom length % 4 ≠ 0 →
      BucketFull B' j.val H → False := by
    intro Bcur B' hplay
    induction hplay with
    | nil Bcur =>
      intro _ _ _ _ _ hcnt hfull
      have hpos : 0 < verandaEmptyCount Bcur j.val col.val bottom length := by omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact not_bucketFull_of_false_B hfull (by omega) (by have := col.isLt; omega)
        (by have := hver.2.1; omega) (by have := hver.2.2.1; omega) hk.2
    | @step Bcur B' q htraj hrest ih =>
      intro hfr hbalc hbot htop hnn hcnt hfull
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      -- Check whether `q` touches ANY cell `(col, bottom + k)` for `k < length`
      have htouch_nonI : q.kind ≠ .I → ∀ k < length, (6 * (j.val : ℤ) + col.val, bottom + k) ∉ q.cells := by
        intro hne k hk hmem
        have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbalc hbalc.2.1 hne hreach
          (6 * (j.val : ℤ) + col.val, bottom + k) hmem (by omega) (by have := col.isLt; omega) (by omega)
        dsimp at hcond
        have hcol_eq : (col.val : ℤ) = (ib.val : ℤ) := by omega
        rcases hcond.2 with h1 | h2
        · omega
        · -- bottom + k = b - 1, so bottom + length = b (since bottom + length - 1 < b and k < length)
          have hb_eq : bottom + length = b := by omega
          have hbal_f := hbalc.2.2 ib
          simp only [ne_eq, not_true_eq_false, decide_false] at hbal_f
          rw [hb_eq, hcol_eq] at htop
          rw [hbal_f] at htop; cases htop
      have htouch_horizI : ∀ x₀ y₀ : ℤ,
          q.cells.toFinset = {(x₀, y₀), (x₀ + 1, y₀), (x₀ + 2, y₀), (x₀ + 3, y₀)} →
          ∀ k < length, (6 * (j.val : ℤ) + col.val, bottom + k) ∉ q.cells := by
        intro x₀ y₀ hfin k hk hmem
        have hin := List.mem_toFinset.mpr hmem
        rw [hfin] at hin
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hin
        have hy0 : y₀ = bottom + k := by rcases hin with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        -- At row y₀, (3, y₀) and (4, y₀) are occupied (and (-1, y₀) and (5, y₀) are occupied)!
        have h34_occ : bucketCell Bcur j.val 3 y₀ = true := by
          rcases hnn y₀ (by omega) (by omega) with hmod | ⟨h3, _⟩
          · exact (bucketCell_notch_wall_B hfr j (by have := hver.2.1; omega)
              (by have := hver.2.2.1; omega) hmod).1
          · exact h3
        have hL := bucketCell_left_wall_B hfr j (y := y₀) (by have := hver.2.1; omega)
          (by have := hver.2.2.1; omega)
        have hR := bucketCell_right_wall_B hfr j (y := y₀) (by have := hver.2.1; omega)
          (by have := hver.2.2.1; omega)
        -- 4 consecutive x-coords in [6j, 6j+4] containing x_col must hit 6j-1, 6j+3, or 6j+5!
        have hx_hit : (6 * (j.val : ℤ) - 1, y₀) ∈ q.cells ∨
            (6 * (j.val : ℤ) + 3, y₀) ∈ q.cells ∨ (6 * (j.val : ℤ) + 5, y₀) ∈ q.cells := by
          have hcol_lt := col.isLt
          have hx0_cases : x₀ ≤ 6 * (j.val : ℤ) - 1 ∨ x₀ = 6 * (j.val : ℤ) ∨
              x₀ = 6 * (j.val : ℤ) + 1 ∨ x₀ = 6 * (j.val : ℤ) + 2 ∨
              6 * (j.val : ℤ) + 3 ≤ x₀ := by omega
          have hxb : x₀ ≤ 6 * (j.val : ℤ) + col.val ∧ 6 * (j.val : ℤ) + col.val ≤ x₀ + 3 := by
            rcases hin with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
          have hmem_of : ∀ x : ℤ, x = x₀ ∨ x = x₀ + 1 ∨ x = x₀ + 2 ∨ x = x₀ + 3 →
              (x, y₀) ∈ q.cells := by
            intro x hx; apply List.mem_toFinset.mp; rw [hfin]
            simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
            rcases hx with rfl | rfl | rfl | rfl <;> simp
          rcases hx0_cases with h | h | h | h | h
          · left; exact hmem_of (6 * (j.val : ℤ) - 1) (by omega)
          · right; left; exact hmem_of (6 * (j.val : ℤ) + 3) (by omega)
          · right; left; exact hmem_of (6 * (j.val : ℤ) + 3) (by omega)
          · right; left; exact hmem_of (6 * (j.val : ℤ) + 3) (by omega)
          · right; right; exact hmem_of (6 * (j.val : ℤ) + 5) (by omega)
        rcases hx_hit with hm | hm | hm
        · have hc := hclear _ hm; unfold bucketCell at hL
          have : (6 * (j.val : ℤ) + -1, y₀) = (6 * (j.val : ℤ) - 1, y₀) := by ext <;> omega
          rw [this] at hL; rw [hL] at hc; cases hc
        · have hc := hclear _ hm; unfold bucketCell at h34_occ; rw [h34_occ] at hc; cases hc
        · have hc := hclear _ hm; unfold bucketCell at hR; rw [hR] at hc; cases hc
      -- Now compute `verandaEmptyCount (Bcur.insert q) % 4`!
      have hcnt' : verandaEmptyCount (Bcur.insert q) j.val col.val bottom length % 4 ≠ 0 := by
        by_cases hI : q.kind = .I
        · rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
          · have hsame : verandaEmptyCount (Bcur.insert q) j.val col.val bottom length =
                verandaEmptyCount Bcur j.val col.val bottom length := by
              unfold verandaEmptyCount; congr 1; ext k
              simp only [Finset.mem_filter, Finset.mem_range]
              refine and_congr_right fun hk => ?_
              constructor
              · intro h; cases hB : bucketCell Bcur j.val col.val (bottom + k) with
                | false => rfl
                | true => rw [bucketCell_insert_of_true hB] at h; cases h
              · intro h; exact bucketCell_insert_of_not_mem h (htouch_horizI x₀ y₀ hfin k hk)
            rw [hsame]; exact hcnt
          · -- Vertical `.I` at column `x₀`: either `x₀ ≠ 6j + col` (no change) or `x₀ = 6j + col`
            by_cases hxcol : x₀ = 6 * (j.val : ℤ) + col.val
            · -- If it touches any `bottom + k`, then all 4 cells lie in `[bottom, bottom + length)`!
              by_cases hhit : ∃ k < length, (6 * (j.val : ℤ) + col.val, bottom + k) ∈ q.cells
              · rcases hhit with ⟨k0, hk0, hm0⟩
                have hm0' := List.mem_toFinset.mpr hm0; rw [hfin] at hm0'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm0'
                have hy0_ge : bottom ≤ y₀ := by
                  by_contra hlt; push Not at hlt
                  have hbm1 : (6 * (j.val : ℤ) + col.val, bottom - 1) ∈ q.cells := by
                    apply List.mem_toFinset.mp; rw [hfin]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                    rcases hm0' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
                  have hc := hclear _ hbm1; unfold bucketCell at hbot; rw [hbot] at hc; cases hc
                have hy0_le : y₀ + 3 < bottom + length := by
                  by_contra hge; push Not at hge
                  have htopm : (6 * (j.val : ℤ) + col.val, bottom + length) ∈ q.cells := by
                    apply List.mem_toFinset.mp; rw [hfin]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                    rcases hm0' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
                  have hc := hclear _ htopm; unfold bucketCell at htop; rw [htop] at hc; cases hc
                -- The 4 indices `d, d+1, d+2, d+3` (where `d = (y₀ - bottom).toNat`) are in `range length`,
                -- empty in `Bcur`, and filled in `Bcur.insert q`!
                set d : ℕ := (y₀ - bottom).toNat
                set S4 : Finset ℕ := {d, d + 1, d + 2, d + 3}
                have hS4_card : S4.card = 4 := by
                  simp only [S4]
                  rw [Finset.card_insert_of_notMem (by simp),
                    Finset.card_insert_of_notMem (by simp),
                    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
                set E0 := (Finset.range length).filter fun k : ℕ => bucketCell Bcur j.val col.val (bottom + (k : ℤ)) = false
                set E1 := (Finset.range length).filter fun k : ℕ => bucketCell (Bcur.insert q) j.val col.val (bottom + (k : ℤ)) = false
                have hmem_q : ∀ k : ℕ, (6 * (j.val : ℤ) + col.val, bottom + k) ∈ q.cells ↔ k ∈ S4 := by
                  intro k
                  rw [← List.mem_toFinset, hfin]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, S4]
                  omega
                have hS4_sub : S4 ⊆ E0 := by
                  intro k hk
                  rw [Finset.mem_filter, Finset.mem_range]
                  have hmq := (hmem_q k).mpr hk
                  have hk_lt : k < length := by
                    simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hk; omega
                  exact ⟨hk_lt, hclear _ hmq⟩
                have hE1_eq : E1 = E0 \ S4 := by
                  ext k
                  simp only [E1, E0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
                  constructor
                  · intro ⟨hk, hf⟩
                    have hf0 : bucketCell Bcur j.val col.val (bottom + k) = false := by
                      cases hB : bucketCell Bcur j.val col.val (bottom + k) with
                      | false => rfl
                      | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
                    refine ⟨⟨hk, hf0⟩, fun hk4 => ?_⟩
                    have hmq := (hmem_q k).mpr hk4
                    have ht := bucketCell_insert_of_mem hfr (by omega) (by have := col.isLt; omega)
                      (by have := hver.2.1; omega) (by have := hver.2.2.1; omega) hmq
                    rw [ht] at hf; cases hf
                  · rintro ⟨⟨hk, hf0⟩, hnot4⟩
                    exact ⟨hk, bucketCell_insert_of_not_mem hf0 (mt (hmem_q k).mp hnot4)⟩
                have hcard : E1.card + 4 = E0.card := by
                  rw [hE1_eq, ← hS4_card, Finset.card_sdiff_add_card_eq_card hS4_sub]
                change E1.card % 4 ≠ 0
                change E0.card % 4 ≠ 0 at hcnt
                omega
              · push Not at hhit
                have hsame : verandaEmptyCount (Bcur.insert q) j.val col.val bottom length =
                    verandaEmptyCount Bcur j.val col.val bottom length := by
                  unfold verandaEmptyCount; congr 1; ext k
                  simp only [Finset.mem_filter, Finset.mem_range]
                  refine and_congr_right fun hk => ?_
                  constructor
                  · intro h; cases hB : bucketCell Bcur j.val col.val (bottom + k) with
                    | false => rfl
                    | true => rw [bucketCell_insert_of_true hB] at h; cases h
                  · intro h; exact bucketCell_insert_of_not_mem h (hhit k hk)
                rw [hsame]; exact hcnt
            · have hnot : ∀ k < length, (6 * (j.val : ℤ) + col.val, bottom + k) ∉ q.cells := by
                intro k _ hm
                have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                rcases hm' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
              have hsame : verandaEmptyCount (Bcur.insert q) j.val col.val bottom length =
                  verandaEmptyCount Bcur j.val col.val bottom length := by
                unfold verandaEmptyCount; congr 1; ext k
                simp only [Finset.mem_filter, Finset.mem_range]
                refine and_congr_right fun hk => ?_
                constructor
                · intro h; cases hB : bucketCell Bcur j.val col.val (bottom + k) with
                  | false => rfl
                  | true => rw [bucketCell_insert_of_true hB] at h; cases h
                · intro h; exact bucketCell_insert_of_not_mem h (hnot k hk)
              rw [hsame]; exact hcnt
        · have hsame : verandaEmptyCount (Bcur.insert q) j.val col.val bottom length =
              verandaEmptyCount Bcur j.val col.val bottom length := by
            unfold verandaEmptyCount; congr 1; ext k
            simp only [Finset.mem_filter, Finset.mem_range]
            refine and_congr_right fun hk => ?_
            constructor
            · intro h; cases hB : bucketCell Bcur j.val col.val (bottom + k) with
              | false => rfl
              | true => rw [bucketCell_insert_of_true hB] at h; cases h
            · intro h; exact bucketCell_insert_of_not_mem h (htouch_nonI hI k hk)
          rw [hsame]; exact hcnt
      rcases balcony_insert (q := q) hbalc with hbal' | ⟨hb0, hb1, hb2⟩
      · exact ih (bucketFrame_insert hfr) hbal'
          (bucketCell_insert_of_true hbot) (bucketCell_insert_of_true htop)
          (fun y hy1 hy2 => by
            rcases hnn y hy1 hy2 with h | ⟨h3, h4⟩
            · exact Or.inl h
            · exact Or.inr ⟨bucketCell_insert_of_true h3, bucketCell_insert_of_true h4⟩)
          hcnt' hfull
      · have hpos : 0 < verandaEmptyCount (Bcur.insert q) j.val col.val bottom length := by omega
        obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter, Finset.mem_range] at hk
        have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
          hbalc.1 hbalc.2.1 (by omega) (by have := col.isLt; omega)
          (by have := hver.2.1; omega) (by omega) hb0 hb1 hb2 hk.2
        exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull⟩
  rintro ⟨B', hplay, hfull⟩
  exact hgen hplay hframe hbal hver.2.2.2.2.1 hver.2.2.2.2.2 hnonotch hcnt0 hfull

/-! ### Lemma B5: `FlatDiscrepancy` (with balcony above ceiling) is unfillable (mod-4 diff invariant!) -/

/-- Count of empty cells in column `col` of bucket `j` in rows `[h, h + n)`. -/
def colEmptyCount (B : Board) (j : ℕ) (col h : ℤ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k : ℕ => bucketCell B j col (h + (k : ℤ)) = false).card


private lemma geom_G2_B_aux (t : Piece) (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (o : Fin 4) :
    ∀ u ∈ offsetsB t o,
      (0, 1) ∈ shiftedB t o u ∨ (0, -1) ∈ shiftedB t o u ∨
      (1, 0) ∈ shiftedB t o u ∨ (-1, 1) ∈ shiftedB t o u ∨ (-1, -1) ∈ shiftedB t o u ∨
      ((t = .I ∧ (-3, 0) ∈ shiftedB t o u ∧ (-2, 0) ∈ shiftedB t o u ∧ (-1, 0) ∈ shiftedB t o u) ∨
       (t = .LG ∧ (-2, 0) ∈ shiftedB t o u ∧ (-1, 0) ∈ shiftedB t o u)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> fin_cases o <;> decide

theorem noRG_unfillable_of_spurnedNotch {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    (hsp : SpurnedNotch B j.val H) :
    ¬ ∃ B', AnyPlayNoRG R B B' ∧ BucketFull B' j.val H := by
  rcases hsp with ⟨r, hopen, h1r⟩
  rintro ⟨B', hplay, hfull⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  have hr4 : 4 ≤ r := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hrH : r + 1 < H := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hrmod : (r + 1) % 6 = 5 := hopen.2.2.1
  have h4f : bucketCell B j.val 4 r = false := hopen.2.2.2.2
  have hgen : ∀ {Bcur B' : Board}, AnyPlayNoRG R Bcur B' → BucketFrame Bcur s H →
      bucketCell Bcur j.val 1 r = true → bucketCell Bcur j.val 4 r = false →
      BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ _ h4f' hfull'
      exact not_bucketFull_of_false_B hfull' (by omega) (by omega) (by omega) (by omega) h4f'
    | @step Bcur B' q hk htraj _ ih =>
      intro hfr h1r' h4f' hfull'
      have hclear := trajectory_clear_B htraj
      have h34u := bucketCell_notch_wall_B hfr j (y := r + 1) (by omega) (by omega) (by omega)
      have h34d := bucketCell_notch_wall_B hfr j (y := r - 1) (by omega) (by omega) (by omega)
      have h5 := bucketCell_right_wall_B hfr j (y := r) (by omega) (by omega)
      have hnot4 : (6 * (j.val : ℤ) + 4, r) ∉ q.cells := by
        intro hm4
        rcases mem_cells_iff_B.mp hm4 with ⟨u, hu, heq⟩
        have hnot : ∀ d : Cell, Bcur.occupied (6 * (j.val : ℤ) + 4 + d.1, r + d.2) = true →
            d ∉ shiftedB q.kind q.orientation u := by
          intro d hocc hd
          have hc := hclear _ (shiftedB_mem_cells heq hd)
          dsimp at hc; rw [hocc] at hc; cases hc
        rcases geom_G2_B_aux q.kind hk q.orientation u hu with h | h | h | h | h | ⟨hI, h1, _, _⟩ | ⟨hLG, _, h3⟩
        · exact absurd h (hnot (0, 1) (by simpa [bucketCell, add_assoc] using h34u.2))
        · exact absurd h (hnot (0, -1) (by simpa [bucketCell, sub_eq_add_neg, add_assoc] using h34d.2))
        · exact absurd h (hnot (1, 0) (by simpa [bucketCell, add_assoc] using h5))
        · exact absurd h (hnot (-1, 1) (by
            have : (6 * (j.val : ℤ) + 4 + -1, r + 1) = (6 * (j.val : ℤ) + 3, r + 1) := by ext <;> omega
            rw [this]; exact h34u.1))
        · exact absurd h (hnot (-1, -1) (by
            have : (6 * (j.val : ℤ) + 4 + -1, r + -1) = (6 * (j.val : ℤ) + 3, r - 1) := by ext <;> omega
            rw [this]; exact h34d.1))
        · have h1m : (6 * (j.val : ℤ) + 1, r) ∈ q.cells := by
            convert shiftedB_mem_cells heq h1 using 1; ext <;> omega
          have hc := hclear _ h1m; unfold bucketCell at h1r'; rw [h1r'] at hc; cases hc
        · have h3m : (6 * (j.val : ℤ) + 3, r) ∈ q.cells := by
            convert shiftedB_mem_cells heq h3 using 1; ext <;> omega
          have h3f : bucketCell Bcur j.val 3 r = false := hclear _ h3m
          have hopen' : OpenNotch Bcur j.val H r := ⟨by omega, by omega, hrmod, h3f, h4f'⟩
          have hreach : Reachable R Bcur H .LG q := by rw [← hLG]; exact trajectory_reachable_B hfr htraj
          exact hReason.2.2.1 Bcur s H hfr j r q hopen' h1r' hreach ⟨h3m, hm4⟩
      exact ih (bucketFrame_insert hfr) (bucketCell_insert_of_true h1r')
        (bucketCell_insert_of_not_mem h4f' hnot4) hfull'
  exact hgen hplay hframe h1r h4f hfull

end TetrisHard.Rows.Padded

namespace TetrisHard.Rows.Padded
open TetrisHard.Rows

lemma piece_cells_length (q : PieceState) : q.cells.length = 4 := by
  cases h : q.kind <;> simp [PieceState.cells, h, Piece.base]


lemma position_mem_cells_A (q : PieceState) : q.position ∈ q.cells := by
  have h0 : (0, 0) ∈ q.kind.base := by cases q.kind <;> decide
  have hcw : ∀ n : ℕ, clockwise^[n] (0, 0) = (0, 0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
  unfold PieceState.cells
  refine List.mem_map.mpr ⟨(0, 0), h0, ?_⟩
  by_cases h : q.kind = .Sq <;> simp [h, hcw]


end TetrisHard.Rows.Padded

namespace TetrisHard.Rows.Padded.Carbon
open TetrisHard.Rows
open TetrisHard.Rows.Padded

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


lemma noRGSeqPlay_to_anyPlayNoRG {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U ts us U') : AnyPlayNoRG R U U' := by
  induction hp with
  | nil U => exact .nil U
  | step _ ht _ _ _ htraj _ ih =>
    have hk : _ = _ := trajectory_kind_eq htraj
    exact .step (by rwa [hk]) (by rwa [hk]) ih


lemma anyPlayNoRG_to_anyPlay {R : Rotation} {U B' : Board}
    (hp : AnyPlayNoRG R U B') : AnyPlay R U B' := by
  induction hp with
  | nil U => exact .nil U
  | step _ htraj _ ih => exact .step htraj ih

lemma noRGSeqPlay_trans {R : Rotation} {s s' H' : ℕ}
    {U1 U2 U3 : Board} {ts1 ts2 : List Piece} {us1 us2 : List PieceState}
    (hp1 : NoRGSeqPlay R s s' H' U1 ts1 us1 U2)
    (hp2 : NoRGSeqPlay R s s' H' U2 ts2 us2 U3) :
    NoRGSeqPlay R s s' H' U1 (ts1 ++ ts2) (us1 ++ us2) U3 := by
  induction hp1 with
  | nil _ => simpa using hp2
  | step j ht hfr hin hy htraj _ ih =>
    exact .step j ht hfr hin hy htraj (ih hp2)

lemma noRGSeqPlay_bucketFrame_end {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts : List Piece} {us : List PieceState}
    (hfr0 : BucketFrame U s' H')
    (hp : NoRGSeqPlay R s s' H' U ts us U') : BucketFrame U' s' H' := by
  induction hp with
  | nil _ => exact hfr0
  | step _ _ hfr _ _ _ _ ih => exact ih (bucketFrame_insert hfr)


lemma allFillableStrict_of_play {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U ts us U')
    (hall : AllFillableStrict R s s' H' U') :
    AllFillableStrict R s s' H' U := by
  intro j
  obtain ⟨ts2, us2, U_end, hp2, hfull⟩ := hall j
  exact ⟨ts ++ ts2, us ++ us2, U_end, noRGSeqPlay_trans hp hp2, hfull⟩

lemma fillableStrict_to_anyPlayNoRG {R : Rotation} {s s' H' : ℕ} {U : Board} {j : Fin s}
    (hf : FillableStrict R s s' H' U j) :
    ∃ B', AnyPlayNoRG R U B' ∧ BucketFull B' j.val H' := by
  rcases hf with ⟨_, _, U_end, hp, hfull⟩
  exact ⟨U_end, noRGSeqPlay_to_anyPlayNoRG hp, hfull⟩

lemma fillableStrict_to_anyPlay {R : Rotation} {s s' H' : ℕ} {U : Board} {j : Fin s}
    (hf : FillableStrict R s s' H' U j) :
    ∃ B', AnyPlay R U B' ∧ BucketFull B' j.val H' := by
  obtain ⟨B', hp, hfull⟩ := fillableStrict_to_anyPlayNoRG hf
  exact ⟨B', anyPlayNoRG_to_anyPlay hp, hfull⟩

lemma not_fillableStrict_of_anyPlay {R : Rotation} {s s' H' : ℕ} {U : Board} {j : Fin s}
    (hunf : ¬ ∃ B', AnyPlay R U B' ∧ BucketFull B' j.val H') :
    ¬ FillableStrict R s s' H' U j :=
  fun hf => hunf (fillableStrict_to_anyPlay hf)

lemma not_fillableStrict_of_anyPlayNoRG {R : Rotation} {s s' H' : ℕ} {U : Board} {j : Fin s}
    (hunf : ¬ ∃ B', AnyPlayNoRG R U B' ∧ BucketFull B' j.val H') :
    ¬ FillableStrict R s s' H' U j :=
  fun hf => hunf (fillableStrict_to_anyPlayNoRG hf)

lemma inBucket_unique_of_mem {j k : ℕ} {u : PieceState} {x y : ℤ}
    (hx0 : 0 ≤ x) (hx6 : x < 6)
    (hin : InBucket k u) (hmem : (6 * (j : ℤ) + x, y) ∈ u.cells) : k = j := by
  have hk := hin _ hmem
  dsimp at hk
  omega

lemma bucketCell_insert_other_bucket {U : Board} {j k : ℕ} (hne : j ≠ k)
    {u : PieceState} (hin : InBucket k u) {x y : ℤ} (hx0 : 0 ≤ x) (hx6 : x < 6) :
    bucketCell (U.insert u) j x y = bucketCell U j x y := by
  cases hB : bucketCell U j x y with
  | true => exact bucketCell_insert_of_true hB
  | false =>
    apply bucketCell_insert_of_not_mem hB
    intro hmem
    exact hne (inBucket_unique_of_mem hx0 hx6 hin hmem).symm

/-! ### Additional `HasHole` Builders -/

/-- If notch `r` has `(2, r) = true` while `(4, r) = false`, then `{(3, r), (4, r)}` is sealed (`HasHole`). -/
lemma hasHole_of_blocked_notch {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    (j : Fin s') {r : ℤ} (hr1 : 1 ≤ r) (hrH : r + 1 < (H' : ℤ)) (hmod : (r + 1) % 6 = 5)
    (h2r : bucketCell U j.val 2 r = true) (h4f : bucketCell U j.val 4 r = false) :
    HasHole U j.val H' := by
  have h34u := bucketCell_notch_wall_B hframe j (y := r + 1) (by omega) (by omega) (by omega)
  have h34d := bucketCell_notch_wall_B hframe j (y := r - 1) (by omega) (by omega) (by omega)
  have h5 := bucketCell_right_wall_B hframe j (y := r) (by omega) (by omega)
  refine ⟨4, r, by omega, by omega, by omega, by omega, h4f, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ a b : Cell,
      ((a = (6 * (j.val : ℤ) + 3, r) ∨ a = (6 * (j.val : ℤ) + 4, r)) →
        EmptyAdjacent U a b →
        (b = (6 * (j.val : ℤ) + 3, r) ∨ b = (6 * (j.val : ℤ) + 4, r))) := by
    intro a b ha hadj
    rcases hadj with ⟨_, hbf, hdist⟩
    have hstep : (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
        (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
      rcases abs_cases (a.1 - b.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (a.2 - b.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases ha with rfl | rfl
    · rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · right; ext <;> dsimp at * <;> omega
      · have hb : (6 * (j.val : ℤ) + 2, r) = b := by ext <;> dsimp at * <;> omega
        unfold bucketCell at h2r; rw [hb, hbf] at h2r; cases h2r
      · have hb : (6 * (j.val : ℤ) + 3, r + 1) = b := by ext <;> dsimp at * <;> omega
        have ht := h34u.1; unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
      · have hb : (6 * (j.val : ℤ) + 3, r - 1) = b := by ext <;> dsimp at * <;> omega
        have ht := h34d.1; unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
    · rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hb : (6 * (j.val : ℤ) + 5, r) = b := by ext <;> dsimp at * <;> omega
        unfold bucketCell at h5; rw [hb, hbf] at h5; cases h5
      · left; ext <;> dsimp at * <;> omega
      · have hb : (6 * (j.val : ℤ) + 4, r + 1) = b := by ext <;> dsimp at * <;> omega
        have ht := h34u.2; unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
      · have hb : (6 * (j.val : ℤ) + 4, r - 1) = b := by ext <;> dsimp at * <;> omega
        have ht := h34d.2; unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent U) (6 * (j.val : ℤ) + 4, r) v →
      v = (6 * (j.val : ℤ) + 3, r) ∨ v = (6 * (j.val : ℤ) + 4, r) := by
    intro v hp
    induction hp with
    | refl => exact Or.inr rfl
    | tail _ hst ih => exact hstay _ _ ih hst
  rcases hbox z hpath with rfl | rfl <;> (dsimp at hzH; omega)

/-- Column 0 sealed at `y_top` with column 1 occupied on `[0, y_top)`. -/
lemma hasHole_of_col0_seal {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    (j : Fin s') {y₀ y_top : ℤ}
    (hy0 : 0 ≤ y₀) (hylt : y₀ < y_top) (hyH : y_top < (H' : ℤ))
    (hf : bucketCell U j.val 0 y₀ = false)
    (htop : bucketCell U j.val 0 y_top = true)
    (hcol1 : ∀ y : ℤ, 0 ≤ y → y < y_top → bucketCell U j.val 1 y = true) :
    HasHole U j.val H' := by
  refine ⟨0, y₀, by omega, by omega, hy0, by omega, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ a b : Cell,
      (a.1 = 6 * (j.val : ℤ) ∧ 0 ≤ a.2 ∧ a.2 < y_top) →
      EmptyAdjacent U a b →
      (b.1 = 6 * (j.val : ℤ) ∧ 0 ≤ b.2 ∧ b.2 < y_top) := by
    intro a b ha hadj
    rcases hadj with ⟨_, hbf, hdist⟩
    have hstep : (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
        (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
      rcases abs_cases (a.1 - b.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (a.2 - b.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have ht := hcol1 a.2 ha.2.1 ha.2.2
      have hb : (6 * (j.val : ℤ) + 1, a.2) = b := by ext <;> omega
      unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
    · have hw := bucketCell_left_wall_B hframe j (y := a.2) ha.2.1 (by omega)
      have hb : (6 * (j.val : ℤ) + -1, a.2) = b := by ext <;> omega
      unfold bucketCell at hw; rw [hb, hbf] at hw; cases hw
    · by_cases heq : b.2 = y_top
      · have hb : (6 * (j.val : ℤ) + 0, y_top) = b := by ext <;> omega
        unfold bucketCell at htop; rw [hb, hbf] at htop; cases htop
      · omega
    · by_cases hneg : b.2 = -1
      · unfold Board.occupied at hbf
        have : ¬ (0 ≤ b.2 ∧ b.2 < U.height) := by omega
        simp [this] at hbf
      · omega
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent U) (6 * (j.val : ℤ) + 0, y₀) v →
      v.1 = 6 * (j.val : ℤ) ∧ 0 ≤ v.2 ∧ v.2 < y_top := by
    intro v hp
    induction hp with
    | refl => exact ⟨by dsimp; omega, hy0, hylt⟩
    | tail _ hst ih => exact hstay _ _ ih hst
  have := hbox z hpath; omega

/-- Column 2 sealed at `y_top` with columns 1 and 3 occupied on `[0, y_top)`. -/
lemma hasHole_of_col2_seal {U : Board} {s' H' : ℕ} (_hframe : BucketFrame U s' H')
    (j : Fin s') {y₀ y_top : ℤ}
    (hy0 : 0 ≤ y₀) (hylt : y₀ < y_top) (hyH : y_top < (H' : ℤ))
    (hf : bucketCell U j.val 2 y₀ = false)
    (htop : bucketCell U j.val 2 y_top = true)
    (hcol13 : ∀ y : ℤ, 0 ≤ y → y < y_top →
      bucketCell U j.val 1 y = true ∧ bucketCell U j.val 3 y = true) :
    HasHole U j.val H' := by
  refine ⟨2, y₀, by omega, by omega, hy0, by omega, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ a b : Cell,
      (a.1 = 6 * (j.val : ℤ) + 2 ∧ 0 ≤ a.2 ∧ a.2 < y_top) →
      EmptyAdjacent U a b →
      (b.1 = 6 * (j.val : ℤ) + 2 ∧ 0 ≤ b.2 ∧ b.2 < y_top) := by
    intro a b ha hadj
    rcases hadj with ⟨_, hbf, hdist⟩
    have hstep : (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
        (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
      rcases abs_cases (a.1 - b.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (a.2 - b.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have ht := (hcol13 a.2 ha.2.1 ha.2.2).2
      have hb : (6 * (j.val : ℤ) + 3, a.2) = b := by ext <;> omega
      unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
    · have ht := (hcol13 a.2 ha.2.1 ha.2.2).1
      have hb : (6 * (j.val : ℤ) + 1, a.2) = b := by ext <;> omega
      unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
    · by_cases heq : b.2 = y_top
      · have hb : (6 * (j.val : ℤ) + 2, y_top) = b := by ext <;> omega
        unfold bucketCell at htop; rw [hb, hbf] at htop; cases htop
      · omega
    · by_cases hneg : b.2 = -1
      · unfold Board.occupied at hbf
        have : ¬ (0 ≤ b.2 ∧ b.2 < U.height) := by omega
        simp [this] at hbf
      · omega
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent U) (6 * (j.val : ℤ) + 2, y₀) v →
      v.1 = 6 * (j.val : ℤ) + 2 ∧ 0 ≤ v.2 ∧ v.2 < y_top := by
    intro v hp
    induction hp with
    | refl => exact ⟨rfl, hy0, hylt⟩
    | tail _ hst ih => exact hstay _ _ ih hst
  have := hbox z hpath; omega

/-- Generalized col-0 seal above a row `y_low` where cols `1..4` are occupied and col 1 is occupied on `[y_low, y_top)`. -/
lemma hasHole_of_col0_balcony_seal {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    (j : Fin s') {y_low y_top : ℤ}
    (hy0 : 0 ≤ y_low) (hylt : y_low < y_top) (hyH : y_top < (H' : ℤ))
    (hf : bucketCell U j.val 0 (y_top - 1) = false)
    (htop : bucketCell U j.val 0 y_top = true)
    (h1l : bucketCell U j.val 1 y_low = true) (h2l : bucketCell U j.val 2 y_low = true)
    (h3l : bucketCell U j.val 3 y_low = true) (h4l : bucketCell U j.val 4 y_low = true)
    (hcol1 : ∀ y : ℤ, y_low ≤ y → y < y_top → bucketCell U j.val 1 y = true) :
    HasHole U j.val H' := by
  refine ⟨0, y_top - 1, by omega, by omega, by omega, by omega, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ a b : Cell,
      (6 * (j.val : ℤ) ≤ a.1 ∧ a.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ a.2 ∧ a.2 < y_top ∧
        (y_low ≤ a.2 → a.1 = 6 * (j.val : ℤ))) →
      EmptyAdjacent U a b →
      (6 * (j.val : ℤ) ≤ b.1 ∧ b.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ b.2 ∧ b.2 < y_top ∧
        (y_low ≤ b.2 → b.1 = 6 * (j.val : ℤ))) := by
    intro a b ha hadj
    rcases hadj with ⟨_, hbf, hdist⟩
    have hstep : (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
        (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
      rcases abs_cases (a.1 - b.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (a.2 - b.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · by_cases h5 : b.1 = 6 * (j.val : ℤ) + 5
      · have hw := bucketCell_right_wall_B hframe j (y := b.2) (by omega) (by omega)
        have hb : (6 * (j.val : ℤ) + 5, b.2) = b := by ext <;> omega
        unfold bucketCell at hw; rw [hb, hbf] at hw; cases hw
      · refine ⟨by omega, by omega, by omega, by omega, fun hge => ?_⟩
        have ha0 := ha.2.2.2.2 (by omega)
        have ht := hcol1 a.2 (by omega) ha.2.2.2.1
        have hb : (6 * (j.val : ℤ) + 1, a.2) = b := by ext <;> omega
        unfold bucketCell at ht; rw [hb, hbf] at ht; cases ht
    · by_cases hm1 : b.1 = 6 * (j.val : ℤ) - 1
      · have hw := bucketCell_left_wall_B hframe j (y := b.2) (by omega) (by omega)
        have hb : (6 * (j.val : ℤ) + -1, b.2) = b := by ext <;> omega
        unfold bucketCell at hw; rw [hb, hbf] at hw; cases hw
      · refine ⟨by omega, by omega, by omega, by omega, fun hge => ?_⟩
        have ha0 := ha.2.2.2.2 (by omega)
        omega
    · by_cases heq : b.2 = y_top
      · have ha0 := ha.2.2.2.2 (by omega)
        have hb : (6 * (j.val : ℤ) + 0, y_top) = b := by ext <;> omega
        unfold bucketCell at htop; rw [hb, hbf] at htop; cases htop
      · refine ⟨by omega, by omega, by omega, by omega, fun hge => ?_⟩
        by_cases ha_ge : y_low ≤ a.2
        · have := ha.2.2.2.2 ha_ge; omega
        · have hbl : b.2 = y_low := by omega
          have hdx : b.1 - 6 * (j.val : ℤ) = 0 ∨ b.1 - 6 * (j.val : ℤ) = 1 ∨
              b.1 - 6 * (j.val : ℤ) = 2 ∨ b.1 - 6 * (j.val : ℤ) = 3 ∨
              b.1 - 6 * (j.val : ℤ) = 4 := by omega
          rcases hdx with h | h | h | h | h
          · omega
          · have hb : (6 * (j.val : ℤ) + 1, y_low) = b := by ext <;> omega
            unfold bucketCell at h1l; rw [hb, hbf] at h1l; cases h1l
          · have hb : (6 * (j.val : ℤ) + 2, y_low) = b := by ext <;> omega
            unfold bucketCell at h2l; rw [hb, hbf] at h2l; cases h2l
          · have hb : (6 * (j.val : ℤ) + 3, y_low) = b := by ext <;> omega
            unfold bucketCell at h3l; rw [hb, hbf] at h3l; cases h3l
          · have hb : (6 * (j.val : ℤ) + 4, y_low) = b := by ext <;> omega
            unfold bucketCell at h4l; rw [hb, hbf] at h4l; cases h4l
    · by_cases hneg : b.2 = -1
      · unfold Board.occupied at hbf
        have : ¬ (0 ≤ b.2 ∧ b.2 < U.height) := by omega
        simp [this] at hbf
      · refine ⟨by omega, by omega, by omega, by omega, fun hge => ?_⟩
        have := ha.2.2.2.2 (by omega); omega
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent U) (6 * (j.val : ℤ) + 0, y_top - 1) v →
      6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 < y_top ∧
        (y_low ≤ v.2 → v.1 = 6 * (j.val : ℤ)) := by
    intro v hp
    induction hp with
    | refl => exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, fun _ => by dsimp; omega⟩
    | tail _ hst ih => exact hstay _ _ ih hst
  have := hbox z hpath; omega

/-! ### Remaining Section 5.4 Unfillable Configurations -/

/-- `SpurnedNotch` below a `Balcony` is unfillable even under `AnyPlay`. -/
theorem anyPlay_unfillable_of_spurnedNotch_below_balcony {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r b : ℤ} {ib : Fin 3} (hrb : r < b)
    (hopen : OpenNotch B j.val H r) (h1r : bucketCell B j.val 1 r = true)
    (hbal : Balcony B j.val H b ib) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rintro ⟨B', hplay, hfull⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  have hr4 : 4 ≤ r := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hrH : r + 1 < H := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
      bucketCell Bcur j.val 1 r = true → bucketCell Bcur j.val 4 r = false →
      Balcony Bcur j.val H b ib → BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ _ h4f' _ hfull'
      exact not_bucketFull_of_false_B hfull' (by omega) (by omega) (by omega) (by omega) h4f'
    | @step Bcur B' q htraj hrest ih =>
      intro hfr h1r' h4f' hbal' hfull'
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      have hnot4 : (6 * (j.val : ℤ) + 4, r) ∉ q.cells := by
        intro hm4
        by_cases hI : q.kind = .I
        · have h4u := (bucketCell_notch_wall_B hfr j (y := r + 1) (by omega) (by omega)
            (by rcases hopen with ⟨_, _, hm, _, _⟩; omega)).2
          have h4d := (bucketCell_notch_wall_B hfr j (y := r - 1) (by omega) (by omega)
            (by rcases hopen with ⟨_, _, hm, _, _⟩; omega)).2
          have h5 := bucketCell_right_wall_B hfr j (y := r) (by omega) (by omega)
          have hcov := i_notch_cover hI hclear h4u h4d h5 hm4
          have hc := hclear _ hcov.1; unfold bucketCell at h1r'; rw [h1r'] at hc; cases hc
        · have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbal' hbal'.2.1 hI hreach
            (6 * (j.val : ℤ) + 4, r) hm4 (by omega) (by omega) (by omega)
          dsimp at hcond; have := ib.isLt; omega
      rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
      · exact ih (bucketFrame_insert hfr) (bucketCell_insert_of_true h1r')
          (bucketCell_insert_of_not_mem h4f' hnot4) hbal'' hfull'
      · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
          hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) hrb hb0 hb1 hb2
          (bucketCell_insert_of_not_mem h4f' hnot4)
        exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
  exact hgen hplay hframe h1r hopen.2.2.2.2 hbal hfull

/-- `TwoVeranda` in column `col ∈ {0, 1, 2}` with balcony `b ≥ bottom + 2` is unfillable under `AnyPlay`. -/
theorem anyPlay_unfillable_of_twoVeranda_ge2 {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    (col : Fin 3) {bottom b : ℤ} {ib : Fin 3}
    (hbot0 : 0 ≤ bottom) (hb_ge : bottom + 2 ≤ b)
    (hbal : Balcony B j.val H b ib)
    (hbot_s : bucketCell B j.val col.val (bottom - 1) = true)
    (hf0 : bucketCell B j.val col.val bottom = false)
    (hf1 : bucketCell B j.val col.val (bottom + 1) = false)
    (htop_s : bucketCell B j.val col.val (bottom + 2) = true) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rintro ⟨B', hplay, hfull⟩
  have hbH : b < H := hbal.2.1
  have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
      Balcony Bcur j.val H b ib →
      bucketCell Bcur j.val col.val (bottom - 1) = true →
      bucketCell Bcur j.val col.val bottom = false →
      bucketCell Bcur j.val col.val (bottom + 1) = false →
      bucketCell Bcur j.val col.val (bottom + 2) = true →
      BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ _ _ hf0' _ _ hfull'
      exact not_bucketFull_of_false_B hfull' (by omega) (by have := col.isLt; omega)
        hbot0 (by omega) hf0'
    | @step Bcur B' q htraj hrest ih =>
      intro hfr hbal' hbot_s' hf0' hf1' htop_s' hfull'
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      -- Non-`.I` pieces cannot touch `(col, bottom)` or `(col, bottom + 1)`!
      have hnonI_miss : q.kind ≠ .I →
          (6 * (j.val : ℤ) + col.val, bottom) ∉ q.cells ∧
          (6 * (j.val : ℤ) + col.val, bottom + 1) ∉ q.cells := by
        intro hne
        refine ⟨fun hm0 => ?_, fun hm1 => ?_⟩
        · have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbal' hbal'.2.1 hne hreach
            _ hm0 (by omega) (by have := col.isLt; omega) (by omega)
          dsimp at hcond; omega
        · have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbal' hbal'.2.1 hne hreach
            _ hm1 (by omega) (by have := col.isLt; omega) (by omega)
          dsimp at hcond
          rcases hcond.2 with h1 | h2
          · omega
          · have hb_eq : b = bottom + 2 := by omega
            have hcol_eq : col = ib := by ext; omega
            have hbal_f := hbal'.2.2 ib
            simp only [ne_eq, not_true_eq_false, decide_false] at hbal_f
            rw [← hb_eq, hcol_eq] at htop_s'
            rw [hbal_f] at htop_s'; cases htop_s'
      by_cases hhit : (6 * (j.val : ℤ) + col.val, bottom) ∈ q.cells ∨
          (6 * (j.val : ℤ) + col.val, bottom + 1) ∈ q.cells
      · have hI : q.kind = .I := by
          by_contra hne
          rcases hhit with hm0 | hm1
          · exact (hnonI_miss hne).1 hm0
          · exact (hnonI_miss hne).2 hm1
        rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
        · -- Horizontal `.I` at `y₀ ∈ {bottom, bottom + 1}`!
          have hy0_cases : y₀ = bottom ∨ y₀ = bottom + 1 := by
            rcases hhit with hm | hm <;> (
              have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
              rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega)
          -- At row `y₀`, `(3, y₀)` MUST be `false`, so `(y₀ + 1) % 6 = 5`!
          have h3_mem : (6 * (j.val : ℤ) + 3, y₀) ∈ q.cells := by
            have hL := bucketCell_left_wall_B hfr j (y := y₀) (by omega) (by omega)
            have hR := bucketCell_right_wall_B hfr j (y := y₀) (by omega) (by omega)
            have hmem_of : ∀ x : ℤ, x = x₀ ∨ x = x₀ + 1 ∨ x = x₀ + 2 ∨ x = x₀ + 3 → (x, y₀) ∈ q.cells := by
              intro x hx; apply List.mem_toFinset.mp; rw [hfin]
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
              rcases hx with rfl | rfl | rfl | rfl <;> simp
            have hxb : x₀ ≤ 6 * (j.val : ℤ) + col.val ∧ 6 * (j.val : ℤ) + col.val ≤ x₀ + 3 := by
              rcases hhit with hm | hm <;> (
                have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                rcases hm' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
            have hx0_ge : 6 * (j.val : ℤ) ≤ x₀ := by
              by_contra hlt; push Not at hlt
              have hc := hclear _ (hmem_of (6 * (j.val : ℤ) - 1) (by have := col.isLt; omega))
              unfold bucketCell at hL
              have heq : (6 * (j.val : ℤ) + -1, y₀) = (6 * (j.val : ℤ) - 1, y₀) := by ext <;> omega
              rw [heq, hc] at hL; cases hL
            exact hmem_of (6 * (j.val : ℤ) + 3) (by have := col.isLt; omega)
          have hy0_mod : (y₀ + 1) % 6 = 5 := by
            by_contra hnm
            have h3w := (bucketCell_notch_wall_B hfr j (y := y₀) (by omega) (by omega) hnm).1
            have hc := hclear _ h3_mem; unfold bucketCell at h3w; rw [h3w] at hc; cases hc
          rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
          · -- The OTHER cell of `{bottom, bottom + 1}` becomes a 1-veranda in a non-notch row!
            rcases hy0_cases with rfl | rfl
            · have hm0 : (6 * (j.val : ℤ) + col.val, y₀) ∈ q.cells := by
                rcases hhit with hm | hm
                · exact hm
                · have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                  rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              have hno1 : (6 * (j.val : ℤ) + col.val, y₀ + 1) ∉ q.cells := by
                intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              have hbad : BadNonNotchVeranda (Bcur.insert q) j.val H := by
                refine ⟨⟨col.val, by have := col.isLt; omega⟩, y₀ + 1, 1, ?_, by decide,
                  ⟨b, ib, by omega, hbal''⟩, fun y hy1 hy2 => Or.inl (by omega)⟩
                refine ⟨by omega, by omega, by omega, fun y hy1 hy2 => ?_, ?_, ?_⟩
                · have hy_eq : y = y₀ + 1 := by omega
                  rw [hy_eq]; exact bucketCell_insert_of_not_mem hf1' hno1
                · have hy_eq : y₀ + 1 - 1 = y₀ := by omega
                  rw [hy_eq]; exact bucketCell_insert_of_mem hfr (by omega) (by have := col.isLt; omega)
                    (by omega) (by omega) hm0
                · have hy_eq : y₀ + 1 + (1 : ℕ) = y₀ + 2 := by omega
                  rw [hy_eq]; exact bucketCell_insert_of_true htop_s'
              exact anyPlay_unfillable_of_badNonNotchVeranda hReason (bucketFrame_insert hfr) j hbad
                ⟨B', hrest, hfull'⟩
            · have hm1 : (6 * (j.val : ℤ) + col.val, bottom + 1) ∈ q.cells := by
                rcases hhit with hm | hm
                · have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                  rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
                · exact hm
              have hno0 : (6 * (j.val : ℤ) + col.val, bottom) ∉ q.cells := by
                intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              have hbad : BadNonNotchVeranda (Bcur.insert q) j.val H := by
                refine ⟨⟨col.val, by have := col.isLt; omega⟩, bottom, 1, ?_, by decide,
                  ⟨b, ib, by omega, hbal''⟩, fun y hy1 hy2 => Or.inl (by omega)⟩
                refine ⟨by omega, by omega, by omega, fun y hy1 hy2 => ?_, ?_, ?_⟩
                · have hy_eq : y = bottom := by omega
                  rw [hy_eq]; exact bucketCell_insert_of_not_mem hf0' hno0
                · exact bucketCell_insert_of_true hbot_s'
                · exact bucketCell_insert_of_mem hfr (by omega) (by have := col.isLt; omega)
                    (by omega) (by omega) hm1
              exact anyPlay_unfillable_of_badNonNotchVeranda hReason (bucketFrame_insert hfr) j hbad
                ⟨B', hrest, hfull'⟩
          · rcases hy0_cases with rfl | rfl
            · have hno1 : (6 * (j.val : ℤ) + col.val, y₀ + 1) ∉ q.cells := by
                intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                hbal'.1 hbal'.2.1 (by omega) (by have := col.isLt; omega) (by omega) (by omega)
                hb0 hb1 hb2 (bucketCell_insert_of_not_mem hf1' hno1)
              exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
            · have hno0 : (6 * (j.val : ℤ) + col.val, bottom) ∉ q.cells := by
                intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                hbal'.1 hbal'.2.1 (by omega) (by have := col.isLt; omega) hbot0 (by omega)
                hb0 hb1 hb2 (bucketCell_insert_of_not_mem hf0' hno0)
              exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
        · -- Vertical `.I` at `x₀ = 6j + col`: impossible between `bottom - 1` and `bottom + 2`!
          have hx_bounds : x₀ = 6 * (j.val : ℤ) + col.val ∧ y₀ ≤ bottom + 1 ∧ bottom ≤ y₀ + 3 := by
            rcases hhit with hm | hm <;> (
              have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
              rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
          by_cases hy0_low : y₀ ≤ bottom - 1
          · have hm_bot : (6 * (j.val : ℤ) + col.val, bottom - 1) ∈ q.cells := by
              apply List.mem_toFinset.mp; rw [hfin]
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
              omega
            have hc := hclear _ hm_bot; unfold bucketCell at hbot_s'; rw [hbot_s'] at hc; cases hc
          · have hm_top : (6 * (j.val : ℤ) + col.val, bottom + 2) ∈ q.cells := by
              apply List.mem_toFinset.mp; rw [hfin]
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
              omega
            have hc := hclear _ hm_top; unfold bucketCell at htop_s'; rw [htop_s'] at hc; cases hc
      · push Not at hhit
        rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
        · exact ih (bucketFrame_insert hfr) hbal''
            (bucketCell_insert_of_true hbot_s')
            (bucketCell_insert_of_not_mem hf0' hhit.1)
            (bucketCell_insert_of_not_mem hf1' hhit.2)
            (bucketCell_insert_of_true htop_s') hfull'
        · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
            hbal'.1 hbal'.2.1 (by omega) (by have := col.isLt; omega) hbot0 (by omega)
            hb0 hb1 hb2 (bucketCell_insert_of_not_mem hf0' hhit.1)
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
  exact hgen hplay hframe hbal hbot_s hf0 hf1 htop_s hfull

/-- `SubNotchRectangle` with `r + 2 ≤ b` is unfillable under `AnyPlay`. -/
theorem anyPlay_unfillable_of_subNotchRectangle_ge2 {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {r col d b : ℤ} {ib : Fin 3}
    (hcol : col = 1 ∨ col = 2) (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (hrb : r + 2 ≤ b)
    (hopen : OpenNotch B j.val H r)
    (hbal : Balcony B j.val H b ib)
    (hbot : bucketCell B j.val col (r - d - 1) = true)
    (hemp : ∀ z : ℤ, r - d ≤ z → z ≤ r → bucketCell B j.val col z = false) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rintro ⟨B', hplay, hfull⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  have hr4 : 4 ≤ r := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hrH : r + 1 < H := by rcases hopen with ⟨_, _, hm, _, _⟩; omega
  have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
      OpenNotch Bcur j.val H r → Balcony Bcur j.val H b ib →
      bucketCell Bcur j.val col (r - d - 1) = true →
      (∀ z : ℤ, r - d ≤ z → z ≤ r → bucketCell Bcur j.val col z = false) →
      BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ hopen' _ _ _ hfull'
      exact not_bucketFull_of_false_B hfull' (by omega) (by omega) (by omega) (by omega) hopen'.2.2.2.2
    | @step Bcur B' q htraj hrest ih =>
      intro hfr hopen' hbal' hbot' hemp' hfull'
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      have hnonI_below : q.kind ≠ .I → ∀ x y : ℤ, 0 ≤ x → x < 5 → y ≤ r →
          (6 * (j.val : ℤ) + x, y) ∉ q.cells := by
        intro hne x y hx0 hx5 hyr hm
        have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbal' hbal'.2.1 hne hreach
          _ hm (by omega) (by omega) (by omega)
        dsimp at hcond; omega
      by_cases hm4 : (6 * (j.val : ℤ) + 4, r) ∈ q.cells
      · have hI : q.kind = .I := by by_contra hne; exact hnonI_below hne 4 r (by omega) (by omega) le_rfl hm4
        have h4u := (bucketCell_notch_wall_B hfr j (y := r + 1) (by omega) (by omega)
          (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
        have h4d := (bucketCell_notch_wall_B hfr j (y := r - 1) (by omega) (by omega)
          (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
        have h5 := bucketCell_right_wall_B hfr j (y := r) (by omega) (by omega)
        have hcov := i_notch_cover hI hclear h4u h4d h5 hm4
        have hcol_r : (6 * (j.val : ℤ) + col, r) ∈ q.cells := by
          rcases hcol with rfl | rfl
          · exact hcov.1
          · exact hcov.2.1
        have hno_below : ∀ z : ℤ, r - d ≤ z → z < r → (6 * (j.val : ℤ) + col, z) ∉ q.cells := by
          intro z _ hzr hm
          rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
          · have h1 := List.mem_toFinset.mpr hm4; rw [hfin] at h1
            have h2 := List.mem_toFinset.mpr hm; rw [hfin] at h2
            simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
            rcases h1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ | ⟨_, hy1⟩ | ⟨_, hy1⟩ <;>
              rcases h2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ | ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
          · have h1 := List.mem_toFinset.mpr hm4; rw [hfin] at h1
            have h2 := List.mem_toFinset.mpr hm; rw [hfin] at h2
            simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
            rcases h1 with ⟨hx1, _⟩ | ⟨hx1, _⟩ | ⟨hx1, _⟩ | ⟨hx1, _⟩ <;>
              rcases h2 with ⟨hx2, _⟩ | ⟨hx2, _⟩ | ⟨hx2, _⟩ | ⟨hx2, _⟩ <;> omega
        rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
        · have hbad : BadNonNotchVeranda (Bcur.insert q) j.val H := by
            refine ⟨⟨col.toNat, by omega⟩, r - d, d.toNat, ?_, by omega,
              ⟨b, ib, by omega, hbal''⟩, fun y hy1 hy2 => Or.inl ?_⟩
            · refine ⟨by omega, by omega, by omega, fun y hy1 hy2 => ?_, ?_, ?_⟩
              · have hc_eq : ((col.toNat : ℕ) : ℤ) = col := by omega
                rw [hc_eq]
                exact bucketCell_insert_of_not_mem (hemp' y hy1 (by omega)) (hno_below y hy1 (by omega))
              · have hc_eq : ((col.toNat : ℕ) : ℤ) = col := by omega
                rw [hc_eq]; exact bucketCell_insert_of_true hbot'
              · have hc_eq : ((col.toNat : ℕ) : ℤ) = col := by omega
                have hy_eq : r - d + (d.toNat : ℤ) = r := by omega
                rw [hc_eq, hy_eq]
                exact bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hcol_r
            · have hrmod := hopen'.2.2.1; omega
          exact anyPlay_unfillable_of_badNonNotchVeranda hReason (bucketFrame_insert hfr) j hbad
            ⟨B', hrest, hfull'⟩
        · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
            hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega)
            hb0 hb1 hb2 (bucketCell_insert_of_not_mem (hemp' (r - 1) (by omega) (by omega))
              (hno_below (r - 1) (by omega) (by omega)))
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
      · by_cases hm3 : (6 * (j.val : ℤ) + 3, r) ∈ q.cells
        · have h4u := (bucketCell_notch_wall_B hfr j (y := r + 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
          have h4d := (bucketCell_notch_wall_B hfr j (y := r - 1) (by omega) (by omega)
            (by rcases hopen' with ⟨_, _, hm, _, _⟩; omega)).2
          have h5 := bucketCell_right_wall_B hfr j (y := r) (by omega) (by omega)
          have hhole := hasHole_of_surrounded_B (B := Bcur.insert q) (j := j.val) (H := H) (x := 4) (y := r)
            (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_not_mem hopen'.2.2.2.2 hm4)
            (bucketCell_insert_of_true h5)
            (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm3)
            (bucketCell_insert_of_true h4u)
            (bucketCell_insert_of_true h4d)
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
        · have hopen'' : OpenNotch (Bcur.insert q) j.val H r :=
            ⟨hopen'.1, hopen'.2.1, hopen'.2.2.1,
              bucketCell_insert_of_not_mem hopen'.2.2.2.1 hm3,
              bucketCell_insert_of_not_mem hopen'.2.2.2.2 hm4⟩
          by_cases hhit_col : ∃ z : ℤ, r - d ≤ z ∧ z ≤ r ∧ (6 * (j.val : ℤ) + col, z) ∈ q.cells
          · rcases hhit_col with ⟨z₀, hz1, hz2, hmz⟩
            have hI : q.kind = .I := by by_contra hne; exact hnonI_below hne col z₀ (by omega) (by omega) hz2 hmz
            rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
            · -- Horizontal `.I` at `y₀ = z₀`: hits `x = -1` or `x = 3`!
              exfalso
              have hm' := List.mem_toFinset.mpr hmz; rw [hfin] at hm'
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
              have hy0_eq : y₀ = z₀ := by rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              have hxb : x₀ ≤ 6 * (j.val : ℤ) + col ∧ 6 * (j.val : ℤ) + col ≤ x₀ + 3 := by
                rcases hm' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
              have hmem_of : ∀ x : ℤ, x = x₀ ∨ x = x₀ + 1 ∨ x = x₀ + 2 ∨ x = x₀ + 3 → (x, y₀) ∈ q.cells := by
                intro x hx; apply List.mem_toFinset.mp; rw [hfin]
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                rcases hx with rfl | rfl | rfl | rfl <;> simp
              have hL := bucketCell_left_wall_B hfr j (y := y₀) (by omega) (by omega)
              have hx0_ge : 6 * (j.val : ℤ) ≤ x₀ := by
                by_contra hlt; push Not at hlt
                have hc := hclear _ (hmem_of (6 * (j.val : ℤ) - 1) (by omega))
                unfold bucketCell at hL
                have heq : (6 * (j.val : ℤ) + -1, y₀) = (6 * (j.val : ℤ) - 1, y₀) := by ext <;> omega
                rw [heq, hc] at hL; cases hL
              have h3m : (6 * (j.val : ℤ) + 3, y₀) ∈ q.cells := hmem_of (6 * (j.val : ℤ) + 3) (by omega)
              by_cases hyr : y₀ = r
              · rw [hyr] at h3m; exact hm3 h3m
              · have h3w := (bucketCell_notch_wall_B hfr j (y := y₀) (by omega) (by omega)
                  (by have := hopen'.2.2.1; omega)).1
                have hc := hclear _ h3m; unfold bucketCell at h3w; rw [h3w] at hc; cases hc
            · -- Vertical `.I` at `x₀ = 6j + col`: must contain `(6j + col, r)`!
              have hm' := List.mem_toFinset.mpr hmz; rw [hfin] at hm'
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
              have hx0_eq : x₀ = 6 * (j.val : ℤ) + col := by
                rcases hm' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
              have hy0_ge : r - d ≤ y₀ := by
                by_contra hlt; push Not at hlt
                have hm_bot : (6 * (j.val : ℤ) + col, r - d - 1) ∈ q.cells := by
                  apply List.mem_toFinset.mp; rw [hfin]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
                have hc := hclear _ hm_bot; unfold bucketCell at hbot'; rw [hbot'] at hc; cases hc
              have hm_r : (6 * (j.val : ℤ) + col, r) ∈ q.cells := by
                apply List.mem_toFinset.mp; rw [hfin]
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                rcases hm' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
              rcases hcol with rfl | rfl
              · rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
                · exact anyPlay_unfillable_of_spurnedNotch_below_balcony hReason (bucketFrame_insert hfr) j
                    (by omega) hopen''
                    (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm_r)
                    hbal'' ⟨B', hrest, hfull'⟩
                · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                    hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega)
                    hb0 hb1 hb2 hopen''.2.2.2.2
                  exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
              · have hhole := hasHole_of_blocked_notch (bucketFrame_insert hfr) j (by omega) hrH hopen'.2.2.1
                  (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm_r)
                  hopen''.2.2.2.2
                exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
          · push Not at hhit_col
            rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
            · exact ih (bucketFrame_insert hfr) hopen'' hbal''
                (bucketCell_insert_of_true hbot')
                (fun z hz1 hz2 => bucketCell_insert_of_not_mem (hemp' z hz1 hz2) (hhit_col z hz1 hz2))
                hfull'
            · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega)
                hb0 hb1 hb2 hopen''.2.2.2.2
              exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
  exact hgen hplay hframe hopen hbal hbot hemp hfull

/-- Six empty cells `[h, h + 6)` in col 1 above `(1, h - 1) = true` with notch `h` filled and
`OpenNotch` at `h + 6` below balcony `b ≥ h + 8` is unfillable under `AnyPlay` (Prop C.11 for `a₂ ≥ 2`). -/
theorem anyPlay_unfillable_of_sixBelowOpenNotch {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {h b : ℤ} {ib : Fin 3}
    (hh0 : 0 ≤ h) (hhmod : (h + 1) % 6 = 5)
    (hb_ge : h + 8 ≤ b)
    (hopen : OpenNotch B j.val H (h + 6))
    (hbal : Balcony B j.val H b ib)
    (h1bot : bucketCell B j.val 1 (h - 1) = true)
    (h3h : bucketCell B j.val 3 h = true)
    (hemp : ∀ k : ℕ, k < 6 → bucketCell B j.val 1 (h + (k : ℤ)) = false) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  rintro ⟨B', hplay, hfull⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  have hrH : h + 7 < H := by rcases hopen with ⟨_, _, _, _, _⟩; omega
  have hcnt0 : verandaEmptyCount B j.val 1 h 6 % 4 ≠ 0 := by
    have hall : verandaEmptyCount B j.val 1 h 6 = 6 := by
      unfold verandaEmptyCount
      have hf : ((Finset.range 6).filter fun k : ℕ => bucketCell B j.val 1 (h + (k : ℤ)) = false) =
          Finset.range 6 := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
        exact hemp k
      rw [hf, Finset.card_range]
    rw [hall]; decide
  have hgen : ∀ {Bcur B' : Board}, AnyPlay R Bcur B' → BucketFrame Bcur s H →
      Balcony Bcur j.val H b ib →
      bucketCell Bcur j.val 1 (h - 1) = true →
      bucketCell Bcur j.val 3 h = true →
      (OpenNotch Bcur j.val H (h + 6) ∨ bucketCell Bcur j.val 1 (h + 6) = true) →
      verandaEmptyCount Bcur j.val 1 h 6 % 4 ≠ 0 →
      BucketFull B' j.val H → False := by
    intro Bcur B' hp
    induction hp with
    | nil Bcur =>
      intro _ _ _ _ _ hcnt hfull'
      have hpos : 0 < verandaEmptyCount Bcur j.val 1 h 6 := by omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact not_bucketFull_of_false_B hfull' (by omega) (by omega) (by omega) (by omega) hk.2
    | @step Bcur B' q htraj hrest ih =>
      intro hfr hbal' h1bot' h3h' htop_or hcnt hfull'
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      have hnonI_below : q.kind ≠ .I → ∀ x y : ℤ, 0 ≤ x → x < 5 → y ≤ h + 6 →
          (6 * (j.val : ℤ) + x, y) ∉ q.cells := by
        intro hne x y _ _ _ hm
        have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbal' hbal'.2.1 hne hreach
          _ hm (by omega) (by omega) (by omega)
        dsimp at hcond; omega
      -- Check if `q` touches `(4, h + 6)` or `(3, h + 6)` when `OpenNotch` holds
      by_cases hm4 : (6 * (j.val : ℤ) + 4, h + 6) ∈ q.cells ∧ OpenNotch Bcur j.val H (h + 6)
      · rcases hm4 with ⟨hm4_in, hopen'⟩
        have hI : q.kind = .I := by by_contra hne; exact hnonI_below hne 4 (h + 6) (by omega) (by omega) le_rfl hm4_in
        have h4u := (bucketCell_notch_wall_B hfr j (y := h + 6 + 1) (by omega) (by omega) (by omega)).2
        have h4d := (bucketCell_notch_wall_B hfr j (y := h + 6 - 1) (by omega) (by omega) (by omega)).2
        have h5 := bucketCell_right_wall_B hfr j (y := h + 6) (by omega) (by omega)
        have hcov := i_notch_cover hI hclear h4u h4d h5 hm4_in
        have hsame : verandaEmptyCount (Bcur.insert q) j.val 1 h 6 = verandaEmptyCount Bcur j.val 1 h 6 := by
          unfold verandaEmptyCount; congr 1; ext k
          simp only [Finset.mem_filter, Finset.mem_range]
          refine and_congr_right fun hk => ?_
          constructor
          · intro hf; cases hB : bucketCell Bcur j.val 1 (h + k) with
            | false => rfl
            | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
          · intro hf; apply bucketCell_insert_of_not_mem hf
            intro hm
            rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
            · have h1 := List.mem_toFinset.mpr hm4_in; rw [hfin] at h1
              have h2 := List.mem_toFinset.mpr hm; rw [hfin] at h2
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
              rcases h1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ | ⟨_, hy1⟩ | ⟨_, hy1⟩ <;>
                rcases h2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ | ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
            · have h1 := List.mem_toFinset.mpr hm4_in; rw [hfin] at h1
              have h2 := List.mem_toFinset.mpr hm; rw [hfin] at h2
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
              rcases h1 with ⟨hx1, _⟩ | ⟨hx1, _⟩ | ⟨hx1, _⟩ | ⟨hx1, _⟩ <;>
                rcases h2 with ⟨hx2, _⟩ | ⟨hx2, _⟩ | ⟨hx2, _⟩ | ⟨hx2, _⟩ <;> omega
        rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
        · exact ih (bucketFrame_insert hfr) hbal''
            (bucketCell_insert_of_true h1bot') (bucketCell_insert_of_true h3h')
            (Or.inr (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hcov.1))
            (by rwa [hsame]) hfull'
        · have hpos : 0 < verandaEmptyCount (Bcur.insert q) j.val 1 h 6 := by omega
          obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
          rw [Finset.mem_filter, Finset.mem_range] at hk
          have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
            hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega) hb0 hb1 hb2 hk.2
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
      · by_cases hm3 : (6 * (j.val : ℤ) + 3, h + 6) ∈ q.cells ∧ OpenNotch Bcur j.val H (h + 6)
        · rcases hm3 with ⟨hm3_in, hopen'⟩
          have hnot4 : (6 * (j.val : ℤ) + 4, h + 6) ∉ q.cells := fun h4 => hm4 ⟨h4, hopen'⟩
          have h4u := (bucketCell_notch_wall_B hfr j (y := h + 6 + 1) (by omega) (by omega) (by omega)).2
          have h4d := (bucketCell_notch_wall_B hfr j (y := h + 6 - 1) (by omega) (by omega) (by omega)).2
          have h5 := bucketCell_right_wall_B hfr j (y := h + 6) (by omega) (by omega)
          have hhole := hasHole_of_surrounded_B (B := Bcur.insert q) (j := j.val) (H := H) (x := 4) (y := h + 6)
            (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_not_mem hopen'.2.2.2.2 hnot4)
            (bucketCell_insert_of_true h5)
            (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm3_in)
            (bucketCell_insert_of_true h4u)
            (bucketCell_insert_of_true h4d)
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
        · have htop_or' : OpenNotch (Bcur.insert q) j.val H (h + 6) ∨
              bucketCell (Bcur.insert q) j.val 1 (h + 6) = true := by
            rcases htop_or with hopen' | h1t
            · left
              exact ⟨hopen'.1, hopen'.2.1, hopen'.2.2.1,
                bucketCell_insert_of_not_mem hopen'.2.2.2.1 (fun h3 => hm3 ⟨h3, hopen'⟩),
                bucketCell_insert_of_not_mem hopen'.2.2.2.2 (fun h4 => hm4 ⟨h4, hopen'⟩)⟩
            · exact Or.inr (bucketCell_insert_of_true h1t)
          by_cases hhit : ∃ (k : ℕ), k < 6 ∧ (6 * (j.val : ℤ) + 1, h + (k : ℤ)) ∈ q.cells
          · rcases hhit with ⟨k0, hk0, hmk0⟩
            have hI : q.kind = .I := by
              by_contra hne; exact hnonI_below hne 1 (h + k0) (by omega) (by omega) (by omega) hmk0
            rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
            · -- Horizontal `.I` at `y₀ = h + k0`: hits `x = -1` or `(3, y₀) = true`!
              exfalso
              have hm' := List.mem_toFinset.mpr hmk0; rw [hfin] at hm'
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
              have hy0_eq : y₀ = h + k0 := by rcases hm' with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ <;> omega
              have hxb : x₀ ≤ 6 * (j.val : ℤ) + 1 ∧ 6 * (j.val : ℤ) + 1 ≤ x₀ + 3 := by
                rcases hm' with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ <;> omega
              have hmem_of : ∀ x : ℤ, x = x₀ ∨ x = x₀ + 1 ∨ x = x₀ + 2 ∨ x = x₀ + 3 → (x, y₀) ∈ q.cells := by
                intro x hx; apply List.mem_toFinset.mp; rw [hfin]
                simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                rcases hx with rfl | rfl | rfl | rfl <;> simp
              have hL := bucketCell_left_wall_B hfr j (y := y₀) (by omega) (by omega)
              have hx0_ge : 6 * (j.val : ℤ) ≤ x₀ := by
                by_contra hlt; push Not at hlt
                have hc := hclear _ (hmem_of (6 * (j.val : ℤ) - 1) (by omega))
                unfold bucketCell at hL
                have heq : (6 * (j.val : ℤ) + -1, y₀) = (6 * (j.val : ℤ) - 1, y₀) := by ext <;> omega
                rw [heq, hc] at hL; cases hL
              have h3m : (6 * (j.val : ℤ) + 3, y₀) ∈ q.cells := hmem_of (6 * (j.val : ℤ) + 3) (by omega)
              have h3occ : bucketCell Bcur j.val 3 y₀ = true := by
                by_cases hk_zero : k0 = 0
                · have : y₀ = h := by omega
                  rwa [this]
                · exact (bucketCell_notch_wall_B hfr j (y := y₀) (by omega) (by omega) (by omega)).1
              have hc := hclear _ h3m; unfold bucketCell at h3occ; rw [h3occ] at hc; cases hc
            · -- Vertical `.I` at `x₀ = 6j + 1`!
              have hm' := List.mem_toFinset.mpr hmk0; rw [hfin] at hm'
              simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
              have hx0_eq : x₀ = 6 * (j.val : ℤ) + 1 := by
                rcases hm' with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ <;> omega
              have hy0_ge : h ≤ y₀ := by
                by_contra hlt; push Not at hlt
                have hm_bot : (6 * (j.val : ℤ) + 1, h - 1) ∈ q.cells := by
                  apply List.mem_toFinset.mp; rw [hfin]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  rcases hm' with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ <;> omega
                have hc := hclear _ hm_bot; unfold bucketCell at h1bot'; rw [h1bot'] at hc; cases hc
              by_cases hy0_in : y₀ + 3 < h + 6
              · set d : ℕ := (y₀ - h).toNat
                set S4 : Finset ℕ := {d, d + 1, d + 2, d + 3}
                have hS4_card : S4.card = 4 := by
                  simp only [S4]
                  rw [Finset.card_insert_of_notMem (by simp),
                    Finset.card_insert_of_notMem (by simp),
                    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
                set E0 := (Finset.range 6).filter fun k : ℕ => bucketCell Bcur j.val 1 (h + (k : ℤ)) = false
                set E1 := (Finset.range 6).filter fun k : ℕ => bucketCell (Bcur.insert q) j.val 1 (h + (k : ℤ)) = false
                have hmem_q : ∀ k : ℕ, (6 * (j.val : ℤ) + 1, h + k) ∈ q.cells ↔ k ∈ S4 := by
                  intro k; rw [← List.mem_toFinset, hfin]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, S4]; omega
                have hS4_sub : S4 ⊆ E0 := by
                  intro k hk; rw [Finset.mem_filter, Finset.mem_range]
                  have hmq := (hmem_q k).mpr hk
                  have hk_lt : k < 6 := by simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hk; omega
                  exact ⟨hk_lt, hclear _ hmq⟩
                have hE1_eq : E1 = E0 \ S4 := by
                  ext k; simp only [E1, E0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
                  constructor
                  · intro ⟨hk, hf⟩
                    have hf0 : bucketCell Bcur j.val 1 (h + k) = false := by
                      cases hB : bucketCell Bcur j.val 1 (h + k) with
                      | false => rfl
                      | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
                    refine ⟨⟨hk, hf0⟩, fun hk4 => ?_⟩
                    have ht := bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega)
                      ((hmem_q k).mpr hk4)
                    rw [ht] at hf; cases hf
                  · rintro ⟨⟨hk, hf0⟩, hnot4⟩
                    exact ⟨hk, bucketCell_insert_of_not_mem hf0 (mt (hmem_q k).mp hnot4)⟩
                have hcard : E1.card + 4 = E0.card := by
                  rw [hE1_eq, ← hS4_card, Finset.card_sdiff_add_card_eq_card hS4_sub]
                have hcnt' : verandaEmptyCount (Bcur.insert q) j.val 1 h 6 % 4 ≠ 0 := by
                  change E1.card % 4 ≠ 0; change E0.card % 4 ≠ 0 at hcnt; omega
                rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
                · exact ih (bucketFrame_insert hfr) hbal''
                    (bucketCell_insert_of_true h1bot') (bucketCell_insert_of_true h3h')
                    htop_or' hcnt' hfull'
                · have hpos : 0 < verandaEmptyCount (Bcur.insert q) j.val 1 h 6 := by omega
                  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
                  rw [Finset.mem_filter, Finset.mem_range] at hk
                  have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                    hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega) hb0 hb1 hb2 hk.2
                  exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
              · -- `y₀ + 3 ≥ h + 6`: contains `(6j + 1, h + 6)`!
                have hm_top : (6 * (j.val : ℤ) + 1, h + 6) ∈ q.cells := by
                  apply List.mem_toFinset.mp; rw [hfin]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  rcases hm' with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ <;> omega
                rcases htop_or with hopen' | h1t
                · have hopen'' : OpenNotch (Bcur.insert q) j.val H (h + 6) :=
                    ⟨hopen'.1, hopen'.2.1, hopen'.2.2.1,
                      bucketCell_insert_of_not_mem hopen'.2.2.2.1 (fun h3 => hm3 ⟨h3, hopen'⟩),
                      bucketCell_insert_of_not_mem hopen'.2.2.2.2 (fun h4 => hm4 ⟨h4, hopen'⟩)⟩
                  rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
                  · exact anyPlay_unfillable_of_spurnedNotch_below_balcony hReason (bucketFrame_insert hfr) j
                      (by omega) hopen''
                      (bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hm_top)
                      hbal'' ⟨B', hrest, hfull'⟩
                  · have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                      hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega)
                      hb0 hb1 hb2 hopen''.2.2.2.2
                    exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
                · have hc := hclear _ hm_top; unfold bucketCell at h1t; rw [h1t] at hc; cases hc
          · push Not at hhit
            have hsame : verandaEmptyCount (Bcur.insert q) j.val 1 h 6 = verandaEmptyCount Bcur j.val 1 h 6 := by
              unfold verandaEmptyCount; congr 1; ext k
              simp only [Finset.mem_filter, Finset.mem_range]
              refine and_congr_right fun hk => ?_
              constructor
              · intro hf; cases hB : bucketCell Bcur j.val 1 (h + k) with
                | false => rfl
                | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
              · intro hf; exact bucketCell_insert_of_not_mem hf (hhit k hk)
            rcases balcony_insert (q := q) hbal' with hbal'' | ⟨hb0, hb1, hb2⟩
            · exact ih (bucketFrame_insert hfr) hbal''
                (bucketCell_insert_of_true h1bot') (bucketCell_insert_of_true h3h')
                htop_or' (by rwa [hsame]) hfull'
            · have hpos : 0 < verandaEmptyCount (Bcur.insert q) j.val 1 h 6 := by omega
              obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
              rw [Finset.mem_filter, Finset.mem_range] at hk
              have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
                hbal'.1 hbal'.2.1 (by omega) (by omega) (by omega) (by omega) hb0 hb1 hb2 hk.2
              exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull'⟩
  exact hgen hplay hframe hbal h1bot h3h (Or.inl hopen) hcnt0 hfull


private def shiftedC (t : Piece) (o : Fin 4) (u : Cell) : List Cell :=
  (offsetsC t o).map fun v => (v.1 - u.1, v.2 - u.2)

private lemma mem_cells_iff_C {q : PieceState} {z : Cell} :
    z ∈ q.cells ↔ ∃ u ∈ offsetsC q.kind q.orientation,
      z = (q.position.1 + u.1, q.position.2 + u.2) := by
  rw [piece_cells_eq_map_offsetsC, List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

private lemma shiftedC_mem_cells {q : PieceState} {z₀ u d : Cell}
    (hz₀ : z₀ = (q.position.1 + u.1, q.position.2 + u.2))
    (hd : d ∈ shiftedC q.kind q.orientation u) :
    (z₀.1 + d.1, z₀.2 + d.2) ∈ q.cells := by
  rcases List.mem_map.mp hd with ⟨v, hv, rfl⟩
  rw [mem_cells_iff_C]
  refine ⟨v, hv, ?_⟩
  rcases hz₀ with rfl; ext <;> dsimp <;> omega

private lemma mem_shiftedC_of_mem_cells {q : PieceState} {z₀ u : Cell} (dx dy : ℤ)
    (hz₀ : z₀ = (q.position.1 + u.1, q.position.2 + u.2))
    (hm : (z₀.1 + dx, z₀.2 + dy) ∈ q.cells) :
    (dx, dy) ∈ shiftedC q.kind q.orientation u := by
  rcases mem_cells_iff_C.mp hm with ⟨v, hv, heq⟩
  refine List.mem_map.mpr ⟨v, hv, ?_⟩
  rcases hz₀ with rfl
  simp only [Prod.mk.injEq] at heq; ext <;> dsimp <;> omega

private lemma geom_G2_C_aux (t : Piece) (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (o : Fin 4) :
    ∀ u ∈ offsetsC t o,
      (0, 1) ∈ shiftedC t o u ∨ (0, -1) ∈ shiftedC t o u ∨
      (1, 0) ∈ shiftedC t o u ∨ (-1, 1) ∈ shiftedC t o u ∨ (-1, -1) ∈ shiftedC t o u ∨
      (((!decide ((-2, -1) ∈ shiftedC t o u)) = true ∧ (!decide ((-4, -2) ∈ shiftedC t o u)) = true) ∧
       ((t = .I ∧ (-3, 0) ∈ shiftedC t o u ∧ (-2, 0) ∈ shiftedC t o u ∧ (-1, 0) ∈ shiftedC t o u) ∨
        (t = .LG ∧ (-2, 0) ∈ shiftedC t o u ∧ (-1, 0) ∈ shiftedC t o u ∧ (-2, 1) ∈ shiftedC t o u))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> fin_cases o <;> decide

lemma geom_G2_C {B : Board} {j : ℕ} {r : ℤ} {q : PieceState}
    (hk : q.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece)) (hclear : B.Clear q)
    (h4u : bucketCell B j 4 (r + 1) = true) (h4d : bucketCell B j 4 (r - 1) = true)
    (h5 : bucketCell B j 5 r = true)
    (h3u : bucketCell B j 3 (r + 1) = true) (h3d : bucketCell B j 3 (r - 1) = true)
    (hmem : (6 * (j : ℤ) + 4, r) ∈ q.cells) :
    ((6 * (j : ℤ) + 2, r - 1) ∉ q.cells ∧ (6 * (j : ℤ) + 0, r - 2) ∉ q.cells) ∧
    ((q.kind = .I ∧ (6 * (j : ℤ) + 1, r) ∈ q.cells ∧ (6 * (j : ℤ) + 2, r) ∈ q.cells ∧
        (6 * (j : ℤ) + 3, r) ∈ q.cells) ∨
     (q.kind = .LG ∧ (6 * (j : ℤ) + 2, r) ∈ q.cells ∧ (6 * (j : ℤ) + 3, r) ∈ q.cells ∧
        (6 * (j : ℤ) + 2, r + 1) ∈ q.cells)) := by
  rcases mem_cells_iff_C.mp hmem with ⟨u, hu, heq⟩
  have hnot : ∀ d : Cell, B.occupied (6 * (j : ℤ) + 4 + d.1, r + d.2) = true →
      d ∉ shiftedC q.kind q.orientation u := by
    intro d hocc hd
    have hc := hclear _ (shiftedC_mem_cells heq hd)
    dsimp at hc; rw [hocc] at hc; cases hc
  rcases geom_G2_C_aux q.kind hk q.orientation u hu with h | h | h | h | h | ⟨⟨hn1, hn2⟩, hres⟩
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
    · intro hm; apply hn1; apply mem_shiftedC_of_mem_cells (-2) (-1) heq
      convert hm using 1; ext <;> omega
    · intro hm; apply hn2; apply mem_shiftedC_of_mem_cells (-4) (-2) heq
      convert hm using 1; ext <;> omega
    · rcases hres with ⟨hI, h1, h2, h3⟩ | ⟨hL, h2, h3, h2u⟩
      · left
        exact ⟨hI,
          by convert shiftedC_mem_cells heq h1 using 1; ext <;> omega,
          by convert shiftedC_mem_cells heq h2 using 1; ext <;> omega,
          by convert shiftedC_mem_cells heq h3 using 1; ext <;> omega⟩
      · right
        exact ⟨hL,
          by convert shiftedC_mem_cells heq h2 using 1; ext <;> omega,
          by convert shiftedC_mem_cells heq h3 using 1; ext <;> omega,
          by convert shiftedC_mem_cells heq h2u using 1; ext <;> omega⟩


/-! ### Convenience `FillableStrict` Unfillability Wrappers -/

lemma not_fillableStrict_of_hasHole {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hhole : HasHole U j.val H') :
    ¬ FillableStrict R s s' H' U j :=
  not_fillableStrict_of_anyPlay
    (anyPlay_unfillable_of_hasHole hReason hframe ⟨j.val, by omega⟩ hhole)

lemma not_fillableStrict_of_spurnedNotch {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hsp : SpurnedNotch U j.val H') :
    ¬ FillableStrict R s s' H' U j :=
  not_fillableStrict_of_anyPlayNoRG
    (noRG_unfillable_of_spurnedNotch hReason hframe ⟨j.val, by omega⟩ hsp)

lemma not_fillableStrict_of_flooredNotch {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hfn : FlooredNotch U j.val H') :
    ¬ FillableStrict R s s' H' U j :=
  not_fillableStrict_of_anyPlay
    (anyPlay_unfillable_of_flooredNotch hReason hframe ⟨j.val, by omega⟩ hfn)

lemma not_fillableStrict_of_badNonNotchVeranda {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hbad : BadNonNotchVeranda U j.val H') :
    ¬ FillableStrict R s s' H' U j :=
  not_fillableStrict_of_anyPlay
    (anyPlay_unfillable_of_badNonNotchVeranda hReason hframe ⟨j.val, by omega⟩ hbad)

/-! ### `BucketPattern` Calculus & Parameterized Bucket Shapes -/

lemma bucketPattern_eval {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {x y : ℤ} (hx0 : 0 ≤ x) (hx6 : x < 6) (hy0 : 0 ≤ y) (hyH : y < (H' : ℤ)) :
    bucketCell U j x y =
      ((decide (x = 5 ∨ (3 ≤ x ∧ (y + 1) % 6 ≠ 5))) || pat x.toNat y.toNat) := by
  have hyB : y.toNat < U.height := by have := hframe.2.2.1; omega
  have hxF : x.toNat < 6 := by omega
  have h := hpat ⟨x.toNat, hxF⟩ ⟨y.toNat, hyB⟩
  have hxc : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
  have hyc : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
  have hylt : y.toNat < H' := by omega
  have hmod : ((y.toNat + 1) % 6 ≠ 5) ↔ ((y + 1) % 6 ≠ 5) := by omega
  have hx5 : (x.toNat = 5) ↔ (x = 5) := by omega
  have hx3 : (3 ≤ x.toNat) ↔ (3 ≤ x) := by omega
  dsimp only at h
  rw [hxc, hyc] at h
  rw [h]
  congr 2
  simp [hylt, hx5, hx3, hmod]

lemma bucketPattern_eval_012 {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {x y : ℤ} (hx0 : 0 ≤ x) (hx3 : x < 3) (hy0 : 0 ≤ y) (hyB : y < (H' : ℤ) + 3) :
    bucketCell U j x y = pat x.toNat y.toNat := by
  have hyU : y.toNat < U.height := by have := hframe.2.2.1; omega
  have hxF : x.toNat < 6 := by omega
  have h := hpat ⟨x.toNat, hxF⟩ ⟨y.toNat, hyU⟩
  have hxc : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
  have hyc : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
  dsimp only at h
  rw [hxc, hyc] at h
  rw [h]
  have hnw : ¬ (y.toNat < H' ∧ (x.toNat = 5 ∨ 3 ≤ x.toNat ∧ (y.toNat + 1) % 6 ≠ 5)) := by omega
  simp [hnw]

lemma bucketPattern_eval_neg_y {U : Board} {j : ℕ} {x y : ℤ} (hy : y < 0) :
    bucketCell U j x y = true := by
  unfold bucketCell Board.occupied
  have h : ¬ (0 ≤ y ∧ y < U.height) := by omega
  simp [h]

lemma bucketPattern_congr {U : Board} {j H' : ℕ} {pat1 pat2 : ℕ → ℕ → Bool}
    (hpat : BucketPattern U j H' pat1)
    (heq : ∀ x y : ℕ, x < 6 → y < U.height → pat1 x y = pat2 x y) :
    BucketPattern U j H' pat2 := by
  intro x y
  rw [hpat x y, heq x.val y.val x.isLt y.isLt]

lemma bucketPattern_insert_same {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : Fin s'} {u : PieceState} {pat : ℕ → ℕ → Bool}
    (_hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (hpat : BucketPattern U j.val H' pat) :
    BucketPattern (U.insert u) j.val H'
      (fun x y => pat x y || decide ((6 * (j.val : ℤ) + (x : ℤ), (y : ℤ)) ∈ u.cells)) := by
  intro x y
  by_cases hmem : (6 * (j.val : ℤ) + (x.val : ℤ), (y.val : ℤ)) ∈ u.cells
  · have hyH : y.val < H' := by have := (hy_u _ hmem).2; omega
    have ht := bucketCell_insert_of_mem hframe (j := j) (x := x.val) (y := y.val)
      (by omega) (by have := x.isLt; omega) (by omega) (by omega) hmem
    rw [ht]; simp [hmem]
  · have hcelleq : bucketCell (U.insert u) j.val x.val y.val = bucketCell U j.val x.val y.val := by
      cases hB : bucketCell U j.val x.val y.val with
      | true => exact bucketCell_insert_of_true hB
      | false => exact bucketCell_insert_of_not_mem hB hmem
    rw [hcelleq, hpat x y]
    simp [hmem]

lemma bucketPattern_insert_other {U : Board} {H' j k : ℕ} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j u) {pat : ℕ → ℕ → Bool}
    (hpat : BucketPattern U k H' pat) :
    BucketPattern (U.insert u) k H' pat := by
  intro x y
  rw [bucketCell_insert_other_bucket hne hin (by omega) (by have := x.isLt; omega)]
  exact hpat x y



lemma openNotch_margins {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {r : ℤ} (hr0 : 0 ≤ r) (hrH : r < (H' : ℤ)) (hmod : (r + 1) % 6 = 5) :
    4 ≤ r ∧ r + 6 ≤ (H' : ℤ) := by
  rcases hframe.2.1 with ⟨T, hHT⟩
  omega

private lemma offsetsC_diam :
    ∀ t : Piece, ∀ o : Fin 4, ∀ u ∈ offsetsC t o, ∀ v ∈ offsetsC t o,
      |u.1 - v.1| ≤ 3 ∧ |u.2 - v.2| ≤ 3 := by
  intro t o
  cases t <;> fin_cases o <;> decide

lemma piece_diameter_le_three (q : PieceState) {z₁ z₂ : Cell}
    (hz₁ : z₁ ∈ q.cells) (hz₂ : z₂ ∈ q.cells) :
    |z₁.1 - z₂.1| ≤ 3 ∧ |z₁.2 - z₂.2| ≤ 3 := by
  rcases mem_cells_iff_C.mp hz₁ with ⟨u, hu, rfl⟩
  rcases mem_cells_iff_C.mp hz₂ with ⟨v, hv, rfl⟩
  have hd := offsetsC_diam q.kind q.orientation u hu v hv
  have h1 : q.position.1 + u.1 - (q.position.1 + v.1) = u.1 - v.1 := by ring
  have h2 : q.position.2 + u.2 - (q.position.2 + v.2) = u.2 - v.2 := by ring
  dsimp only
  rwa [h1, h2]

/-- Every settled trajectory `u` in bucket `j` with `0 ≤ z.2 < H'` is `Clear` on `U` and has a
supporting cell `(6j + x_s, y_s) ∈ u.cells` (`0 ≤ x_s < 5`, `0 ≤ y_s < H'`) with `bucketCell U j x_s (y_s - 1) = true`. -/
lemma exists_bucket_support {R : Rotation} {U : Board} {s' H' : ℕ}
    (hframe : BucketFrame U s' H') {j : Fin s'} {t : Piece} {u : PieceState}
    (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U t u) :
    U.Clear u ∧ ¬ U.Clear (translate u 0 (-1)) ∧
    ∃ x_s y_s : ℤ, 0 ≤ x_s ∧ x_s < 5 ∧ 0 ≤ y_s ∧ y_s < (H' : ℤ) ∧
      (6 * (j.val : ℤ) + x_s, y_s) ∈ u.cells ∧ bucketCell U j.val x_s (y_s - 1) = true := by
  obtain ⟨hcl, hblk⟩ := trajectory_clear_and_blocked htraj
  refine ⟨hcl, hblk, ?_⟩
  have hex : ∃ w ∈ (translate u 0 (-1)).cells, U.occupied w = true := by
    by_contra hall; push Not at hall
    apply hblk; intro w hw
    exact Bool.eq_false_iff.mpr (hall w hw)
  rcases hex with ⟨w, hw, hocc⟩
  have htr : (translate u 0 (-1)).cells = u.cells.map (fun z => (z.1, z.2 - 1)) := by
    unfold translate PieceState.cells; rw [List.map_map]
    apply List.map_congr_left; intro a _; simp only [Function.comp_apply]; ext <;> omega
  rw [htr, List.mem_map] at hw
  rcases hw with ⟨z, hz, rfl⟩
  have hzx := hin z hz
  have hzy := hy_u z hz
  have hx5_ne : z.1 ≠ 6 * (j.val : ℤ) + 5 := by
    intro hx5
    have hrw := bucketCell_right_wall_B hframe j hzy.1 hzy.2
    unfold bucketCell at hrw
    have heq : (6 * (j.val : ℤ) + 5, z.2) = z := by ext <;> omega
    rw [heq, hcl z hz] at hrw; cases hrw
  refine ⟨z.1 - 6 * (j.val : ℤ), z.2, by omega, by omega, hzy.1, hzy.2, ?_, ?_⟩
  · convert hz using 1; ext <;> omega
  · unfold bucketCell
    convert hocc using 2; ext <;> omega

/-- Universal Open-Notch Classifier: if `u` (`t ∈ [.LG, .LS, .Sq, .I]`) touches `(6j + 3, r)` or `(6j + 4, r)`
at an `OpenNotch` `r`, then either `HasHole (U.insert u) j H'`, or `t = .I` covering `(1..4, r)`,
or `t = .LG` covering `(2, r+1), (2..4, r)`! -/
lemma classify_at_open_notch {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    (j : Fin s') {r : ℤ} (hopen : OpenNotch U j.val H' r)
    {u : PieceState} (hk : u.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece))
    (hcl : U.Clear u)
    (htouch : (6 * (j.val : ℤ) + 3, r) ∈ u.cells ∨ (6 * (j.val : ℤ) + 4, r) ∈ u.cells) :
    HasHole (U.insert u) j.val H' ∨
    (u.kind = .I ∧ u.cells.toFinset =
      {(6 * (j.val : ℤ) + 1, r), (6 * (j.val : ℤ) + 2, r),
       (6 * (j.val : ℤ) + 3, r), (6 * (j.val : ℤ) + 4, r)}) ∨
    (u.kind = .LG ∧ u.cells.toFinset =
      {(6 * (j.val : ℤ) + 2, r + 1), (6 * (j.val : ℤ) + 2, r),
       (6 * (j.val : ℤ) + 3, r), (6 * (j.val : ℤ) + 4, r)}) := by
  obtain ⟨hr4, hrH6⟩ := openNotch_margins hframe hopen.1 hopen.2.1 hopen.2.2.1
  have hrmod := hopen.2.2.1
  have h34u := bucketCell_notch_wall_B hframe j (y := r + 1) (by omega) (by omega) (by omega)
  have h34d := bucketCell_notch_wall_B hframe j (y := r - 1) (by omega) (by omega) (by omega)
  have h5 := bucketCell_right_wall_B hframe j (y := r) (by omega) (by omega)
  by_cases hm4 : (6 * (j.val : ℤ) + 4, r) ∈ u.cells
  · rcases geom_G2_C hk hcl h34u.2 h34d.2 h5 h34u.1 h34d.1 hm4 with
      ⟨_, ⟨hI, h1, h2, h3⟩ | ⟨hLG, h2, h3, h2u⟩⟩
    · right; left; refine ⟨hI, ?_⟩
      symm; apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact List.mem_toFinset.mpr ‹_›
      · rw [piece_cells_toFinset_card]
        rw [Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    · right; right; refine ⟨hLG, ?_⟩
      symm; apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact List.mem_toFinset.mpr ‹_›
      · rw [piece_cells_toFinset_card]
        rw [Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  · left
    have hm3 : (6 * (j.val : ℤ) + 3, r) ∈ u.cells := by
      rcases htouch with h3 | h4
      · exact h3
      · exact absurd h4 hm4
    exact hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 4) (y := r)
      (by omega) (by omega) (by omega) (by omega)
      (bucketCell_insert_of_not_mem hopen.2.2.2.2 hm4)
      (bucketCell_insert_of_true h5)
      (bucketCell_insert_of_mem hframe (by omega) (by omega) (by omega) (by omega) hm3)
      (bucketCell_insert_of_true h34u.2)
      (bucketCell_insert_of_true h34d.2)

/-- Integer range `[lo, hi]` as a computable list for fast `by decide` enumeration. -/
def intRange (lo hi : ℤ) : List ℤ :=
  (List.range (hi + 1 - lo).toNat).map fun k : ℕ => lo + (k : ℤ)

lemma mem_intRange_of_bounds {lo hi v : ℤ} (h1 : lo ≤ v) (h2 : v ≤ hi) :
    v ∈ intRange lo hi := by
  unfold intRange
  rw [List.mem_map]
  refine ⟨(v - lo).toNat, ?_, by omega⟩
  rw [List.mem_range]
  omega

/-- Relative cells of `(t, o)` at relative anchor `(px, py)`. -/
def relPlacementCells (t : Piece) (o : Fin 4) (px py : ℤ) : List Cell :=
  (offsetsC t o).map fun w => (px + w.1, py + w.2)

/-- Computable list of all valid settled relative placements of `t` inside `[0, 5) × [yLo, yHi]`
with respect to relative occupancy `occ : ℤ → ℤ → Bool`. -/
def validRelPlacements (t : Piece) (occ : ℤ → ℤ → Bool) (yLo yHi : ℤ) : List (List Cell) :=
  (List.finRange 4).flatMap fun o =>
    (intRange (-2) 5).flatMap fun px =>
      (intRange (yLo - 2) (yHi + 2)).filterMap fun py =>
        let cs := relPlacementCells t o px py
        if (cs.all fun c => decide (0 ≤ c.1 ∧ c.1 < 5 ∧ yLo ≤ c.2 ∧ c.2 ≤ yHi) && !(occ c.1 c.2)) &&
           (cs.any fun c => occ c.1 (c.2 - 1)) then
          some cs
        else
          none

/-- Soundness of `validRelPlacements`: any settled piece `u` in bucket `j` whose cells lie in
`[y_ref + yLo, y_ref + yHi]` on a board matching `occ` on `[0, 5) × [yLo - 1, yHi]` has its
relative cell list inside `validRelPlacements t occ yLo yHi`! -/
lemma mem_validRelPlacements {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : Fin s'} {t : Piece} {u : PieceState}
    (huk : u.kind = t)
    (hin : InBucket j.val u)
    (hy_H : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (hcl : U.Clear u)
    (hsupp : ∃ x_s y_s : ℤ, 0 ≤ x_s ∧ x_s < 5 ∧ 0 ≤ y_s ∧ y_s < (H' : ℤ) ∧
      (6 * (j.val : ℤ) + x_s, y_s) ∈ u.cells ∧ bucketCell U j.val x_s (y_s - 1) = true)
    {y_ref yLo yHi : ℤ} {occ : ℤ → ℤ → Bool}
    (hy_box : ∀ z ∈ u.cells, y_ref + yLo ≤ z.2 ∧ z.2 ≤ y_ref + yHi)
    (hocc_eq : ∀ dx dy : ℤ, 0 ≤ dx → dx < 5 → yLo - 1 ≤ dy → dy ≤ yHi →
      bucketCell U j.val dx (y_ref + dy) = occ dx dy) :
    u.cells.map (fun z => (z.1 - 6 * (j.val : ℤ), z.2 - y_ref)) ∈
      validRelPlacements t occ yLo yHi := by
  set px := u.position.1 - 6 * (j.val : ℤ)
  set py := u.position.2 - y_ref
  have hpos_mem : u.position ∈ u.cells := position_mem_cells_A u
  have hpos_x := hin _ hpos_mem
  have hpos_H := hy_H _ hpos_mem
  have hpos_y := hy_box _ hpos_mem
  have hcs_eq : u.cells.map (fun z => (z.1 - 6 * (j.val : ℤ), z.2 - y_ref)) =
      relPlacementCells t u.orientation px py := by
    rw [piece_cells_eq_map_offsetsC, huk, List.map_map]
    unfold relPlacementCells
    apply List.map_congr_left
    intro w _; simp only [Function.comp_apply]; ext <;> dsimp [px, py] <;> omega
  rw [hcs_eq]
  unfold validRelPlacements
  rw [List.mem_flatMap]
  refine ⟨u.orientation, List.mem_finRange _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨px, mem_intRange_of_bounds (by dsimp [px]; omega) (by dsimp [px]; omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨py, mem_intRange_of_bounds (by dsimp [py]; omega) (by dsimp [py]; omega), ?_⟩
  set cs := relPlacementCells t u.orientation px py
  have hall_ok : (cs.all fun c => decide (0 ≤ c.1 ∧ c.1 < 5 ∧ yLo ≤ c.2 ∧ c.2 ≤ yHi) && !(occ c.1 c.2)) = true := by
    rw [List.all_eq_true]
    intro c hc
    have hmem_map : c ∈ u.cells.map (fun z => (z.1 - 6 * (j.val : ℤ), z.2 - y_ref)) := by
      rwa [hcs_eq]
    rw [List.mem_map] at hmem_map
    rcases hmem_map with ⟨z, hz, rfl⟩
    have hzx := hin z hz
    have hzH := hy_H z hz
    have hzb := hy_box z hz
    have hocc_z := hcl z hz
    have hx5_ne : z.1 ≠ 6 * (j.val : ℤ) + 5 := by
      intro hx5
      have hrw := bucketCell_right_wall_B hframe j hzH.1 hzH.2
      unfold bucketCell at hrw
      have heq : (6 * (j.val : ℤ) + 5, z.2) = z := by ext <;> omega
      rw [heq, hocc_z] at hrw; cases hrw
    have hdx0 : 0 ≤ z.1 - 6 * (j.val : ℤ) := by omega
    have hdx5 : z.1 - 6 * (j.val : ℤ) < 5 := by omega
    have hdy1 : yLo ≤ z.2 - y_ref := by omega
    have hdy2 : z.2 - y_ref ≤ yHi := by omega
    have ho := hocc_eq (z.1 - 6 * (j.val : ℤ)) (z.2 - y_ref) hdx0 hdx5 (by omega) hdy2
    have hz_eq : (6 * (j.val : ℤ) + (z.1 - 6 * (j.val : ℤ)), y_ref + (z.2 - y_ref)) = z := by
      ext <;> omega
    unfold bucketCell at ho; rw [hz_eq, hocc_z] at ho
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨⟨hdx0, hdx5, hdy1, hdy2⟩, ho.symm⟩
  have hany_ok : (cs.any fun c => occ c.1 (c.2 - 1)) = true := by
    rw [List.any_eq_true]
    rcases hsupp with ⟨x_s, y_s, hx0, hx5, _, _, hms, hocc_s⟩
    have hsb := hy_box _ hms
    dsimp only at hsb
    refine ⟨(x_s, y_s - y_ref), ?_, ?_⟩
    · rw [← hcs_eq, List.mem_map]
      exact ⟨(6 * (j.val : ℤ) + x_s, y_s), hms, by dsimp; ext <;> omega⟩
    · have ho := hocc_eq x_s (y_s - y_ref - 1) hx0 hx5 (by omega) (by omega)
      have hy_eq : y_ref + (y_s - y_ref - 1) = y_s - 1 := by omega
      rw [hy_eq] at ho
      rw [← ho]; exact hocc_s
  dsimp only
  change (if ((cs.all fun c => decide (0 ≤ c.1 ∧ c.1 < 5 ∧ yLo ≤ c.2 ∧ c.2 ≤ yHi) && !(occ c.1 c.2)) &&
      (cs.any fun c => occ c.1 (c.2 - 1))) = true then some cs else none) = some cs
  rw [hall_ok, hany_ok]; rfl

/-- 3-column variant `validRelPlacements012`: enumerates all settled relative placements of `t` inside
`[0, 3) × [yLo, yHi]`, requiring `occ` agreement ONLY on `0 ≤ dx < 3` (no `y < H'` wall assumption needed!). -/
def validRelPlacements012 (t : Piece) (occ : ℤ → ℤ → Bool) (yLo yHi : ℤ) : List (List Cell) :=
  (List.finRange 4).flatMap fun o =>
    (intRange (-2) 4).flatMap fun px =>
      (intRange (yLo - 2) (yHi + 2)).filterMap fun py =>
        let cs := relPlacementCells t o px py
        if (cs.all fun c => decide (0 ≤ c.1 ∧ c.1 < 3 ∧ yLo ≤ c.2 ∧ c.2 ≤ yHi) && !(occ c.1 c.2)) &&
           (cs.any fun c => occ c.1 (c.2 - 1)) then
          some cs
        else
          none

lemma mem_validRelPlacements012 {U : Board} {j : ℕ} {t : Piece} {u : PieceState}
    (huk : u.kind = t)
    (hx_012 : ∀ z ∈ u.cells, 6 * (j : ℤ) ≤ z.1 ∧ z.1 < 6 * (j : ℤ) + 3)
    (hcl : U.Clear u)
    (hsupp : ∃ x_s y_s : ℤ, 0 ≤ x_s ∧ x_s < 3 ∧
      (6 * (j : ℤ) + x_s, y_s) ∈ u.cells ∧ bucketCell U j x_s (y_s - 1) = true)
    {y_ref yLo yHi : ℤ} {occ : ℤ → ℤ → Bool}
    (hy_box : ∀ z ∈ u.cells, y_ref + yLo ≤ z.2 ∧ z.2 ≤ y_ref + yHi)
    (hocc_eq : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → yLo - 1 ≤ dy → dy ≤ yHi →
      bucketCell U j dx (y_ref + dy) = occ dx dy) :
    u.cells.map (fun z => (z.1 - 6 * (j : ℤ), z.2 - y_ref)) ∈
      validRelPlacements012 t occ yLo yHi := by
  set px := u.position.1 - 6 * (j : ℤ)
  set py := u.position.2 - y_ref
  have hpos_mem : u.position ∈ u.cells := position_mem_cells_A u
  have hpos_x := hx_012 _ hpos_mem
  have hpos_y := hy_box _ hpos_mem
  have hcs_eq : u.cells.map (fun z => (z.1 - 6 * (j : ℤ), z.2 - y_ref)) =
      relPlacementCells t u.orientation px py := by
    rw [piece_cells_eq_map_offsetsC, huk, List.map_map]
    unfold relPlacementCells
    apply List.map_congr_left
    intro w _; simp only [Function.comp_apply]; ext <;> dsimp [px, py] <;> omega
  rw [hcs_eq]
  unfold validRelPlacements012
  rw [List.mem_flatMap]
  refine ⟨u.orientation, List.mem_finRange _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨px, mem_intRange_of_bounds (by dsimp [px]; omega) (by dsimp [px]; omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨py, mem_intRange_of_bounds (by dsimp [py]; omega) (by dsimp [py]; omega), ?_⟩
  set cs := relPlacementCells t u.orientation px py
  have hall_ok : (cs.all fun c => decide (0 ≤ c.1 ∧ c.1 < 3 ∧ yLo ≤ c.2 ∧ c.2 ≤ yHi) && !(occ c.1 c.2)) = true := by
    rw [List.all_eq_true]
    intro c hc
    have hmem_map : c ∈ u.cells.map (fun z => (z.1 - 6 * (j : ℤ), z.2 - y_ref)) := by
      rwa [hcs_eq]
    rw [List.mem_map] at hmem_map
    rcases hmem_map with ⟨z, hz, rfl⟩
    have hzx := hx_012 z hz
    have hzb := hy_box z hz
    have hocc_z := hcl z hz
    have hdx0 : 0 ≤ z.1 - 6 * (j : ℤ) := by omega
    have hdx3 : z.1 - 6 * (j : ℤ) < 3 := by omega
    have hdy1 : yLo ≤ z.2 - y_ref := by omega
    have hdy2 : z.2 - y_ref ≤ yHi := by omega
    have ho := hocc_eq (z.1 - 6 * (j : ℤ)) (z.2 - y_ref) hdx0 hdx3 (by omega) hdy2
    have hz_eq : (6 * (j : ℤ) + (z.1 - 6 * (j : ℤ)), y_ref + (z.2 - y_ref)) = z := by
      ext <;> omega
    unfold bucketCell at ho; rw [hz_eq, hocc_z] at ho
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨⟨hdx0, hdx3, hdy1, hdy2⟩, ho.symm⟩
  have hany_ok : (cs.any fun c => occ c.1 (c.2 - 1)) = true := by
    rw [List.any_eq_true]
    rcases hsupp with ⟨x_s, y_s, hx0, hx3, hms, hocc_s⟩
    have hsb := hy_box _ hms
    dsimp only at hsb
    refine ⟨(x_s, y_s - y_ref), ?_, ?_⟩
    · rw [← hcs_eq, List.mem_map]
      exact ⟨(6 * (j : ℤ) + x_s, y_s), hms, by dsimp; ext <;> omega⟩
    · have ho := hocc_eq x_s (y_s - y_ref - 1) hx0 hx3 (by omega) (by omega)
      have hy_eq : y_ref + (y_s - y_ref - 1) = y_s - 1 := by omega
      rw [hy_eq] at ho
      rw [← ho]; exact hocc_s
  dsimp only
  change (if ((cs.all fun c => decide (0 ≤ c.1 ∧ c.1 < 3 ∧ yLo ≤ c.2 ∧ c.2 ≤ yHi) && !(occ c.1 c.2)) &&
      (cs.any fun c => occ c.1 (c.2 - 1))) = true then some cs else none) = some cs
  rw [hall_ok, hany_ok]; rfl

lemma mem_cells_iff_of_relMap {u : PieceState} {j : ℕ} {y_ref : ℤ} {rel : List Cell}
    (hmap : u.cells.map (fun z => (z.1 - 6 * (j : ℤ), z.2 - y_ref)) = rel)
    (x y : ℤ) :
    (6 * (j : ℤ) + x, y) ∈ u.cells ↔ (x, y - y_ref) ∈ rel := by
  rw [← hmap, List.mem_map]
  constructor
  · intro hm; exact ⟨(6 * (j : ℤ) + x, y), hm, by dsimp; ext <;> omega⟩
  · rintro ⟨z, hz, heq⟩
    simp only [Prod.mk.injEq] at heq
    convert hz using 1; ext <;> omega


lemma bcell0 {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {y : ℤ} (hy0 : 0 ≤ y) (hyB : y < (H' : ℤ) + 3) :
    bucketCell U j 0 y = pat 0 y.toNat :=
  bucketPattern_eval_012 hframe hpat (by omega) (by omega) hy0 hyB

lemma bcell1 {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {y : ℤ} (hy0 : 0 ≤ y) (hyB : y < (H' : ℤ) + 3) :
    bucketCell U j 1 y = pat 1 y.toNat :=
  bucketPattern_eval_012 hframe hpat (by omega) (by omega) hy0 hyB

lemma bcell2 {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {y : ℤ} (hy0 : 0 ≤ y) (hyB : y < (H' : ℤ) + 3) :
    bucketCell U j 2 y = pat 2 y.toNat :=
  bucketPattern_eval_012 hframe hpat (by omega) (by omega) hy0 hyB

lemma bcell3_notch {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {y : ℤ} (hy0 : 0 ≤ y) (hyH : y < (H' : ℤ)) (hmod : (y + 1) % 6 = 5) :
    bucketCell U j 3 y = pat 3 y.toNat := by
  rw [bucketPattern_eval hframe hpat (by omega) (by omega) hy0 hyH]
  have hnw : ¬ ((3 : ℤ) = 5 ∨ 3 ≤ (3 : ℤ) ∧ (y + 1) % 6 ≠ 5) := by omega
  rw [decide_eq_false hnw, Bool.false_or]; rfl

lemma bcell4_notch {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    {j : ℕ} {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j H' pat)
    {y : ℤ} (hy0 : 0 ≤ y) (hyH : y < (H' : ℤ)) (hmod : (y + 1) % 6 = 5) :
    bucketCell U j 4 y = pat 4 y.toNat := by
  rw [bucketPattern_eval hframe hpat (by omega) (by omega) hy0 hyH]
  have hnw : ¬ ((4 : ℤ) = 5 ∨ 3 ≤ (4 : ℤ) ∧ (y + 1) % 6 ≠ 5) := by omega
  rw [decide_eq_false hnw, Bool.false_or]; rfl

lemma bool_or_left {a b : Bool} (ha : a = true) : (a || b) = true := by simp [ha]

lemma bool_or_right {a b : Bool} (hb : b = true) : (a || b) = true := by simp [hb]

lemma bcell_eq_of_eq {B : Board} {j : ℕ} {x₁ y₁ x₂ y₂ : ℤ} {v : Bool}
    (h : bucketCell B j x₂ y₂ = v) (hxy : x₁ = x₂ ∧ y₁ = y₂) :
    bucketCell B j x₁ y₁ = v := by
  rw [hxy.1, hxy.2]; exact h

lemma mem4_of_omega {p a b c d : Cell}
    (h : (p.1 = a.1 ∧ p.2 = a.2) ∨ (p.1 = b.1 ∧ p.2 = b.2) ∨
         (p.1 = c.1 ∧ p.2 = c.2) ∨ (p.1 = d.1 ∧ p.2 = d.2)) :
    p ∈ [a, b, c, d] := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff] using h

lemma not_mem4_of_omega {p a b c d : Cell}
    (h : ¬ ((p.1 = a.1 ∧ p.2 = a.2) ∨ (p.1 = b.1 ∧ p.2 = b.2) ∨
            (p.1 = c.1 ∧ p.2 = c.2) ∨ (p.1 = d.1 ∧ p.2 = d.2))) :
    p ∉ [a, b, c, d] := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff] using h

lemma iff_mem4_of_omega {p a b c d : Cell} {P : Prop}
    (h : ((p.1 = a.1 ∧ p.2 = a.2) ∨ (p.1 = b.1 ∧ p.2 = b.2) ∨
          (p.1 = c.1 ∧ p.2 = c.2) ∨ (p.1 = d.1 ∧ p.2 = d.2)) ↔ P) :
    (p ∈ [a, b, c, d]) ↔ P := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff] using h

lemma mk_balcony_0 {B : Board} {j H : ℕ} {b : ℤ}
    (hb0 : 0 ≤ b) (hbH : b < (H : ℤ))
    (h0 : bucketCell B j 0 b = false)
    (h1 : bucketCell B j 1 b = true)
    (h2 : bucketCell B j 2 b = true) :
    Balcony B j H b 0 := by
  refine ⟨hb0, hbH, fun x => ?_⟩
  fin_cases x <;> dsimp
  · simpa using h0
  · simpa using h1
  · simpa using h2

lemma mk_balcony_2 {B : Board} {j H : ℕ} {b : ℤ}
    (hb0 : 0 ≤ b) (hbH : b < (H : ℤ))
    (h0 : bucketCell B j 0 b = true)
    (h1 : bucketCell B j 1 b = true)
    (h2 : bucketCell B j 2 b = false) :
    Balcony B j H b 2 := by
  refine ⟨hb0, hbH, fun x => ?_⟩
  fin_cases x <;> dsimp
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-- Inverted stepped seal: if row `r_s` has cols `1..4` occupied, `(0, r_s + 1)` is occupied (`r_s + 1 < H'`),
and `(x₀, y₀)` is empty below `r_s`, then `HasHole U j.val H'`. -/
lemma hasHole_of_inverted_stepped_seal {U : Board} {s' H' : ℕ} (hframe : BucketFrame U s' H')
    (j : Fin s') {r_s x₀ y₀ : ℤ}
    (_hr0 : 0 ≤ r_s) (hrH : r_s + 1 < (H' : ℤ))
    (hx0 : 0 ≤ x₀) (hx5 : x₀ < 5) (hy0 : 0 ≤ y₀) (hyr : y₀ < r_s)
    (h1 : bucketCell U j.val 1 r_s = true) (h2 : bucketCell U j.val 2 r_s = true)
    (h3 : bucketCell U j.val 3 r_s = true) (h4 : bucketCell U j.val 4 r_s = true)
    (h0u : bucketCell U j.val 0 (r_s + 1) = true)
    (hf : bucketCell U j.val x₀ y₀ = false) :
    HasHole U j.val H' := by
  refine ⟨x₀, y₀, hx0, hx5, hy0, by omega, hf, ?_⟩
  rintro ⟨z, hzH, _, hpath⟩
  have hstay : ∀ a b : Cell,
      (6 * (j.val : ℤ) ≤ a.1 ∧ a.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ a.2 ∧ a.2 ≤ r_s ∧
        (a.2 = r_s → a.1 = 6 * (j.val : ℤ))) →
      EmptyAdjacent U a b →
      (6 * (j.val : ℤ) ≤ b.1 ∧ b.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ b.2 ∧ b.2 ≤ r_s ∧
        (b.2 = r_s → b.1 = 6 * (j.val : ℤ))) := by
    intro a b ha hadj
    rcases hadj with ⟨_, hbf, hdist⟩
    have hstep : (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
        (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
      rcases abs_cases (a.1 - b.1) with ⟨h1', _⟩ | ⟨h1', _⟩ <;>
        rcases abs_cases (a.2 - b.2) with ⟨h2', _⟩ | ⟨h2', _⟩ <;> omega
    rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · by_cases h5 : b.1 = 6 * (j.val : ℤ) + 5
      · have hw := bucketCell_right_wall_B hframe j (y := b.2) (by omega) (by omega)
        have hb : (6 * (j.val : ℤ) + 5, b.2) = b := by ext <;> omega
        unfold bucketCell at hw; rw [hb, hbf] at hw; cases hw
      · refine ⟨by omega, by omega, by omega, by omega, fun hbr => ?_⟩
        have ha0 := ha.2.2.2.2 (by omega)
        have hb : (6 * (j.val : ℤ) + 1, r_s) = b := by ext <;> omega
        unfold bucketCell at h1; rw [hb, hbf] at h1; cases h1
    · by_cases hm1 : b.1 = 6 * (j.val : ℤ) - 1
      · have hw := bucketCell_left_wall_B hframe j (y := b.2) (by omega) (by omega)
        have hb : (6 * (j.val : ℤ) + -1, b.2) = b := by ext <;> omega
        unfold bucketCell at hw; rw [hb, hbf] at hw; cases hw
      · refine ⟨by omega, by omega, by omega, by omega, fun hbr => ?_⟩
        have ha0 := ha.2.2.2.2 (by omega); omega
    · by_cases htop : b.2 = r_s + 1
      · have ha0 := ha.2.2.2.2 (by omega)
        have hb : (6 * (j.val : ℤ) + 0, r_s + 1) = b := by ext <;> omega
        unfold bucketCell at h0u; rw [hb, hbf] at h0u; cases h0u
      · refine ⟨by omega, by omega, by omega, by omega, fun hbr => ?_⟩
        have hdx : b.1 - 6 * (j.val : ℤ) = 0 ∨ b.1 - 6 * (j.val : ℤ) = 1 ∨
            b.1 - 6 * (j.val : ℤ) = 2 ∨ b.1 - 6 * (j.val : ℤ) = 3 ∨
            b.1 - 6 * (j.val : ℤ) = 4 := by omega
        rcases hdx with hd | hd | hd | hd | hd
        · omega
        · have hb : (6 * (j.val : ℤ) + 1, r_s) = b := by ext <;> omega
          unfold bucketCell at h1; rw [hb, hbf] at h1; cases h1
        · have hb : (6 * (j.val : ℤ) + 2, r_s) = b := by ext <;> omega
          unfold bucketCell at h2; rw [hb, hbf] at h2; cases h2
        · have hb : (6 * (j.val : ℤ) + 3, r_s) = b := by ext <;> omega
          unfold bucketCell at h3; rw [hb, hbf] at h3; cases h3
        · have hb : (6 * (j.val : ℤ) + 4, r_s) = b := by ext <;> omega
          unfold bucketCell at h4; rw [hb, hbf] at h4; cases h4
    · by_cases hneg : b.2 = -1
      · unfold Board.occupied at hbf
        have : ¬ (0 ≤ b.2 ∧ b.2 < U.height) := by omega
        simp [this] at hbf
      · refine ⟨by omega, by omega, by omega, by omega, fun hbr => ?_⟩
        omega
  have hbox : ∀ v, Relation.ReflTransGen (EmptyAdjacent U) (6 * (j.val : ℤ) + x₀, y₀) v →
      6 * (j.val : ℤ) ≤ v.1 ∧ v.1 < 6 * (j.val : ℤ) + 5 ∧ 0 ≤ v.2 ∧ v.2 ≤ r_s ∧
        (v.2 = r_s → v.1 = 6 * (j.val : ℤ)) := by
    intro v hp
    induction hp with
    | refl => exact ⟨by dsimp; omega, by dsimp; omega, hy0, by dsimp; omega, fun h => by dsimp at h; omega⟩
    | tail _ hst ih => exact hstay _ _ ih hst
  have := hbox z hpath; omega

/-- `FlatDiscrepancy` variant where `(3, y) = true` holds on `[h + α + 1, h + α + β]` (so even if `h + α + 1`
was originally a notch row, its col-3 cell is already filled, blocking horizontal `.I`). -/
theorem anyPlay_unfillable_of_flatDiscrepancy_cap3 {R : Rotation} (hReason : Reasonable R)
    {B : Board} {s H : ℕ} (hframe : BucketFrame B s H) (j : Fin s)
    {h : ℤ} {α : ℕ} {b : ℤ} {ib : Fin 3}
    (hh0 : 0 ≤ h) (hceilH : h + α + 1 < b)
    (hbal : Balcony B j.val H b ib)
    (h1b : bucketCell B j.val 1 (h - 1) = true) (h2b : bucketCell B j.val 2 (h - 1) = true)
    (h12 : ∀ y : ℤ, h ≤ y → y ≤ h + α → bucketCell B j.val 1 y = false ∧ bucketCell B j.val 2 y = false)
    (hcap1 : bucketCell B j.val 1 (h + α + 1) = false)
    (hcap3 : bucketCell B j.val 3 (h + α + 1) = true)
    (h1_top : bucketCell B j.val 1 (h + α + 2) = true)
    (h2_top : bucketCell B j.val 2 (h + α + 1) = true) :
    ¬ ∃ B', AnyPlay R B B' ∧ BucketFull B' j.val H := by
  have hbH : b < H := hbal.2.1
  have hdiff0 : ((colEmptyCount B j.val 1 h (α + 2) : ℤ) -
      (colEmptyCount B j.val 2 h (α + 1) : ℤ)) % 4 ≠ 0 := by
    have h1_eq : colEmptyCount B j.val 1 h (α + 2) = α + 2 := by
      unfold colEmptyCount
      have hf : ((Finset.range (α + 2)).filter fun k : ℕ => bucketCell B j.val 1 (h + (k : ℤ)) = false) =
          Finset.range (α + 2) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
        intro hk
        by_cases hkα : k ≤ α
        · exact (h12 (h + k) (by omega) (by omega)).1
        · have : h + (k : ℤ) = h + α + 1 := by omega
          rwa [this]
      rw [hf, Finset.card_range]
    have h2_eq : colEmptyCount B j.val 2 h (α + 1) = α + 1 := by
      unfold colEmptyCount
      have hf : ((Finset.range (α + 1)).filter fun k : ℕ => bucketCell B j.val 2 (h + (k : ℤ)) = false) =
          Finset.range (α + 1) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
        intro hk
        exact (h12 (h + k) (by omega) (by omega)).2
      rw [hf, Finset.card_range]
    rw [h1_eq, h2_eq]; omega
  have hvert_mod4 : ∀ (Bcur : Board) (q : PieceState) (col : ℤ) (n : ℕ),
      BucketFrame Bcur s H →
      (col = 1 ∨ col = 2) → h + n ≤ b →
      Bcur.Clear q →
      bucketCell Bcur j.val col (h - 1) = true →
      bucketCell Bcur j.val col (h + n) = true →
      (∃ x₀ y₀ : ℤ, q.cells.toFinset = {(x₀, y₀), (x₀, y₀ + 1), (x₀, y₀ + 2), (x₀, y₀ + 3)}) →
      (colEmptyCount (Bcur.insert q) j.val col h n : ℤ) = colEmptyCount Bcur j.val col h n ∨
      (colEmptyCount (Bcur.insert q) j.val col h n : ℤ) + 4 = colEmptyCount Bcur j.val col h n := by
    intro Bcur q col n hfr hcol hn hcl hbot htop ⟨x₀, y₀, hfin⟩
    by_cases hhit : ∃ k < n, (6 * (j.val : ℤ) + col, h + k) ∈ q.cells
    · right
      rcases hhit with ⟨k0, hk0, hm0⟩
      have hm0' := List.mem_toFinset.mpr hm0; rw [hfin] at hm0'
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm0'
      have hx0_eq : x₀ = 6 * (j.val : ℤ) + col := by
        rcases hm0' with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ <;> omega
      have hy0_ge : h ≤ y₀ := by
        by_contra hlt; push Not at hlt
        have hm : (6 * (j.val : ℤ) + col, h - 1) ∈ q.cells := by
          apply List.mem_toFinset.mp; rw [hfin]
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          rcases hm0' with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
        have hc := hcl _ hm; unfold bucketCell at hbot; rw [hbot] at hc; cases hc
      have hy0_le : y₀ + 3 < h + n := by
        by_contra hge; push Not at hge
        have hm : (6 * (j.val : ℤ) + col, h + n) ∈ q.cells := by
          apply List.mem_toFinset.mp; rw [hfin]
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          rcases hm0' with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
        have hc := hcl _ hm; unfold bucketCell at htop; rw [htop] at hc; cases hc
      set d : ℕ := (y₀ - h).toNat
      set S4 : Finset ℕ := {d, d + 1, d + 2, d + 3}
      have hS4_card : S4.card = 4 := by
        simp only [S4]
        rw [Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
      set E0 := (Finset.range n).filter fun k : ℕ => bucketCell Bcur j.val col (h + (k : ℤ)) = false
      set E1 := (Finset.range n).filter fun k : ℕ => bucketCell (Bcur.insert q) j.val col (h + (k : ℤ)) = false
      have hmem_q : ∀ k : ℕ, (6 * (j.val : ℤ) + col, h + k) ∈ q.cells ↔ k ∈ S4 := by
        intro k; rw [← List.mem_toFinset, hfin]
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, S4]; omega
      have hS4_sub : S4 ⊆ E0 := by
        intro k hk; rw [Finset.mem_filter, Finset.mem_range]
        have hmq := (hmem_q k).mpr hk
        have hk_lt : k < n := by simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hk; omega
        exact ⟨hk_lt, hcl _ hmq⟩
      have hE1_eq : E1 = E0 \ S4 := by
        ext k; simp only [E1, E0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro ⟨hk, hf⟩
          have hf0 : bucketCell Bcur j.val col (h + k) = false := by
            cases hB : bucketCell Bcur j.val col (h + k) with
            | false => rfl
            | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
          refine ⟨⟨hk, hf0⟩, fun hk4 => ?_⟩
          have ht := bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) ((hmem_q k).mpr hk4)
          rw [ht] at hf; cases hf
        · rintro ⟨⟨hk, hf0⟩, hnot4⟩
          exact ⟨hk, bucketCell_insert_of_not_mem hf0 (mt (hmem_q k).mp hnot4)⟩
      have hcard : E1.card + 4 = E0.card := by
        rw [hE1_eq, ← hS4_card, Finset.card_sdiff_add_card_eq_card hS4_sub]
      change (E1.card : ℤ) + 4 = E0.card; omega
    · left; push Not at hhit
      have hsame : colEmptyCount (Bcur.insert q) j.val col h n = colEmptyCount Bcur j.val col h n := by
        unfold colEmptyCount; congr 1; ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        refine and_congr_right fun hk => ?_
        constructor
        · intro hf; cases hB : bucketCell Bcur j.val col (h + k) with
          | false => rfl
          | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
        · intro hf; exact bucketCell_insert_of_not_mem hf (hhit k hk)
      rw [hsame]
  have hgen : ∀ {Bcur B' : Board},
      AnyPlay R Bcur B' →
      BucketFrame Bcur s H →
      Balcony Bcur j.val H b ib →
      bucketCell Bcur j.val 1 (h - 1) = true →
      bucketCell Bcur j.val 2 (h - 1) = true →
      bucketCell Bcur j.val 1 (h + α + 2) = true →
      bucketCell Bcur j.val 2 (h + α + 1) = true →
      bucketCell Bcur j.val 3 (h + α + 1) = true →
      ((colEmptyCount Bcur j.val 1 h (α + 2) : ℤ) -
        (colEmptyCount Bcur j.val 2 h (α + 1) : ℤ)) % 4 ≠ 0 →
      BucketFull B' j.val H → False := by
    intro Bcur B' hplay
    induction hplay with
    | nil Bcur =>
      intro _ _ _ _ _ _ _ hdiff hfull
      have h0i : colEmptyCount Bcur j.val 1 h (α + 2) = 0 := by
        unfold colEmptyCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk; rw [Finset.mem_range] at hk
        intro hf; exact not_bucketFull_of_false_B hfull (by omega) (by omega) (by omega) (by omega) hf
      have h0k : colEmptyCount Bcur j.val 2 h (α + 1) = 0 := by
        unfold colEmptyCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk; rw [Finset.mem_range] at hk
        intro hf; exact not_bucketFull_of_false_B hfull (by omega) (by omega) (by omega) (by omega) hf
      rw [h0i, h0k] at hdiff; simp at hdiff
    | @step Bcur B' q htraj hrest ih =>
      intro hfr hbalc h1b' h2b' h1t' h2t' h3t' hdiff hfull
      have hclear := trajectory_clear_B htraj
      have hreach := trajectory_reachable_B hfr htraj
      have hdiff' : ((colEmptyCount (Bcur.insert q) j.val 1 h (α + 2) : ℤ) -
          (colEmptyCount (Bcur.insert q) j.val 2 h (α + 1) : ℤ)) % 4 ≠ 0 := by
        by_cases hI : q.kind = .I
        · rcases i_cells_cases hI with ⟨x₀, y₀, hfin⟩ | ⟨x₀, y₀, hfin⟩
          · by_cases hy_in : h ≤ y₀ ∧ y₀ < h + (α + 2)
            · by_cases hhit_j : (6 * (j.val : ℤ) + 1, y₀) ∈ q.cells ∨ (6 * (j.val : ℤ) + 2, y₀) ∈ q.cells
              · have hx0_bounds : x₀ = 6 * (j.val : ℤ) ∨ x₀ = 6 * (j.val : ℤ) + 1 := by
                  have hL := bucketCell_left_wall_B hfr j (y := y₀) (by omega) (by omega)
                  have hR := bucketCell_right_wall_B hfr j (y := y₀) (by omega) (by omega)
                  have hmem_of : ∀ x : ℤ, x = x₀ ∨ x = x₀ + 1 ∨ x = x₀ + 2 ∨ x = x₀ + 3 → (x, y₀) ∈ q.cells := by
                    intro x hx; apply List.mem_toFinset.mp; rw [hfin]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                    rcases hx with rfl | rfl | rfl | rfl <;> simp
                  have hxb : x₀ ≤ 6 * (j.val : ℤ) + 2 ∧ 6 * (j.val : ℤ) + 1 ≤ x₀ + 3 := by
                    rcases hhit_j with hm | hm <;> (
                      have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                      rcases hm' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega)
                  have hx0_ge : 6 * (j.val : ℤ) ≤ x₀ := by
                    by_contra hlt; push Not at hlt
                    have hc := hclear _ (hmem_of (6 * (j.val : ℤ) - 1) (by omega))
                    unfold bucketCell at hL
                    have heq : (6 * (j.val : ℤ) + -1, y₀) = (6 * (j.val : ℤ) - 1, y₀) := by ext <;> omega
                    rw [heq, hc] at hL; cases hL
                  have hneR : x₀ ≠ 6 * (j.val : ℤ) + 2 := by
                    intro hx; have hc := hclear _ (hmem_of (6 * (j.val : ℤ) + 5) (by omega))
                    unfold bucketCell at hR; rw [hR] at hc; cases hc
                  omega
                by_cases hy_low : y₀ < h + (α + 1)
                · set k0 : ℕ := (y₀ - h).toNat
                  have h1_mem : (6 * (j.val : ℤ) + 1, y₀) ∈ q.cells := by
                    apply List.mem_toFinset.mp; rw [hfin]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
                    rcases hx0_bounds with rfl | rfl <;> omega
                  have h2_mem : (6 * (j.val : ℤ) + 2, y₀) ∈ q.cells := by
                    apply List.mem_toFinset.mp; rw [hfin]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
                    rcases hx0_bounds with rfl | rfl <;> omega
                  have hdec : ∀ (col : ℤ) (n : ℕ), (col = 1 ∨ col = 2) → k0 < n →
                      h + n ≤ b → (6 * (j.val : ℤ) + col, y₀) ∈ q.cells →
                      colEmptyCount (Bcur.insert q) j.val col h n + 1 = colEmptyCount Bcur j.val col h n := by
                    intro col n _ hk0n _ hmq
                    set E0 := (Finset.range n).filter fun k : ℕ => bucketCell Bcur j.val col (h + (k : ℤ)) = false
                    set E1 := (Finset.range n).filter fun k : ℕ => bucketCell (Bcur.insert q) j.val col (h + (k : ℤ)) = false
                    have hk0_in : k0 ∈ E0 := by
                      rw [Finset.mem_filter, Finset.mem_range]
                      refine ⟨hk0n, ?_⟩
                      have heq : h + (k0 : ℤ) = y₀ := by omega
                      rw [heq]; exact hclear _ hmq
                    have hE1 : E1 = E0.erase k0 := by
                      ext k; simp only [E1, E0, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
                      constructor
                      · intro ⟨hk, hf⟩
                        have hne : k ≠ k0 := by
                          rintro rfl
                          have heq : h + (k0 : ℤ) = y₀ := by omega
                          rw [heq] at hf
                          have ht := bucketCell_insert_of_mem hfr (by omega) (by omega) (by omega) (by omega) hmq
                          rw [ht] at hf; cases hf
                        have hf0 : bucketCell Bcur j.val col (h + k) = false := by
                          cases hB : bucketCell Bcur j.val col (h + k) with
                          | false => rfl
                          | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
                        exact ⟨hne, hk, hf0⟩
                      · rintro ⟨hne, hk, hf0⟩
                        refine ⟨hk, bucketCell_insert_of_not_mem hf0 ?_⟩
                        intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                        rcases hm' with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
                    change E1.card + 1 = E0.card
                    rw [hE1, Finset.card_erase_of_mem hk0_in]
                    have := Finset.card_pos.mpr ⟨k0, hk0_in⟩; omega
                  have hd1 := hdec 1 (α + 2) (Or.inl rfl) (by omega) (by omega) h1_mem
                  have hd2 := hdec 2 (α + 1) (Or.inr rfl) (by omega) (by omega) h2_mem
                  omega
                · have hy_eq : y₀ = h + α + 1 := by omega
                  have h3m : (6 * (j.val : ℤ) + 3, h + α + 1) ∈ q.cells := by
                    rw [← hy_eq]; apply List.mem_toFinset.mp; rw [hfin]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
                    rcases hx0_bounds with rfl | rfl <;> omega
                  have hc := hclear _ h3m; unfold bucketCell at h3t'; rw [h3t'] at hc; cases hc
              · push Not at hhit_j
                have hsame : ∀ (col : ℤ) (n : ℕ), (col = 1 ∨ col = 2) →
                    colEmptyCount (Bcur.insert q) j.val col h n = colEmptyCount Bcur j.val col h n := by
                  intro col n hcol
                  unfold colEmptyCount; congr 1; ext k
                  simp only [Finset.mem_filter, Finset.mem_range]
                  refine and_congr_right fun _ => ?_
                  constructor
                  · intro hf; cases hB : bucketCell Bcur j.val col (h + k) with
                    | false => rfl
                    | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
                  · intro hf; apply bucketCell_insert_of_not_mem hf
                    intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                    have hy_eq : h + k = y₀ := by rcases hm' with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
                    rw [hy_eq] at hm
                    rcases hcol with rfl | rfl
                    · exact hhit_j.1 hm
                    · exact hhit_j.2 hm
                rw [hsame 1 (α + 2) (Or.inl rfl), hsame 2 (α + 1) (Or.inr rfl)]
                exact hdiff
            · have hsame : ∀ (col : ℤ) (n : ℕ), n ≤ α + 2 →
                  colEmptyCount (Bcur.insert q) j.val col h n = colEmptyCount Bcur j.val col h n := by
                intro col n _
                unfold colEmptyCount; congr 1; ext k
                simp only [Finset.mem_filter, Finset.mem_range]
                refine and_congr_right fun _ => ?_
                constructor
                · intro hf; cases hB : bucketCell Bcur j.val col (h + k) with
                  | false => rfl
                  | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
                · intro hf; apply bucketCell_insert_of_not_mem hf
                  intro hm; have hm' := List.mem_toFinset.mpr hm; rw [hfin] at hm'
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
                  rcases hm' with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
              rw [hsame 1 (α + 2) le_rfl, hsame 2 (α + 1) (by omega)]
              exact hdiff
          · have h1 := hvert_mod4 Bcur q 1 (α + 2) hfr (Or.inl rfl) (by omega) hclear h1b'
              (by convert h1t' using 2; omega) ⟨x₀, y₀, hfin⟩
            have h2 := hvert_mod4 Bcur q 2 (α + 1) hfr (Or.inr rfl) (by omega) hclear h2b'
              (by convert h2t' using 2; omega) ⟨x₀, y₀, hfin⟩
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
        · have hnot_low : ∀ (col : ℤ) (n : ℕ), ((col = 1 ∧ n = α + 2) ∨ (col = 2 ∧ n = α + 1)) →
              ∀ k < n, (6 * (j.val : ℤ) + col, h + k) ∉ q.cells := by
            intro col n hcn k hk hm
            have hcond := hReason.2.2.2.1 Bcur s H hfr j b ib q.kind q hbalc hbalc.2.1 hI hreach
              (6 * (j.val : ℤ) + col, h + k) hm (by rcases hcn with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega)
              (by rcases hcn with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega)
              (by rcases hcn with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega)
            dsimp at hcond
            rcases hcond.2 with h1 | h2
            · rcases hcn with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
            · rcases hcn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · have hb_eq : b = h + α + 2 := by omega
                have hcol_eq : (1 : ℤ) = (ib.val : ℤ) := by omega
                have hbal_f := hbalc.2.2 ib
                simp only [ne_eq, not_true_eq_false, decide_false] at hbal_f
                rw [hb_eq, ← hcol_eq] at hbal_f; rw [hbal_f] at h1t'; cases h1t'
              · omega
          have hsame : ∀ (col : ℤ) (n : ℕ), ((col = 1 ∧ n = α + 2) ∨ (col = 2 ∧ n = α + 1)) →
              colEmptyCount (Bcur.insert q) j.val col h n = colEmptyCount Bcur j.val col h n := by
            intro col n hcn
            unfold colEmptyCount; congr 1; ext k
            simp only [Finset.mem_filter, Finset.mem_range]
            refine and_congr_right fun hk => ?_
            constructor
            · intro hf; cases hB : bucketCell Bcur j.val col (h + k) with
              | false => rfl
              | true => rw [bucketCell_insert_of_true hB] at hf; cases hf
            · intro hf; exact bucketCell_insert_of_not_mem hf (hnot_low col n hcn k hk)
          rw [hsame 1 (α + 2) (Or.inl ⟨rfl, rfl⟩), hsame 2 (α + 1) (Or.inr ⟨rfl, rfl⟩)]
          exact hdiff
      rcases balcony_insert (q := q) hbalc with hbal' | ⟨hb0, hb1, hb2⟩
      · exact ih (bucketFrame_insert hfr) hbal'
          (bucketCell_insert_of_true h1b') (bucketCell_insert_of_true h2b')
          (bucketCell_insert_of_true h1t') (bucketCell_insert_of_true h2t')
          (bucketCell_insert_of_true h3t') hdiff' hfull
      · have hne0 : 0 < colEmptyCount (Bcur.insert q) j.val 1 h (α + 2) ∨
            0 < colEmptyCount (Bcur.insert q) j.val 2 h (α + 1) := by omega
        rcases hne0 with hp | hp
        · obtain ⟨k, hk⟩ := Finset.card_pos.mp hp
          rw [Finset.mem_filter, Finset.mem_range] at hk
          have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
            hbalc.1 hbalc.2.1 (by omega) (by omega) (by omega) (by omega) hb0 hb1 hb2 hk.2
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull⟩
        · obtain ⟨k, hk⟩ := Finset.card_pos.mp hp
          rw [Finset.mem_filter, Finset.mem_range] at hk
          have hhole := hasHole_of_closed_012 (bucketFrame_insert hfr) j
            hbalc.1 hbalc.2.1 (by omega) (by omega) (by omega) (by omega) hb0 hb1 hb2 hk.2
          exact anyPlay_unfillable_of_hasHole hReason (bucketFrame_insert hfr) j hhole ⟨B', hrest, hfull⟩
  rintro ⟨B', hplay, hfull⟩
  exact hgen hplay hframe hbal h1b h2b h1_top h2_top hcap3 hdiff0 hfull

/-! ### Reusable Splitters: `sameCellSet`, `split_012_or_openNotch`, `sq_012_cases`, `isoNotchOcc` -/

def sameCellSet (cs tgt : List Cell) : Bool :=
  cs.all (fun c => decide (c ∈ tgt)) && tgt.all (fun c => decide (c ∈ cs))

def allInTargets (css : List (List Cell)) (tgts : List (List Cell)) : Bool :=
  css.all fun cs => tgts.any fun tgt => sameCellSet cs tgt

lemma mem_targets_of_rel012 {R : Rotation} {U : Board} {s' H' : ℕ}
    (hframe : BucketFrame U s' H') {j : Fin s'} {t : Piece} {u : PieceState}
    (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U t u)
    (hx_012 : ∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3)
    {y_ref yLo yHi : ℤ} {occ : ℤ → ℤ → Bool}
    (hy_box : ∀ z ∈ u.cells, y_ref + yLo ≤ z.2 ∧ z.2 ≤ y_ref + yHi)
    (hocc_eq : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → yLo - 1 ≤ dy → dy ≤ yHi →
      bucketCell U j.val dx (y_ref + dy) = occ dx dy)
    {tgts : List (List Cell)}
    (hdec : allInTargets (validRelPlacements012 t occ yLo yHi) tgts = true) :
    ∃ tgt ∈ tgts, ∀ x y : ℤ,
      ((6 * (j.val : ℤ) + x, y) ∈ u.cells ↔ (x, y - y_ref) ∈ tgt) := by
  obtain ⟨hcl, _, x_s, y_s, hx0, _, _, _, hms, hocc_s⟩ :=
    exists_bucket_support hframe (j := j) hin hy_u htraj
  have hx3 : x_s < 3 := by have := hx_012 _ hms; dsimp at this; omega
  have hmem := mem_validRelPlacements012 (trajectory_kind_eq htraj) hx_012 hcl
    ⟨x_s, y_s, hx0, hx3, hms, hocc_s⟩ hy_box hocc_eq
  unfold allInTargets at hdec
  rw [List.all_eq_true] at hdec
  have hany := hdec _ hmem
  rw [List.any_eq_true] at hany
  rcases hany with ⟨tgt, htgt, hsame⟩
  unfold sameCellSet at hsame
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hsame
  refine ⟨tgt, htgt, fun x y => ?_⟩
  rw [mem_cells_iff_of_relMap rfl x y]
  constructor
  · intro hm; exact of_decide_eq_true (hsame.1 _ hm)
  · intro hm; exact of_decide_eq_true (hsame.2 _ hm)

/-- Universal Open-Notch vs 3-Column Splitter: for any pattern `pat` with `pat 3 y = pat 4 y`,
every fillable placement `u` either stays in cols `0, 1, 2` (`hx_012`) or enters an `OpenNotch` `r`
as horizontal `.I` or notch `.LG` (`addNotchLG pat r`)! -/
lemma split_012_or_openNotch {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j.val H' pat)
    (hsym34 : ∀ y : ℕ, pat 3 y = pat 4 y)
    {t : Piece} (ht : t ∈ ([.LG, .LS, .Sq, .I] : List Piece))
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U t u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    (∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3) ∨
    (∃ r : ℕ, r < H' ∧ (r + 1) % 6 = 5 ∧ pat 3 r = false ∧ OpenNotch U j.val H' r ∧
      ((t = .I ∧ ∀ x y : ℤ,
          (6 * (j.val : ℤ) + x, y) ∈ u.cells ↔ (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) ∧ y = (r : ℤ)) ∨
       (t = .LG ∧ BucketPattern (U.insert u) j.val H' (addNotchLG pat r) ∧ ∀ x y : ℤ,
          (6 * (j.val : ℤ) + x, y) ∈ u.cells ↔
            (x = 2 ∧ y = (r : ℤ) + 1) ∨ (2 ≤ x ∧ x ≤ 4 ∧ y = (r : ℤ))))) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  have hcl := (trajectory_clear_and_blocked htraj).1
  have huk := trajectory_kind_eq htraj
  by_cases hx_012 : ∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3
  · exact Or.inl hx_012
  · right
    push Not at hx_012
    rcases hx_012 with ⟨z₀, hz₀, hzx_ge⟩
    have hzx_in := hin z₀ hz₀
    have hzy := hy_u z₀ hz₀
    have hocc_z := hcl z₀ hz₀
    have hx5_ne : z₀.1 ≠ 6 * (j.val : ℤ) + 5 := by
      intro hx5
      have hrw := bucketCell_right_wall_B hframe j_pad hzy.1 hzy.2
      unfold bucketCell at hrw
      have heq : (6 * (j.val : ℤ) + 5, z₀.2) = z₀ := by ext <;> omega
      rw [heq, hocc_z] at hrw; cases hrw
    have hx34 : z₀.1 = 6 * (j.val : ℤ) + 3 ∨ z₀.1 = 6 * (j.val : ℤ) + 4 := by
      have := hzx_ge hzx_in.1; omega
    set r : ℕ := z₀.2.toNat
    have hr_cast : (r : ℤ) = z₀.2 := Int.toNat_of_nonneg hzy.1
    have hrH : r < H' := by omega
    have hrmod : (r + 1) % 6 = 5 := by
      by_contra hnm
      have hw := bucketCell_notch_wall_B hframe j_pad hzy.1 hzy.2 (by omega)
      rcases hx34 with hx3 | hx4
      · have heq : (6 * (j.val : ℤ) + 3, z₀.2) = z₀ := by ext <;> omega
        have ht := hw.1; unfold bucketCell at ht; dsimp [j_pad] at ht; rw [heq, hocc_z] at ht; cases ht
      · have heq : (6 * (j.val : ℤ) + 4, z₀.2) = z₀ := by ext <;> omega
        have ht := hw.2; unfold bucketCell at ht; dsimp [j_pad] at ht; rw [heq, hocc_z] at ht; cases ht
    have hrmodZ : ((r : ℤ) + 1) % 6 = 5 := by omega
    have hpat3 : pat 3 r = false := by
      rcases hx34 with hx3 | hx4
      · have hev := bucketPattern_eval hframe hpat (x := 3) (y := r) (by omega) (by omega) (by omega) (by omega)
        have heq : (6 * (j.val : ℤ) + 3, (r : ℤ)) = z₀ := by ext <;> omega
        unfold bucketCell at hev; rw [heq, hocc_z] at hev
        simpa [hrmodZ] using hev.symm
      · rw [hsym34 r]
        have hev := bucketPattern_eval hframe hpat (x := 4) (y := r) (by omega) (by omega) (by omega) (by omega)
        have heq : (6 * (j.val : ℤ) + 4, (r : ℤ)) = z₀ := by ext <;> omega
        unfold bucketCell at hev; rw [heq, hocc_z] at hev
        simpa [hrmodZ] using hev.symm
    have hopen : OpenNotch U j.val H' r := by
      refine ⟨by omega, by omega, hrmodZ, ?_, ?_⟩
      · have hev := bucketPattern_eval hframe hpat (x := 3) (y := r) (by omega) (by omega) (by omega) (by omega)
        simpa [hrmodZ, hpat3] using hev
      · have hev := bucketPattern_eval hframe hpat (x := 4) (y := r) (by omega) (by omega) (by omega) (by omega)
        have hp4 : pat 4 r = false := by rwa [← hsym34 r]
        simpa [hrmodZ, hp4] using hev
    have htouch : (6 * (j.val : ℤ) + 3, (r : ℤ)) ∈ u.cells ∨ (6 * (j.val : ℤ) + 4, (r : ℤ)) ∈ u.cells := by
      rcases hx34 with hx3 | hx4
      · left; convert hz₀ using 1; ext <;> omega
      · right; convert hz₀ using 1; ext <;> omega
    rcases classify_at_open_notch hframe j_pad hopen (by rwa [huk]) hcl htouch with
      hhole | ⟨hI, hfin⟩ | ⟨hLG, hfin⟩
    · exact absurd hfill (not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole)
    · refine ⟨r, hrH, hrmod, hpat3, hopen, Or.inl ⟨by rwa [← huk], fun x y => ?_⟩⟩
      rw [← List.mem_toFinset, hfin]
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, j_pad]
      omega
    · have hiff : ∀ x y : ℤ,
          (6 * (j.val : ℤ) + x, y) ∈ u.cells ↔
            (x = 2 ∧ y = (r : ℤ) + 1) ∨ (2 ≤ x ∧ x ≤ 4 ∧ y = (r : ℤ)) := by
        intro x y
        rw [← List.mem_toFinset, hfin]
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, j_pad]
        omega
      have hpat' : BucketPattern (U.insert u) j.val H' (addNotchLG pat r) := by
        apply bucketPattern_congr (bucketPattern_insert_same hframe (j := j_pad) hin hy_u hpat)
        intro x y _ _
        unfold addNotchLG
        congr 1
        rw [decide_eq_decide]
        rw [hiff x y]
        omega
      exact ⟨r, hrH, hrmod, hpat3, hopen, Or.inr ⟨by rwa [← huk], hpat', hiff⟩⟩

/-- Exact `.Sq` characterization on any `pat` with `pat 3 y = pat 4 y`! -/
lemma sq_012_cases {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j.val H' pat)
    (hsym34 : ∀ y : ℕ, pat 3 y = pat 4 y)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    ∃ x₀ y₀ : ℕ, (x₀ = 0 ∨ x₀ = 1) ∧ y₀ + 1 < H' ∧
      (∀ x y : ℤ, (6 * (j.val : ℤ) + x, y) ∈ u.cells ↔
        ((x = (x₀ : ℤ) ∨ x = (x₀ : ℤ) + 1) ∧ (y = (y₀ : ℤ) ∨ y = (y₀ : ℤ) + 1))) ∧
      pat x₀ y₀ = false ∧ pat (x₀ + 1) y₀ = false ∧
      pat x₀ (y₀ + 1) = false ∧ pat (x₀ + 1) (y₀ + 1) = false ∧
      (y₀ = 0 ∨ pat x₀ (y₀ - 1) = true ∨ pat (x₀ + 1) (y₀ - 1) = true) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat hsym34 (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · obtain ⟨hcl, _, x_s, y_s, hx0_s, _, _, _, hms, hocc_s⟩ :=
      exists_bucket_support hframe (j := j_pad) hin hy_u htraj
    have huk := trajectory_kind_eq htraj
    have hcells : u.cells = [(u.position.1, u.position.2), (u.position.1 + 1, u.position.2),
        (u.position.1, u.position.2 - 1), (u.position.1 + 1, u.position.2 - 1)] := by
      simp [PieceState.cells, huk, Piece.base, sub_eq_add_neg]
    have htl := hx_012 (u.position.1, u.position.2) (by simp [hcells])
    have hbr := hx_012 (u.position.1 + 1, u.position.2 - 1) (by simp [hcells])
    have htl_y := hy_u (u.position.1, u.position.2) (by simp [hcells])
    have hbr_y := hy_u (u.position.1 + 1, u.position.2 - 1) (by simp [hcells])
    dsimp at htl hbr htl_y hbr_y
    set x₀ : ℕ := (u.position.1 - 6 * (j.val : ℤ)).toNat
    set y₀ : ℕ := (u.position.2 - 1).toNat
    have hx0_or : x₀ = 0 ∨ x₀ = 1 := by omega
    have hy0_lt : y₀ + 1 < H' := by omega
    have hpx : u.position.1 = 6 * (j.val : ℤ) + (x₀ : ℤ) := by omega
    have hpy : u.position.2 = (y₀ : ℤ) + 1 := by omega
    have hiff : ∀ x y : ℤ, (6 * (j.val : ℤ) + x, y) ∈ u.cells ↔
        ((x = (x₀ : ℤ) ∨ x = (x₀ : ℤ) + 1) ∧ (y = (y₀ : ℤ) ∨ y = (y₀ : ℤ) + 1)) := by
      intro x y; rw [hcells, hpx, hpy]
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      omega
    have hpat_f : ∀ dx dy : ℕ, dx < 3 → dy < H' →
        (6 * (j.val : ℤ) + (dx : ℤ), (dy : ℤ)) ∈ u.cells → pat dx dy = false := by
      intro dx dy hdx3 hdyH hm
      have hev := bucketPattern_eval_012 hframe hpat (x := dx) (y := dy)
        (by omega) (by omega) (by omega) (by omega)
      unfold bucketCell at hev; rw [hcl _ hm] at hev
      simpa using hev.symm
    refine ⟨x₀, y₀, hx0_or, hy0_lt, hiff,
      hpat_f x₀ y₀ (by omega) (by omega) ((hiff _ _).mpr ⟨Or.inl rfl, Or.inl rfl⟩),
      hpat_f (x₀ + 1) y₀ (by omega) (by omega) ((hiff _ _).mpr ⟨Or.inr (by omega), Or.inl rfl⟩),
      hpat_f x₀ (y₀ + 1) (by omega) (by omega) ((hiff _ _).mpr ⟨Or.inl rfl, Or.inr (by omega)⟩),
      hpat_f (x₀ + 1) (y₀ + 1) (by omega) (by omega) ((hiff _ _).mpr ⟨Or.inr (by omega), Or.inr (by omega)⟩), ?_⟩
    by_cases hyz : y₀ = 0
    · exact Or.inl hyz
    · right
      have hms' := (hiff x_s y_s).mp hms
      have hys_eq : y_s = (y₀ : ℤ) := by
        rcases hms'.2 with rfl | rfl
        · rfl
        · exfalso
          rcases hms'.1 with rfl | rfl
          · have hf := hpat_f x₀ y₀ (by omega) (by omega) ((hiff _ _).mpr ⟨Or.inl rfl, Or.inl rfl⟩)
            have hev := bucketPattern_eval_012 hframe hpat (x := x₀) (y := y₀)
              (by omega) (by omega) (by omega) (by omega)
            have hy_sub : (y₀ : ℤ) + 1 - 1 = (y₀ : ℤ) := by omega
            rw [hy_sub] at hocc_s; dsimp [j_pad] at hocc_s
            rw [hocc_s] at hev; simp [hf] at hev
          · have hf := hpat_f (x₀ + 1) y₀ (by omega) (by omega) ((hiff _ _).mpr ⟨Or.inr (by omega), Or.inl rfl⟩)
            have hev := bucketPattern_eval_012 hframe hpat (x := (x₀ : ℤ) + 1) (y := y₀)
              (by omega) (by omega) (by omega) (by omega)
            have hy_sub : (y₀ : ℤ) + 1 - 1 = (y₀ : ℤ) := by omega
            rw [hy_sub] at hocc_s; dsimp [j_pad] at hocc_s
            rw [hocc_s] at hev
            have hxt : ((x₀ : ℤ) + 1).toNat = x₀ + 1 := by omega
            rw [hxt, Int.toNat_natCast, hf] at hev; cases hev
      rw [hys_eq] at hocc_s; dsimp [j_pad] at hocc_s
      rcases hms'.1 with rfl | rfl
      · left
        have hev := bucketPattern_eval_012 hframe hpat (x := x₀) (y := (y₀ : ℤ) - 1)
          (by omega) (by omega) (by omega) (by omega)
        rw [hocc_s] at hev
        have hyt : ((y₀ : ℤ) - 1).toNat = y₀ - 1 := by omega
        rw [Int.toNat_natCast, hyt] at hev; exact hev.symm
      · right
        have hev := bucketPattern_eval_012 hframe hpat (x := (x₀ : ℤ) + 1) (y := (y₀ : ℤ) - 1)
          (by omega) (by omega) (by omega) (by omega)
        rw [hocc_s] at hev
        have hxt : ((x₀ : ℤ) + 1).toNat = x₀ + 1 := by omega
        have hyt : ((y₀ : ℤ) - 1).toNat = y₀ - 1 := by omega
        rw [hxt, hyt] at hev; exact hev.symm
  · cases hI
  · cases hLG

/-- Bounding box helper for 3-column placements on `pat` with floor `y_floor` and ceiling `y_top`. -/
lemma box_of_012_bounds {R : Rotation} {U : Board} {s' H' : ℕ}
    (hframe : BucketFrame U s' H') {j : Fin s'} {t : Piece} {u : PieceState}
    {pat : ℕ → ℕ → Bool} (hpat : BucketPattern U j.val H' pat)
    {y_floor y_top : ℕ}
    (hfloor : ∀ x y : ℕ, x < 3 → y < y_floor → pat x y = true)
    (htop : ∀ x y : ℕ, x < 3 → y_top ≤ y → pat x y = false)
    (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U t u)
    (hx_012 : ∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3) :
    ∀ z ∈ u.cells, (y_floor : ℤ) ≤ z.2 ∧ z.2 ≤ (y_top : ℤ) + 3 := by
  obtain ⟨hcl, _, x_s, y_s, hx0, _, hy0_s, hyH_s, hms, hocc_s⟩ :=
    exists_bucket_support hframe (j := j) hin hy_u htraj
  have hx3 : x_s < 3 := by have := hx_012 _ hms; dsimp at this; omega
  have hys_le : y_s ≤ (y_top : ℤ) := by
    by_cases hy0 : y_s = 0
    · omega
    · have hev := bucketPattern_eval_012 hframe hpat (x := x_s) (y := y_s - 1)
        hx0 hx3 (by omega) (by omega)
      rw [hocc_s] at hev
      by_contra hgt; push Not at hgt
      have hf := htop x_s.toNat (y_s - 1).toNat (by omega) (by omega)
      rw [hf] at hev; cases hev
  intro z hz
  have hzx := hx_012 z hz
  have hzy := hy_u z hz
  have hd := (piece_diameter_le_three u hz hms).2
  rw [abs_le] at hd
  refine ⟨?_, by dsimp at hd; omega⟩
  by_contra hlt; push Not at hlt
  have hev := bucketPattern_eval_012 hframe hpat (x := z.1 - 6 * (j.val : ℤ)) (y := z.2)
    (by omega) (by omega) hzy.1 (by omega)
  have ht := hfloor (z.1 - 6 * (j.val : ℤ)).toNat z.2.toNat (by omega) (by omega)
  unfold bucketCell at hev
  have hz_eq : (6 * (j.val : ℤ) + (z.1 - 6 * (j.val : ℤ)), z.2) = z := by ext <;> omega
  rw [hz_eq, hcl z hz, ht] at hev; cases hev

/-- Local occupancy around an isolated notch `LG` at `y_ref = r`. -/
def isoNotchOcc (dx dy : ℤ) : Bool :=
  decide (dx = 2 ∧ (dy = 0 ∨ dy = 1))

lemma isoNotch_LS_check :
    allInTargets (validRelPlacements012 .LS isoNotchOcc (-1) 5)
      [[(1, 1), (1, 2), (2, 2), (2, 3)],
       [(1, 2), (2, 2), (0, 3), (1, 3)]] = true := by decide

lemma isoNotch_LG_check :
    allInTargets (validRelPlacements012 .LG isoNotchOcc (-1) 5)
      [[(0, 2), (1, 2), (2, 2), (0, 3)],
       [(0, 3), (1, 3), (2, 3), (2, 2)],
       [(1, 2), (2, 2), (2, 3), (2, 4)],
       [(1, 0), (1, 1), (1, 2), (2, 2)]] = true := by decide

/-- Disjoint Base vs Isolated-Notch Splitter on `addNotchLG basePat r` when `y_top + 4 ≤ r`! -/
lemma split_base_or_isoNotch {R : Rotation} {U : Board} {s' H' : ℕ}
    (hframe : BucketFrame U s' H') {j : Fin s'} {t : Piece} {u : PieceState}
    {basePat : ℕ → ℕ → Bool} {r : ℕ}
    (hrH6 : r + 6 ≤ H')
    (hpat : BucketPattern U j.val H' (addNotchLG basePat r))
    {y_floor y_top : ℕ}
    (hfy : y_floor ≤ y_top)
    (hfloor : ∀ x y : ℕ, x < 3 → y < y_floor → basePat x y = true)
    (htop : ∀ x y : ℕ, x < 3 → y_top ≤ y → basePat x y = false)
    (hr_sep : y_top + 4 ≤ r)
    (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U t u)
    (hx_012 : ∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3) :
    ((∀ z ∈ u.cells, (y_floor : ℤ) ≤ z.2 ∧ z.2 ≤ (y_top : ℤ) + 3) ∧
      (∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ (y_top : ℤ) + 3 - (y_floor : ℤ) →
        bucketCell U j.val dx ((y_floor : ℤ) + dy) =
          (if (y_floor : ℤ) + dy < 0 then true else basePat dx.toNat ((y_floor : ℤ) + dy).toNat))) ∨
    ((∀ z ∈ u.cells, (r : ℤ) - 1 ≤ z.2 ∧ z.2 ≤ (r : ℤ) + 5) ∧
      (∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -2 ≤ dy → dy ≤ 5 →
        bucketCell U j.val dx ((r : ℤ) + dy) = isoNotchOcc dx dy)) := by
  obtain ⟨hcl, _, x_s, y_s, hx0, _, hy0_s, hyH_s, hms, hocc_s⟩ :=
    exists_bucket_support hframe (j := j) hin hy_u htraj
  have hx3 : x_s < 3 := by have := hx_012 _ hms; dsimp at this; omega
  by_cases hys_low : y_s ≤ (y_top : ℤ)
  · left
    refine ⟨?_, ?_⟩
    · intro z hz
      have hzx := hx_012 z hz
      have hzy := hy_u z hz
      have hd := (piece_diameter_le_three u hz hms).2
      rw [abs_le] at hd
      refine ⟨?_, by dsimp at hd; omega⟩
      by_contra hlt; push Not at hlt
      have hev := bucketPattern_eval_012 hframe hpat (x := z.1 - 6 * (j.val : ℤ)) (y := z.2)
        (by omega) (by omega) hzy.1 (by omega)
      have ht : addNotchLG basePat r (z.1 - 6 * (j.val : ℤ)).toNat z.2.toNat = true := by
        unfold addNotchLG; rw [hfloor _ _ (by omega) (by omega)]; rfl
      unfold bucketCell at hev
      have hz_eq : (6 * (j.val : ℤ) + (z.1 - 6 * (j.val : ℤ)), z.2) = z := by ext <;> omega
      rw [hz_eq, hcl z hz, ht] at hev; cases hev
    · intro dx dy hdx0 hdx3 hdy1 hdy2
      by_cases hneg : (y_floor : ℤ) + dy < 0
      · rw [if_pos hneg]; exact bucketPattern_eval_neg_y hneg
      · rw [if_neg hneg]
        rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
        unfold addNotchLG
        have hnr : ¬ ((dx.toNat = 2 ∧ ((y_floor : ℤ) + dy).toNat = r + 1) ∨
            (2 ≤ dx.toNat ∧ dx.toNat ≤ 4 ∧ ((y_floor : ℤ) + dy).toNat = r)) := by omega
        rw [decide_eq_false_iff_not.mpr hnr, Bool.or_false]
  · right
    push Not at hys_low
    have hys_eq : y_s = (r : ℤ) + 2 := by
      have hev := (bucketPattern_eval_012 hframe hpat (x := x_s) (y := y_s - 1)
        hx0 hx3 (by omega) (by omega)).symm
      rw [hocc_s] at hev
      unfold addNotchLG at hev
      rw [htop x_s.toNat (y_s - 1).toNat (by omega) (by omega), Bool.false_or, decide_eq_true_eq] at hev
      rcases hev with ⟨hx2, hyr1⟩ | ⟨_, _, hyr⟩
      · omega
      · exfalso
        have hxs2 : x_s = 2 := by omega
        have hys1 : y_s = (r : ℤ) + 1 := by omega
        rw [hxs2, hys1] at hms
        have hev2 := bucketPattern_eval_012 hframe hpat (x := 2) (y := (r : ℤ) + 1)
          (by omega) (by omega) (by omega) (by omega)
        unfold bucketCell at hev2; rw [hcl _ hms] at hev2
        unfold addNotchLG at hev2
        have ht2 : decide (((2 : ℤ).toNat = 2 ∧ ((r : ℤ) + 1).toNat = r + 1) ∨
            (2 ≤ (2 : ℤ).toNat ∧ (2 : ℤ).toNat ≤ 4 ∧ ((r : ℤ) + 1).toNat = r)) = true := by
          rw [decide_eq_true_eq]; left; omega
        rw [ht2, Bool.or_true] at hev2; cases hev2
    refine ⟨?_, ?_⟩
    · intro z hz
      have hd := (piece_diameter_le_three u hz hms).2
      rw [abs_le] at hd
      dsimp at hd; omega
    · intro dx dy hdx0 hdx3 hdy1 hdy2
      rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
      unfold addNotchLG isoNotchOcc
      rw [htop dx.toNat ((r : ℤ) + dy).toNat (by omega) (by omega), Bool.false_or]
      rw [decide_eq_decide]; omega

/-! ### Symmetry of Columns 3 & 4 for Standard Patterns -/

lemma unpreppedPat_sym34 (h gap : ℕ) (hgap : gap = 0 ∨ gap = 2) (y : ℕ) :
    unpreppedPat h gap 3 y = unpreppedPat h gap 4 y := by
  unfold unpreppedPat; rw [decide_eq_decide]; rcases hgap with rfl | rfl <;> omega

lemma overflatPat_sym34 (h y : ℕ) : overflatPat h 3 y = overflatPat h 4 y := by
  unfold overflatPat; rw [decide_eq_decide]; omega

lemma triggerHappyPat_sym34 (h y : ℕ) : triggerHappyPat h 3 y = triggerHappyPat h 4 y := by
  unfold triggerHappyPat; rw [decide_eq_decide]; omega

lemma iUpPat_sym34 (h y : ℕ) : iUpPat h 3 y = iUpPat h 4 y := by
  unfold iUpPat unpreppedPat; simp

lemma shortPlateauPat_sym34 (h y : ℕ) : shortPlateauPat h 3 y = shortPlateauPat h 4 y := by
  unfold shortPlateauPat unpreppedPat; simp

lemma tallPlateauPat_sym34 (h y : ℕ) : tallPlateauPat h 3 y = tallPlateauPat h 4 y := by
  unfold tallPlateauPat; rw [decide_eq_decide]; omega

lemma addNotchLG_sym34 {pat : ℕ → ℕ → Bool} (hsym : ∀ y, pat 3 y = pat 4 y) (r y : ℕ) :
    addNotchLG pat r 3 y = addNotchLG pat r 4 y := by
  unfold addNotchLG; rw [hsym y]; simp

lemma weirdPlateauPat_sym34 (h y : ℕ) : weirdPlateauPat h 3 y = weirdPlateauPat h 4 y := by
  unfold weirdPlateauPat
  rw [addNotchLG_sym34 (addNotchLG_sym34 (unpreppedPat_sym34 h 0 (Or.inl rfl)) h) (h + 6) y]
  simp

/-! ### Helper: `FlooredNotch` at `h` on `unpreppedPat h gap` whenever a `Balcony` exists at `b > h`! -/

lemma unfillable_floored_of_unprepped_insert {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h gap : ℕ} {pat : ℕ → ℕ → Bool}
    (hh4 : 4 ≤ h) (hh_lt : h < H') (hmod : (h + 1) % 6 = 5) (hgap : gap = 0 ∨ gap = 2)
    (hpat : BucketPattern U j.val H' pat)
    (hpat_low : ∀ x y : ℕ, x < 5 → (y < h ∨ 3 ≤ x) → y ≤ h → pat x y = unpreppedPat h gap x y)
    {u : PieceState}
    (hno_34h : (6 * (j.val : ℤ) + 3, (h : ℤ)) ∉ u.cells ∧ (6 * (j.val : ℤ) + 4, (h : ℤ)) ∉ u.cells)
    (hno_hm1 : ∀ x : ℤ, 0 ≤ x → x < 3 → (6 * (j.val : ℤ) + x, (h : ℤ) - 1) ∉ u.cells)
    {b : ℤ} {ib : Fin 3} (hb_gt : (h : ℤ) < b)
    (hbal : Balcony (U.insert u) j.val H' b ib) :
    ¬ FillableStrict R s s' H' (U.insert u) j := by
  apply not_fillableStrict_of_flooredNotch hReason hs_le (bucketFrame_insert hframe) j
  have hopenU : OpenNotch U j.val H' h := by
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast,
        hpat_low 3 h (by omega) (Or.inr (by omega)) le_rfl]
      unfold unpreppedPat; simp
    · rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast,
        hpat_low 4 h (by omega) (Or.inr (by omega)) le_rfl]
      unfold unpreppedPat; simp
  have hopen' : OpenNotch (U.insert u) j.val H' h :=
    ⟨hopenU.1, hopenU.2.1, hopenU.2.2.1,
      bucketCell_insert_of_not_mem hopenU.2.2.2.1 hno_34h.1,
      bucketCell_insert_of_not_mem hopenU.2.2.2.2 hno_34h.2⟩
  have hyt : ((h : ℤ) - 1).toNat = h - 1 := by omega
  refine ⟨h, hopen', ⟨b, ib, hb_gt, hbal⟩, ?_⟩
  rcases hgap with rfl | rfl
  · right; left
    have h0 : bucketCell U j.val 0 ((h : ℤ) - 1) = false := by
      rw [bcell0 hframe hpat (by omega) (by omega), hyt, hpat_low 0 (h - 1) (by omega) (Or.inl (by omega)) (by omega)]
      unfold unpreppedPat; simp; omega
    have h1 : bucketCell U j.val 1 ((h : ℤ) - 1) = true := by
      rw [bcell1 hframe hpat (by omega) (by omega), hyt, hpat_low 1 (h - 1) (by omega) (Or.inl (by omega)) (by omega)]
      unfold unpreppedPat; rw [decide_eq_true_eq]; omega
    have h2 : bucketCell U j.val 2 ((h : ℤ) - 1) = true := by
      rw [bcell2 hframe hpat (by omega) (by omega), hyt, hpat_low 2 (h - 1) (by omega) (Or.inl (by omega)) (by omega)]
      unfold unpreppedPat; rw [decide_eq_true_eq]; omega
    exact ⟨bucketCell_insert_of_not_mem h0 (hno_hm1 0 (by omega) (by omega)),
      bucketCell_insert_of_true h1, bucketCell_insert_of_true h2⟩
  · left
    have h0 : bucketCell U j.val 0 ((h : ℤ) - 1) = true := by
      rw [bcell0 hframe hpat (by omega) (by omega), hyt, hpat_low 0 (h - 1) (by omega) (Or.inl (by omega)) (by omega)]
      unfold unpreppedPat; rw [decide_eq_true_eq]; omega
    have h1 : bucketCell U j.val 1 ((h : ℤ) - 1) = true := by
      rw [bcell1 hframe hpat (by omega) (by omega), hyt, hpat_low 1 (h - 1) (by omega) (Or.inl (by omega)) (by omega)]
      unfold unpreppedPat; rw [decide_eq_true_eq]; omega
    have h2 : bucketCell U j.val 2 ((h : ℤ) - 1) = false := by
      rw [bcell2 hframe hpat (by omega) (by omega), hyt, hpat_low 2 (h - 1) (by omega) (Or.inl (by omega)) (by omega)]
      unfold unpreppedPat; simp; omega
    exact ⟨bucketCell_insert_of_true h0, bucketCell_insert_of_true h1,
      bucketCell_insert_of_not_mem h2 (hno_hm1 2 (by omega) (by omega))⟩


/-! ### Appendix C.1.1: Unprepped Buckets (Propositions C.1 – C.4) -/

def relUnpreppedOcc (gap : ℕ) (dx dy : ℤ) : Bool :=
  if dy < 0 then true
  else decide (dy < 4 ∧ dx ≠ (gap : ℤ))

private lemma c1_g0_check :
    allInTargets (validRelPlacements012 .I (relUnpreppedOcc 0) 0 7)
      [[(0, 0), (0, 1), (0, 2), (0, 3)],
       [(1, 4), (1, 5), (1, 6), (1, 7)],
       [(2, 4), (2, 5), (2, 6), (2, 7)]] = true := by decide

private lemma c1_g2_check :
    allInTargets (validRelPlacements012 .I (relUnpreppedOcc 2) 0 7)
      [[(2, 0), (2, 1), (2, 2), (2, 3)],
       [(0, 4), (0, 5), (0, 6), (0, 7)],
       [(1, 4), (1, 5), (1, 6), (1, 7)]] = true := by decide

private lemma c1_g0_top_check :
    allInTargets (validRelPlacements012 .I (relUnpreppedOcc 0) 0 3)
      [[(0, 0), (0, 1), (0, 2), (0, 3)]] = true := by decide

private lemma c1_g2_top_check :
    allInTargets (validRelPlacements012 .I (relUnpreppedOcc 2) 0 3)
      [[(2, 0), (2, 1), (2, 2), (2, 3)]] = true := by decide

private lemma c24_top_check (t : Piece) (ht : t = .LG ∨ t = .LS) (gap : ℕ) (hg : gap = 0 ∨ gap = 2) :
    allInTargets (validRelPlacements012 t (relUnpreppedOcc gap) 0 3) [] = true := by
  rcases ht with rfl | rfl <;> rcases hg with rfl | rfl <;> decide


private lemma c2_g0_check :
    allInTargets (validRelPlacements012 .LG (relUnpreppedOcc 0) 0 7)
      [[(0, 2), (0, 3), (0, 4), (1, 4)],
       [(0, 4), (1, 4), (2, 4), (0, 5)],
       [(0, 5), (1, 5), (2, 5), (2, 4)],
       [(1, 4), (2, 4), (2, 5), (2, 6)],
       [(1, 4), (1, 5), (1, 6), (2, 6)],
       [(0, 4), (1, 4), (1, 5), (1, 6)]] = true := by decide

private lemma c2_g2_check :
    allInTargets (validRelPlacements012 .LG (relUnpreppedOcc 2) 0 7)
      [[(0, 4), (1, 4), (2, 4), (2, 3)],
       [(0, 4), (1, 4), (2, 4), (0, 5)],
       [(1, 4), (2, 4), (2, 5), (2, 6)],
       [(0, 4), (1, 4), (1, 5), (1, 6)],
       [(0, 4), (0, 5), (0, 6), (1, 6)],
       [(1, 4), (1, 5), (1, 6), (2, 6)]] = true := by decide

/-- Helper killing all 3-column `.LG` placements on `unpreppedPat h gap` (reused in `prop_C2` & `prop_C10`!). -/
lemma kill_lg_012_on_unprepped {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h gap : ℕ} {pat : ℕ → ℕ → Bool}
    (hh4 : 4 ≤ h) (hh6 : h + 6 ≤ H') (hmod : (h + 1) % 6 = 5) (hgap : gap = 0 ∨ gap = 2)
    (hpat : BucketPattern U j.val H' pat)
    (hpat_low : ∀ x y : ℕ, x < 5 → y ≤ h + 3 → pat x y = unpreppedPat h gap x y)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LG u)
    (hx_012 : ∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3)
    (hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 4) + 7)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 7 →
      bucketCell U j.val dx (((h : ℤ) - 4) + dy) = relUnpreppedOcc gap dx dy := by
    intro dx dy hdx0 hdx3 hdy1 hdy2
    unfold relUnpreppedOcc
    by_cases hneg : ((h : ℤ) - 4) + dy < 0
    · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
    · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega),
        hpat_low dx.toNat (((h : ℤ) - 4) + dy).toNat (by omega) (by omega)]
      by_cases hdy_neg : dy < 0
      · rw [if_pos hdy_neg]; unfold unpreppedPat; rw [decide_eq_true_eq]; omega
      · rw [if_neg hdy_neg]; unfold unpreppedPat; rw [decide_eq_decide]; omega
  have h3f : bucketCell U j.val 3 h = false := by
    rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast, hpat_low 3 h (by omega) (by omega)]
    unfold unpreppedPat; simp
  have h4f : bucketCell U j.val 4 h = false := by
    rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast, hpat_low 4 h (by omega) (by omega)]
    unfold unpreppedPat; simp
  rcases hgap with rfl | rfl
  · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c2_g0_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    have h0f4 : bucketCell U j.val 0 ((h : ℤ) - 4) = false := by
      rw [bcell0 hframe hpat (by omega) (by omega), hpat_low 0 _ (by omega) (by omega)]
      unfold unpreppedPat; simp; omega
    rcases htgt with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm02 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 2) ∈ u.cells := (hiff 0 ((h : ℤ) - 2)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 4) (y_top := (h : ℤ) - 2)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem h0f4 (mt (hiff 0 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm02)
        (fun y hy0 hylt => bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat hy0 (by omega), hpat_low 1 y.toNat (by omega) (by omega)]
          unfold unpreppedPat; rw [decide_eq_true_eq]; omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := h) (x₀ := 0) (y₀ := (h : ℤ) - 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h0f4 (mt (hiff 0 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 1) ∈ u.cells := (hiff 2 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := (h : ℤ) + 1) (x₀ := 0) (y₀ := (h : ℤ) - 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h0f4 (mt (hiff 0 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := h)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
  · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c2_g2_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    have h2f4 : bucketCell U j.val 2 ((h : ℤ) - 4) = false := by
      rw [bcell2 hframe hpat (by omega) (by omega), hpat_low 2 _ (by omega) (by omega)]
      unfold unpreppedPat; simp; omega
    rcases htgt with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := h) (x₀ := 2) (y₀ := (h : ℤ) - 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h2f4 (mt (hiff 2 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := h) (x₀ := 2) (y₀ := (h : ℤ) - 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h2f4 (mt (hiff 2 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := h)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
    · have hm02 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 2) ∈ u.cells := (hiff 0 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
      have hm12 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 2) ∈ u.cells := (hiff 1 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
      have h2f : bucketCell U j.val 2 ((h : ℤ) + 2) = false := by
        rw [bcell2 hframe hpat (by omega) (by omega),
          show ((h : ℤ) + 2).toNat = h + 2 by omega, hpat_low 2 (h + 2) (by omega) (by omega)]
        unfold unpreppedPat; simp
      have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 2) 2 :=
        mk_balcony_2 (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm02)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
          (bucketCell_insert_of_not_mem h2f (mt (hiff 2 ((h : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
      exact unfillable_floored_of_unprepped_insert hReason hs_le hframe j hh4 (by omega) hmod (Or.inr rfl) hpat
        (fun x y hx _ hy => hpat_low x y hx (by omega))
        ⟨mt (hiff 3 h).mp (not_mem4_of_omega (by omega)),
         mt (hiff 4 h).mp (not_mem4_of_omega (by omega))⟩
        (fun x _ _ => mt (hiff x ((h : ℤ) - 1)).mp (not_mem4_of_omega (by omega)))
        (by omega) hbal hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill

/-- Proposition C.2: `.LG` in `UnpreppedAt` produces `addNotchLG (unpreppedPat h gap) r` with `gap = 2 → h < r`! -/
theorem prop_C2 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hunp : UnpreppedAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LG u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    ∃ gap r : ℕ, 4 ≤ h ∧ h ≤ r ∧ r + 6 ≤ H' ∧ (h + 1) % 6 = 5 ∧ (r + 1) % 6 = 5 ∧
      (gap = 0 ∨ gap = 2) ∧ (gap = 2 → h + 6 ≤ r) ∧
      BucketPattern (U.insert u) j.val H' (addNotchLG (unpreppedPat h gap) r) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  rcases hunp with ⟨gap, hh4, hhH, hmod, hgap, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (unpreppedPat_sym34 h gap hgap)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨r, hrH, hrmod, hpat3r, hopen, ⟨hI, _⟩ | ⟨_, hpat', hiff⟩⟩
  · exfalso
    by_cases hh_eq : h = H'
    · subst h
      have hy_box3 : ∀ z ∈ u.cells, ((H' : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((H' : ℤ) - 4) + 3 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := H' - 4) (y_top := H')
          (fun x y hx hy => by unfold unpreppedPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold unpreppedPat; simp [show ¬ y < H' by omega])
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; have := hy_u z hz; omega
      have hocc3 : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 3 →
          bucketCell U j.val dx (((H' : ℤ) - 4) + dy) = relUnpreppedOcc gap dx dy := by
        intro dx dy hdx0 hdx3 hdy1 hdy2
        unfold relUnpreppedOcc
        by_cases hneg : ((H' : ℤ) - 4) + dy < 0
        · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
        · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
          by_cases hdy_neg : dy < 0
          · rw [if_pos hdy_neg]; unfold unpreppedPat; rw [decide_eq_true_eq]; omega
          · rw [if_neg hdy_neg]; unfold unpreppedPat; rw [decide_eq_decide]; omega
      obtain ⟨_, hm, _⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
        hy_box3 hocc3 (c24_top_check .LG (Or.inl rfl) gap hgap)
      cases hm
    · have hh6 : h + 6 ≤ H' := by omega
      have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 4) + 7 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat
          (y_floor := h - 4) (y_top := h)
          (fun x y hx hy => by unfold unpreppedPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold unpreppedPat; simp [show ¬ y < h by omega])
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; omega
      exact kill_lg_012_on_unprepped hReason hs_le hframe j hh4 hh6 hmod hgap hpat
        (fun _ _ _ _ => rfl) hin hy_u htraj hx_012 hy_box hfill
  · cases hI
  · obtain ⟨_, hrH6⟩ := openNotch_margins hframe hopen.1 hopen.2.1 hopen.2.2.1
    have hr_ge : h ≤ r := by
      unfold unpreppedPat at hpat3r; simp only [decide_eq_false_iff_not] at hpat3r
      rcases hgap with rfl | rfl <;> omega
    refine ⟨gap, r, hh4, hr_ge, by omega, hmod, hrmod, hgap, fun hg2 => ?_, hpat'⟩
    by_contra hlt6
    have hrh : r = h := by omega
    subst r; subst gap
    have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (Or.inr ⟨by omega, by omega, rfl⟩)
    have h2f : bucketCell U j.val 2 ((h : ℤ) - 1) = false := by
      rw [bcell2 hframe hpat (by omega) (by omega)]; unfold unpreppedPat; simp; omega
    have hhole := hasHole_of_col2_seal (bucketFrame_insert hframe) j_pad
      (y₀ := (h : ℤ) - 1) (y_top := h) (by omega) (by omega) (by omega)
      (bucketCell_insert_of_not_mem h2f (mt (hiff 2 ((h : ℤ) - 1)).mp (by omega)))
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
      (fun y hy0 hylt => ⟨bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat hy0 (by omega)]; unfold unpreppedPat; rw [decide_eq_true_eq]; omega),
        bucketCell_insert_of_true (by
          rw [bucketPattern_eval hframe hpat (by omega) (by omega) hy0 (by omega)]
          unfold unpreppedPat; apply bool_or_right; rw [decide_eq_true_eq]; omega)⟩)
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill

/-- Proposition C.3: `.Sq` in `UnpreppedAt` is impossible! -/
theorem prop_C3 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hunp : UnpreppedAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hunp with ⟨gap, hh4, hhH, hmod, hgap, hpat⟩
  obtain ⟨x₀, y₀, hx0, hyH, hiff, hf00, hf10, _, _, hsup⟩ :=
    sq_012_cases hReason hs_le hframe j hpat (unpreppedPat_sym34 h gap hgap) hin hy_u htraj hfill
  unfold unpreppedPat at hf00 hf10 hsup
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hf00 hf10 hsup
  have hy0_eq : y₀ = h := by rcases hx0 with rfl | rfl <;> rcases hgap with rfl | rfl <;> omega
  subst y₀
  have h3f : bucketCell U j.val 3 h = false := by
    rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
    unfold unpreppedPat; simp
  have h4f : bucketCell U j.val 4 h = false := by
    rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
    unfold unpreppedPat; simp
  rcases hx0 with rfl | rfl
  · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr ⟨Or.inr rfl, Or.inl rfl⟩
    exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
      ⟨h, ⟨by omega, by omega, by omega,
        bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (by omega)),
        bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (by omega))⟩,
        bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
  · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr ⟨by omega, Or.inl rfl⟩
    have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := h)
      (by omega) (by omega) (by omega)
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
      (bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (by omega)))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill

private lemma c4_g0_check :
    allInTargets (validRelPlacements012 .LS (relUnpreppedOcc 0) 0 7)
      [[(0, 3), (0, 4), (1, 4), (1, 5)],
       [(1, 4), (1, 5), (2, 5), (2, 6)],
       [(1, 4), (2, 4), (0, 5), (1, 5)]] = true := by decide

private lemma c4_g2_check :
    allInTargets (validRelPlacements012 .LS (relUnpreppedOcc 2) 0 7)
      [[(0, 4), (0, 5), (1, 5), (1, 6)],
       [(1, 4), (1, 5), (2, 5), (2, 6)],
       [(1, 4), (2, 4), (0, 5), (1, 5)]] = true := by decide

/-- Helper killing all 3-column `.LS` placements on `unpreppedPat h gap` (reused in `prop_C4` & `prop_C9`!). -/
lemma kill_ls_012_on_unprepped {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h gap : ℕ} {pat : ℕ → ℕ → Bool}
    (hh4 : 4 ≤ h) (hh6 : h + 6 ≤ H') (hmod : (h + 1) % 6 = 5) (hgap : gap = 0 ∨ gap = 2)
    (hpat : BucketPattern U j.val H' pat)
    (hpat_low : ∀ x y : ℕ, x < 5 → y ≤ h + 3 → pat x y = unpreppedPat h gap x y)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hx_012 : ∀ z ∈ u.cells, 6 * (j.val : ℤ) ≤ z.1 ∧ z.1 < 6 * (j.val : ℤ) + 3)
    (hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 4) + 7)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 7 →
      bucketCell U j.val dx (((h : ℤ) - 4) + dy) = relUnpreppedOcc gap dx dy := by
    intro dx dy hdx0 hdx3 hdy1 hdy2
    unfold relUnpreppedOcc
    by_cases hneg : ((h : ℤ) - 4) + dy < 0
    · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
    · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega),
        hpat_low dx.toNat (((h : ℤ) - 4) + dy).toNat (by omega) (by omega)]
      by_cases hdy_neg : dy < 0
      · rw [if_pos hdy_neg]; unfold unpreppedPat; rw [decide_eq_true_eq]; omega
      · rw [if_neg hdy_neg]; unfold unpreppedPat; rw [decide_eq_decide]; omega
  have h3f : bucketCell U j.val 3 h = false := by
    rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast,
      hpat_low 3 h (by omega) (by omega)]
    unfold unpreppedPat; simp
  have h4f : bucketCell U j.val 4 h = false := by
    rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast,
      hpat_low 4 h (by omega) (by omega)]
    unfold unpreppedPat; simp
  rcases hgap with rfl | rfl
  · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c4_g0_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    rcases htgt with rfl | rfl | rfl
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 1) ∈ u.cells := (hiff 0 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
      have h0f : bucketCell U j.val 0 ((h : ℤ) - 4) = false := by
        rw [bcell0 hframe hpat (by omega) (by omega), hpat_low 0 _ (by omega) (by omega)]
        unfold unpreppedPat; simp; omega
      have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 4) (y_top := (h : ℤ) - 1)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem h0f (mt (hiff 0 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (fun y hy0 hylt => bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat hy0 (by omega), hpat_low 1 y.toNat (by omega) (by omega)]
          unfold unpreppedPat; rw [decide_eq_true_eq]; omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
    · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := h)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c4_g2_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    rcases htgt with rfl | rfl | rfl
    · have hm01 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm11 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have h2f : bucketCell U j.val 2 ((h : ℤ) + 1) = false := by
        rw [bcell2 hframe hpat (by omega) (by omega),
          show ((h : ℤ) + 1).toNat = h + 1 by omega, hpat_low 2 (h + 1) (by omega) (by omega)]
        unfold unpreppedPat; simp
      have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 1) 2 :=
        mk_balcony_2 (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm01)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm11)
          (bucketCell_insert_of_not_mem h2f (mt (hiff 2 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
      exact unfillable_floored_of_unprepped_insert hReason hs_le hframe j hh4 (by omega) hmod (Or.inr rfl) hpat
        (fun x y hx _ hy => hpat_low x y hx (by omega))
        ⟨mt (hiff 3 h).mp (not_mem4_of_omega (by omega)),
         mt (hiff 4 h).mp (not_mem4_of_omega (by omega))⟩
        (fun x _ _ => mt (hiff x ((h : ℤ) - 1)).mp (not_mem4_of_omega (by omega)))
        (by omega) hbal hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
    · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := h)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill

/-- Proposition C.4: `.LS` in `UnpreppedAt` is impossible! -/
theorem prop_C4 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hunp : UnpreppedAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  rcases hunp with ⟨gap, hh4, hhH, hmod, hgap, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (unpreppedPat_sym34 h gap hgap)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · by_cases hh_eq : h = H'
    · subst h
      have hy_box3 : ∀ z ∈ u.cells, ((H' : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((H' : ℤ) - 4) + 3 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := H' - 4) (y_top := H')
          (fun x y hx hy => by unfold unpreppedPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold unpreppedPat; simp [show ¬ y < H' by omega])
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; have := hy_u z hz; omega
      have hocc3 : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 3 →
          bucketCell U j.val dx (((H' : ℤ) - 4) + dy) = relUnpreppedOcc gap dx dy := by
        intro dx dy hdx0 hdx3 hdy1 hdy2
        unfold relUnpreppedOcc
        by_cases hneg : ((H' : ℤ) - 4) + dy < 0
        · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
        · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
          by_cases hdy_neg : dy < 0
          · rw [if_pos hdy_neg]; unfold unpreppedPat; rw [decide_eq_true_eq]; omega
          · rw [if_neg hdy_neg]; unfold unpreppedPat; rw [decide_eq_decide]; omega
      obtain ⟨_, hm, _⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
        hy_box3 hocc3 (c24_top_check .LS (Or.inr rfl) gap hgap)
      cases hm
    · have hh6 : h + 6 ≤ H' := by omega
      have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 4) + 7 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat
          (y_floor := h - 4) (y_top := h)
          (fun x y hx hy => by unfold unpreppedPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold unpreppedPat; simp [show ¬ y < h by omega])
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; omega
      exact kill_ls_012_on_unprepped hReason hs_le hframe j hh4 hh6 hmod hgap hpat
        (fun _ _ _ _ => rfl) hin hy_u htraj hx_012 hy_box hfill
  · cases hI
  · cases hLG

lemma addNotchLG_comm (pat : ℕ → ℕ → Bool) (r₁ r₂ x y : ℕ) :
    addNotchLG (addNotchLG pat r₁) r₂ x y = addNotchLG (addNotchLG pat r₂) r₁ x y := by
  unfold addNotchLG; rw [Bool.or_assoc, Bool.or_assoc, Bool.or_comm (decide _) (decide _)]

def relLgUp0AtHOcc (dx dy : ℤ) : Bool :=
  if dy < 0 then true
  else decide ((dy < 4 ∧ dx ≠ 0) ∨ (dx = 2 ∧ (dy = 4 ∨ dy = 5)))

private lemma c9_rh_check :
    allInTargets (validRelPlacements012 .LS relLgUp0AtHOcc 0 9)
      [[(0, 3), (0, 4), (1, 4), (1, 5)],
       [(1, 5), (1, 6), (2, 6), (2, 7)],
       [(1, 6), (2, 6), (0, 7), (1, 7)]] = true := by decide

/-- Proposition C.9: `.LS` in `addNotchLG (unpreppedPat h gap) r` (`gap = 2 → h + 6 ≤ r`) is impossible! -/
theorem prop_C9 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h gap r : ℕ} (hh4 : 4 ≤ h) (hr_ge : h ≤ r) (hrH6 : r + 6 ≤ H')
    (hmod : (h + 1) % 6 = 5) (hrmod : (r + 1) % 6 = 5)
    (hgap : gap = 0 ∨ gap = 2) (hg2 : gap = 2 → h + 6 ≤ r)
    (hpat : BucketPattern U j.val H' (addNotchLG (unpreppedPat h gap) r))
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat
      (addNotchLG_sym34 (unpreppedPat_sym34 h gap hgap) r) (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · by_cases hrh : r = h
    · subst r
      have hg0 : gap = 0 := hgap.resolve_right fun hg => by have := hg2 hg; omega
      subst gap
      have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 4) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 4) + 9 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 4) (y_top := h + 2)
          (fun x y hx hy => by unfold addNotchLG unpreppedPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold addNotchLG unpreppedPat; simp; omega)
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; omega
      have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 9 →
          bucketCell U j.val dx (((h : ℤ) - 4) + dy) = relLgUp0AtHOcc dx dy := by
        intro dx dy hdx0 hdx3 hdy1 hdy2
        unfold relLgUp0AtHOcc
        by_cases hneg : ((h : ℤ) - 4) + dy < 0
        · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
        · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
          by_cases hdy_neg : dy < 0
          · rw [if_pos hdy_neg]; unfold addNotchLG unpreppedPat; apply bool_or_left; rw [decide_eq_true_eq]; omega
          · rw [if_neg hdy_neg]; unfold addNotchLG unpreppedPat; rw [← Bool.decide_or, decide_eq_decide]; omega
      obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
        hy_box hocc_rel c9_rh_check
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
      rcases htgt with rfl | rfl | rfl
      · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 1) ∈ u.cells := (hiff 0 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
        have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 4) (y_top := (h : ℤ) - 1)
          (by omega) (by omega) (by omega)
          (bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) - 4)).mp (not_mem4_of_omega (by omega))))
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
          (fun y hy0 hylt => bucketCell_insert_of_true (by
            rw [bcell1 hframe hpat hy0 (by omega)]
            unfold addNotchLG unpreppedPat; apply bool_or_left; rw [decide_eq_true_eq]; omega))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm11 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
        have hm12 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 2) ∈ u.cells := (hiff 1 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm22 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 2) ∈ u.cells := (hiff 2 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 2) 0 :=
          mk_balcony_0 (by omega) (by omega)
            (bucketCell_insert_of_not_mem (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
        have hbad : BadNonNotchVeranda (U.insert u) j.val H' := by
          refine ⟨⟨1, by decide⟩, h, 1, ?_, by decide, ⟨(h : ℤ) + 2, 0, by omega, hbal⟩,
            fun y hy1 hy2 => Or.inr ?_⟩
          · refine ⟨by omega, by omega, by omega, fun y hy1 hy2 => ?_, ?_, ?_⟩
            · have hy_eq : y = h := by omega
              rw [hy_eq]; dsimp
              exact bucketCell_insert_of_not_mem (by
                rw [bcell1 hframe hpat (by omega) (by omega), Int.toNat_natCast]
                unfold addNotchLG unpreppedPat; simp) (mt (hiff 1 h).mp (not_mem4_of_omega (by omega)))
            · dsimp; exact bucketCell_insert_of_true (by
                rw [bcell1 hframe hpat (by omega) (by omega)]
                unfold addNotchLG unpreppedPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
            · dsimp; exact bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm11
          · have hy_eq : y = h := by omega
            rw [hy_eq]
            exact ⟨bucketCell_insert_of_true (by
                rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
                unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega),
              bucketCell_insert_of_true (by
                rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
                unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega)⟩
        exact not_fillableStrict_of_badNonNotchVeranda hReason hs_le (bucketFrame_insert hframe) j hbad hfill
      · have hm12 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 2) ∈ u.cells := (hiff 1 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm22 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 2) ∈ u.cells := (hiff 2 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm03 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 3) ∈ u.cells := (hiff 0 ((h : ℤ) + 3)).mpr (mem4_of_omega (by omega))
        have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 2) (by omega) (by omega) (by omega)
        have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
          (r_s := (h : ℤ) + 2) (x₀ := 1) (y₀ := (h : ℤ) + 1)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
          (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm03)
          (bucketCell_insert_of_not_mem (by
            rw [bcell1 hframe hpat (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
            unfold addNotchLG unpreppedPat; simp) (mt (hiff 1 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · rcases split_base_or_isoNotch hframe (j := j_pad) hrH6 hpat (y_floor := h - 4) (y_top := h)
          (by omega)
          (fun x y hx hy => by unfold unpreppedPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold unpreppedPat; simp [show ¬ y < h by omega])
          (by omega) hin hy_u htraj hx_012 with
        ⟨hy_base, _⟩ | ⟨hy_iso, hocc_iso⟩
      · exact kill_ls_012_on_unprepped hReason hs_le hframe j hh4 (by omega) hmod hgap hpat
          (fun x y _ hy => by unfold addNotchLG; simp [show ¬ ((x = 2 ∧ y = r + 1) ∨ (2 ≤ x ∧ x ≤ 4 ∧ y = r)) by omega])
          hin hy_u htraj hx_012 (fun z hz => by have := hy_base z hz; omega) hfill
      · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          hy_iso hocc_iso isoNotch_LS_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        rcases htgt with rfl | rfl
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hbal : Balcony (U.insert u) j.val H' ((r : ℤ) + 2) 0 :=
            mk_balcony_0 (by omega) (by omega)
              (bucketCell_insert_of_not_mem (by
                rw [bcell0 hframe hpat (by omega) (by omega)]
                unfold addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((r : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
          exact unfillable_floored_of_unprepped_insert hReason hs_le hframe j hh4 (by omega) hmod hgap hpat
            (fun x y _ _ hy => by unfold addNotchLG; simp [show ¬ ((x = 2 ∧ y = r + 1) ∨ (2 ≤ x ∧ x ≤ 4 ∧ y = r)) by omega])
            ⟨mt (hiff 3 h).mp (not_mem4_of_omega (by omega)),
             mt (hiff 4 h).mp (not_mem4_of_omega (by omega))⟩
            (fun x _ _ => mt (hiff x ((h : ℤ) - 1)).mp (not_mem4_of_omega (by omega))) (by omega) hbal hfill
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm03 : (6 * (j.val : ℤ) + 0, (r : ℤ) + 3) ∈ u.cells := (hiff 0 ((r : ℤ) + 3)).mpr (mem4_of_omega (by omega))
          have h34 := bucketCell_notch_wall_B hframe j_pad (y := (r : ℤ) + 2) (by omega) (by omega) (by omega)
          have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
            (r_s := (r : ℤ) + 2) (x₀ := 1) (y₀ := (r : ℤ) + 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
            (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm03)
            (bucketCell_insert_of_not_mem (by
              rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold addNotchLG unpreppedPat; simp; omega) (mt (hiff 1 ((r : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

/-! ### Appendix C.1.5 + `WeirdPlateauAt`: Dead Plateau Transitions (Propositions C.13 – C.16 & WP) -/

def relTallOcc (dx dy : ℤ) : Bool :=
  if dy < 0 then true
  else decide (dy < 9 ∧ dx ≠ 0)

private lemma c13_check :
    allInTargets (validRelPlacements012 .LS relTallOcc 0 12)
      [[(0, 8), (0, 9), (1, 9), (1, 10)],
       [(1, 9), (1, 10), (2, 10), (2, 11)],
       [(1, 9), (2, 9), (0, 10), (1, 10)]] = true := by decide

/-- Proposition C.13: `.LS` in `TallPlateauAt` is impossible! -/
theorem prop_C13 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (htp : TallPlateauAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  rcases htp with ⟨hh9, hhH, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (tallPlateauPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 9) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 9) + 12 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 9) (y_top := h)
        (fun x y hx hy => by unfold tallPlateauPat; rw [decide_eq_true_eq]; omega)
        (fun x y _ hy => by unfold tallPlateauPat; simp [show ¬ y < h by omega])
        hin hy_u htraj hx_012
      intro z hz; have := hb z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 12 →
        bucketCell U j.val dx (((h : ℤ) - 9) + dy) = relTallOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      unfold relTallOcc
      by_cases hneg : ((h : ℤ) - 9) + dy < 0
      · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
      · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
        by_cases hdy_neg : dy < 0
        · rw [if_pos hdy_neg]; unfold tallPlateauPat; rw [decide_eq_true_eq]; omega
        · rw [if_neg hdy_neg]; unfold tallPlateauPat; rw [decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c13_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    rcases htgt with rfl | rfl | rfl
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 1) ∈ u.cells := (hiff 0 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 9) (y_top := (h : ℤ) - 1)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem (by
          rw [bcell0 hframe hpat (by omega) (by omega)]
          unfold tallPlateauPat; simp; omega) (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (fun y hy0 hylt => bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat hy0 (by omega)]
          unfold tallPlateauPat; rw [decide_eq_true_eq]; omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hh1_lt : (h : ℤ) + 1 < H' := (hy_u _ hm1).2
      have h3f : bucketCell U j.val 3 ((h : ℤ) + 1) = false := by
        rw [bcell3_notch hframe hpat (by omega) hh1_lt (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
        rw [bcell4_notch hframe hpat (by omega) hh1_lt (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨(h : ℤ) + 1, ⟨by omega, hh1_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm1⟩ hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hh1_lt : (h : ℤ) + 1 < H' := (hy_u _ hm1).2
      have h3f : bucketCell U j.val 3 ((h : ℤ) + 1) = false := by
        rw [bcell3_notch hframe hpat (by omega) hh1_lt (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
        rw [bcell4_notch hframe hpat (by omega) hh1_lt (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨(h : ℤ) + 1, ⟨by omega, hh1_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm1⟩ hfill
  · cases hI
  · cases hLG

/-- Proposition C.14: `.Sq` in `TallPlateauAt` is impossible! -/
theorem prop_C14 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (htp : TallPlateauAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  rcases htp with ⟨hh9, _, hmod, hpat⟩
  obtain ⟨x₀, y₀, hx0, hyH, hiff, hf00, hf10, _, _, hsup⟩ :=
    sq_012_cases hReason hs_le hframe j hpat (tallPlateauPat_sym34 h) hin hy_u htraj hfill
  unfold tallPlateauPat at hf00 hf10 hsup
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hf00 hf10 hsup
  have hy0_eq : y₀ = h := by rcases hx0 with rfl | rfl <;> omega
  subst y₀
  have hh7 : h + 7 ≤ H' := by omega
  rcases hx0 with rfl | rfl
  · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr ⟨Or.inl rfl, Or.inl rfl⟩
    have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 9) (y_top := h)
      (by omega) (by omega) (by omega)
      (bucketCell_insert_of_not_mem (by
        rw [bcell0 hframe hpat (by omega) (by omega)]
        unfold tallPlateauPat; simp; omega) (mt (hiff 0 ((h : ℤ) - 9)).mp (by omega)))
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
      (fun y hy0 hylt => bucketCell_insert_of_true (by
        rw [bcell1 hframe hpat hy0 (by omega)]
        unfold tallPlateauPat; rw [decide_eq_true_eq]; omega))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · have hm21 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 1) ∈ u.cells := (hiff 2 ((h : ℤ) + 1)).mpr ⟨by omega, Or.inr (by omega)⟩
    have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
      rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
      unfold tallPlateauPat; simp
    have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := (h : ℤ) + 1)
      (by omega) (by omega) (by omega)
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm21)
      (bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (by omega)))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill

private lemma c15_check :
    allInTargets (validRelPlacements012 .LG relTallOcc 0 12)
      [[(0, 7), (0, 8), (0, 9), (1, 9)],
       [(0, 9), (1, 9), (2, 9), (0, 10)],
       [(0, 10), (1, 10), (2, 10), (2, 9)],
       [(0, 9), (1, 9), (1, 10), (1, 11)],
       [(1, 9), (2, 9), (2, 10), (2, 11)],
       [(1, 9), (1, 10), (1, 11), (2, 11)]] = true := by decide

/-- Proposition C.15: `.LG` in `TallPlateauAt` produces `addNotchLG (tallPlateauPat h) r` (`h + 1 ≤ r`)! -/
theorem prop_C15 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (htp : TallPlateauAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LG u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    ∃ r : ℕ, 9 ≤ h ∧ h + 1 ≤ r ∧ r + 6 ≤ H' ∧ (h + 2) % 6 = 5 ∧ (r + 1) % 6 = 5 ∧
      BucketPattern (U.insert u) j.val H' (addNotchLG (tallPlateauPat h) r) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨T, hHT⟩
  rcases htp with ⟨hh9, hhH, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (tallPlateauPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨r, _, hrmod, hpat3r, hopen, ⟨hI, _⟩ | ⟨_, hpat', _⟩⟩
  · exfalso
    have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 9) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 9) + 12 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 9) (y_top := h)
        (fun x y hx hy => by unfold tallPlateauPat; rw [decide_eq_true_eq]; omega)
        (fun x y _ hy => by unfold tallPlateauPat; simp [show ¬ y < h by omega])
        hin hy_u htraj hx_012
      intro z hz; have := hb z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 12 →
        bucketCell U j.val dx (((h : ℤ) - 9) + dy) = relTallOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      unfold relTallOcc
      by_cases hneg : ((h : ℤ) - 9) + dy < 0
      · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
      · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
        by_cases hdy_neg : dy < 0
        · rw [if_pos hdy_neg]; unfold tallPlateauPat; rw [decide_eq_true_eq]; omega
        · rw [if_neg hdy_neg]; unfold tallPlateauPat; rw [decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c15_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    have h0f9 : bucketCell U j.val 0 ((h : ℤ) - 9) = false := by
      rw [bcell0 hframe hpat (by omega) (by omega)]
      unfold tallPlateauPat; simp; omega
    rcases htgt with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 2) ∈ u.cells := (hiff 0 ((h : ℤ) - 2)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 9) (y_top := (h : ℤ) - 2)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem h0f9 (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (fun y hy0 hylt => bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat hy0 (by omega)]
          unfold tallPlateauPat; rw [decide_eq_true_eq]; omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := h) (x₀ := 0) (y₀ := (h : ℤ) - 9) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h0f9 (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 1) ∈ u.cells := (hiff 2 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hh1_lt := (hy_u _ hm0).2
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := (h : ℤ) + 1) (x₀ := 0) (y₀ := (h : ℤ) - 9) (by omega) hh1_lt (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm2)
        (bucketCell_insert_of_not_mem h0f9 (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 9) (y_top := h)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem h0f9 (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (fun y hy0 hylt => bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat hy0 (by omega)]
          unfold tallPlateauPat; rw [decide_eq_true_eq]; omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm21 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 1) ∈ u.cells := (hiff 2 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm22 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 2) ∈ u.cells := (hiff 2 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
      have hh2_lt := (hy_u _ hm22).2
      have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
        rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := (h : ℤ) + 1)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm21)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm11 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hh1_lt := (hy_u _ hm11).2
      have h3f : bucketCell U j.val 3 ((h : ℤ) + 1) = false := by
        rw [bcell3_notch hframe hpat (by omega) hh1_lt (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
        rw [bcell4_notch hframe hpat (by omega) hh1_lt (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold tallPlateauPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨(h : ℤ) + 1, ⟨by omega, hh1_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm11⟩ hfill
  · cases hI
  · obtain ⟨_, hrH6⟩ := openNotch_margins hframe hopen.1 hopen.2.1 hopen.2.2.1
    have hr_ge : h + 1 ≤ r := by
      unfold tallPlateauPat at hpat3r; simp only [decide_eq_false_iff_not] at hpat3r; omega
    exact ⟨r, hh9, hr_ge, by omega, hmod, hrmod, hpat'⟩

def relLgTPAtH1Occ (dx dy : ℤ) : Bool :=
  if dy < 0 then true
  else decide ((dy < 9 ∧ dx ≠ 0) ∨ (dx = 2 ∧ (dy = 10 ∨ dy = 11)))

private lemma c16_rh1_check :
    allInTargets (validRelPlacements012 .LS relLgTPAtH1Occ 0 15)
      [[(0, 8), (0, 9), (1, 9), (1, 10)],
       [(1, 9), (2, 9), (0, 10), (1, 10)],
       [(1, 11), (1, 12), (2, 12), (2, 13)],
       [(1, 12), (2, 12), (0, 13), (1, 13)]] = true := by decide

/-- Proposition C.16: `.LS` in `addNotchLG (tallPlateauPat h) r` (`h + 1 ≤ r`) is impossible! -/
theorem prop_C16 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h r : ℕ} (hh9 : 9 ≤ h) (hr_ge : h + 1 ≤ r) (hrH6 : r + 6 ≤ H')
    (hmod : (h + 2) % 6 = 5) (hrmod : (r + 1) % 6 = 5)
    (hpat : BucketPattern U j.val H' (addNotchLG (tallPlateauPat h) r))
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat
      (addNotchLG_sym34 (tallPlateauPat_sym34 h) r) (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · by_cases hrh : r = h + 1
    · subst r
      have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 9) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 9) + 15 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 9) (y_top := h + 3)
          (fun x y hx hy => by unfold addNotchLG tallPlateauPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold addNotchLG tallPlateauPat; simp; omega)
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; omega
      have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 15 →
          bucketCell U j.val dx (((h : ℤ) - 9) + dy) = relLgTPAtH1Occ dx dy := by
        intro dx dy hdx0 hdx3 hdy1 hdy2
        unfold relLgTPAtH1Occ
        by_cases hneg : ((h : ℤ) - 9) + dy < 0
        · rw [bucketPattern_eval_neg_y hneg, if_pos (by omega)]
        · rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
          by_cases hdy_neg : dy < 0
          · rw [if_pos hdy_neg]; unfold addNotchLG tallPlateauPat; apply bool_or_left; rw [decide_eq_true_eq]; omega
          · rw [if_neg hdy_neg]; unfold addNotchLG tallPlateauPat; rw [← Bool.decide_or, decide_eq_decide]; omega
      obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
        hy_box hocc_rel c16_rh1_check
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
      rcases htgt with rfl | rfl | rfl | rfl
      · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 1) ∈ u.cells := (hiff 0 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
        have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 9) (y_top := (h : ℤ) - 1)
          (by omega) (by omega) (by omega)
          (bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold addNotchLG tallPlateauPat; simp; omega) (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
          (fun y hy0 hylt => bucketCell_insert_of_true (by
            rw [bcell1 hframe hpat hy0 (by omega)]
            unfold addNotchLG tallPlateauPat; apply bool_or_left; rw [decide_eq_true_eq]; omega))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm01 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
        have hm11 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
        have hhole := hasHole_of_closed_row (bucketFrame_insert hframe) j_pad
          (r := (h : ℤ) + 1) (x₀ := 0) (y₀ := h) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm01)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm11)
          (bucketCell_insert_of_true (by
            rw [bcell2 hframe hpat (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
            unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_true (by
            rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
            unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_true (by
            rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
            unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega), Int.toNat_natCast]
            unfold addNotchLG tallPlateauPat; simp) (mt (hiff 0 h).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm12 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 2) ∈ u.cells := (hiff 1 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm13 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 3) ∈ u.cells := (hiff 1 ((h : ℤ) + 3)).mpr (mem4_of_omega (by omega))
        have hm23 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 3) ∈ u.cells := (hiff 2 ((h : ℤ) + 3)).mpr (mem4_of_omega (by omega))
        have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 3) 0 :=
          mk_balcony_0 (by omega) (by omega)
            (bucketCell_insert_of_not_mem (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold addNotchLG tallPlateauPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 3)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm13)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm23)
        exact not_fillableStrict_of_anyPlay (j := j)
          (anyPlay_unfillable_of_twoVeranda_ge2 hReason (bucketFrame_insert hframe) j_pad 1
            (bottom := h) (b := (h : ℤ) + 3) (ib := 0) (by omega) (by omega) hbal
            (bucketCell_insert_of_true (by
              dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold addNotchLG tallPlateauPat; apply bool_or_left; rw [decide_eq_true_eq]; omega))
            (bucketCell_insert_of_not_mem (by
              dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega), Int.toNat_natCast]
              unfold addNotchLG tallPlateauPat; simp) (mt (hiff 1 h).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_not_mem (by
              dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
              unfold addNotchLG tallPlateauPat; simp) (mt (hiff 1 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)) hfill
      · have hm13 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 3) ∈ u.cells := (hiff 1 ((h : ℤ) + 3)).mpr (mem4_of_omega (by omega))
        have hm23 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 3) ∈ u.cells := (hiff 2 ((h : ℤ) + 3)).mpr (mem4_of_omega (by omega))
        have hm04 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 4) ∈ u.cells := (hiff 0 ((h : ℤ) + 4)).mpr (mem4_of_omega (by omega))
        have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 3) (by omega) (by omega) (by omega)
        have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
          (r_s := (h : ℤ) + 3) (x₀ := 1) (y₀ := (h : ℤ) + 2)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm13)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm23)
          (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm04)
          (bucketCell_insert_of_not_mem (by
            rw [bcell1 hframe hpat (by omega) (by omega), show ((h : ℤ) + 2).toNat = h + 2 by omega]
            unfold addNotchLG tallPlateauPat; simp) (mt (hiff 1 ((h : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · rcases split_base_or_isoNotch hframe (j := j_pad) hrH6 hpat (y_floor := h - 9) (y_top := h)
          (by omega)
          (fun x y hx hy => by unfold tallPlateauPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold tallPlateauPat; simp [show ¬ y < h by omega])
          (by omega) hin hy_u htraj hx_012 with
        ⟨hy_base, hocc_base⟩ | ⟨hy_iso, hocc_iso⟩
      · have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 12 →
            bucketCell U j.val dx (((h : ℤ) - 9) + dy) = relTallOcc dx dy := by
          intro dx dy hdx0 hdx3 hdy1 hdy2
          dsimp only [j_pad] at hocc_base
          rw [show ((h : ℤ) - 9) + dy = ((h - 9 : ℕ) : ℤ) + dy by omega, hocc_base dx dy hdx0 hdx3 hdy1 (by omega)]
          unfold relTallOcc
          by_cases hneg : ((h - 9 : ℕ) : ℤ) + dy < 0
          · rw [if_pos hneg, if_pos (by omega)]
          · rw [if_neg hneg]
            by_cases hdy_neg : dy < 0
            · rw [if_pos hdy_neg]; unfold tallPlateauPat; rw [decide_eq_true_eq]; omega
            · rw [if_neg hdy_neg]; unfold tallPlateauPat; rw [decide_eq_decide]; omega
        obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          (fun z hz => by have := hy_base z hz; omega) hocc_rel c13_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        have h3f : bucketCell U j.val 3 ((h : ℤ) + 1) = false := by
          rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
          unfold addNotchLG tallPlateauPat; simp; omega
        have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
          rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
          unfold addNotchLG tallPlateauPat; simp; omega
        rcases htgt with rfl | rfl | rfl
        · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) - 1) ∈ u.cells := (hiff 0 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
          have hhole := hasHole_of_col0_seal (bucketFrame_insert hframe) j_pad (y₀ := (h : ℤ) - 9) (y_top := (h : ℤ) - 1)
            (by omega) (by omega) (by omega)
            (bucketCell_insert_of_not_mem (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold addNotchLG tallPlateauPat; simp; omega) (mt (hiff 0 ((h : ℤ) - 9)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
            (fun y hy0 hylt => bucketCell_insert_of_true (by
              rw [bcell1 hframe hpat hy0 (by omega)]
              unfold addNotchLG tallPlateauPat; apply bool_or_left; rw [decide_eq_true_eq]; omega))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
        · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
          exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
            ⟨(h : ℤ) + 1, ⟨by omega, by omega, by omega,
              bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))),
              bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega)))⟩,
              bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
        · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
          exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
            ⟨(h : ℤ) + 1, ⟨by omega, by omega, by omega,
              bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))),
              bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega)))⟩,
              bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
      · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          hy_iso hocc_iso isoNotch_LS_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        rcases htgt with rfl | rfl
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hbal : Balcony (U.insert u) j.val H' ((r : ℤ) + 2) 0 :=
            mk_balcony_0 (by omega) (by omega)
              (bucketCell_insert_of_not_mem (by
                rw [bcell0 hframe hpat (by omega) (by omega)]
                unfold addNotchLG tallPlateauPat; simp; omega) (mt (hiff 0 ((r : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
          have h3f : bucketCell U j.val 3 ((h : ℤ) + 1) = false := by
            rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
            unfold addNotchLG tallPlateauPat; simp; omega
          have h4f : bucketCell U j.val 4 ((h : ℤ) + 1) = false := by
            rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
            unfold addNotchLG tallPlateauPat; simp; omega
          exact not_fillableStrict_of_anyPlay (j := j)
            (anyPlay_unfillable_of_subNotchRectangle_ge2 hReason (bucketFrame_insert hframe) j_pad
              (r := (h : ℤ) + 1) (col := 1) (d := 1) (b := (r : ℤ) + 2) (ib := 0)
              (Or.inl rfl) le_rfl (by omega) (by omega)
              ⟨by omega, by omega, by omega,
                bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))),
                bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega)))⟩
              hbal
              (by
                have h' : bucketCell (U.insert u) j_pad.val 1 ((h : ℤ) - 1) = true :=
                  bucketCell_insert_of_true (by
                    dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
                    unfold addNotchLG tallPlateauPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
                exact bcell_eq_of_eq h' (by omega))
              (fun z hz1 hz2 => bucketCell_insert_of_not_mem (by
                dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
                unfold addNotchLG tallPlateauPat; simp; omega) (mt (hiff 1 z).mp (not_mem4_of_omega (by omega))))) hfill
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm03 : (6 * (j.val : ℤ) + 0, (r : ℤ) + 3) ∈ u.cells := (hiff 0 ((r : ℤ) + 3)).mpr (mem4_of_omega (by omega))
          have h34 := bucketCell_notch_wall_B hframe j_pad (y := (r : ℤ) + 2) (by omega) (by omega) (by omega)
          have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
            (r_s := (r : ℤ) + 2) (x₀ := 1) (y₀ := (r : ℤ) + 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
            (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm03)
            (bucketCell_insert_of_not_mem (by
              rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold addNotchLG tallPlateauPat; simp; omega) (mt (hiff 1 ((r : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

/-! ### `WeirdPlateauAt` Transitions (Closing the Prop C.11 `{1, 2}`-Plateau Case!) -/

def weirdPlusSqPat (h : ℕ) (x y : ℕ) : Bool :=
  weirdPlateauPat h x y || decide ((x = 1 ∨ x = 2) ∧ (y = h + 10 ∨ y = h + 11))

lemma weirdPlusSqPat_sym34 (h y : ℕ) : weirdPlusSqPat h 3 y = weirdPlusSqPat h 4 y := by
  unfold weirdPlusSqPat; rw [weirdPlateauPat_sym34]; simp

/-- Balcony at `h + 9` on `weirdPlateauPat h` (or `addNotchLG (weirdPlateauPat h) r` with `h + 12 ≤ r`)
forces any non-`.I` piece `u` in cols `0..4` to stay at `z.2 ≥ h + 8`! -/
lemma weirdPlateau_nonI_ge_h8 {R : Rotation} (hReason : Reasonable R)
    {s' H' : ℕ} {U : Board} (hframe : BucketFrame U s' H') (j_pad : Fin s')
    {h : ℕ} {pat : ℕ → ℕ → Bool}
    (hh12 : h + 12 ≤ H')
    (hpat : BucketPattern U j_pad.val H' pat)
    (hbal_row : ∀ x : ℕ, x < 3 → pat x (h + 9) = decide (x ≠ 0))
    {t : Piece} (hneI : t ≠ .I) {u : PieceState}
    (hin : InBucket j_pad.val u) (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U t u) :
    ∀ z ∈ u.cells, (h : ℤ) + 8 ≤ z.2 := by
  have hcl := (trajectory_clear_and_blocked htraj).1
  have hbal : Balcony U j_pad.val H' ((h : ℤ) + 9) 0 := by
    refine ⟨by omega, by omega, fun x => ?_⟩
    rw [bucketPattern_eval_012 hframe hpat (by omega) (by have := x.isLt; omega) (by omega) (by omega)]
    have hyt : ((h : ℤ) + 9).toNat = h + 9 := by omega
    rw [Int.toNat_natCast, hyt, hbal_row x.val (by have := x.isLt; omega)]
    fin_cases x <;> rfl
  intro z hz
  have hzx := hin z hz
  have hzy := hy_u z hz
  have hx5 : z.1 < 6 * (j_pad.val : ℤ) + 5 := by
    by_contra hge
    have hrw := bucketCell_right_wall_B hframe j_pad hzy.1 hzy.2
    unfold bucketCell at hrw
    have heq : (6 * (j_pad.val : ℤ) + 5, z.2) = z := by ext <;> omega
    rw [heq, hcl z hz] at hrw; cases hrw
  by_cases hle : z.2 ≤ (h : ℤ) + 9
  · have hcond := hReason.2.2.2.1 U s' H' hframe j_pad ((h : ℤ) + 9) 0 t u
      hbal (by omega) hneI (trajectory_reachable_B hframe htraj) z hz hzx.1 hx5 hle
    omega
  · omega

def relWeirdTopOcc (dx dy : ℤ) : Bool :=
  decide ((dy = -1 ∧ dx = 2) ∨ ((dy = 0 ∨ dy = 1) ∧ (dx = 1 ∨ dx = 2)))

private lemma wp_LS_check :
    allInTargets (validRelPlacements012 .LS relWeirdTopOcc 0 5)
      [[(0, 1), (0, 2), (1, 2), (1, 3)],
       [(1, 2), (1, 3), (2, 3), (2, 4)],
       [(1, 2), (2, 2), (0, 3), (1, 3)]] = true := by decide

/-- `.LS` in `WeirdPlateauAt` is impossible! -/
theorem prop_WP_LS {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hwp : WeirdPlateauAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨_, _⟩
  rcases hwp with ⟨hh4, hh12, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (weirdPlateauPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · have hy_low := weirdPlateau_nonI_ge_h8 hReason hframe j_pad hh12 hpat
      (fun x hx => by unfold weirdPlateauPat addNotchLG unpreppedPat; rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega)
      (by decide) hin hy_u htraj
    have hy_box : ∀ z ∈ u.cells, ((h : ℤ) + 8) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) + 8) + 5 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := 0) (y_top := h + 10)
        (fun _ _ _ hy => by omega)
        (fun x y _ hy => by unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega)
        hin hy_u htraj hx_012
      intro z hz; have := hy_low z hz; have := hb z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 5 →
        bucketCell U j.val dx (((h : ℤ) + 8) + dy) = relWeirdTopOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
      unfold weirdPlateauPat addNotchLG unpreppedPat relWeirdTopOcc
      rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel wp_LS_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    rcases htgt with rfl | rfl | rfl
    · have hm09 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 9) ∈ u.cells := (hiff 0 ((h : ℤ) + 9)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := (h : ℤ) + 9) (x₀ := 0) (y₀ := (h : ℤ) + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm09)
        (bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
        (bucketCell_insert_of_true (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
        (bucketCell_insert_of_not_mem (by
          rw [bcell0 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 8)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm110 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 10) ∈ u.cells := (hiff 1 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have hm211 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 11) ∈ u.cells := (hiff 2 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
      have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 10) (by omega) (by omega) (by omega)).1
      have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) + 10)
        (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 2 ((h : ℤ) + 10)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_true h3w)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm110)
        (by
          have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm211
          exact bcell_eq_of_eq h' (by omega))
        (by
          have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) + 9) = true :=
            bucketCell_insert_of_true (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm110 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 10) ∈ u.cells := (hiff 1 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have hm210 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 10) ∈ u.cells := (hiff 2 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have hm011 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 11) ∈ u.cells := (hiff 0 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
      have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 10) (by omega) (by omega) (by omega)
      have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
        (r_s := (h : ℤ) + 10) (x₀ := 0) (y₀ := (h : ℤ) + 9)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm110)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm210)
        (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm011)
        (bucketCell_insert_of_not_mem (by
          rw [bcell0 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 9)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

private lemma wp_LG_check :
    allInTargets (validRelPlacements012 .LG relWeirdTopOcc 0 5)
      [[(0, 0), (0, 1), (0, 2), (1, 2)],
       [(0, 2), (1, 2), (2, 2), (0, 3)],
       [(0, 3), (1, 3), (2, 3), (2, 2)],
       [(0, 2), (1, 2), (1, 3), (1, 4)],
       [(1, 2), (2, 2), (2, 3), (2, 4)],
       [(1, 2), (1, 3), (1, 4), (2, 4)]] = true := by decide

/-- `.LG` in `WeirdPlateauAt` produces `addNotchLG (weirdPlateauPat h) r` (`h + 12 ≤ r`)! -/
theorem prop_WP_LG {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hwp : WeirdPlateauAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LG u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    ∃ r : ℕ, 4 ≤ h ∧ h + 12 ≤ r ∧ r + 6 ≤ H' ∧ (h + 1) % 6 = 5 ∧ (r + 1) % 6 = 5 ∧
      BucketPattern (U.insert u) j.val H' (addNotchLG (weirdPlateauPat h) r) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨_, _⟩
  rcases hwp with ⟨hh4, hh12, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (weirdPlateauPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨r, _, hrmod, hpat3r, hopen, ⟨hI, _⟩ | ⟨_, hpat', _⟩⟩
  · exfalso
    have hy_low := weirdPlateau_nonI_ge_h8 hReason hframe j_pad hh12 hpat
      (fun x hx => by unfold weirdPlateauPat addNotchLG unpreppedPat; rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega)
      (by decide) hin hy_u htraj
    have hy_box : ∀ z ∈ u.cells, ((h : ℤ) + 8) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) + 8) + 5 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := 0) (y_top := h + 10)
        (fun _ _ _ hy => by omega)
        (fun x y _ hy => by unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega)
        hin hy_u htraj hx_012
      intro z hz; have := hy_low z hz; have := hb z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 5 →
        bucketCell U j.val dx (((h : ℤ) + 8) + dy) = relWeirdTopOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
      unfold weirdPlateauPat addNotchLG unpreppedPat relWeirdTopOcc
      rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel wp_LG_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    have h1hf : bucketCell U j.val 1 h = false := by
      rw [bcell1 hframe hpat (by omega) (by omega), Int.toNat_natCast]
      unfold weirdPlateauPat addNotchLG unpreppedPat; simp
    rcases htgt with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm09 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 9) ∈ u.cells := (hiff 0 ((h : ℤ) + 9)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := (h : ℤ) + 9) (x₀ := 1) (y₀ := h) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm09)
        (bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
        (bucketCell_insert_of_true (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
        (bucketCell_insert_of_not_mem h1hf (mt (hiff 1 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 10) ∈ u.cells := (hiff 0 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 10) ∈ u.cells := (hiff 1 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 10) ∈ u.cells := (hiff 2 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := (h : ℤ) + 10) (x₀ := 1) (y₀ := h) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h1hf (mt (hiff 1 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm0 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 11) ∈ u.cells := (hiff 0 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 11) ∈ u.cells := (hiff 1 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 11) ∈ u.cells := (hiff 2 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
        (b := (h : ℤ) + 11) (x₀ := 1) (y₀ := h) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2)
        (bucketCell_insert_of_not_mem h1hf (mt (hiff 1 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm010 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 10) ∈ u.cells := (hiff 0 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
      have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 9) (by omega) (by omega) (by omega)
      have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
        (r_s := (h : ℤ) + 9) (x₀ := 1) (y₀ := h)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
        (bucketCell_insert_of_true (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
        (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm010)
        (bucketCell_insert_of_not_mem h1hf (mt (hiff 1 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm212 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 12) ∈ u.cells := (hiff 2 ((h : ℤ) + 12)).mpr (mem4_of_omega (by omega))
      have hh12_lt := (hy_u _ hm212).2
      have h4f : bucketCell U j.val 4 ((h : ℤ) + 12) = false := by
        rw [bcell4_notch hframe hpat (by omega) hh12_lt (by omega), show ((h : ℤ) + 12).toNat = h + 12 by omega]
        unfold weirdPlateauPat addNotchLG unpreppedPat; simp
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := (h : ℤ) + 12)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh12_lt hm212)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 12)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · have hm212 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 12) ∈ u.cells := (hiff 2 ((h : ℤ) + 12)).mpr (mem4_of_omega (by omega))
      have hh12_lt := (hy_u _ hm212).2
      have h4f : bucketCell U j.val 4 ((h : ℤ) + 12) = false := by
        rw [bcell4_notch hframe hpat (by omega) hh12_lt (by omega), show ((h : ℤ) + 12).toNat = h + 12 by omega]
        unfold weirdPlateauPat addNotchLG unpreppedPat; simp
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := (h : ℤ) + 12)
        (by omega) (by omega) (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh12_lt hm212)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 12)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · obtain ⟨_, hrH6⟩ := openNotch_margins hframe hopen.1 hopen.2.1 hopen.2.2.1
    have hr_ge : h + 12 ≤ r := by
      unfold weirdPlateauPat addNotchLG unpreppedPat at hpat3r
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hpat3r; omega
    exact ⟨r, hh4, hr_ge, by omega, hmod, hrmod, hpat'⟩

def relLgWPAtH12Occ (dx dy : ℤ) : Bool :=
  decide ((dy = -1 ∧ dx = 2) ∨ ((dy = 0 ∨ dy = 1) ∧ (dx = 1 ∨ dx = 2)) ∨ (dx = 2 ∧ (dy = 4 ∨ dy = 5)))

private lemma wp_lg_LS_rh12_check :
    allInTargets (validRelPlacements012 .LS relLgWPAtH12Occ 0 9)
      [[(0, 1), (0, 2), (1, 2), (1, 3)],
       [(1, 2), (2, 2), (0, 3), (1, 3)],
       [(1, 5), (1, 6), (2, 6), (2, 7)],
       [(1, 6), (2, 6), (0, 7), (1, 7)]] = true := by decide

/-- `.LS` in `addNotchLG (weirdPlateauPat h) r` (`h + 12 ≤ r`) is impossible! -/
theorem prop_WP_LS_lgWp {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h r : ℕ} (hh4 : 4 ≤ h) (hr_ge : h + 12 ≤ r) (hrH6 : r + 6 ≤ H')
    (hmod : (h + 1) % 6 = 5) (hrmod : (r + 1) % 6 = 5)
    (hpat : BucketPattern U j.val H' (addNotchLG (weirdPlateauPat h) r))
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat
      (addNotchLG_sym34 (weirdPlateauPat_sym34 h) r) (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · have hy_low := weirdPlateau_nonI_ge_h8 hReason hframe j_pad (h := h) (by omega) hpat
      (fun x hx => by unfold weirdPlateauPat addNotchLG unpreppedPat; dsimp only; rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega)
      (by decide) hin hy_u htraj
    by_cases hrh : r = h + 12
    · subst r
      have hy_box : ∀ z ∈ u.cells, ((h : ℤ) + 8) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) + 8) + 9 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := 0) (y_top := h + 14)
          (fun _ _ _ hy => by omega)
          (fun x y _ hy => by unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega)
          hin hy_u htraj hx_012
        intro z hz; have := hy_low z hz; have := hb z hz; omega
      have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 9 →
          bucketCell U j.val dx (((h : ℤ) + 8) + dy) = relLgWPAtH12Occ dx dy := by
        intro dx dy hdx0 hdx3 hdy1 hdy2
        rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
        unfold weirdPlateauPat addNotchLG unpreppedPat relLgWPAtH12Occ; dsimp only
        rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega
      obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
        hy_box hocc_rel wp_lg_LS_rh12_check
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
      rcases htgt with rfl | rfl | rfl | rfl
      · have hm09 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 9) ∈ u.cells := (hiff 0 ((h : ℤ) + 9)).mpr (mem4_of_omega (by omega))
        have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
          (b := (h : ℤ) + 9) (x₀ := 0) (y₀ := (h : ℤ) + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm09)
          (bucketCell_insert_of_true (by
            rw [bcell1 hframe hpat (by omega) (by omega)]
            unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_true (by
            rw [bcell2 hframe hpat (by omega) (by omega)]
            unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 8)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm110 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 10) ∈ u.cells := (hiff 1 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
        have hm210 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 10) ∈ u.cells := (hiff 2 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
        have hm011 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 11) ∈ u.cells := (hiff 0 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
        have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 10) (by omega) (by omega) (by omega)
        have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
          (r_s := (h : ℤ) + 10) (x₀ := 0) (y₀ := (h : ℤ) + 9)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm110)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm210)
          (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm011)
          (bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 9)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm114 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 14) ∈ u.cells := (hiff 1 ((h : ℤ) + 14)).mpr (mem4_of_omega (by omega))
        have hm214 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 14) ∈ u.cells := (hiff 2 ((h : ℤ) + 14)).mpr (mem4_of_omega (by omega))
        have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 14) 0 :=
          mk_balcony_0 (by omega) (by omega)
            (bucketCell_insert_of_not_mem (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 14)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm114)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm214)
        exact not_fillableStrict_of_anyPlay (j := j)
          (anyPlay_unfillable_of_twoVeranda_ge2 hReason (bucketFrame_insert hframe) j_pad 2
            (bottom := (h : ℤ) + 10) (b := (h : ℤ) + 14) (ib := 0) (by omega) (by omega) hbal
            (by
              have h' : bucketCell (U.insert u) j_pad.val 2 ((h : ℤ) + 9) = true :=
                bucketCell_insert_of_true (by
                  dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega)]
                  unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right
                  rw [decide_eq_true_eq]; omega)
              exact bcell_eq_of_eq h' (by omega))
            (bucketCell_insert_of_not_mem (by
              dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 2 ((h : ℤ) + 10)).mp (not_mem4_of_omega (by omega))))
            (by
              have h' : bucketCell (U.insert u) j_pad.val 2 ((h : ℤ) + 11) = false :=
                bucketCell_insert_of_not_mem (by
                  dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega)]
                  unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 2 ((h : ℤ) + 11)).mp (not_mem4_of_omega (by omega)))
              exact bcell_eq_of_eq h' (by omega))
            (by
              have h' : bucketCell (U.insert u) j_pad.val 2 ((h : ℤ) + 12) = true :=
                bucketCell_insert_of_true (by
                  dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega)]
                  unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega)
              exact bcell_eq_of_eq h' (by omega))) hfill
      · have hm114 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 14) ∈ u.cells := (hiff 1 ((h : ℤ) + 14)).mpr (mem4_of_omega (by omega))
        have hm214 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 14) ∈ u.cells := (hiff 2 ((h : ℤ) + 14)).mpr (mem4_of_omega (by omega))
        have hm015 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 15) ∈ u.cells := (hiff 0 ((h : ℤ) + 15)).mpr (mem4_of_omega (by omega))
        have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 14) (by omega) (by omega) (by omega)
        have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
          (r_s := (h : ℤ) + 14) (x₀ := 1) (y₀ := (h : ℤ) + 13)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm114)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm214)
          (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm015)
          (bucketCell_insert_of_not_mem (by
            rw [bcell1 hframe hpat (by omega) (by omega)]
            unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 1 ((h : ℤ) + 13)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · rcases split_base_or_isoNotch hframe (j := j_pad) hrH6 hpat (y_floor := 0) (y_top := h + 10)
          (by omega)
          (fun _ _ _ hy => by omega)
          (fun x y _ hy => by unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega)
          (by omega) hin hy_u htraj hx_012 with
        ⟨hy_base, _⟩ | ⟨hy_iso, hocc_iso⟩
      · have hy_box : ∀ z ∈ u.cells, ((h : ℤ) + 8) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) + 8) + 5 := by
          intro z hz; have := hy_low z hz; have := hy_base z hz; omega
        have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 5 →
            bucketCell U j.val dx (((h : ℤ) + 8) + dy) = relWeirdTopOcc dx dy := by
          intro dx dy hdx0 hdx3 hdy1 hdy2
          rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
          unfold weirdPlateauPat addNotchLG unpreppedPat relWeirdTopOcc; dsimp only
          rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega
        obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          hy_box hocc_rel wp_LS_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        rcases htgt with rfl | rfl | rfl
        · have hm09 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 9) ∈ u.cells := (hiff 0 ((h : ℤ) + 9)).mpr (mem4_of_omega (by omega))
          have hhole := hasHole_of_closed_012 (bucketFrame_insert hframe) j_pad
            (b := (h : ℤ) + 9) (x₀ := 0) (y₀ := (h : ℤ) + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm09)
            (bucketCell_insert_of_true (by
              rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right; rw [decide_eq_true_eq]; omega))
            (bucketCell_insert_of_true (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right; rw [decide_eq_true_eq]; omega))
            (bucketCell_insert_of_not_mem (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 8)).mp (not_mem4_of_omega (by omega))))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
        · have hm110 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 10) ∈ u.cells := (hiff 1 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
          have hm211 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 11) ∈ u.cells := (hiff 2 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
          have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 10) (by omega) (by omega) (by omega)).1
          have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) + 10)
            (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_not_mem (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 2 ((h : ℤ) + 10)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_true h3w)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm110)
            (by
              have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm211
              exact bcell_eq_of_eq h' (by omega))
            (by
              have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) + 9) = true :=
                bucketCell_insert_of_true (by
                  rw [bcell2 hframe hpat (by omega) (by omega)]
                  unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right; rw [decide_eq_true_eq]; omega)
              exact bcell_eq_of_eq h' (by omega))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
        · have hm110 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 10) ∈ u.cells := (hiff 1 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
          have hm210 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 10) ∈ u.cells := (hiff 2 ((h : ℤ) + 10)).mpr (mem4_of_omega (by omega))
          have hm011 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 11) ∈ u.cells := (hiff 0 ((h : ℤ) + 11)).mpr (mem4_of_omega (by omega))
          have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 10) (by omega) (by omega) (by omega)
          have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
            (r_s := (h : ℤ) + 10) (x₀ := 0) (y₀ := (h : ℤ) + 9)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm110)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm210)
            (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm011)
            (bucketCell_insert_of_not_mem (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 9)).mp (not_mem4_of_omega (by omega))))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          hy_iso hocc_iso isoNotch_LS_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        rcases htgt with rfl | rfl
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hbal : Balcony (U.insert u) j.val H' ((r : ℤ) + 2) 0 :=
            mk_balcony_0 (by omega) (by omega)
              (bucketCell_insert_of_not_mem (by
                rw [bcell0 hframe hpat (by omega) (by omega)]
                unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((r : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
          have h3f : bucketCell U j.val 3 ((h : ℤ) + 12) = false := by
            rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 12).toNat = h + 12 by omega]
            unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega
          have h4f : bucketCell U j.val 4 ((h : ℤ) + 12) = false := by
            rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 12).toNat = h + 12 by omega]
            unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega
          exact not_fillableStrict_of_anyPlay (j := j)
            (anyPlay_unfillable_of_subNotchRectangle_ge2 hReason (bucketFrame_insert hframe) j_pad
              (r := (h : ℤ) + 12) (col := 1) (d := 2) (b := (r : ℤ) + 2) (ib := 0)
              (Or.inl rfl) (by omega) (by omega) (by omega)
              ⟨by omega, by omega, by omega,
                bucketCell_insert_of_not_mem h3f (mt (hiff 3 ((h : ℤ) + 12)).mp (not_mem4_of_omega (by omega))),
                bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 12)).mp (not_mem4_of_omega (by omega)))⟩
              hbal
              (by
                have h' : bucketCell (U.insert u) j_pad.val 1 ((h : ℤ) + 9) = true :=
                  bucketCell_insert_of_true (by
                    dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
                    unfold addNotchLG weirdPlateauPat; apply bool_or_left; apply bool_or_right
                    rw [decide_eq_true_eq]; omega)
                exact bcell_eq_of_eq h' (by omega))
              (fun z hz1 hz2 => bucketCell_insert_of_not_mem (by
                dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
                unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 1 z).mp (not_mem4_of_omega (by omega))))) hfill
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm03 : (6 * (j.val : ℤ) + 0, (r : ℤ) + 3) ∈ u.cells := (hiff 0 ((r : ℤ) + 3)).mpr (mem4_of_omega (by omega))
          have h34 := bucketCell_notch_wall_B hframe j_pad (y := (r : ℤ) + 2) (by omega) (by omega) (by omega)
          have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
            (r_s := (r : ℤ) + 2) (x₀ := 1) (y₀ := (r : ℤ) + 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
            (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm03)
            (bucketCell_insert_of_not_mem (by
              rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 1 ((r : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

/-- `.Sq` #1 in `WeirdPlateauAt` produces `weirdPlusSqPat h`! -/
theorem prop_WP_Sq1 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hwp : WeirdPlateauAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    4 ≤ h ∧ h + 12 ≤ H' ∧ (h + 1) % 6 = 5 ∧
      BucketPattern (U.insert u) j.val H' (weirdPlusSqPat h) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hframe.2.1 with ⟨_, _⟩
  rcases hwp with ⟨hh4, hh12, hmod, hpat⟩
  have hy_low := weirdPlateau_nonI_ge_h8 hReason hframe j_pad hh12 hpat
    (fun x hx => by unfold weirdPlateauPat addNotchLG unpreppedPat; rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega)
    (by decide) hin hy_u htraj
  obtain ⟨x₀, y₀, hx0, _, hiff, hf00, hf10, _, _, hsup⟩ :=
    sq_012_cases hReason hs_le hframe j hpat (weirdPlateauPat_sym34 h) hin hy_u htraj hfill
  have hy0_ge : h + 8 ≤ y₀ := by
    have := hy_low _ ((hiff x₀ y₀).mpr ⟨Or.inl rfl, Or.inl rfl⟩); dsimp at this; omega
  unfold weirdPlateauPat addNotchLG unpreppedPat at hf00 hf10 hsup
  simp only [Bool.or_eq_false_iff, Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq] at hf00 hf10 hsup
  have hy0_eq : y₀ = h + 10 := by rcases hx0 with rfl | rfl <;> omega
  subst y₀
  rcases hx0 with rfl | rfl
  · exfalso
    have hm010 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 10) ∈ u.cells := (hiff 0 ((h : ℤ) + 10)).mpr ⟨Or.inl rfl, Or.inl (by omega)⟩
    have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 9) (by omega) (by omega) (by omega)
    have hhole := hasHole_of_col0_balcony_seal (bucketFrame_insert hframe) j_pad
      (y_low := (h : ℤ) + 9) (y_top := (h : ℤ) + 10) (by omega) (by omega) (by omega)
      (by
        have h' : bucketCell (U.insert u) j.val 0 ((h : ℤ) + 9) = false :=
          bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 9)).mp (by omega))
        exact bcell_eq_of_eq h' (by omega))
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm010)
      (bucketCell_insert_of_true (by
        rw [bcell1 hframe hpat (by omega) (by omega)]
        unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
      (bucketCell_insert_of_true (by
        rw [bcell2 hframe hpat (by omega) (by omega)]
        unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
      (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
      (fun y hy1 hy2 => by
        have hy_eq : y = (h : ℤ) + 9 := by omega
        rw [hy_eq]; exact bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat (by omega) (by omega)]
          unfold weirdPlateauPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · refine ⟨hh4, hh12, hmod, ?_⟩
    apply bucketPattern_congr (bucketPattern_insert_same hframe (j := j_pad) hin hy_u hpat)
    intro x y _ _
    unfold weirdPlusSqPat; congr 1
    rw [decide_eq_decide, hiff x y]; omega

/-- `.Sq` #2 in `weirdPlusSqPat h` is impossible! -/
theorem prop_WP_Sq2 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hh4 : 4 ≤ h) (hh12 : h + 12 ≤ H') (hmod : (h + 1) % 6 = 5)
    (hpat : BucketPattern U j.val H' (weirdPlusSqPat h))
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  have hy_low := weirdPlateau_nonI_ge_h8 hReason hframe j_pad hh12 hpat
    (fun x hx => by unfold weirdPlusSqPat weirdPlateauPat addNotchLG unpreppedPat; rw [← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, ← Bool.decide_or, decide_eq_decide]; omega)
    (by decide) hin hy_u htraj
  obtain ⟨x₀, y₀, hx0, hyH, hiff, hf00, hf10, _, _, hsup⟩ :=
    sq_012_cases hReason hs_le hframe j hpat (weirdPlusSqPat_sym34 h) hin hy_u htraj hfill
  have hy0_ge : h + 8 ≤ y₀ := by
    have := hy_low _ ((hiff x₀ y₀).mpr ⟨Or.inl rfl, Or.inl rfl⟩); dsimp at this; omega
  unfold weirdPlusSqPat weirdPlateauPat addNotchLG unpreppedPat at hf00 hf10 hsup
  simp only [Bool.or_eq_false_iff, Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq] at hf00 hf10 hsup
  have hy0_eq : y₀ = h + 12 := by rcases hx0 with rfl | rfl <;> omega
  subst y₀
  rcases hx0 with rfl | rfl
  · have hm012 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 12) ∈ u.cells := (hiff 0 ((h : ℤ) + 12)).mpr ⟨Or.inl rfl, Or.inl (by omega)⟩
    have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 11) (by omega) (by omega) (by omega)
    have hhole := hasHole_of_col0_balcony_seal (bucketFrame_insert hframe) j_pad
      (y_low := (h : ℤ) + 11) (y_top := (h : ℤ) + 12) (by omega) (by omega) (by omega)
      (by
        have h' : bucketCell (U.insert u) j.val 0 ((h : ℤ) + 11) = false :=
          bucketCell_insert_of_not_mem (by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold weirdPlusSqPat weirdPlateauPat addNotchLG unpreppedPat; simp; omega) (mt (hiff 0 ((h : ℤ) + 11)).mp (by omega))
        exact bcell_eq_of_eq h' (by omega))
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm012)
      (bucketCell_insert_of_true (by
        rw [bcell1 hframe hpat (by omega) (by omega)]
        unfold weirdPlusSqPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
      (bucketCell_insert_of_true (by
        rw [bcell2 hframe hpat (by omega) (by omega)]
        unfold weirdPlusSqPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
      (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
      (fun y hy1 hy2 => by
        have hy_eq : y = (h : ℤ) + 11 := by omega
        rw [hy_eq]; exact bucketCell_insert_of_true (by
          rw [bcell1 hframe hpat (by omega) (by omega)]
          unfold weirdPlusSqPat; apply bool_or_right; rw [decide_eq_true_eq]; omega))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · have hm212 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 12) ∈ u.cells := (hiff 2 ((h : ℤ) + 12)).mpr ⟨by omega, Or.inl (by omega)⟩
    have h4f : bucketCell U j.val 4 ((h : ℤ) + 12) = false := by
      rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), show ((h : ℤ) + 12).toNat = h + 12 by omega]
      unfold weirdPlusSqPat weirdPlateauPat addNotchLG unpreppedPat; simp
    have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := (h : ℤ) + 12)
      (by omega) (by omega) (by omega)
      (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm212)
      (bucketCell_insert_of_not_mem h4f (mt (hiff 4 ((h : ℤ) + 12)).mp (by omega)))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill

/-! ### Bundled `DeadPlateau` Transitions -/

def DeadAfterLG (U : Board) (j H' : ℕ) : Prop :=
  (∃ h r : ℕ, 9 ≤ h ∧ h + 1 ≤ r ∧ r + 6 ≤ H' ∧ (h + 2) % 6 = 5 ∧ (r + 1) % 6 = 5 ∧
    BucketPattern U j H' (addNotchLG (tallPlateauPat h) r)) ∨
  (∃ h r : ℕ, 4 ≤ h ∧ h + 12 ≤ r ∧ r + 6 ≤ H' ∧ (h + 1) % 6 = 5 ∧ (r + 1) % 6 = 5 ∧
    BucketPattern U j H' (addNotchLG (weirdPlateauPat h) r))

def DeadAfterSq (U : Board) (j H' : ℕ) : Prop :=
  ∃ h : ℕ, 4 ≤ h ∧ h + 12 ≤ H' ∧ (h + 1) % 6 = 5 ∧ BucketPattern U j H' (weirdPlusSqPat h)

lemma deadPlateau_LS {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hdp : DeadPlateau U j.val H')
    {u : PieceState} (hin : InBucket j.val u) (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u) (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  rcases hdp with ⟨h, htp⟩ | ⟨h, hwp⟩
  · exact prop_C13 hReason hs_le hframe j htp hin hy_u htraj hfill
  · exact prop_WP_LS hReason hs_le hframe j hwp hin hy_u htraj hfill

lemma deadPlateau_LG {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hdp : DeadPlateau U j.val H')
    {u : PieceState} (hin : InBucket j.val u) (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LG u) (hfill : FillableStrict R s s' H' (U.insert u) j) :
    DeadAfterLG (U.insert u) j.val H' := by
  rcases hdp with ⟨h, htp⟩ | ⟨h, hwp⟩
  · obtain ⟨r, hh9, hr, hrH, hm, hrm, hp⟩ := prop_C15 hReason hs_le hframe j htp hin hy_u htraj hfill
    exact Or.inl ⟨h, r, hh9, hr, hrH, hm, hrm, hp⟩
  · obtain ⟨r, hh4, hr, hrH, hm, hrm, hp⟩ := prop_WP_LG hReason hs_le hframe j hwp hin hy_u htraj hfill
    exact Or.inr ⟨h, r, hh4, hr, hrH, hm, hrm, hp⟩

lemma deadAfterLG_LS {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hda : DeadAfterLG U j.val H')
    {u : PieceState} (hin : InBucket j.val u) (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u) (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  rcases hda with ⟨h, r, hh9, hr, hrH, hm, hrm, hp⟩ | ⟨h, r, hh4, hr, hrH, hm, hrm, hp⟩
  · exact prop_C16 hReason hs_le hframe j hh9 hr hrH hm hrm hp hin hy_u htraj hfill
  · exact prop_WP_LS_lgWp hReason hs_le hframe j hh4 hr hrH hm hrm hp hin hy_u htraj hfill

lemma deadPlateau_Sq1 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hdp : DeadPlateau U j.val H')
    {u : PieceState} (hin : InBucket j.val u) (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u) (hfill : FillableStrict R s s' H' (U.insert u) j) :
    DeadAfterSq (U.insert u) j.val H' := by
  rcases hdp with ⟨h, htp⟩ | ⟨h, hwp⟩
  · exact False.elim (prop_C14 hReason hs_le hframe j htp hin hy_u htraj hfill)
  · obtain ⟨hh4, hh12, hm, hp⟩ := prop_WP_Sq1 hReason hs_le hframe j hwp hin hy_u htraj hfill
    exact ⟨h, hh4, hh12, hm, hp⟩

lemma deadAfterSq_Sq2 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    (hda : DeadAfterSq U j.val H')
    {u : PieceState} (hin : InBucket j.val u) (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u) (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  rcases hda with ⟨h, hh4, hh12, hm, hp⟩
  exact prop_WP_Sq2 hReason hs_le hframe j hh4 hh12 hm hp hin hy_u htraj hfill

def relFlatOcc (dx dy : ℤ) : Bool :=
  let _ := dx
  decide (dy < 0)

/-! ### Appendix C.1.6: Underflat Buckets (Propositions C.17 – C.20) -/

private lemma c17_check :
    allInTargets (validRelPlacements012 .LG relFlatOcc 0 3)
      [[(0, 0), (1, 0), (2, 0), (0, 1)],
       [(0, 1), (1, 1), (2, 1), (2, 0)],
       [(0, 0), (1, 0), (1, 1), (1, 2)],
       [(1, 0), (2, 0), (2, 1), (2, 2)],
       [(0, 0), (0, 1), (0, 2), (1, 2)],
       [(1, 0), (1, 1), (1, 2), (2, 2)]] = true := by decide


private lemma c19_check :
    allInTargets (validRelPlacements012 .LS relFlatOcc 0 3)
      [[(0, 0), (0, 1), (1, 1), (1, 2)],
       [(1, 0), (1, 1), (2, 1), (2, 2)],
       [(1, 0), (2, 0), (0, 1), (1, 1)]] = true := by decide

/-- Proposition C.19: `.LS` in `UnderflatAt` is impossible! -/
theorem prop_C19 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (huf : UnderflatAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases huf with ⟨hh4, _, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (overflatPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · have hy_box : ∀ z ∈ u.cells, (h : ℤ) + 0 ≤ z.2 ∧ z.2 ≤ (h : ℤ) + 3 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h) (y_top := h)
        (fun x y hx hy => by unfold overflatPat; rw [decide_eq_true_eq]; omega)
        (fun x y _ hy => by unfold overflatPat; simp [show ¬ y < h by omega])
        hin hy_u htraj hx_012
      intro z hz; have := hb z hz; omega
    have hh_lt : (h : ℤ) < H' := by
      rcases cells_nonempty_B u with ⟨z, hz⟩
      have := hy_box z hz; have := hy_u z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 3 →
        bucketCell U j.val dx ((h : ℤ) + dy) = relFlatOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
      unfold overflatPat relFlatOcc; rw [decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c19_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    have h3f : bucketCell U j.val 3 h = false := by
      rw [bcell3_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
      unfold overflatPat; simp
    have h4f : bucketCell U j.val 4 h = false := by
      rw [bcell4_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
      unfold overflatPat; simp
    rcases htgt with rfl | rfl | rfl
    · have hm01 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm11 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hh1_lt : (h : ℤ) + 1 < H' := (hy_u _ hm01).2
      have h2f : bucketCell U j.val 2 ((h : ℤ) + 1) = false := by
        rw [bcell2 hframe hpat (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold overflatPat; simp
      have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 1) 2 :=
        mk_balcony_2 (by omega) hh1_lt
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm01)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm11)
          (bucketCell_insert_of_not_mem h2f (mt (hiff 2 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_flooredNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, hh_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          ⟨(h : ℤ) + 1, 2, by omega, hbal⟩,
          Or.inr (Or.inr ⟨bucketCell_insert_of_true (by
              rw [bcell0 hframe hpat (by omega) (by omega)]
              unfold overflatPat; rw [decide_eq_true_eq]; omega),
            bucketCell_insert_of_true (by
              rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold overflatPat; rw [decide_eq_true_eq]; omega),
            bucketCell_insert_of_true (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold overflatPat; rw [decide_eq_true_eq]; omega)⟩)⟩ hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, hh_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh_lt hm1⟩ hfill
    · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ)) ∈ u.cells := (hiff 2 h).mpr (mem4_of_omega (by omega))
      have hm0u : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hhole := hasHole_of_blocked_notch (bucketFrame_insert hframe) j_pad (r := h)
        (by omega) (hy_u _ hm0u).2 (by omega)
        (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh_lt hm2)
        (bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

/-- Proposition C.28: `.Sq` in `TriggerHappyAt` is impossible! -/
theorem prop_C28 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hth : TriggerHappyAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .Sq u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hth with ⟨hh6, _, hmod, hpat⟩
  obtain ⟨x₀, y₀, hx0, hyH, hiff, hf00, hf10, _, _, hsup⟩ :=
    sq_012_cases hReason hs_le hframe j hpat (triggerHappyPat_sym34 h) hin hy_u htraj hfill
  unfold triggerHappyPat at hf00 hf10 hsup
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hf00 hf10 hsup
  have hy0_eq : y₀ = h - 1 := by rcases hx0 with rfl | rfl <;> omega
  subst y₀
  rcases hx0 with rfl | rfl
  · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr ⟨Or.inr rfl, Or.inr (by omega)⟩
    have h3f : bucketCell U j.val 3 h = false := by
      rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
      unfold triggerHappyPat; simp
    have h4f : bucketCell U j.val 4 h = false := by
      rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
      unfold triggerHappyPat; simp
    exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
      ⟨h, ⟨by omega, by omega, by omega,
        bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (by omega)),
        bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (by omega))⟩,
        bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
  · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) - 1) ∈ u.cells := (hiff 2 ((h : ℤ) - 1)).mpr ⟨by omega, Or.inl (by omega)⟩
    have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) - 2) (by omega) (by omega) (by omega)).1
    have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) - 2)
      (by omega) (by omega) (by omega) (by omega)
      (bucketCell_insert_of_not_mem (by
        rw [bcell2 hframe hpat (by omega) (by omega)]
        unfold triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (by omega)))
      (bucketCell_insert_of_true h3w)
      (bucketCell_insert_of_true (by
        rw [show (2 : ℤ) - 1 = 1 by rfl, bcell1 hframe hpat (by omega) (by omega)]
        unfold triggerHappyPat; rw [decide_eq_true_eq]; omega))
      (by
        have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2
        exact bcell_eq_of_eq h' (by omega))
      (by
        have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) - 3) = true :=
          bucketCell_insert_of_true (by
            rw [bcell2 hframe hpat (by omega) (by omega)]
            unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
        exact bcell_eq_of_eq h' (by omega))
    exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill

def relTHOcc (dx dy : ℤ) : Bool :=
  decide (dy < 0 ∨ (dy = 0 ∧ dx ≠ 2))

private lemma c29_check :
    allInTargets (validRelPlacements012 .LG relTHOcc 0 4)
      [[(0, 1), (1, 1), (2, 1), (2, 0)],
       [(0, 1), (1, 1), (2, 1), (0, 2)],
       [(0, 1), (1, 1), (1, 2), (1, 3)],
       [(1, 1), (2, 1), (2, 2), (2, 3)],
       [(0, 1), (0, 2), (0, 3), (1, 3)],
       [(1, 1), (1, 2), (1, 3), (2, 3)]] = true := by decide

/-- Proposition C.29: `.LG` in `TriggerHappyAt` produces `UnderflatAt` or `addNotchLG (triggerHappyPat h) r` (`h ≤ r`)! -/
theorem prop_C29 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hth : TriggerHappyAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LG u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) :
    UnderflatAt (U.insert u) j.val H' h ∨
    (∃ r : ℕ, 6 ≤ h ∧ h ≤ r ∧ r + 6 ≤ H' ∧ (h + 1) % 6 = 5 ∧ (r + 1) % 6 = 5 ∧
      BucketPattern (U.insert u) j.val H' (addNotchLG (triggerHappyPat h) r)) := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hth with ⟨hh6, hhH, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (triggerHappyPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨r, _, hrmod, hpat3r, hopen, ⟨hI, _⟩ | ⟨_, hpat', _⟩⟩
  · have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 2) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 2) + 4 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 2) (y_top := h - 1)
        (fun x y hx hy => by unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
        (fun x y _ hy => by unfold triggerHappyPat; simp; omega)
        hin hy_u htraj hx_012
      intro z hz; have := hb z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 4 →
        bucketCell U j.val dx (((h : ℤ) - 2) + dy) = relTHOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
      unfold triggerHappyPat relTHOcc; rw [decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c29_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    rcases htgt with rfl | rfl | rfl | rfl | rfl | rfl
    · left
      refine ⟨by omega, hhH, hmod, ?_⟩
      intro x y
      rw [bucketPattern_insert_same hframe (j := j_pad) hin hy_u hpat x y]
      have hmem_eq : decide ((6 * (j.val : ℤ) + (x.val : ℤ), (y.val : ℤ)) ∈ u.cells) =
          decide ((x.val ≤ 2 ∧ y.val = h - 1) ∨ (x.val = 2 ∧ y.val = h - 2)) := by
        rw [decide_eq_decide, hiff x.val y.val]; exact iff_mem4_of_omega (by omega)
      dsimp only [j_pad]; rw [hmem_eq]; unfold triggerHappyPat overflatPat
      have hx_lt := x.isLt
      by_cases hy_eq : y.val = h - 1
      · rw [hy_eq]
        by_cases hx3 : 3 ≤ x.val
        · simp [show h - 1 < H' by omega, show (h - 1 + 1) % 6 ≠ 5 by omega, hx3]
        · congr 1
          rw [← Bool.decide_or, decide_eq_decide]; omega
      · congr 1; rw [← Bool.decide_or, decide_eq_decide]; omega
    · exfalso
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) - 1) ∈ u.cells := (hiff 2 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
      have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) - 2) (by omega) (by omega) (by omega)).1
      have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) - 2)
        (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_true h3w)
        (bucketCell_insert_of_true (by
          rw [show (2 : ℤ) - 1 = 1 by rfl, bcell1 hframe hpat (by omega) (by omega)]
          unfold triggerHappyPat; rw [decide_eq_true_eq]; omega))
        (by
          have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2
          exact bcell_eq_of_eq h' (by omega))
        (by
          have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) - 3) = true :=
            bucketCell_insert_of_true (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · exfalso
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hh_lt : (h : ℤ) < H' := (hy_u _ hm1).2
      have h3f : bucketCell U j.val 3 h = false := by
        rw [bcell3_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      have h4f : bucketCell U j.val 4 h = false := by
        rw [bcell4_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, hh_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh_lt hm1⟩ hfill
    · exfalso
      have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) - 1) ∈ u.cells := (hiff 2 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
      have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) - 2) (by omega) (by omega) (by omega)).1
      have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) - 2)
        (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_true h3w)
        (bucketCell_insert_of_true (by
          rw [show (2 : ℤ) - 1 = 1 by rfl, bcell1 hframe hpat (by omega) (by omega)]
          unfold triggerHappyPat; rw [decide_eq_true_eq]; omega))
        (by
          have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2
          exact bcell_eq_of_eq h' (by omega))
        (by
          have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) - 3) = true :=
            bucketCell_insert_of_true (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · exfalso
      have hm01 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 1) ∈ u.cells := (hiff 0 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hm11 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 1) ∈ u.cells := (hiff 1 ((h : ℤ) + 1)).mpr (mem4_of_omega (by omega))
      have hh1_lt : (h : ℤ) + 1 < H' := (hy_u _ hm01).2
      have h2f : bucketCell U j.val 2 ((h : ℤ) + 1) = false := by
        rw [bcell2 hframe hpat (by omega) (by omega), show ((h : ℤ) + 1).toNat = h + 1 by omega]
        unfold triggerHappyPat; simp; omega
      have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 1) 2 :=
        mk_balcony_2 (by omega) hh1_lt
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm01)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm11)
          (bucketCell_insert_of_not_mem h2f (mt (hiff 2 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
      exact not_fillableStrict_of_anyPlay (j := j)
        (anyPlay_unfillable_of_twoVeranda_ge2 hReason (bucketFrame_insert hframe) j_pad 1
          (bottom := (h : ℤ) - 1) (b := (h : ℤ) + 1) (ib := 2) (by omega) (by omega) hbal
          (by
            have h' : bucketCell (U.insert u) j_pad.val 1 ((h : ℤ) - 2) = true :=
              bucketCell_insert_of_true (by
                dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
                unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
            exact bcell_eq_of_eq h' (by omega))
          (bucketCell_insert_of_not_mem (by
            dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega)]
            unfold triggerHappyPat; simp; omega) (mt (hiff 1 ((h : ℤ) - 1)).mp (not_mem4_of_omega (by omega))))
          (by
            have h' : bucketCell (U.insert u) j_pad.val 1 h = false :=
              bucketCell_insert_of_not_mem (by
                dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega), Int.toNat_natCast]
                unfold triggerHappyPat; simp) (mt (hiff 1 h).mp (not_mem4_of_omega (by omega)))
            exact bcell_eq_of_eq h' (by omega))
          (by
            have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh1_lt hm11
            exact bcell_eq_of_eq h' (by omega))) hfill
    · exfalso
      have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hh_lt : (h : ℤ) < H' := (hy_u _ hm1).2
      have h3f : bucketCell U j.val 3 h = false := by
        rw [bcell3_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      have h4f : bucketCell U j.val 4 h = false := by
        rw [bcell4_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, hh_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh_lt hm1⟩ hfill
  · cases hI
  · obtain ⟨_, hrH6⟩ := openNotch_margins hframe hopen.1 hopen.2.1 hopen.2.2.1
    have hr_ge : h ≤ r := by
      unfold triggerHappyPat at hpat3r; simp only [decide_eq_false_iff_not] at hpat3r; omega
    exact Or.inr ⟨r, hh6, hr_ge, by omega, hmod, hrmod, hpat'⟩

private lemma c30_check :
    allInTargets (validRelPlacements012 .LS relTHOcc 0 4)
      [[(0, 1), (0, 2), (1, 2), (1, 3)],
       [(1, 1), (1, 2), (2, 2), (2, 3)],
       [(1, 1), (2, 1), (0, 2), (1, 2)]] = true := by decide

/-- Proposition C.30: `.LS` in `TriggerHappyAt` is impossible! -/
theorem prop_C30 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h : ℕ} (hth : TriggerHappyAt U j.val H' h)
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases hth with ⟨hh6, hhH, hmod, hpat⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat (triggerHappyPat_sym34 h)
      (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 2) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 2) + 4 := by
      have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 2) (y_top := h - 1)
        (fun x y hx hy => by unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
        (fun x y _ hy => by unfold triggerHappyPat; simp; omega)
        hin hy_u htraj hx_012
      intro z hz; have := hb z hz; omega
    have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 4 →
        bucketCell U j.val dx (((h : ℤ) - 2) + dy) = relTHOcc dx dy := by
      intro dx dy hdx0 hdx3 hdy1 hdy2
      rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
      unfold triggerHappyPat relTHOcc; rw [decide_eq_decide]; omega
    obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
      hy_box hocc_rel c30_check
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
    rcases htgt with rfl | rfl | rfl
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hh_lt : (h : ℤ) < H' := (hy_u _ hm1).2
      have h3f : bucketCell U j.val 3 h = false := by
        rw [bcell3_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      have h4f : bucketCell U j.val 4 h = false := by
        rw [bcell4_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, hh_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh_lt hm1⟩ hfill
    · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
      have hh_lt : (h : ℤ) < H' := (hy_u _ hm1).2
      have h3f : bucketCell U j.val 3 h = false := by
        rw [bcell3_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      have h4f : bucketCell U j.val 4 h = false := by
        rw [bcell4_notch hframe hpat (by omega) hh_lt (by omega), Int.toNat_natCast]
        unfold triggerHappyPat; simp
      exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
        ⟨h, ⟨by omega, hh_lt, by omega,
          bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
          bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
          bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) hh_lt hm1⟩ hfill
    · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) - 1) ∈ u.cells := (hiff 2 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
      have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) - 2) (by omega) (by omega) (by omega)).1
      have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) - 2)
        (by omega) (by omega) (by omega) (by omega)
        (bucketCell_insert_of_not_mem (by
          rw [bcell2 hframe hpat (by omega) (by omega)]
          unfold triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (not_mem4_of_omega (by omega))))
        (bucketCell_insert_of_true h3w)
        (bucketCell_insert_of_true (by
          rw [show (2 : ℤ) - 1 = 1 by rfl, bcell1 hframe hpat (by omega) (by omega)]
          unfold triggerHappyPat; rw [decide_eq_true_eq]; omega))
        (by
          have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2
          exact bcell_eq_of_eq h' (by omega))
        (by
          have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) - 3) = true :=
            bucketCell_insert_of_true (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega))
      exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

/-- Reusable helper killing `Balcony` at `b ≥ r₁ + 2` on `addNotchLG (triggerHappyPat h) r₁` (or `LG-TH-2`)! -/
lemma kill_balcony_on_lgTH {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (_hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h r₁ : ℕ} {pat : ℕ → ℕ → Bool}
    (hh6 : 6 ≤ h) (hr_ge : h ≤ r₁) (hrH6 : r₁ + 6 ≤ H') (hmod : (h + 1) % 6 = 5)
    (hpat : BucketPattern U j.val H' pat)
    (hpat_low : ∀ x y : ℕ, x < 5 → y ≤ h → pat x y = addNotchLG (triggerHappyPat h) r₁ x y)
    {u : PieceState}
    (hno_low : ∀ x y : ℤ, 0 ≤ x → x < 5 → y ≤ (h : ℤ) → (6 * (j.val : ℤ) + x, y) ∉ u.cells)
    {b : ℤ} {ib : Fin 3} (hb_ge : (r₁ : ℤ) + 2 ≤ b)
    (hbal : Balcony (U.insert u) j.val H' b ib) :
    ¬ FillableStrict R s s' H' (U.insert u) j := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  by_cases hrh : r₁ = h
  · subst r₁
    exact not_fillableStrict_of_anyPlay (j := j)
      (anyPlay_unfillable_of_twoVeranda_ge2 hReason (bucketFrame_insert hframe) j_pad 2
        (bottom := (h : ℤ) - 2) (b := b) (ib := ib) (by omega) (by omega) hbal
        (by
          have h' : bucketCell (U.insert u) j_pad.val 2 ((h : ℤ) - 3) = true :=
            bucketCell_insert_of_true (by
              dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega),
                hpat_low 2 _ (by omega) (by omega)]
              unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega))
        (bucketCell_insert_of_not_mem (by
          dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega),
            hpat_low 2 _ (by omega) (by omega)]
          unfold addNotchLG triggerHappyPat; simp; omega) (hno_low 2 ((h : ℤ) - 2) (by omega) (by omega) (by omega)))
        (by
          have h' : bucketCell (U.insert u) j_pad.val 2 ((h : ℤ) - 1) = false :=
            bucketCell_insert_of_not_mem (by
              dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega),
                hpat_low 2 _ (by omega) (by omega)]
              unfold addNotchLG triggerHappyPat; simp; omega) (hno_low 2 ((h : ℤ) - 1) (by omega) (by omega) (by omega))
          exact bcell_eq_of_eq h' (by omega))
        (by
          have h' : bucketCell (U.insert u) j_pad.val 2 h = true :=
            bucketCell_insert_of_true (by
              dsimp [j_pad]; rw [bcell2 hframe hpat (by omega) (by omega), Int.toNat_natCast,
                hpat_low 2 h (by omega) le_rfl]
              unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega)))
  · have h3f : bucketCell U j.val 3 h = false := by
      rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast, hpat_low 3 h (by omega) le_rfl]
      unfold addNotchLG triggerHappyPat; simp; omega
    have h4f : bucketCell U j.val 4 h = false := by
      rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast, hpat_low 4 h (by omega) le_rfl]
      unfold addNotchLG triggerHappyPat; simp; omega
    exact not_fillableStrict_of_anyPlay (j := j)
      (anyPlay_unfillable_of_subNotchRectangle_ge2 hReason (bucketFrame_insert hframe) j_pad
        (r := h) (col := 1) (d := 1) (b := b) (ib := ib)
        (Or.inl rfl) le_rfl (by omega) (by omega)
        ⟨by omega, by omega, by omega,
          bucketCell_insert_of_not_mem h3f (hno_low 3 h (by omega) (by omega) le_rfl),
          bucketCell_insert_of_not_mem h4f (hno_low 4 h (by omega) (by omega) le_rfl)⟩
        hbal
        (by
          have h' : bucketCell (U.insert u) j_pad.val 1 ((h : ℤ) - 2) = true :=
            bucketCell_insert_of_true (by
              dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega),
                hpat_low 1 _ (by omega) (by omega)]
              unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
          exact bcell_eq_of_eq h' (by omega))
        (fun z hz1 hz2 => bucketCell_insert_of_not_mem (by
          dsimp [j_pad]; rw [bcell1 hframe hpat (by omega) (by omega),
            hpat_low 1 z.toNat (by omega) (by omega)]
          unfold addNotchLG triggerHappyPat; simp; omega) (hno_low 1 z (by omega) (by omega) hz2)))


def relLgTHAtHOcc (dx dy : ℤ) : Bool :=
  decide (dy < 0 ∨ (dy = 0 ∧ dx ≠ 2) ∨ (dx = 2 ∧ (dy = 2 ∨ dy = 3)))

private lemma c32_rh_check :
    allInTargets (validRelPlacements012 .LS relLgTHAtHOcc 0 7)
      [[(0, 1), (0, 2), (1, 2), (1, 3)],
       [(1, 1), (2, 1), (0, 2), (1, 2)],
       [(1, 3), (1, 4), (2, 4), (2, 5)],
       [(1, 4), (2, 4), (0, 5), (1, 5)]] = true := by decide

/-- Proposition C.32: `.LS` in `addNotchLG (triggerHappyPat h) r` (`h ≤ r`) is impossible! -/
theorem prop_C32 {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U : Board} (hframe : BucketFrame U s' H') (j : Fin s)
    {h r : ℕ} (hh6 : 6 ≤ h) (hr_ge : h ≤ r) (hrH6 : r + 6 ≤ H')
    (hmod : (h + 1) % 6 = 5) (hrmod : (r + 1) % 6 = 5)
    (hpat : BucketPattern U j.val H' (addNotchLG (triggerHappyPat h) r))
    {u : PieceState} (hin : InBucket j.val u)
    (hy_u : ∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ))
    (htraj : Trajectory R U .LS u)
    (hfill : FillableStrict R s s' H' (U.insert u) j) : False := by
  let j_pad : Fin s' := ⟨j.val, by omega⟩
  rcases split_012_or_openNotch hReason hs_le hframe j hpat
      (addNotchLG_sym34 (triggerHappyPat_sym34 h) r) (by decide) hin hy_u htraj hfill with
    hx_012 | ⟨_, _, _, _, _, ⟨hI, _⟩ | ⟨hLG, _⟩⟩
  · by_cases hrh : r = h
    · subst r
      have hy_box : ∀ z ∈ u.cells, ((h : ℤ) - 2) + 0 ≤ z.2 ∧ z.2 ≤ ((h : ℤ) - 2) + 7 := by
        have hb := box_of_012_bounds hframe (j := j_pad) hpat (y_floor := h - 2) (y_top := h + 2)
          (fun x y hx hy => by unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold addNotchLG triggerHappyPat; simp; omega)
          hin hy_u htraj hx_012
        intro z hz; have := hb z hz; omega
      have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 7 →
          bucketCell U j.val dx (((h : ℤ) - 2) + dy) = relLgTHAtHOcc dx dy := by
        intro dx dy hdx0 hdx3 hdy1 hdy2
        rw [bucketPattern_eval_012 hframe hpat hdx0 hdx3 (by omega) (by omega)]
        unfold addNotchLG triggerHappyPat relLgTHAtHOcc
        rw [← Bool.decide_or, decide_eq_decide]; omega
      obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
        hy_box hocc_rel c32_rh_check
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
      rcases htgt with rfl | rfl | rfl | rfl
      · have hm0h : (6 * (j.val : ℤ) + 0, (h : ℤ)) ∈ u.cells := (hiff 0 h).mpr (mem4_of_omega (by omega))
        have hm1h : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
        have hhole := hasHole_of_closed_row (bucketFrame_insert hframe) j_pad
          (r := h) (x₀ := 2) (y₀ := (h : ℤ) - 2) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm0h)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1h)
          (bucketCell_insert_of_true (by
            rw [bcell2 hframe hpat (by omega) (by omega), Int.toNat_natCast]
            unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_true (by
            rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
            unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_true (by
            rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
            unfold addNotchLG; apply bool_or_right; rw [decide_eq_true_eq]; omega))
          (bucketCell_insert_of_not_mem (by
            rw [bcell2 hframe hpat (by omega) (by omega)]
            unfold addNotchLG triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) - 1) ∈ u.cells := (hiff 2 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
        have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) - 2) (by omega) (by omega) (by omega)).1
        have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) - 2)
          (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_not_mem (by
            rw [bcell2 hframe hpat (by omega) (by omega)]
            unfold addNotchLG triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (not_mem4_of_omega (by omega))))
          (bucketCell_insert_of_true h3w)
          (bucketCell_insert_of_true (by
            rw [show (2 : ℤ) - 1 = 1 by rfl, bcell1 hframe hpat (by omega) (by omega)]
            unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega))
          (by
            have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2
            exact bcell_eq_of_eq h' (by omega))
          (by
            have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) - 3) = true :=
              bucketCell_insert_of_true (by
                rw [bcell2 hframe hpat (by omega) (by omega)]
                unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
            exact bcell_eq_of_eq h' (by omega))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · have hm12 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 2) ∈ u.cells := (hiff 1 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm22 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 2) ∈ u.cells := (hiff 2 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have h0f : bucketCell U j.val 0 ((h : ℤ) + 2) = false := by
          rw [bcell0 hframe hpat (by omega) (by omega)]
          unfold addNotchLG triggerHappyPat; simp; omega
        have hbal : Balcony (U.insert u) j.val H' ((h : ℤ) + 2) 0 :=
          mk_balcony_0 (by omega) (by omega)
            (bucketCell_insert_of_not_mem h0f (mt (hiff 0 ((h : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
        exact kill_balcony_on_lgTH hReason hs_le hframe j hh6 le_rfl hrH6 hmod hpat
          (fun _ _ _ _ => rfl) (fun x y _ _ hy => mt (hiff x y).mp (not_mem4_of_omega (by omega))) le_rfl hbal hfill
      · have hm12 : (6 * (j.val : ℤ) + 1, (h : ℤ) + 2) ∈ u.cells := (hiff 1 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm22 : (6 * (j.val : ℤ) + 2, (h : ℤ) + 2) ∈ u.cells := (hiff 2 ((h : ℤ) + 2)).mpr (mem4_of_omega (by omega))
        have hm03 : (6 * (j.val : ℤ) + 0, (h : ℤ) + 3) ∈ u.cells := (hiff 0 ((h : ℤ) + 3)).mpr (mem4_of_omega (by omega))
        have h34 := bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) + 2) (by omega) (by omega) (by omega)
        have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
          (r_s := (h : ℤ) + 2) (x₀ := 1) (y₀ := (h : ℤ) + 1)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
          (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
          (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm03)
          (bucketCell_insert_of_not_mem (by
            rw [bcell1 hframe hpat (by omega) (by omega)]
            unfold addNotchLG triggerHappyPat; simp; omega) (mt (hiff 1 ((h : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
        exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
    · rcases split_base_or_isoNotch hframe (j := j_pad) hrH6 hpat (y_floor := h - 2) (y_top := h - 1)
          (by omega)
          (fun x y hx hy => by unfold triggerHappyPat; rw [decide_eq_true_eq]; omega)
          (fun x y _ hy => by unfold triggerHappyPat; simp; omega)
          (by omega) hin hy_u htraj hx_012 with
        ⟨hy_base, hocc_base⟩ | ⟨hy_iso, hocc_iso⟩
      · have hocc_rel : ∀ dx dy : ℤ, 0 ≤ dx → dx < 3 → -1 ≤ dy → dy ≤ 4 →
            bucketCell U j.val dx (((h : ℤ) - 2) + dy) = relTHOcc dx dy := by
          intro dx dy hdx0 hdx3 hdy1 hdy2
          dsimp only [j_pad] at hocc_base
          rw [show ((h : ℤ) - 2) + dy = ((h - 2 : ℕ) : ℤ) + dy by omega, hocc_base dx dy hdx0 hdx3 hdy1 (by omega), if_neg (by omega)]
          unfold triggerHappyPat relTHOcc; rw [decide_eq_decide]; omega
        obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          (fun z hz => by have := hy_base z hz; omega) hocc_rel c30_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        have h3f : bucketCell U j.val 3 h = false := by
          rw [bcell3_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
          unfold addNotchLG triggerHappyPat; simp; omega
        have h4f : bucketCell U j.val 4 h = false := by
          rw [bcell4_notch hframe hpat (by omega) (by omega) (by omega), Int.toNat_natCast]
          unfold addNotchLG triggerHappyPat; simp; omega
        rcases htgt with rfl | rfl | rfl
        · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
          exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
            ⟨h, ⟨by omega, by omega, by omega,
              bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
              bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
              bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
        · have hm1 : (6 * (j.val : ℤ) + 1, (h : ℤ)) ∈ u.cells := (hiff 1 h).mpr (mem4_of_omega (by omega))
          exact not_fillableStrict_of_spurnedNotch hReason hs_le (bucketFrame_insert hframe) j
            ⟨h, ⟨by omega, by omega, by omega,
              bucketCell_insert_of_not_mem h3f (mt (hiff 3 h).mp (not_mem4_of_omega (by omega))),
              bucketCell_insert_of_not_mem h4f (mt (hiff 4 h).mp (not_mem4_of_omega (by omega)))⟩,
              bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm1⟩ hfill
        · have hm2 : (6 * (j.val : ℤ) + 2, (h : ℤ) - 1) ∈ u.cells := (hiff 2 ((h : ℤ) - 1)).mpr (mem4_of_omega (by omega))
          have h3w := (bucketCell_notch_wall_B hframe j_pad (y := (h : ℤ) - 2) (by omega) (by omega) (by omega)).1
          have hhole := hasHole_of_surrounded_B (B := U.insert u) (j := j.val) (H := H') (x := 2) (y := (h : ℤ) - 2)
            (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_not_mem (by
              rw [bcell2 hframe hpat (by omega) (by omega)]
              unfold addNotchLG triggerHappyPat; simp; omega) (mt (hiff 2 ((h : ℤ) - 2)).mp (not_mem4_of_omega (by omega))))
            (bucketCell_insert_of_true h3w)
            (bucketCell_insert_of_true (by
              rw [show (2 : ℤ) - 1 = 1 by rfl, bcell1 hframe hpat (by omega) (by omega)]
              unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega))
            (by
              have h' := bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm2
              exact bcell_eq_of_eq h' (by omega))
            (by
              have h' : bucketCell (U.insert u) j.val 2 ((h : ℤ) - 3) = true :=
                bucketCell_insert_of_true (by
                  rw [bcell2 hframe hpat (by omega) (by omega)]
                  unfold addNotchLG triggerHappyPat; apply bool_or_left; rw [decide_eq_true_eq]; omega)
              exact bcell_eq_of_eq h' (by omega))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
      · obtain ⟨tgt, htgt, hiff⟩ := mem_targets_of_rel012 hframe (j := j_pad) hin hy_u htraj hx_012
          hy_iso hocc_iso isoNotch_LS_check
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htgt
        rcases htgt with rfl | rfl
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have h0f : bucketCell U j.val 0 ((r : ℤ) + 2) = false := by
            rw [bcell0 hframe hpat (by omega) (by omega)]
            unfold addNotchLG triggerHappyPat; simp; omega
          have hbal : Balcony (U.insert u) j.val H' ((r : ℤ) + 2) 0 :=
            mk_balcony_0 (by omega) (by omega)
              (bucketCell_insert_of_not_mem h0f (mt (hiff 0 ((r : ℤ) + 2)).mp (not_mem4_of_omega (by omega))))
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
              (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
          exact kill_balcony_on_lgTH hReason hs_le hframe j hh6 hr_ge hrH6 hmod hpat
            (fun _ _ _ _ => rfl) (fun x y _ _ hy => mt (hiff x y).mp (not_mem4_of_omega (by omega))) le_rfl hbal hfill
        · have hm12 : (6 * (j.val : ℤ) + 1, (r : ℤ) + 2) ∈ u.cells := (hiff 1 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm22 : (6 * (j.val : ℤ) + 2, (r : ℤ) + 2) ∈ u.cells := (hiff 2 ((r : ℤ) + 2)).mpr (mem4_of_omega (by omega))
          have hm03 : (6 * (j.val : ℤ) + 0, (r : ℤ) + 3) ∈ u.cells := (hiff 0 ((r : ℤ) + 3)).mpr (mem4_of_omega (by omega))
          have h34 := bucketCell_notch_wall_B hframe j_pad (y := (r : ℤ) + 2) (by omega) (by omega) (by omega)
          have hhole := hasHole_of_inverted_stepped_seal (bucketFrame_insert hframe) j_pad
            (r_s := (r : ℤ) + 2) (x₀ := 1) (y₀ := (r : ℤ) + 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm12)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm22)
            (bucketCell_insert_of_true h34.1) (bucketCell_insert_of_true h34.2)
            (bucketCell_insert_of_mem hframe (j := j_pad) (by omega) (by omega) (by omega) (by omega) hm03)
            (bucketCell_insert_of_not_mem (by
              rw [bcell1 hframe hpat (by omega) (by omega)]
              unfold addNotchLG triggerHappyPat; simp; omega) (mt (hiff 1 ((r : ℤ) + 1)).mp (not_mem4_of_omega (by omega))))
          exact not_fillableStrict_of_hasHole hReason hs_le (bucketFrame_insert hframe) j hhole hfill
  · cases hI
  · cases hLG

end TetrisHard.Rows.Padded.Carbon

namespace TetrisHard.Rows.Padded
open TetrisHard.Rows
open TetrisHard.Rows.Padded.Carbon

private lemma unpreppedAt_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u) {h : ℕ}
    (hunp : UnpreppedAt U k.val H' h) :
    UnpreppedAt (U.insert u) k.val H' h := by
  rcases hunp with ⟨gap, hh4, hhH, hmod, hgap, hpat⟩
  exact ⟨gap, hh4, hhH, hmod, hgap,
    bucketPattern_insert_other (fun he => hne (Fin.ext he)) hin hpat⟩

private lemma overflatAt_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u) {h : ℕ}
    (hof : OverflatAt U k.val H' h) :
    OverflatAt (U.insert u) k.val H' h :=
  ⟨hof.1, hof.2.1, hof.2.2.1,
    bucketPattern_insert_other (fun he => hne (Fin.ext he)) hin hof.2.2.2⟩

private lemma underflatAt_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u) {h : ℕ}
    (huf : UnderflatAt U k.val H' h) :
    UnderflatAt (U.insert u) k.val H' h :=
  ⟨huf.1, huf.2.1, huf.2.2.1,
    bucketPattern_insert_other (fun he => hne (Fin.ext he)) hin huf.2.2.2⟩

private lemma triggerHappyAt_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u) {h : ℕ}
    (hth : TriggerHappyAt U k.val H' h) :
    TriggerHappyAt (U.insert u) k.val H' h :=
  ⟨hth.1, hth.2.1, hth.2.2.1,
    bucketPattern_insert_other (fun he => hne (Fin.ext he)) hin hth.2.2.2⟩

private lemma deadPlateau_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u)
    (hdp : DeadPlateau U k.val H') :
    DeadPlateau (U.insert u) k.val H' := by
  have hne_v : k.val ≠ j.val := fun he => hne (Fin.ext he)
  rcases hdp with ⟨h, hh9, hhH, hm, hp⟩ | ⟨h, hh4, hh12, hm, hp⟩
  · exact Or.inl ⟨h, hh9, hhH, hm, bucketPattern_insert_other hne_v hin hp⟩
  · exact Or.inr ⟨h, hh4, hh12, hm, bucketPattern_insert_other hne_v hin hp⟩


private lemma noRGSeqPlay_cons_unpack {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {t : Piece} {ts : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U (t :: ts) us U')
    (hall : AllFillableStrict R s s' H' U') :
    ∃ (j : Fin s) (u : PieceState) (us' : List PieceState),
      BucketFrame U s' H' ∧
      InBucket j.val u ∧
      (∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ)) ∧
      Trajectory R U t u ∧
      NoRGSeqPlay R s s' H' (U.insert u) ts us' U' ∧
      AllFillableStrict R s s' H' (U.insert u) := by
  cases hp with
  | step j _ hfr hin hy htraj hrest =>
    exact ⟨j, _, _, hfr, hin, hy, htraj, hrest, allFillableStrict_of_play hrest hall⟩


private lemma deadAfterLG_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u)
    (hda : DeadAfterLG U k.val H') :
    DeadAfterLG (U.insert u) k.val H' := by
  have hne_v : k.val ≠ j.val := fun he => hne (Fin.ext he)
  rcases hda with ⟨h, r, hh9, hr, hrH, hm, hrm, hp⟩ | ⟨h, r, hh4, hr, hrH, hm, hrm, hp⟩
  · exact Or.inl ⟨h, r, hh9, hr, hrH, hm, hrm, bucketPattern_insert_other hne_v hin hp⟩
  · exact Or.inr ⟨h, r, hh4, hr, hrH, hm, hrm, bucketPattern_insert_other hne_v hin hp⟩

private lemma deadAfterSq_insert_other {U : Board} {s H' : ℕ} {j k : Fin s} (hne : k ≠ j)
    {u : PieceState} (hin : InBucket j.val u)
    (hda : DeadAfterSq U k.val H') :
    DeadAfterSq (U.insert u) k.val H' := by
  rcases hda with ⟨h, hh4, hh12, hm, hp⟩
  exact ⟨h, hh4, hh12, hm, bucketPattern_insert_other (fun he => hne (Fin.ext he)) hin hp⟩


/-- `DeadTriggerState` cannot survive `.Sq :: .Sq :: ts_tail`. -/
private lemma dead_th_kills_sq_sq {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U U' : Board} {ts_tail : List Piece} {us : List PieceState}
    {j_dp j_th : Fin s} {h_th : ℕ} {h : Fin s → ℕ}
    (hdt : DeadTriggerState U s H' j_dp j_th h_th h)
    (hp : NoRGSeqPlay R s s' H' U (.Sq :: .Sq :: ts_tail) us U')
    (hall : AllFillableStrict R s s' H' U') : False := by
  rcases hdt with ⟨hne_dt, hdp, hth, hunp⟩
  obtain ⟨j₁, u₁, _, hfr1, hin1, hy1, htr1, hrest1, hfill1⟩ := noRGSeqPlay_cons_unpack hp hall
  obtain ⟨j₂, u₂, _, hfr2, hin2, hy2, htr2, _, hfill2⟩ := noRGSeqPlay_cons_unpack hrest1 hall
  by_cases hj1_th : j₁ = j_th
  · subst hj1_th
    exact prop_C28 hReason hs_le hfr1 j₁ hth hin1 hy1 htr1 (hfill1 j₁)
  · by_cases hj1_dp : j₁ = j_dp
    · subst hj1_dp
      have hda := deadPlateau_Sq1 hReason hs_le hfr1 j₁ hdp hin1 hy1 htr1 (hfill1 j₁)
      have hth1 := triggerHappyAt_insert_other (Ne.symm hne_dt) hin1 hth
      by_cases hj2_dp : j₂ = j₁
      · subst hj2_dp
        exact deadAfterSq_Sq2 hReason hs_le hfr2 j₂ hda hin2 hy2 htr2 (hfill2 j₂)
      · by_cases hj2_th : j₂ = j_th
        · subst hj2_th
          exact prop_C28 hReason hs_le hfr2 j₂ hth1 hin2 hy2 htr2 (hfill2 j₂)
        · have hunp2 := unpreppedAt_insert_other hj2_dp hin1 (hunp j₂ hj2_dp hj2_th)
          exact prop_C3 hReason hs_le hfr2 j₂ hunp2 hin2 hy2 htr2 (hfill2 j₂)
    · exact prop_C3 hReason hs_le hfr1 j₁ (hunp j₁ hj1_dp hj1_th) hin1 hy1 htr1 (hfill1 j₁)

/-- `DeadTriggerState` cannot survive `.LG :: .LS :: ts_tail`. -/
private lemma dead_th_kills_lg_ls {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U U' : Board} {ts_tail : List Piece} {us : List PieceState}
    {j_dp j_th : Fin s} {h_th : ℕ} {h : Fin s → ℕ}
    (hdt : DeadTriggerState U s H' j_dp j_th h_th h)
    (hp : NoRGSeqPlay R s s' H' U (.LG :: .LS :: ts_tail) us U')
    (hall : AllFillableStrict R s s' H' U') : False := by
  rcases hdt with ⟨hne_dt, hdp, hth, hunp⟩
  obtain ⟨j₁, u₁, _, hfr1, hin1, hy1, htr1, hrest1, hfill1⟩ := noRGSeqPlay_cons_unpack hp hall
  obtain ⟨j₂, u₂, _, hfr2, hin2, hy2, htr2, _, hfill2⟩ := noRGSeqPlay_cons_unpack hrest1 hall
  by_cases hj1_dp : j₁ = j_dp
  · subst hj1_dp
    have hda := deadPlateau_LG hReason hs_le hfr1 j₁ hdp hin1 hy1 htr1 (hfill1 j₁)
    have hth1 := triggerHappyAt_insert_other (Ne.symm hne_dt) hin1 hth
    by_cases hj2_dp : j₂ = j₁
    · subst hj2_dp
      exact deadAfterLG_LS hReason hs_le hfr2 j₂ hda hin2 hy2 htr2 (hfill2 j₂)
    · by_cases hj2_th : j₂ = j_th
      · subst hj2_th
        exact prop_C30 hReason hs_le hfr2 j₂ hth1 hin2 hy2 htr2 (hfill2 j₂)
      · have hunp2 := unpreppedAt_insert_other hj2_dp hin1 (hunp j₂ hj2_dp hj2_th)
        exact prop_C4 hReason hs_le hfr2 j₂ hunp2 hin2 hy2 htr2 (hfill2 j₂)
  · by_cases hj1_th : j₁ = j_th
    · subst hj1_th
      have hdp1 := deadPlateau_insert_other hne_dt hin1 hdp
      rcases prop_C29 hReason hs_le hfr1 j₁ hth hin1 hy1 htr1 (hfill1 j₁) with
        huf1 | ⟨r, hh6, hr_ge, hrH6, hmod, hrmod, hpat1⟩
      · by_cases hj2_dp : j₂ = j_dp
        · subst hj2_dp
          exact deadPlateau_LS hReason hs_le hfr2 j₂ hdp1 hin2 hy2 htr2 (hfill2 j₂)
        · by_cases hj2_th : j₂ = j₁
          · subst hj2_th
            exact prop_C19 hReason hs_le hfr2 j₂ huf1 hin2 hy2 htr2 (hfill2 j₂)
          · have hunp2 := unpreppedAt_insert_other hj2_th hin1 (hunp j₂ hj2_dp hj2_th)
            exact prop_C4 hReason hs_le hfr2 j₂ hunp2 hin2 hy2 htr2 (hfill2 j₂)
      · by_cases hj2_dp : j₂ = j_dp
        · subst hj2_dp
          exact deadPlateau_LS hReason hs_le hfr2 j₂ hdp1 hin2 hy2 htr2 (hfill2 j₂)
        · by_cases hj2_th : j₂ = j₁
          · subst hj2_th
            exact prop_C32 hReason hs_le hfr2 j₂ hh6 hr_ge hrH6 hmod hrmod hpat1
              hin2 hy2 htr2 (hfill2 j₂)
          · have hunp2 := unpreppedAt_insert_other hj2_th hin1 (hunp j₂ hj2_dp hj2_th)
            exact prop_C4 hReason hs_le hfr2 j₂ hunp2 hin2 hy2 htr2 (hfill2 j₂)
    · obtain ⟨gap1, r1, hh4_1, hr_ge1, hrH6_1, hmod_1, hrmod_1, hgap_1, hg2_1, hpat1⟩ :=
        prop_C2 hReason hs_le hfr1 j₁ (hunp j₁ hj1_dp hj1_th) hin1 hy1 htr1 (hfill1 j₁)
      have hdp1 := deadPlateau_insert_other (Ne.symm hj1_dp) hin1 hdp
      have hth1 := triggerHappyAt_insert_other (Ne.symm hj1_th) hin1 hth
      by_cases hj2_dp : j₂ = j_dp
      · subst hj2_dp
        exact deadPlateau_LS hReason hs_le hfr2 j₂ hdp1 hin2 hy2 htr2 (hfill2 j₂)
      · by_cases hj2_th : j₂ = j_th
        · subst hj2_th
          exact prop_C30 hReason hs_le hfr2 j₂ hth1 hin2 hy2 htr2 (hfill2 j₂)
        · by_cases hj2_1 : j₂ = j₁
          · subst hj2_1
            exact prop_C9 hReason hs_le hfr2 j₂ hh4_1 hr_ge1 hrH6_1 hmod_1 hrmod_1
              hgap_1 hg2_1 hpat1 hin2 hy2 htr2 (hfill2 j₂)
          · have hunp2 := unpreppedAt_insert_other hj2_1 hin1 (hunp j₂ hj2_dp hj2_th)
            exact prop_C4 hReason hs_le hfr2 j₂ hunp2 hin2 hy2 htr2 (hfill2 j₂)

end TetrisHard.Rows.Padded

theorem solution
    (R : TetrisHard.Rows.Rotation) (hReason : TetrisHard.Rows.Reasonable R) (s s' H' : ℕ) (hs_le : s ≤ s') :
    (∀ (U U' : TetrisHard.Rows.Board) (ts_tail : List TetrisHard.Rows.Piece) (us : List TetrisHard.Rows.PieceState)
       (j_dp j_th : Fin s) (h_th : ℕ) (h : Fin s → ℕ),
      TetrisHard.Rows.Padded.DeadTriggerState U s H' j_dp j_th h_th h →
      TetrisHard.Rows.Padded.NoRGSeqPlay R s s' H' U (.Sq :: .Sq :: ts_tail) us U' →
      TetrisHard.Rows.Padded.AllFillableStrict R s s' H' U' → False) ∧
    (∀ (U U' : TetrisHard.Rows.Board) (ts_tail : List TetrisHard.Rows.Piece) (us : List TetrisHard.Rows.PieceState)
       (j_dp j_th : Fin s) (h_th : ℕ) (h : Fin s → ℕ),
      TetrisHard.Rows.Padded.DeadTriggerState U s H' j_dp j_th h_th h →
      TetrisHard.Rows.Padded.NoRGSeqPlay R s s' H' U (.LG :: .LS :: ts_tail) us U' →
      TetrisHard.Rows.Padded.AllFillableStrict R s s' H' U' → False) := by
  open TetrisHard.Rows.Padded in
  exact ⟨fun _ _ _ _ _ _ _ _ hdt hp hall => dead_th_kills_sq_sq hReason hs_le hdt hp hall,
    fun _ _ _ _ _ _ _ _ hdt hp hall => dead_th_kills_lg_ls hReason hs_le hdt hp hall⟩
