-- Prove2me | solution 1 for TetrisHard.Rows.Padded.paddedReservoir_completeness
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:03:34.356235+00:00
-- url     : https://prove2.me/submissions/e1597ed0-b4fb-4f45-bb00-e7c0d7dbfa0f

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction

set_option autoImplicit false

namespace TetrisHard.Rows.Padded

open TetrisHard.Rows

lemma row_all_id_iff (B : Board) (y : Fin B.height) :
    (List.ofFn fun x : Fin B.width => B.cell y x).all id = true ↔
      ∀ x : Fin B.width, B.cell y x = true := by
  simp [List.all_eq_true, List.mem_ofFn]

lemma piece_rotated_offset_bound (t : Piece) (o : Fin 4) (z : Cell) (hz : z ∈ t.base) :
    -2 ≤ (if t = .Sq then z else clockwise^[o.val] z).1 ∧
    (if t = .Sq then z else clockwise^[o.val] z).1 ≤ 2 ∧
    -2 ≤ (if t = .Sq then z else clockwise^[o.val] z).2 ∧
    (if t = .Sq then z else clockwise^[o.val] z).2 ≤ 2 := by
  fin_cases o <;> cases t <;> simp [Piece.base, clockwise] at hz ⊢ <;>
    (rcases hz with rfl | rfl | rfl | rfl <;> norm_num)

lemma admissible_empty_displacement {R : Rotation} (hR : R.Admissible)
    (t : Piece) (o : Fin 4) (f cw : Bool) :
    ∃ d : Cell,
      R.rule t o f cw (fun _ _ => false) = some d ∧
      |d.1| ≤ ((max R.radius 2 : ℕ) : ℤ) + 2 ∧
      |d.2| ≤ ((max R.radius 2 : ℕ) : ℤ) + 2 := by
  have hisSome := hR.1 t o f cw
  cases hrule : R.rule t o f cw (fun _ _ => false) with
  | none => simp [hrule] at hisSome
  | some d =>
    set M : ℕ := max R.radius 2
    have hMR : R.radius ≤ M := le_max_left _ _
    have hM2 : 2 ≤ M := le_max_right _ _
    let B : Board := { height := 2 * M + 1, width := 2 * M + 1, cell := fun _ _ => false }
    let q : PieceState := { kind := t, orientation := o, position := (M, M), fixed := f }
    have hclear : B.Clear q := by
      intro c hc
      simp only [PieceState.cells, List.mem_map] at hc
      rcases hc with ⟨z, hz, rfl⟩
      have hb := piece_rotated_offset_bound t o z hz
      set u := if t = .Sq then z else clockwise^[o.val] z
      simp only [B, Board.occupied, q]
      split_ifs with h1 h2
      · rfl
      · omega
      · omega
    have hclear' := hR.2 B q cw hclear
    have hpatch : (fun y x : Fin (2 * R.radius + 1) =>
        B.occupied (q.position.1 + (x.val : ℤ) - R.radius,
          q.position.2 + (y.val : ℤ) - R.radius)) = fun _ _ => false := by
      funext y x
      simp only [B, Board.occupied, q]
      split_ifs with hy hx
      · rfl
      · omega
      · omega
    have happly : R.apply B q cw =
        { q with
          orientation := ⟨(o.val + if cw then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩
          position := (M + d.1, M + d.2) } := by
      unfold Rotation.apply
      dsimp only [q]
      rw [hpatch, hrule]
    rw [happly] at hclear'
    have hne : t.base ≠ [] := by cases t <;> simp [Piece.base]
    obtain ⟨z0, hz0⟩ := List.exists_mem_of_ne_nil t.base hne
    let o' : Fin 4 := ⟨(o.val + if cw then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩
    set u0 := if t = .Sq then z0 else clockwise^[o'.val] z0
    have hmem : ((M : ℤ) + d.1 + u0.1, (M : ℤ) + d.2 + u0.2) ∈
        ({ q with orientation := o', position := (M + d.1, M + d.2) } : PieceState).cells := by
      simp only [PieceState.cells, List.mem_map]
      exact ⟨z0, hz0, rfl⟩
    have hocc := hclear' _ hmem
    have hb : -2 ≤ u0.1 ∧ u0.1 ≤ 2 ∧ -2 ≤ u0.2 ∧ u0.2 ≤ 2 := piece_rotated_offset_bound t o' z0 hz0
    simp only [B, Board.occupied] at hocc
    split_ifs at hocc with hy hx
    refine ⟨d, rfl, abs_le.mpr (by omega), abs_le.mpr (by omega)⟩


/-! ### Section 1: Play Composition and Board Settle Helpers -/

/-- Full consumption of `ts` from board `B` to `B'` clearing `v` rows. -/
def CanPlay (R : Rotation) (B : Board) (ts : List Piece) (B' : Board) (v : ℕ) : Prop :=
  ∃ qs, qs.length = ts.length ∧ Play R B ts qs B' v

lemma CanPlay.nil (R : Rotation) (B : Board) : CanPlay R B [] B 0 :=
  ⟨[], rfl, Play.stop B []⟩

lemma CanPlay.cons {R : Rotation} {B B' : Board} {t : Piece} {ts : List Piece}
    {q : PieceState} {v : ℕ}
    (ht : Trajectory R B t q) (h : CanPlay R (B.settle q) ts B' v) :
    CanPlay R B (t :: ts) B' (B.gain q + v) := by
  rcases h with ⟨qs, hlen, hqs⟩
  exact ⟨q :: qs, by simp [hlen], Play.step ht hqs⟩

lemma CanPlay.single {R : Rotation} {B : Board} {t : Piece} {q : PieceState}
    (ht : Trajectory R B t q) :
    CanPlay R B [t] (B.settle q) (B.gain q) := by
  simpa using CanPlay.cons ht (CanPlay.nil R (B.settle q))

lemma CanPlay.append {R : Rotation} {B1 B2 B3 : Board} {ts1 ts2 : List Piece} {v1 v2 : ℕ}
    (h1 : CanPlay R B1 ts1 B2 v1) (h2 : CanPlay R B2 ts2 B3 v2) :
    CanPlay R B1 (ts1 ++ ts2) B3 (v1 + v2) := by
  rcases h1 with ⟨qs1, hlen1, hp1⟩
  rcases h2 with ⟨qs2, hlen2, hp2⟩
  refine ⟨qs1 ++ qs2, by simp [hlen1, hlen2], ?_⟩
  induction hp1 with
  | stop B ts =>
    simp only [List.length_nil] at hlen1
    have hts : ts = [] := List.eq_nil_of_length_eq_zero hlen1.symm
    subst hts
    simpa using hp2
  | step ht hrest ih =>
    simp only [List.length_cons, Nat.succ.injEq] at hlen1
    simpa [Nat.add_assoc] using Play.step ht (ih hlen1 hp2)

lemma CanPlay.toAttainable {R : Rotation} {G : Game} {B' : Board} {v : ℕ}
    (h : CanPlay R G.board G.pieces B' v) : Attainable R G v := by
  rcases h with ⟨qs, _, hp⟩
  exact ⟨qs, B', hp⟩

lemma board_ext {B1 B2 : Board} (hh : B1.height = B2.height) (hw : B1.width = B2.width)
    (hc : ∀ (y : ℕ) (hy1 : y < B1.height) (hy2 : y < B2.height)
      (x : ℕ) (hx1 : x < B1.width) (hx2 : x < B2.width),
      B1.cell ⟨y, hy1⟩ ⟨x, hx1⟩ = B2.cell ⟨y, hy2⟩ ⟨x, hx2⟩) : B1 = B2 := by
  cases B1; cases B2
  dsimp at hh hw hc
  subst hh; subst hw
  congr 1
  funext y x
  exact hc y.val y.isLt y.isLt x.val x.isLt x.isLt

lemma row_all_id_eq_false_iff (B : Board) (y : Fin B.height) :
    (List.ofFn fun x : Fin B.width => B.cell y x).all id = false ↔
      ∃ x : Fin B.width, B.cell y x = false := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have htrue : ∀ x : Fin B.width, B.cell y x = true := fun x =>
      Bool.eq_true_of_not_eq_false (hall x)
    have := (row_all_id_iff B y).mpr htrue
    rw [this] at h
    simp at h
  · rintro ⟨x, hx⟩
    rw [Bool.eq_false_iff]
    intro h
    have := (row_all_id_iff B y).mp h x
    rw [hx] at this
    simp at this

/-- When every row of `B.insert q` has a `false` cell, `B.gain q = 0` and `B.settle q = B.insert q`. -/
lemma settle_eq_insert_of_not_full (B : Board) (q : PieceState)
    (hnf : ∀ y : Fin B.height, ∃ x : Fin B.width, (B.insert q).cell y x = false) :
    B.gain q = 0 ∧ B.settle q = B.insert q := by
  set B1 := B.insert q
  have hrow_f : ∀ r ∈ B1.rows, r.all id = false := by
    intro r hr
    simp only [Board.rows, List.mem_ofFn] at hr
    rcases hr with ⟨y, rfl⟩
    exact (row_all_id_eq_false_iff B1 y).mpr (hnf y)
  have hgain : B.gain q = 0 := by
    unfold Board.gain Board.fullCount
    have hnil : B1.rows.filter (fun r => r.all id) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      simp [hrow_f r hr]
    simp [B1, hnil]
  have hsurv : B1.rows.filter (fun r => !(r.all id)) = B1.rows := by
    rw [List.filter_eq_self]
    intro r hr
    simp [hrow_f r hr]
  refine ⟨hgain, ?_⟩
  apply board_ext (by rfl) (by rfl)
  intro y hy1 hy2 x hx1 hx2
  change ((B1.rows.filter fun r => !(r.all id)).getD y []).getD x false = B1.cell ⟨y, hy2⟩ ⟨x, hx2⟩
  rw [hsurv]
  have h1 : B1.rows.getD y [] = List.ofFn (fun x' : Fin B1.width => B1.cell ⟨y, hy2⟩ x') := by
    simp [Board.rows, List.getD_eq_getElem?_getD, hy2]
  rw [h1]
  simp [List.getD_eq_getElem?_getD, hx2]

/-- Clearing a contiguous band `[a, b)` of full rows shifts rows `≥ b` down by `b - a` and
fills the top `b - a` rows with `false`. -/
lemma settle_clear_band (B : Board) (q : PieceState) (a b : ℕ)
    (hab : a ≤ b) (hbH : b ≤ B.height)
    (hbelow : ∀ y : Fin B.height, y.val < a → ∃ x : Fin B.width, (B.insert q).cell y x = false)
    (hband : ∀ y : Fin B.height, a ≤ y.val → y.val < b → ∀ x : Fin B.width, (B.insert q).cell y x = true)
    (habove : ∀ y : Fin B.height, b ≤ y.val → ∃ x : Fin B.width, (B.insert q).cell y x = false) :
    B.gain q = b - a ∧
    ∀ (y : Fin (B.settle q).height) (x : Fin (B.settle q).width),
      (B.settle q).cell y x =
        if _ : y.val < a then (B.insert q).cell ⟨y.val, y.isLt⟩ ⟨x.val, x.isLt⟩
        else if hy2 : y.val + (b - a) < B.height then
          (B.insert q).cell ⟨y.val + (b - a), hy2⟩ ⟨x.val, x.isLt⟩
        else false := by
  set B1 := B.insert q
  have hlen : B1.rows.length = B.height := by simp [Board.rows, B1, Board.insert]
  have hsplit : B1.rows = B1.rows.take a ++ (B1.rows.drop a).take (b - a) ++ B1.rows.drop b := by
    have h1 : B1.rows.take a ++ B1.rows.drop a = B1.rows := List.take_append_drop a B1.rows
    have h2 : (B1.rows.drop a).take (b - a) ++ (B1.rows.drop a).drop (b - a) = B1.rows.drop a :=
      List.take_append_drop (b - a) (B1.rows.drop a)
    rw [List.drop_drop, Nat.add_sub_of_le hab] at h2
    rw [List.append_assoc, h2, h1]
  have hbelow_f : ∀ r ∈ B1.rows.take a, r.all id = false := by
    intro r hr
    rw [List.mem_iff_getElem] at hr
    rcases hr with ⟨i, hi, rfl⟩
    simp only [List.length_take, hlen] at hi
    have hia : i < a := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hiH : i < B.height := by omega
    rw [List.getElem_take]
    simp only [Board.rows, List.getElem_ofFn]
    exact (row_all_id_eq_false_iff B1 ⟨i, hiH⟩).mpr (hbelow ⟨i, hiH⟩ hia)
  have hband_t : ∀ r ∈ (B1.rows.drop a).take (b - a), r.all id = true := by
    intro r hr
    rw [List.mem_iff_getElem] at hr
    rcases hr with ⟨i, hi, rfl⟩
    simp only [List.length_take, List.length_drop, hlen] at hi
    have hib : i < b - a := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have haiH : a + i < B.height := by omega
    rw [List.getElem_take, List.getElem_drop]
    simp only [Board.rows, List.getElem_ofFn]
    exact (row_all_id_iff B1 ⟨a + i, haiH⟩).mpr (hband ⟨a + i, haiH⟩ (by dsimp; omega) (by dsimp; omega))
  have habove_f : ∀ r ∈ B1.rows.drop b, r.all id = false := by
    intro r hr
    rw [List.mem_iff_getElem] at hr
    rcases hr with ⟨i, hi, rfl⟩
    simp only [List.length_drop, hlen] at hi
    have hbiH : b + i < B.height := by omega
    rw [List.getElem_drop]
    simp only [Board.rows, List.getElem_ofFn]
    exact (row_all_id_eq_false_iff B1 ⟨b + i, hbiH⟩).mpr (habove ⟨b + i, hbiH⟩ (by dsimp; omega))
  have hf1 : (B1.rows.take a).filter (fun r => r.all id) = [] := by
    rw [List.filter_eq_nil_iff]; intro r hr; simp [hbelow_f r hr]
  have hf2 : ((B1.rows.drop a).take (b - a)).filter (fun r => r.all id) =
      (B1.rows.drop a).take (b - a) := by
    rw [List.filter_eq_self]; intro r hr; exact hband_t r hr
  have hf3 : (B1.rows.drop b).filter (fun r => r.all id) = [] := by
    rw [List.filter_eq_nil_iff]; intro r hr; simp [habove_f r hr]
  have hgain : B.gain q = b - a := by
    unfold Board.gain Board.fullCount
    change (B1.rows.filter (fun r => r.all id)).length = b - a
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_append, hf1, hf2, hf3]
    simp [hlen]
    omega
  have hs1 : (B1.rows.take a).filter (fun r => !(r.all id)) = B1.rows.take a := by
    rw [List.filter_eq_self]; intro r hr; simp [hbelow_f r hr]
  have hs2 : ((B1.rows.drop a).take (b - a)).filter (fun r => !(r.all id)) = [] := by
    rw [List.filter_eq_nil_iff]; intro r hr; simp [hband_t r hr]
  have hs3 : (B1.rows.drop b).filter (fun r => !(r.all id)) = B1.rows.drop b := by
    rw [List.filter_eq_self]; intro r hr; simp [habove_f r hr]
  have hsurv : B1.rows.filter (fun r => !(r.all id)) = B1.rows.take a ++ B1.rows.drop b := by
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_append, hs1, hs2, hs3, List.append_nil]
  refine ⟨hgain, ?_⟩
  intro y x
  change ((B1.rows.filter fun r => !(r.all id)).getD y.val []).getD x.val false = _
  rw [hsurv]
  have htlen : (B1.rows.take a).length = a := by simp [hlen]; omega
  have hdlen : (B1.rows.drop b).length = B.height - b := by simp [hlen]
  by_cases hy1 : y.val < a
  · simp only [hy1, ↓reduceDIte]
    have hget : (B1.rows.take a ++ B1.rows.drop b).getD y.val [] = (B1.rows.take a)[y.val]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hget, List.getElem_take]
    have hxlt : x.val < B1.width := x.isLt
    simp only [Board.rows, List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      hxlt, ↓reduceDIte, Option.getD_some]
    rfl
  · simp only [hy1, ↓reduceDIte]
    by_cases hy2 : y.val + (b - a) < B.height
    · simp only [hy2, ↓reduceDIte]
      have hidx : y.val - a < (B1.rows.drop b).length := by omega
      have hget : (B1.rows.take a ++ B1.rows.drop b).getD y.val [] =
          (B1.rows.drop b)[y.val - a]'hidx := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), htlen,
          List.getElem?_eq_getElem hidx, Option.getD_some]
      rw [hget, List.getElem_drop]
      have hsum : b + (y.val - a) = y.val + (b - a) := by omega
      have hxlt : x.val < B1.width := x.isLt
      simp only [Board.rows, List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        hxlt, ↓reduceDIte, Option.getD_some]
      congr 1; ext; exact hsum
    · simp only [hy2, ↓reduceDIte]
      have hge : (B1.rows.take a ++ B1.rows.drop b).length ≤ y.val := by
        rw [List.length_append, htlen, hdlen]; omega
      have hget : (B1.rows.take a ++ B1.rows.drop b).getD y.val [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      rw [hget]; simp

/-! ### Section 2: General Free-Rotation + Drop-and-Slide Trajectory Lemma -/

private lemma clear_of_staging {B : Board} {topOcc : ℕ}
    (hempty : ∀ y : Fin B.height, topOcc ≤ y.val → ∀ x : Fin B.width, B.cell y x = false)
    {t : Piece} {o : Fin 4} {px py : ℤ}
    (hpy_lo : (topOcc : ℤ) + 2 ≤ py) (hpy_hi : py + 2 < B.height)
    (hpx : ∀ z ∈ t.base,
      let u := if t = .Sq then z else clockwise^[o.val] z
      0 ≤ px + u.1 ∧ px + u.1 < B.width) :
    B.Clear { kind := t, orientation := o, position := (px, py), fixed := false } := by
  intro c hc
  simp only [PieceState.cells, List.mem_map] at hc
  rcases hc with ⟨z, hz, rfl⟩
  have hb := piece_rotated_offset_bound t o z hz
  have hx := hpx z hz
  dsimp only at hx ⊢
  set u := if t = .Sq then z else clockwise^[o.val] z
  have hy0 : 0 ≤ py + u.2 ∧ py + u.2 < B.height := by omega
  have hx0 : 0 ≤ px + u.1 ∧ px + u.1 < B.width := hx
  simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
  exact hempty ⟨(py + u.2).toNat, by omega⟩ (by dsimp; omega) ⟨(px + u.1).toNat, by omega⟩

private lemma clear_of_staging_box {B : Board} {topOcc : ℕ}
    (hempty : ∀ y : Fin B.height, topOcc ≤ y.val → ∀ x : Fin B.width, B.cell y x = false)
    {t : Piece} {o : Fin 4} {px py : ℤ}
    (hpy_lo : (topOcc : ℤ) + 2 ≤ py) (hpy_hi : py + 2 < B.height)
    (hpx_lo : 2 ≤ px) (hpx_hi : px + 2 < B.width) :
    B.Clear { kind := t, orientation := o, position := (px, py), fixed := false } :=
  clear_of_staging hempty hpy_lo hpy_hi fun z hz => by
    have hb := piece_rotated_offset_bound t o z hz
    dsimp only
    omega

private lemma clear_x_bounds {B : Board} {t : Piece} {o : Fin 4} {px py : ℤ}
    (hcl : B.Clear { kind := t, orientation := o, position := (px, py), fixed := false }) :
    ∀ z ∈ t.base,
      let u := if t = .Sq then z else clockwise^[o.val] z
      0 ≤ px + u.1 ∧ px + u.1 < B.width := by
  intro z hz
  set u := if t = .Sq then z else clockwise^[o.val] z
  have hmem : (px + u.1, py + u.2) ∈
      ({ kind := t, orientation := o, position := (px, py), fixed := false } : PieceState).cells := by
    simp only [PieceState.cells, List.mem_map]
    exact ⟨z, hz, rfl⟩
  have hocc := hcl _ hmem
  simp only [Board.occupied] at hocc
  split_ifs at hocc with hy hx
  exact hx

private lemma reach_horiz {R : Rotation} {B : Board} {t : Piece} {o : Fin 4} {y x1 x2 : ℤ}
    (hcl : ∀ x' : ℤ, min x1 x2 ≤ x' → x' ≤ max x1 x2 →
      B.Clear { kind := t, orientation := o, position := (x', y), fixed := false }) :
    Relation.ReflTransGen (Move R B)
      { kind := t, orientation := o, position := (x1, y), fixed := false }
      { kind := t, orientation := o, position := (x2, y), fixed := false } := by
  suffices h : ∀ (n : ℕ) (x1 x2 : ℤ), (x2 - x1).natAbs = n →
      (∀ x' : ℤ, min x1 x2 ≤ x' → x' ≤ max x1 x2 →
        B.Clear { kind := t, orientation := o, position := (x', y), fixed := false }) →
      Relation.ReflTransGen (Move R B)
        { kind := t, orientation := o, position := (x1, y), fixed := false }
        { kind := t, orientation := o, position := (x2, y), fixed := false } from
    h (x2 - x1).natAbs x1 x2 rfl hcl
  intro n
  induction n with
  | zero =>
    intro x1 x2 hn _
    have heq : x1 = x2 := by omega
    subst heq
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro x1 x2 hn hcl'
    by_cases hlt : x1 < x2
    · have hstep : Move R B
          { kind := t, orientation := o, position := (x1, y), fixed := false }
          { kind := t, orientation := o, position := (x1 + 1, y), fixed := false } := by
        refine ⟨rfl, hcl' x1 (by omega) (by omega), hcl' (x1 + 1) (by omega) (by omega), ?_⟩
        right; right; left; simp [translate]
      exact Relation.ReflTransGen.head hstep (ih (x1 + 1) x2 (by omega) fun x' h1 h2 =>
        hcl' x' (by omega) (by omega))
    · have hstep : Move R B
          { kind := t, orientation := o, position := (x1, y), fixed := false }
          { kind := t, orientation := o, position := (x1 - 1, y), fixed := false } := by
        refine ⟨rfl, hcl' x1 (by omega) (by omega), hcl' (x1 - 1) (by omega) (by omega), ?_⟩
        right; left; simp [translate, sub_eq_add_neg]
      exact Relation.ReflTransGen.head hstep (ih (x1 - 1) x2 (by omega) fun x' h1 h2 =>
        hcl' x' (by omega) (by omega))

private lemma reach_down {R : Rotation} {B : Board} {t : Piece} {o : Fin 4} {x y1 y2 : ℤ}
    (hle : y2 ≤ y1)
    (hcl : ∀ y' : ℤ, y2 ≤ y' → y' ≤ y1 →
      B.Clear { kind := t, orientation := o, position := (x, y'), fixed := false }) :
    Relation.ReflTransGen (Move R B)
      { kind := t, orientation := o, position := (x, y1), fixed := false }
      { kind := t, orientation := o, position := (x, y2), fixed := false } := by
  suffices h : ∀ (n : ℕ) (y1 : ℤ), y2 ≤ y1 → (y1 - y2).natAbs = n →
      (∀ y' : ℤ, y2 ≤ y' → y' ≤ y1 →
        B.Clear { kind := t, orientation := o, position := (x, y'), fixed := false }) →
      Relation.ReflTransGen (Move R B)
        { kind := t, orientation := o, position := (x, y1), fixed := false }
        { kind := t, orientation := o, position := (x, y2), fixed := false } from
    h (y1 - y2).natAbs y1 hle rfl hcl
  intro n
  induction n with
  | zero =>
    intro y1 hle' hn _
    have heq : y1 = y2 := by omega
    subst heq
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro y1 hle' hn hcl'
    have hstep : Move R B
        { kind := t, orientation := o, position := (x, y1), fixed := false }
        { kind := t, orientation := o, position := (x, y1 - 1), fixed := false } := by
      refine ⟨rfl, hcl' y1 (by omega) (by omega), hcl' (y1 - 1) (by omega) (by omega), ?_⟩
      right; right; right; left; simp [translate, sub_eq_add_neg]
    exact Relation.ReflTransGen.head hstep (ih (y1 - 1) (by omega) (by omega) fun y' h1 h2 =>
      hcl' y' h1 (by omega))

private lemma spawn_clear_and_down {R : Rotation} {B : Board} {topOcc : ℕ}
    (hW : 2 * max R.radius 2 + 9 ≤ B.width)
    (hH : topOcc + 5 * max R.radius 2 + 12 ≤ B.height)
    (hempty : ∀ y : Fin B.height, topOcc ≤ y.val → ∀ x : Fin B.width, B.cell y x = false)
    (t : Piece) :
    B.Clear (spawn B t) ∧
    Relation.ReflTransGen (Move R B) (spawn B t)
      { kind := t, orientation := 0,
        position := (((max R.radius 2 : ℕ) : ℤ) + 4, (B.height : ℤ) - ((max R.radius 2 : ℕ) : ℤ) - 5),
        fixed := false } := by
  set M : ℕ := max R.radius 2
  have hM2 : 2 ≤ M := le_max_right _ _
  set sx : ℤ := (B.width / 2 : ℕ) - 1
  set sy : ℤ := (B.height : ℤ) - 1 - (t.base.map Prod.snd).foldl max 0
  have hfold_le : ∀ z ∈ t.base, z.2 ≤ (t.base.map Prod.snd).foldl max 0 := by
    cases t <;> simp [Piece.base]
  have hfold_bd : 0 ≤ (t.base.map Prod.snd).foldl max 0 ∧ (t.base.map Prod.snd).foldl max 0 ≤ 1 := by
    cases t <;> simp [Piece.base]
  have hsx_bd : 2 ≤ sx ∧ sx + 2 < B.width := by
    have : 13 ≤ B.width := by omega
    omega
  set yrot : ℤ := (B.height : ℤ) - M - 5
  have hcl_down : ∀ y' : ℤ, yrot ≤ y' → y' ≤ sy →
      B.Clear { kind := t, orientation := 0, position := (sx, y'), fixed := false } := by
    intro y' hy1 hy2 c hc
    simp only [PieceState.cells, List.mem_map] at hc
    rcases hc with ⟨z, hz, rfl⟩
    have hb := piece_rotated_offset_bound t 0 z hz
    have hz2 : z.2 ≤ (t.base.map Prod.snd).foldl max 0 := hfold_le z hz
    have hu : (if t = .Sq then z else clockwise^[(0 : Fin 4).val] z) = z := by simp
    simp only [hu] at hb ⊢
    have hy0 : 0 ≤ y' + z.2 ∧ y' + z.2 < B.height := by omega
    have hx0 : 0 ≤ sx + z.1 ∧ sx + z.1 < B.width := by omega
    simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
    exact hempty ⟨(y' + z.2).toNat, by omega⟩ (by dsimp; omega) ⟨(sx + z.1).toNat, by omega⟩
  have hspawn_eq : spawn B t = { kind := t, orientation := 0, position := (sx, sy), fixed := false } := rfl
  refine ⟨by rw [hspawn_eq]; exact hcl_down sy (by omega) le_rfl, ?_⟩
  rw [hspawn_eq]
  have hdown := reach_down (R := R) (B := B) (t := t) (o := 0) (x := sx) (y1 := sy) (y2 := yrot)
    (by omega) hcl_down
  have hhoriz := reach_horiz (R := R) (B := B) (t := t) (o := 0) (y := yrot) (x1 := sx)
    (x2 := (M : ℤ) + 4) (fun x' hx1 hx2 =>
      clear_of_staging_box hempty (by omega) (by omega) (by omega) (by omega))
  exact Relation.ReflTransGen.trans hdown hhoriz

private lemma step_rotate_cw {R : Rotation} (hR : R.Admissible)
    {B : Board} {topOcc : ℕ}
    (hW : 2 * max R.radius 2 + 9 ≤ B.width)
    (hempty : ∀ y : Fin B.height, topOcc ≤ y.val → ∀ x : Fin B.width, B.cell y x = false)
    (t : Piece) (o : Fin 4) (ycur : ℤ)
    (hy_lo : (topOcc : ℤ) + ((max R.radius 2 : ℕ) : ℤ) + 4 ≤ ycur)
    (hy_hi : ycur + ((max R.radius 2 : ℕ) : ℤ) + 4 < B.height) :
    Relation.ReflTransGen (Move R B)
      { kind := t, orientation := o, position := (((max R.radius 2 : ℕ) : ℤ) + 4, ycur), fixed := false }
      { kind := t, orientation := ⟨(o.val + 1) % 4, Nat.mod_lt _ (by decide)⟩,
        position := (((max R.radius 2 : ℕ) : ℤ) + 4, ycur - ((max R.radius 2 : ℕ) : ℤ) - 2), fixed := false } := by
  set M : ℕ := max R.radius 2
  have hMR : R.radius ≤ M := le_max_left _ _
  have hM2 : 2 ≤ M := le_max_right _ _
  set xrot : ℤ := (M : ℤ) + 4
  set q : PieceState := { kind := t, orientation := o, position := (xrot, ycur), fixed := false }
  have hcl_q : B.Clear q :=
    clear_of_staging_box hempty (by omega) (by omega) (by omega) (by omega)
  have hpatch : (fun y x : Fin (2 * R.radius + 1) =>
      B.occupied (q.position.1 + (x.val : ℤ) - R.radius,
        q.position.2 + (y.val : ℤ) - R.radius)) = fun _ _ => false := by
    funext y x
    dsimp only [q]
    have hy0 : 0 ≤ ycur + (y.val : ℤ) - R.radius ∧ ycur + (y.val : ℤ) - R.radius < B.height := by omega
    have hx0 : 0 ≤ xrot + (x.val : ℤ) - R.radius ∧ xrot + (x.val : ℤ) - R.radius < B.width := by omega
    simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
    exact hempty ⟨(ycur + (y.val : ℤ) - R.radius).toNat, by omega⟩ (by dsimp; omega)
      ⟨(xrot + (x.val : ℤ) - R.radius).toNat, by omega⟩
  obtain ⟨d, hd_rule, hd1, hd2⟩ := admissible_empty_displacement hR t o false true
  have hd1' : -((M : ℤ) + 2) ≤ d.1 ∧ d.1 ≤ (M : ℤ) + 2 := abs_le.mp hd1
  have hd2' : -((M : ℤ) + 2) ≤ d.2 ∧ d.2 ≤ (M : ℤ) + 2 := abs_le.mp hd2
  set o' : Fin 4 := ⟨(o.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
  set q1 : PieceState := { kind := t, orientation := o', position := (xrot + d.1, ycur + d.2), fixed := false }
  have happly : R.apply B q true = q1 := by
    unfold Rotation.apply
    dsimp only [q]
    rw [hpatch, hd_rule]
    rfl
  have hcl_q1 : B.Clear q1 := by
    rw [← happly]
    exact hR.2 B q true hcl_q
  have hrot : Move R B q q1 := ⟨rfl, hcl_q, hcl_q1, Or.inl ⟨true, happly.symm⟩⟩
  have hhoriz := reach_horiz (R := R) (B := B) (t := t) (o := o') (y := ycur + d.2)
    (x1 := xrot + d.1) (x2 := xrot) (fun x' hx1 hx2 =>
      clear_of_staging_box hempty (by omega) (by omega) (by omega) (by omega))
  have hdown := reach_down (R := R) (B := B) (t := t) (o := o') (x := xrot)
    (y1 := ycur + d.2) (y2 := ycur - (M : ℤ) - 2) (by omega) (fun y' hy1 hy2 =>
      clear_of_staging_box hempty (by omega) (by omega) (by omega) (by omega))
  exact Relation.ReflTransGen.head hrot (Relation.ReflTransGen.trans hhoriz hdown)

/-- Any piece can be freely rotated in the empty staging area above `topOcc`, dropped vertically
along `x_drop` to `y`, slid horizontally to `x_target`, and fixed if resting on an occupied cell. -/
lemma trajectory_of_drop_slide {R : Rotation} (hR : R.Admissible)
    {B : Board} {topOcc : ℕ}
    (hW : 2 * max R.radius 2 + 9 ≤ B.width)
    (hH : topOcc + 5 * max R.radius 2 + 12 ≤ B.height)
    (hempty : ∀ y : Fin B.height, topOcc ≤ y.val → ∀ x : Fin B.width, B.cell y x = false)
    {t : Piece} {o : Fin 4} {x_drop x_target y : ℤ}
    (hy : y ≤ (topOcc : ℤ) + 2)
    (hdrop : ∀ y' : ℤ, y ≤ y' → y' ≤ (topOcc : ℤ) + 2 →
      B.Clear { kind := t, orientation := o, position := (x_drop, y'), fixed := false })
    (hslide : ∀ x' : ℤ, min x_drop x_target ≤ x' → x' ≤ max x_drop x_target →
      B.Clear { kind := t, orientation := o, position := (x', y), fixed := false })
    (hrest : ¬ B.Clear (translate { kind := t, orientation := o, position := (x_target, y), fixed := false } 0 (-1))) :
    Trajectory R B t { kind := t, orientation := o, position := (x_target, y), fixed := true } := by
  set M : ℕ := max R.radius 2
  have hM2 : 2 ≤ M := le_max_right _ _
  set xrot : ℤ := (M : ℤ) + 4
  obtain ⟨hcl0, hreach0⟩ := spawn_clear_and_down (R := R) hW hH hempty t
  -- Rotate o.val times from (xrot, B.height - M - 5)
  have hrot_k : ∀ k : ℕ, k ≤ 3 →
      Relation.ReflTransGen (Move R B)
        { kind := t, orientation := 0, position := (xrot, (B.height : ℤ) - M - 5), fixed := false }
        { kind := t, orientation := ⟨k % 4, Nat.mod_lt _ (by decide)⟩,
          position := (xrot, (B.height : ℤ) - (k + 1) * M - (2 * k + 5)), fixed := false } := by
    intro k hk
    induction k with
    | zero =>
      simp only [Nat.zero_mod, Nat.cast_zero, zero_add, one_mul, mul_zero]
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      have ih' := ih (by omega)
      have hkm_hi : ((k : ℤ) + 1) * M ≤ 3 * M := by
        have : (k : ℤ) + 1 ≤ 3 := by omega
        nlinarith
      have hkm_lo : (M : ℤ) ≤ ((k : ℤ) + 1) * M := by nlinarith
      have hstep := step_rotate_cw hR hW hempty t ⟨k % 4, Nat.mod_lt _ (by decide)⟩
        ((B.height : ℤ) - (k + 1) * M - (2 * k + 5)) (by omega) (by omega)
      have hpos : (B.height : ℤ) - (k + 1) * M - (2 * k + 5) - (M : ℤ) - 2 =
          (B.height : ℤ) - ((k + 1 : ℕ) + 1) * M - (2 * (k + 1 : ℕ) + 5) := by push_cast; ring
      have hor : (⟨(k % 4 + 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
          ⟨(k + 1) % 4, Nat.mod_lt _ (by decide)⟩ := by
        ext; simp [Nat.add_mod]
      rw [hpos, hor] at hstep
      exact Relation.ReflTransGen.trans ih' hstep
  have ho_eq : (⟨o.val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = o := by
    ext; exact Nat.mod_eq_of_lt o.isLt
  set yend : ℤ := (B.height : ℤ) - (o.val + 1) * M - (2 * o.val + 5)
  have hreach1 : Relation.ReflTransGen (Move R B) (spawn B t)
      { kind := t, orientation := o, position := (xrot, yend), fixed := false } := by
    have hr := hrot_k o.val (by omega)
    rw [ho_eq] at hr
    exact Relation.ReflTransGen.trans hreach0 hr
  have hyend_lo : (topOcc : ℤ) + 2 ≤ yend := by
    have : ((o.val : ℤ) + 1) * M ≤ 4 * M := by
      have : (o.val : ℤ) ≤ 3 := by omega
      nlinarith
    omega
  have hyend_hi : yend + 2 < B.height := by
    have : (M : ℤ) ≤ ((o.val : ℤ) + 1) * M := by nlinarith
    omega
  have hxd_bd := clear_x_bounds (hdrop y le_rfl hy)
  -- Move horizontally from xrot to x_drop at yend
  have hreach2 : Relation.ReflTransGen (Move R B)
      { kind := t, orientation := o, position := (xrot, yend), fixed := false }
      { kind := t, orientation := o, position := (x_drop, yend), fixed := false } :=
    reach_horiz fun x' hx1 hx2 =>
      clear_of_staging hempty hyend_lo hyend_hi fun z hz => by
        have hb := piece_rotated_offset_bound t o z hz
        have hxd := hxd_bd z hz
        dsimp only at hxd ⊢
        omega
  -- Drop down from yend to y at x_drop
  have hreach3 : Relation.ReflTransGen (Move R B)
      { kind := t, orientation := o, position := (x_drop, yend), fixed := false }
      { kind := t, orientation := o, position := (x_drop, y), fixed := false } :=
    reach_down (by omega) fun y' hy1 hy2 => by
      by_cases hle : y' ≤ (topOcc : ℤ) + 2
      · exact hdrop y' hy1 hle
      · exact clear_of_staging hempty (by omega) (by omega) hxd_bd
  -- Slide horizontally from x_drop to x_target at y
  have hreach4 : Relation.ReflTransGen (Move R B)
      { kind := t, orientation := o, position := (x_drop, y), fixed := false }
      { kind := t, orientation := o, position := (x_target, y), fixed := false } :=
    reach_horiz hslide
  -- Fix at (x_target, y)
  have hcl_final : B.Clear { kind := t, orientation := o, position := (x_target, y), fixed := false } :=
    hslide x_target (min_le_right _ _) (le_max_right _ _)
  have hfix : Move R B
      { kind := t, orientation := o, position := (x_target, y), fixed := false }
      { kind := t, orientation := o, position := (x_target, y), fixed := true } :=
    ⟨rfl, hcl_final, hcl_final, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hrest⟩)))⟩
  refine ⟨hcl0, ?_, rfl⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.trans hreach1
      (Relation.ReflTransGen.trans hreach2
        (Relation.ReflTransGen.trans hreach3 hreach4)))
    hfix

/-! ### Section 3: Phase 1a — Bucket Filling (`numberPieces P ++ List.replicate P.s .I`) -/

def baseY (pad K r : ℕ) : ℕ := r + 2 + 4 * K + 12 * pad

/-- Board during Phase 1a: identical to `paddedReservoirBoard` except bucket `j` has cell predicate `colState j`. -/
def phase1Board (P : ThreePartition) (pad K st r : ℕ)
    (colState : Fin P.s → ℕ → ℕ → Bool) : Board where
  height := baseY pad K r + (baseBoard P st).height
  width := 6 * (P.s + pad) + 3
  cell := fun y x =>
    if y.val < r then decide (x.val = 0)
    else if y.val = r then decide (x.val ≠ 6 * (P.s + pad))
    else if y.val = r + 1 then decide (x.val < 6 * (P.s + pad))
    else if y.val < r + 2 + 4 * K then decide (x.val ≠ 6 * (P.s + pad) - 1)
    else if y.val < baseY pad K r then decide (x.val ≠ 6 * P.s + 2)
    else if y.val < baseY pad K r + baseHeight P then
      if hx : x.val < 6 * P.s then
        colState ⟨x.val / 6, by omega⟩ (x.val % 6) (y.val - baseY pad K r)
      else if x.val = 6 * P.s then
        decide (y.val - baseY pad K r + 2 < baseHeight P)
      else if x.val = 6 * P.s + 1 then
        decide (y.val - baseY pad K r + 1 < baseHeight P)
      else if x.val = 6 * P.s + 2 then
        decide (y.val - baseY pad K r + 2 = baseHeight P)
      else true
    else false

def bucketCellAt (h rx ry : ℕ) : Bool :=
  if ry < h then true
  else if ry < h + 4 then decide (rx ≠ 2)
  else bucketInitial rx ry

def bucketCellFull (k rx ry : ℕ) : Bool :=
  if ry < k then true else bucketInitial rx ry

lemma bucketInitial_mod6 (x y : ℕ) : bucketInitial (x % 6) y = bucketInitial x y := by
  simp [bucketInitial]

lemma bucketCellAt_zero (rx ry : ℕ) (hrx : rx < 6) :
    bucketCellAt 0 rx ry = bucketInitial rx ry := by
  unfold bucketCellAt bucketInitial
  by_cases hy : ry < 4
  · have hmod : rx % 6 = rx := Nat.mod_eq_of_lt hrx
    rw [hmod]
    have hny : (ry + 1) % 6 ≠ 5 := by omega
    by_cases h1 : rx < 2
    · simp [hy, h1]; omega
    · by_cases h2 : rx = 2
      · simp [hy, h2]
      · by_cases h3 : rx < 5
        · simp [hy, h1, h2, h3, hny]
        · simp [hy, h1, h2, h3]
  · simp [hy]

lemma phase1Board_init (P : ThreePartition) (pad K st r : ℕ) :
    phase1Board P pad K st r (fun _ => bucketCellAt 0) = paddedReservoirBoard P pad K st r := by
  apply board_ext (by rfl) (by rfl)
  intro y hy1 hy2 x hx1 hx2
  simp only [phase1Board, paddedReservoirBoard, baseY]
  by_cases h1 : y < r
  · simp [h1]
  by_cases h2 : y = r
  · simp [h2]
  by_cases h3 : y = r + 1
  · simp [h3]
  by_cases h4 : y < r + 2 + 4 * K
  · simp [h1, h2, h3, h4]
  by_cases h5 : y < r + 2 + 4 * K + 12 * pad
  · simp [h1, h2, h3, h4, h5]
  simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  by_cases h6 : y < r + 2 + 4 * K + 12 * pad + baseHeight P
  · simp only [h6, ↓reduceIte]
    by_cases hx3 : x < 6 * P.s + 3
    · simp only [hx3, ↓reduceIte]
      have hy0 : 0 ≤ (y : ℤ) - (r + 2 + 4 * K + 12 * pad) := by omega
      have hyH : (y : ℤ) - (r + 2 + 4 * K + 12 * pad) < (baseBoard P st).height := by
        simp [baseBoard]; omega
      have hx0 : (0 : ℤ) ≤ x ∧ (x : ℤ) < (baseBoard P st).width := by simp [baseBoard]; omega
      simp only [Board.occupied, hy0, hyH, hx0, and_self, ↓reduceDIte]
      have htoNat : ((y : ℤ) - (r + 2 + 4 * K + 12 * pad)).toNat = y - (r + 2 + 4 * K + 12 * pad) := by omega
      have hge : ¬ baseHeight P ≤ y - (r + 2 + 4 * K + 12 * pad) := by omega
      simp only [baseBoard, htoNat, Int.toNat_natCast, hge, ↓reduceIte]
      by_cases hx : x < 6 * P.s
      · simp only [hx, ↓reduceDIte, ↓reduceIte]
        rw [bucketCellAt_zero (x % 6) _ (Nat.mod_lt _ (by decide)), bucketInitial_mod6]
      · simp only [hx, ↓reduceDIte, ↓reduceIte]
        by_cases he0 : x = 6 * P.s
        · simp [he0]; rfl
        · by_cases he1 : x = 6 * P.s + 1
          · simp [he1]; rfl
          · have he2 : x = 6 * P.s + 2 := by omega
            simp [he2]; rfl
    · have hx : ¬ x < 6 * P.s := by omega
      have he0 : x ≠ 6 * P.s := by omega
      have he1 : x ≠ 6 * P.s + 1 := by omega
      have he2 : x ≠ 6 * P.s + 2 := by omega
      simp [hx3, hx, he0, he1, he2]
  · simp only [h6, ↓reduceIte]
    by_cases hx3 : x < 6 * P.s + 3
    · simp only [hx3, ↓reduceIte]
      have hy0 : 0 ≤ (y : ℤ) - (r + 2 + 4 * K + 12 * pad) := by omega
      have hyH : (y : ℤ) - (r + 2 + 4 * K + 12 * pad) < (baseBoard P st).height := by
        simp [paddedReservoirBoard] at hy2; omega
      have hx0 : (0 : ℤ) ≤ x ∧ (x : ℤ) < (baseBoard P st).width := by simp [baseBoard]; omega
      simp only [Board.occupied, hy0, hyH, hx0, and_self, ↓reduceDIte]
      have htoNat : ((y : ℤ) - (r + 2 + 4 * K + 12 * pad)).toNat = y - (r + 2 + 4 * K + 12 * pad) := by omega
      have hge : baseHeight P ≤ y - (r + 2 + 4 * K + 12 * pad) := by omega
      simp [baseBoard, htoNat, hge]
    · simp [hx3]

lemma phase1Board_empty (P : ThreePartition) (pad K st r : ℕ)
    (colState : Fin P.s → ℕ → ℕ → Bool)
    (y : Fin (phase1Board P pad K st r colState).height)
    (hy : baseY pad K r + baseHeight P ≤ y.val)
    (x : Fin (phase1Board P pad K st r colState).width) :
    (phase1Board P pad K st r colState).cell y x = false := by
  simp only [phase1Board, baseY] at hy ⊢
  have h1 : ¬ y.val < r := by omega
  have h2 : ¬ y.val = r := by omega
  have h3 : ¬ y.val = r + 1 := by omega
  have h4 : ¬ y.val < r + 2 + 4 * K := by omega
  have h5 : ¬ y.val < r + 2 + 4 * K + 12 * pad := by omega
  have h6 : ¬ y.val < r + 2 + 4 * K + 12 * pad + baseHeight P := by omega
  simp [h1, h2, h3, h4, h5, h6]

lemma phase1Board_occupied_bucket (P : ThreePartition) (pad K st r : ℕ)
    (colState : Fin P.s → ℕ → ℕ → Bool)
    (j : Fin P.s) (rx ry : ℤ)
    (hrx0 : 0 ≤ rx) (hrx6 : rx < 6) (hry0 : 0 ≤ ry)
    (hryH : ry < (baseBoard P st).height) :
    (phase1Board P pad K st r colState).occupied (6 * (j.val : ℤ) + rx, (baseY pad K r : ℤ) + ry) =
      if ry < baseHeight P then colState j rx.toNat ry.toNat else false := by
  have hy0 : 0 ≤ (baseY pad K r : ℤ) + ry ∧
      (baseY pad K r : ℤ) + ry < (phase1Board P pad K st r colState).height := by
    simp only [phase1Board]; omega
  have hx0 : 0 ≤ 6 * (j.val : ℤ) + rx ∧
      6 * (j.val : ℤ) + rx < (phase1Board P pad K st r colState).width := by
    simp only [phase1Board]; omega
  simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
  have hyt : ((baseY pad K r : ℤ) + ry).toNat = baseY pad K r + ry.toNat := by omega
  have hxt : (6 * (j.val : ℤ) + rx).toNat = 6 * j.val + rx.toNat := by omega
  simp only [phase1Board, hyt, hxt]
  have h1 : ¬ baseY pad K r + ry.toNat < r := by unfold baseY; omega
  have h2 : ¬ baseY pad K r + ry.toNat = r := by unfold baseY; omega
  have h3 : ¬ baseY pad K r + ry.toNat = r + 1 := by unfold baseY; omega
  have h4 : ¬ baseY pad K r + ry.toNat < r + 2 + 4 * K := by unfold baseY; omega
  have h5 : ¬ baseY pad K r + ry.toNat < baseY pad K r := by omega
  simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  by_cases hlt : ry < baseHeight P
  · have hlt' : baseY pad K r + ry.toNat < baseY pad K r + baseHeight P := by omega
    have hxs : 6 * j.val + rx.toNat < 6 * P.s := by omega
    simp only [hlt, hlt', hxs, ↓reduceIte, ↓reduceDIte]
    have hdiv : (6 * j.val + rx.toNat) / 6 = j.val := by omega
    have hmod : (6 * j.val + rx.toNat) % 6 = rx.toNat := by omega
    have hsub : baseY pad K r + ry.toNat - baseY pad K r = ry.toNat := by omega
    have hfin : (⟨(6 * j.val + rx.toNat) / 6, by omega⟩ : Fin P.s) = j := by ext; exact hdiv
    rw [hfin, hmod, hsub]
  · have hlt' : ¬ baseY pad K r + ry.toNat < baseY pad K r + baseHeight P := by omega
    simp [hlt, hlt']

lemma phase1Board_occupied_below_baseY (P : ThreePartition) (pad K st r : ℕ)
    (hpad : 1 ≤ pad) (colState : Fin P.s → ℕ → ℕ → Bool)
    (j : Fin P.s) (rx : ℤ) (hrx0 : 0 ≤ rx) (hrx6 : rx < 6) :
    (phase1Board P pad K st r colState).occupied (6 * (j.val : ℤ) + rx, (baseY pad K r : ℤ) - 1) = true := by
  have hy0 : 0 ≤ (baseY pad K r : ℤ) - 1 ∧
      (baseY pad K r : ℤ) - 1 < (phase1Board P pad K st r colState).height := by
    simp only [phase1Board, baseY]; omega
  have hx0 : 0 ≤ 6 * (j.val : ℤ) + rx ∧
      6 * (j.val : ℤ) + rx < (phase1Board P pad K st r colState).width := by
    simp only [phase1Board]; omega
  simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
  have hyt : ((baseY pad K r : ℤ) - 1).toNat = baseY pad K r - 1 := by unfold baseY; omega
  have hxt : (6 * (j.val : ℤ) + rx).toNat = 6 * j.val + rx.toNat := by omega
  simp only [phase1Board, hyt, hxt]
  have h1 : ¬ baseY pad K r - 1 < r := by unfold baseY; omega
  have h2 : ¬ baseY pad K r - 1 = r := by unfold baseY; omega
  have h3 : ¬ baseY pad K r - 1 = r + 1 := by unfold baseY; omega
  have h4 : ¬ baseY pad K r - 1 < r + 2 + 4 * K := by unfold baseY; omega
  have h5 : baseY pad K r - 1 < baseY pad K r := by unfold baseY; omega
  simp only [h1, h2, h3, h4, h5, ↓reduceIte, decide_eq_true_eq]
  omega

/-- Generic single-piece step inside bucket `j` during Phase 1a (0 rows cleared). -/
lemma play_bucket_piece {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool)
    (j : Fin P.s) (t : Piece) (o : Fin 4) (rx_drop rx_target ry : ℤ)
    (newB : ℕ → ℕ → Bool)
    (hry : ry ≤ (baseHeight P : ℤ) + 2)
    (hcells_in : ∀ c ∈ (PieceState.mk t o
        (6 * (j.val : ℤ) + rx_target, (baseY pad K r : ℤ) + ry) true).cells,
      6 * (j.val : ℤ) ≤ c.1 ∧ c.1 < 6 * (j.val : ℤ) + 6 ∧
      (baseY pad K r : ℤ) ≤ c.2 ∧ c.2 < (baseY pad K r : ℤ) + baseHeight P)
    (hdrop : ∀ ry' : ℤ, ry ≤ ry' → ry' ≤ (baseHeight P : ℤ) + 2 →
      (phase1Board P pad K st r colState).Clear
        (PieceState.mk t o (6 * (j.val : ℤ) + rx_drop, (baseY pad K r : ℤ) + ry') false))
    (hslide : ∀ rx' : ℤ, min rx_drop rx_target ≤ rx' → rx' ≤ max rx_drop rx_target →
      (phase1Board P pad K st r colState).Clear
        (PieceState.mk t o (6 * (j.val : ℤ) + rx', (baseY pad K r : ℤ) + ry) false))
    (hrest : ∃ c ∈ (translate (PieceState.mk t o
        (6 * (j.val : ℤ) + rx_target, (baseY pad K r : ℤ) + ry) false) 0 (-1)).cells,
      (phase1Board P pad K st r colState).occupied c = true)
    (hupd : ∀ rx < 6, ∀ ry' < baseHeight P,
      (colState j rx ry' || decide ((6 * (j.val : ℤ) + rx, (baseY pad K r : ℤ) + ry') ∈
        (PieceState.mk t o
          (6 * (j.val : ℤ) + rx_target, (baseY pad K r : ℤ) + ry) true).cells)) = newB rx ry') :
    CanPlay R (phase1Board P pad K st r colState) [t]
      (phase1Board P pad K st r (Function.update colState j newB)) 0 := by
  set B := phase1Board P pad K st r colState
  set q : PieceState :=
    PieceState.mk t o (6 * (j.val : ℤ) + rx_target, (baseY pad K r : ℤ) + ry) true
  have hW : 2 * max R.radius 2 + 9 ≤ B.width := by
    simp only [B, phase1Board]; omega
  have hH : baseY pad K r + baseHeight P + 5 * max R.radius 2 + 12 ≤ B.height := by
    simp only [B, phase1Board, baseBoard]; omega
  have htraj : Trajectory R B t q := by
    apply trajectory_of_drop_slide hR hW hH (phase1Board_empty P pad K st r colState)
      (x_drop := 6 * (j.val : ℤ) + rx_drop) (x_target := 6 * (j.val : ℤ) + rx_target)
      (y := (baseY pad K r : ℤ) + ry)
    · push_cast; omega
    · intro y' hy1 hy2
      have h := hdrop (y' - baseY pad K r) (by omega) (by omega)
      have heq : (baseY pad K r : ℤ) + (y' - baseY pad K r) = y' := by ring
      rwa [heq] at h
    · intro x' hx1 hx2
      have h := hslide (x' - 6 * (j.val : ℤ)) (by omega) (by omega)
      have heq : 6 * (j.val : ℤ) + (x' - 6 * (j.val : ℤ)) = x' := by ring
      rwa [heq] at h
    · intro hcl
      rcases hrest with ⟨c, hc, hocc⟩
      have hf := hcl c hc
      rw [hocc] at hf; simp at hf
  have hnf : ∀ y : Fin B.height, ∃ x : Fin B.width, (B.insert q).cell y x = false := by
    intro y
    by_cases h1 : y.val < r
    · refine ⟨⟨1, by simp [B, phase1Board]⟩, ?_⟩
      have hnot : ((1 : ℤ), (y.val : ℤ)) ∉ q.cells := fun hm => by
        have := hcells_in _ hm; unfold baseY at this; omega
      simp [Board.insert, B, phase1Board, h1, hnot]
    · by_cases h2 : y.val < r + 2
      · refine ⟨⟨6 * (P.s + pad), by simp [B, phase1Board]⟩, ?_⟩
        have hnot : ((6 * (P.s + pad) : ℤ), (y.val : ℤ)) ∉ q.cells := fun hm => by
          have := hcells_in _ hm; unfold baseY at this; omega
        have hcell : B.cell y ⟨6 * (P.s + pad), by simp [B, phase1Board]⟩ = false := by
          by_cases he : y.val = r
          · simp [B, phase1Board, he]
          · have he1 : y.val = r + 1 := by omega
            simp [B, phase1Board, he1]
        simp only [Board.insert, hcell, Bool.false_or, decide_eq_false_iff_not]
        simpa using hnot
      · by_cases h3 : y.val < r + 2 + 4 * K
        · refine ⟨⟨6 * (P.s + pad) - 1, by simp [B, phase1Board]; omega⟩, ?_⟩
          have hnot : (((6 * (P.s + pad) - 1 : ℕ) : ℤ), (y.val : ℤ)) ∉ q.cells := fun hm => by
            have := hcells_in _ hm; unfold baseY at this; omega
          have hne1 : ¬ y.val = r := by omega
          have hne2 : ¬ y.val = r + 1 := by omega
          simp [Board.insert, B, phase1Board, h1, hne1, hne2, h3, hnot]
        · by_cases h4 : y.val < baseY pad K r
          · refine ⟨⟨6 * P.s + 2, by simp [B, phase1Board]⟩, ?_⟩
            have hnot : (6 * (P.s : ℤ) + 2, (y.val : ℤ)) ∉ q.cells := fun hm => by
              have := hcells_in _ hm; omega
            have hne1 : ¬ y.val = r := by omega
            have hne2 : ¬ y.val = r + 1 := by omega
            simp [Board.insert, B, phase1Board, h1, hne1, hne2, h3, h4, hnot]
          · by_cases h5 : y.val < baseY pad K r + baseHeight P
            · by_cases htop : y.val - baseY pad K r + 2 = baseHeight P
              · refine ⟨⟨6 * P.s, by simp [B, phase1Board]; omega⟩, ?_⟩
                have hnot : (6 * (P.s : ℤ), (y.val : ℤ)) ∉ q.cells := fun hm => by
                  have := hcells_in _ hm; omega
                have hne1 : ¬ y.val = r := by omega
                have hne2 : ¬ y.val = r + 1 := by omega
                have hnotlt : ¬ 6 * P.s < 6 * P.s := Nat.lt_irrefl _
                simp only [Board.insert, B, phase1Board, h1, hne1, hne2, h3, h4, h5, hnotlt,
                  ↓reduceIte, ↓reduceDIte, Nat.cast_mul, Nat.cast_ofNat, hnot, decide_false,
                  Bool.or_false, decide_eq_false_iff_not]
                omega
              · refine ⟨⟨6 * P.s + 2, by simp [B, phase1Board]⟩, ?_⟩
                have hnot : (6 * (P.s : ℤ) + 2, (y.val : ℤ)) ∉ q.cells := fun hm => by
                  have := hcells_in _ hm; omega
                have hne1 : ¬ y.val = r := by omega
                have hne2 : ¬ y.val = r + 1 := by omega
                have hnotlt : ¬ 6 * P.s + 2 < 6 * P.s := by omega
                have hne0 : 6 * P.s + 2 ≠ 6 * P.s := by omega
                have hne1' : 6 * P.s + 2 ≠ 6 * P.s + 1 := by omega
                simp only [Board.insert, B, phase1Board, h1, hne1, hne2, h3, h4, h5, hnotlt,
                  hne0, hne1', ↓reduceIte, ↓reduceDIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
                  hnot, decide_false, Bool.or_false, decide_eq_false_iff_not]
                exact htop
            · refine ⟨⟨0, by simp [B, phase1Board]⟩, ?_⟩
              have hnot : ((0 : ℤ), (y.val : ℤ)) ∉ q.cells := fun hm => by
                have := hcells_in _ hm; omega
              have hcell : B.cell y ⟨0, by simp [B, phase1Board]⟩ = false :=
                phase1Board_empty P pad K st r colState y (by omega) ⟨0, by simp [phase1Board]⟩
              simp [Board.insert, hcell, hnot]
  obtain ⟨hgain, hsettle⟩ := settle_eq_insert_of_not_full B q hnf
  have hplay := CanPlay.single htraj
  rw [hgain, hsettle] at hplay
  suffices heq : B.insert q = phase1Board P pad K st r (Function.update colState j newB) by
    rwa [heq] at hplay
  apply board_ext (by rfl) (by rfl)
  intro y hy1 hy2 x hx1 hx2
  simp only [Board.insert, B, phase1Board]
  by_cases hband : baseY pad K r ≤ y ∧ y < baseY pad K r + baseHeight P ∧ x < 6 * P.s
  · rcases hband with ⟨hy_lo, hy_hi, hx_lt⟩
    have h1 : ¬ y < r := by unfold baseY at hy_lo; omega
    have h2 : ¬ y = r := by unfold baseY at hy_lo; omega
    have h3 : ¬ y = r + 1 := by unfold baseY at hy_lo; omega
    have h4 : ¬ y < r + 2 + 4 * K := by unfold baseY at hy_lo; omega
    have h5 : ¬ y < baseY pad K r := by omega
    simp only [h1, h2, h3, h4, h5, hy_hi, hx_lt, ↓reduceIte, ↓reduceDIte]
    by_cases hj : x / 6 = j.val
    · have hfin : (⟨x / 6, by omega⟩ : Fin P.s) = j := by ext; exact hj
      rw [hfin, Function.update_self]
      have hx_eq : (x : ℤ) = 6 * (j.val : ℤ) + (x % 6 : ℕ) := by omega
      have hy_eq : (y : ℤ) = (baseY pad K r : ℤ) + (y - baseY pad K r : ℕ) := by omega
      rw [hx_eq, hy_eq]
      exact hupd (x % 6) (Nat.mod_lt _ (by decide)) (y - baseY pad K r) (by omega)
    · have hfin : (⟨x / 6, by omega⟩ : Fin P.s) ≠ j := fun h => hj (congrArg Fin.val h)
      rw [Function.update_of_ne hfin]
      have hnot : ((x : ℤ), (y : ℤ)) ∉ q.cells := fun hm => by
        have := hcells_in _ hm; omega
      simp [hnot]
  · have hnot : ((x : ℤ), (y : ℤ)) ∉ q.cells := fun hm => by
      have := hcells_in _ hm; omega
    simp only [hnot, decide_false, Bool.or_false]
    by_cases h1 : y < r
    · simp [h1]
    by_cases h2 : y = r
    · simp [h2]
    by_cases h3 : y = r + 1
    · simp [h3]
    by_cases h4 : y < r + 2 + 4 * K
    · simp [h1, h2, h3, h4]
    by_cases h5 : y < baseY pad K r
    · simp [h1, h2, h3, h4, h5]
    by_cases h6 : y < baseY pad K r + baseHeight P
    · have hnx : ¬ x < 6 * P.s := fun hx => hband ⟨by omega, h6, hx⟩
      simp [h1, h2, h3, h4, h5, h6, hnx]
    · simp [h1, h2, h3, h4, h5, h6]

private lemma phase1_cell_false {P : ThreePartition} {pad K st r : ℕ}
    {colState : Fin P.s → ℕ → ℕ → Bool} {j : Fin P.s} {rx ry : ℤ}
    (hrx0 : 0 ≤ rx) (hrx6 : rx < 6) (hry0 : 0 ≤ ry) (hryH : ry < (baseBoard P st).height)
    (h : ry < baseHeight P → colState j rx.toNat ry.toNat = false) :
    (phase1Board P pad K st r colState).occupied (6 * (j.val : ℤ) + rx, (baseY pad K r : ℤ) + ry) = false := by
  rw [phase1Board_occupied_bucket P pad K st r colState j rx ry hrx0 hrx6 hry0 hryH]
  split_ifs with hlt
  · exact h hlt
  · rfl

private lemma cells_I_1 (x y : ℤ) (f : Bool) :
    (PieceState.mk .I 1 (x, y) f).cells = [(x, y + 1), (x, y), (x, y - 1), (x, y - 2)] := by
  simp [PieceState.cells, Piece.base, clockwise, sub_eq_add_neg]

private lemma cells_Sq (o : Fin 4) (x y : ℤ) (f : Bool) :
    (PieceState.mk .Sq o (x, y) f).cells = [(x, y), (x + 1, y), (x, y - 1), (x + 1, y - 1)] := by
  simp [PieceState.cells, Piece.base, sub_eq_add_neg]

private lemma cells_LG_1 (x y : ℤ) (f : Bool) :
    (PieceState.mk .LG 1 (x, y) f).cells = [(x + 1, y), (x, y), (x - 1, y), (x - 1, y + 1)] := by
  simp [PieceState.cells, Piece.base, clockwise, sub_eq_add_neg]

private lemma cells_LG_3 (x y : ℤ) (f : Bool) :
    (PieceState.mk .LG 3 (x, y) f).cells = [(x - 1, y), (x, y), (x + 1, y), (x + 1, y - 1)] := by
  simp [PieceState.cells, Piece.base, clockwise, sub_eq_add_neg]

private lemma cells_LS_1 (x y : ℤ) (f : Bool) :
    (PieceState.mk .LS 1 (x, y) f).cells = [(x + 1, y), (x, y), (x, y + 1), (x - 1, y + 1)] := by
  simp [PieceState.cells, Piece.base, clockwise, sub_eq_add_neg]

private lemma cells_RG_1 (x y : ℤ) (f : Bool) :
    (PieceState.mk .RG 1 (x, y) f).cells = [(x + 1, y), (x, y), (x - 1, y), (x - 1, y - 1)] := by
  simp [PieceState.cells, Piece.base, clockwise, sub_eq_add_neg]

private lemma bucketInitial_cols012 {rx ry : ℕ} (hrx : rx < 3) (hry : 4 ≤ ry) :
    bucketInitial rx ry = false := by
  unfold bucketInitial
  have hmod : rx % 6 = rx := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  by_cases h1 : rx < 2
  · simp [h1]; omega
  · have h2 : rx = 2 := by omega
    simp [h2]

private lemma bucketInitial_notch {rx ry : ℕ} (hrx : rx < 5) (hry : 4 ≤ ry) (hmod : ry % 6 = 4) :
    bucketInitial rx ry = false := by
  unfold bucketInitial
  have hm : rx % 6 = rx := Nat.mod_eq_of_lt (by omega)
  rw [hm]
  by_cases h1 : rx < 2
  · simp [h1]; omega
  · by_cases h2 : rx = 2
    · simp [h2]
    · have h3 : rx < 5 := hrx
      simp [h1, h2, h3]; omega

/-- Helper: prove `phase1Board.occupied (x, y) = false` by matching `(x, y)` to `(6 * j + rx, baseY + ry)`. -/
private lemma phase1_occ_false {P : ThreePartition} {pad K st r : ℕ}
    {colState : Fin P.s → ℕ → ℕ → Bool} {j : Fin P.s} {x y rx ry : ℤ}
    (hx : x = 6 * (j.val : ℤ) + rx) (hy : y = (baseY pad K r : ℤ) + ry)
    (hrx0 : 0 ≤ rx) (hrx6 : rx < 6) (hry0 : 0 ≤ ry) (hryH : ry < (baseBoard P st).height)
    (h : ry < baseHeight P → colState j rx.toNat ry.toNat = false) :
    (phase1Board P pad K st r colState).occupied (x, y) = false := by
  rw [hx, hy]
  exact phase1_cell_false hrx0 hrx6 hry0 hryH h

private lemma phase1_occ_true {P : ThreePartition} {pad K st r : ℕ}
    {colState : Fin P.s → ℕ → ℕ → Bool} {j : Fin P.s} {x y rx ry : ℤ}
    (hx : x = 6 * (j.val : ℤ) + rx) (hy : y = (baseY pad K r : ℤ) + ry)
    (hrx0 : 0 ≤ rx) (hrx6 : rx < 6) (hry0 : 0 ≤ ry) (hryB : ry < baseHeight P)
    (hryH : ry < (baseBoard P st).height)
    (h : colState j rx.toNat ry.toNat = true) :
    (phase1Board P pad K st r colState).occupied (x, y) = true := by
  rw [hx, hy, phase1Board_occupied_bucket P pad K st r colState j rx ry hrx0 hrx6 hry0 hryH]
  simp [hryB, h]

/-- Place `.I` (`o = 1`) in col 2 at height `h .. h + 3`, turning `bucketCellAt h` into `bucketCellFull (h + 4)`. -/
private lemma play_slot_I {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (h : ℕ)
    (hcur : colState j = bucketCellAt h) (hh : h + 4 ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) [.I]
      (phase1Board P pad K st r (Function.update colState j (bucketCellFull (h + 4)))) 0 := by
  have hst_ht : (baseHeight P : ℤ) + 5 ≤ (baseBoard P st).height := by
    have : 2 ≤ max R.radius 2 := le_max_right _ _
    simp only [baseBoard]; omega
  have hcol2_f : ∀ ry : ℤ, (h : ℤ) ≤ ry → ry < baseHeight P → colState j (2 : ℤ).toNat ry.toNat = false := by
    intro ry hry _
    rw [hcur]; unfold bucketCellAt
    have hge : ¬ ry.toNat < h := by omega
    by_cases hlt : ry.toNat < h + 4
    · simp [hge, hlt]
    · simp only [hge, hlt, ↓reduceIte]
      exact bucketInitial_cols012 (by omega) (by omega)
  apply play_bucket_piece hR P hs pad K st r hpad hst colState j .I 1 2 2 (h + 2)
    (bucketCellFull (h + 4)) (by omega)
  · intro c hc
    rw [cells_I_1] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> omega
  · intro ry' hy1 hy2 c hc
    rw [cells_I_1] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact phase1_occ_false (rx := 2) (ry := ry' + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
    · exact phase1_occ_false (rx := 2) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
    · exact phase1_occ_false (rx := 2) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
    · exact phase1_occ_false (rx := 2) (ry := ry' - 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
  · intro rx' hx1 hx2 c hc
    have hrx : rx' = 2 := by omega
    subst hrx
    rw [cells_I_1] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact phase1_occ_false (rx := 2) (ry := h + 3) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
    · exact phase1_occ_false (rx := 2) (ry := h + 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
    · exact phase1_occ_false (rx := 2) (ry := h + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
    · exact phase1_occ_false (rx := 2) (ry := h) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol2_f _ (by omega))
  · refine ⟨(6 * (j.val : ℤ) + 2, (baseY pad K r : ℤ) + h - 1), ?_, ?_⟩
    · simp only [translate]; rw [cells_I_1]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      right; right; right; ext <;> ring
    · by_cases hh0 : h = 0
      · subst hh0
        have heq : (baseY pad K r : ℤ) + (0 : ℕ) - 1 = (baseY pad K r : ℤ) - 1 := by ring
        rw [heq]
        exact phase1Board_occupied_below_baseY P pad K st r (by omega) colState j 2 (by omega) (by omega)
      · exact phase1_occ_true (rx := 2) (ry := h - 1) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [hcur]; unfold bucketCellAt; simp; left; omega)
  · intro rx hrx ry' hry'
    rw [hcur, cells_I_1]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    unfold bucketCellAt bucketCellFull
    by_cases h1 : ry' < h
    · simp [h1, show ry' < h + 4 by omega]
    · by_cases h2 : ry' < h + 4
      · by_cases hx2 : rx = 2
        · subst hx2; simp [h1, h2]; omega
        · simp [h1, h2, hx2]
      · simp [h1, h2]; omega

/-- Place `[.LG, .Sq]` to fill rows `h + 4, h + 5` (including the notch at `h + 4`), turning
`bucketCellFull (h + 4)` into `bucketCellFull (h + 6)`. -/
private lemma play_notch_fill {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (h : ℕ)
    (hcur : colState j = bucketCellFull (h + 4))
    (hmod : h % 6 = 0) (hh : h + 6 ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) [.LG, .Sq]
      (phase1Board P pad K st r (Function.update colState j (bucketCellFull (h + 6)))) 0 := by
  have hst_ht : (baseHeight P : ℤ) + 5 ≤ (baseBoard P st).height := by
    have : 2 ≤ max R.radius 2 := le_max_right _ _
    simp only [baseBoard]; omega
  have hcols_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 3 → (h : ℤ) + 4 ≤ ry → ry < baseHeight P →
      colState j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ _
    rw [hcur]; unfold bucketCellFull
    have hge : ¬ ry.toNat < h + 4 := by omega
    simp only [hge, ↓reduceIte]
    exact bucketInitial_cols012 (by omega) (by omega)
  have hnotch_f : ∀ rx : ℤ, 0 ≤ rx → rx < 5 → colState j rx.toNat ((h : ℤ) + 4).toNat = false := by
    intro rx _ _
    rw [hcur]; unfold bucketCellFull
    have hge : ¬ ((h : ℤ) + 4).toNat < h + 4 := by omega
    simp only [hge, ↓reduceIte]
    exact bucketInitial_notch (by omega) (by omega) (by omega)
  let midB : ℕ → ℕ → Bool := fun rx ry =>
    bucketCellFull (h + 4) rx ry ||
      decide ((rx = 4 ∧ ry = h + 4) ∨ (rx = 3 ∧ ry = h + 4) ∨
        (rx = 2 ∧ ry = h + 4) ∨ (rx = 2 ∧ ry = h + 5))
  -- Step 1: .LG (o = 1) dropped at rx = 1, slid right to rx = 3 at ry = h + 4
  have hstep1 : CanPlay R (phase1Board P pad K st r colState) [.LG]
      (phase1Board P pad K st r (Function.update colState j midB)) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst colState j .LG 1 1 3 (h + 4)
      midB (by omega)
    · intro c hc
      rw [cells_LG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc
      rw [cells_LG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 2) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcols_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcols_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcols_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry' + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcols_f _ _ (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      rw [cells_LG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := rx' + 1) (ry := h + 4) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (fun _ => hnotch_f _ (by omega) (by omega))
      · exact phase1_occ_false (rx := rx') (ry := h + 4) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (fun _ => hnotch_f _ (by omega) (by omega))
      · exact phase1_occ_false (rx := rx' - 1) (ry := h + 4) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (fun _ => hnotch_f _ (by omega) (by omega))
      · exact phase1_occ_false (rx := rx' - 1) (ry := h + 5) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcols_f _ _ (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 2, (baseY pad K r : ℤ) + h + 3), ?_, ?_⟩
      · simp only [translate]; rw [cells_LG_1]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right; left; ext <;> ring
      · exact phase1_occ_true (rx := 2) (ry := h + 3) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [hcur]; unfold bucketCellFull; simp [show ((h : ℤ) + 3).toNat < h + 4 by omega])
    · intro rx hrx ry' hry'
      rw [hcur, cells_LG_1]
      simp only [midB, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      congr 1; apply decide_eq_decide.mpr; omega
  -- Step 2: .Sq at (0, h + 5)
  have hmid_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 2 → (h : ℤ) + 4 ≤ ry → ry < baseHeight P →
      Function.update colState j midB j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ _
    rw [Function.update_self]; simp only [midB, bucketCellFull]
    have hge : ¬ ry.toNat < h + 4 := by omega
    have hbi : bucketInitial rx.toNat ry.toNat = false := bucketInitial_cols012 (by omega) (by omega)
    simp [hge, hbi]; omega
  have hstep2 : CanPlay R (phase1Board P pad K st r (Function.update colState j midB)) [.Sq]
      (phase1Board P pad K st r (Function.update (Function.update colState j midB) j (bucketCellFull (h + 6)))) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst (Function.update colState j midB) j
      .Sq 0 0 0 (h + 5) (bucketCellFull (h + 6)) (by omega)
    · intro c hc
      rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc
      rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      have hrx : rx' = 0 := by omega
      subst hrx
      rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := h + 5) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := h + 5) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := h + 4) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := h + 4) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hmid_f _ _ (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 0, (baseY pad K r : ℤ) + h + 3), ?_, ?_⟩
      · simp only [translate]; rw [cells_Sq]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right; left; ext <;> ring
      · exact phase1_occ_true (rx := 0) (ry := h + 3) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [Function.update_self]; simp [midB, bucketCellFull, show ((h : ℤ) + 3).toNat < h + 4 by omega])
    · intro rx hrx ry' hry'
      rw [Function.update_self, cells_Sq]
      simp only [midB, bucketCellFull, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      by_cases h1 : ry' < h + 4
      · simp [h1, show ry' < h + 6 by omega]
      · by_cases h2 : ry' < h + 6
        · simp only [h1, h2, ↓reduceIte]
          by_cases hy4 : ry' = h + 4
          · subst hy4
            by_cases hx2 : rx < 2
            · simp; omega
            · by_cases hx5 : rx < 5
              · simp; omega
              · have hx5' : rx = 5 := by omega
                subst hx5'; simp [bucketInitial]
          · have hy5 : ry' = h + 5 := by omega
            subst hy5
            by_cases hx2 : rx < 2
            · simp; omega
            · by_cases hx2' : rx = 2
              · subst hx2'; simp
              · have hbi : bucketInitial rx (h + 5) = true := by
                  unfold bucketInitial
                  have hm : rx % 6 = rx := Nat.mod_eq_of_lt hrx
                  rw [hm]
                  have h1' : ¬ rx < 2 := by omega
                  have h2' : ¬ rx = 2 := by omega
                  simp only [h1', h2', ↓reduceIte]
                  split_ifs
                  · simp; omega
                  · rfl
                simp [hbi]
        · cases bucketInitial rx ry' <;> (simp [h1, h2]; try omega)
  rw [Function.update_idem] at hstep2
  simpa using CanPlay.append hstep1 hstep2

/-- Play `initiator = [.I, .LG, .Sq]` in bucket `j`, advancing `bucketCellAt h` to `bucketCellFull (h + 6)`. -/
private lemma play_initiator {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (h : ℕ)
    (hcur : colState j = bucketCellAt h)
    (hmod : h % 6 = 0) (hh : h + 6 ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) initiator
      (phase1Board P pad K st r (Function.update colState j (bucketCellFull (h + 6)))) 0 := by
  have h1 := play_slot_I hR P hs pad K st r hpad hst colState j h hcur (by omega)
  have h2 := play_notch_fill hR P hs pad K st r hpad hst
    (Function.update colState j (bucketCellFull (h + 4))) j h (Function.update_self j _ _) hmod hh
  rw [Function.update_idem] at h2
  simpa [initiator] using CanPlay.append h1 h2

/-- Play `filler = [.LG, .LS, .LG, .LG, .Sq]` in bucket `j`, advancing `bucketCellFull k` to `bucketCellFull (k + 6)`. -/
private lemma play_filler {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (k : ℕ)
    (hcur : colState j = bucketCellFull k)
    (hmod : k % 6 = 0) (hk6 : 6 ≤ k) (hk : k + 6 ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) filler
      (phase1Board P pad K st r (Function.update colState j (bucketCellFull (k + 6)))) 0 := by
  have hst_ht : (baseHeight P : ℤ) + 5 ≤ (baseBoard P st).height := by
    have : 2 ≤ max R.radius 2 := le_max_right _ _
    simp only [baseBoard]; omega
  let f1 : ℕ → ℕ → Bool := fun rx ry =>
    bucketCellFull k rx ry ||
      decide ((rx = 2 ∧ ry = k) ∨ (rx = 1 ∧ ry = k) ∨ (rx = 0 ∧ ry = k) ∨ (rx = 0 ∧ ry = k + 1))
  let f2 : ℕ → ℕ → Bool := fun rx ry =>
    f1 rx ry ||
      decide ((rx = 2 ∧ ry = k + 1) ∨ (rx = 1 ∧ ry = k + 1) ∨
        (rx = 1 ∧ ry = k + 2) ∨ (rx = 0 ∧ ry = k + 2))
  have hcol_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 3 → (k : ℤ) ≤ ry → ry < baseHeight P →
      colState j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ _
    rw [hcur]; unfold bucketCellFull
    have hge : ¬ ry.toNat < k := by omega
    simp only [hge, ↓reduceIte]
    exact bucketInitial_cols012 (by omega) (by omega)
  -- Step 1: .LG (o = 1) at (1, k)
  have hstep1 : CanPlay R (phase1Board P pad K st r colState) [.LG]
      (phase1Board P pad K st r (Function.update colState j f1)) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst colState j .LG 1 1 1 k f1 (by omega)
    · intro c hc; rw [cells_LG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc; rw [cells_LG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 2) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry' + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      have hrx : rx' = 1 := by omega
      subst hrx; rw [cells_LG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 2) (ry := k) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := k) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := k + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 1, (baseY pad K r : ℤ) + k - 1), ?_, ?_⟩
      · simp only [translate]; rw [cells_LG_1]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; left; ext <;> ring
      · exact phase1_occ_true (rx := 1) (ry := k - 1) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [hcur]; unfold bucketCellFull; simp; left; omega)
    · intro rx hrx ry' hry'
      rw [hcur, cells_LG_1]
      simp only [f1, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      congr 1; apply decide_eq_decide.mpr; omega
  -- Step 2: .LS (o = 1) at (1, k + 1)
  have hf1_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 3 → (k : ℤ) + 1 ≤ ry →
      ¬ (rx = 0 ∧ ry = k + 1) → ry < baseHeight P →
      Function.update colState j f1 j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ hne _
    rw [Function.update_self]; simp only [f1, bucketCellFull]
    have hge : ¬ ry.toNat < k := by omega
    have hbi : bucketInitial rx.toNat ry.toNat = false := bucketInitial_cols012 (by omega) (by omega)
    simp [hge, hbi]; omega
  have hstep2 : CanPlay R (phase1Board P pad K st r (Function.update colState j f1)) [.LS]
      (phase1Board P pad K st r (Function.update (Function.update colState j f1) j f2)) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst (Function.update colState j f1) j
      .LS 1 1 1 (k + 1) f2 (by omega)
    · intro c hc; rw [cells_LS_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc; rw [cells_LS_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 2) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry' + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry' + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      have hrx : rx' = 1 := by omega
      subst hrx; rw [cells_LS_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 2) (ry := k + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k + 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := k + 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf1_f _ _ (by omega) (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 1, (baseY pad K r : ℤ) + k), ?_, ?_⟩
      · simp only [translate]; rw [cells_LS_1]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; left; ext <;> ring
      · exact phase1_occ_true (rx := 1) (ry := k) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [Function.update_self]; simp [f1])
    · intro rx hrx ry' hry'
      rw [Function.update_self, cells_LS_1]
      simp only [f2, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      congr 1; apply decide_eq_decide.mpr; omega
  rw [Function.update_idem] at hstep2
  -- Step 3: .LG (o = 3) at (1, k + 3)
  have hf2_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 3 → (k : ℤ) + 2 ≤ ry →
      ¬ (rx ≤ 1 ∧ ry = k + 2) → ry < baseHeight P →
      Function.update colState j f2 j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ hne _
    rw [Function.update_self]; simp only [f2, f1, bucketCellFull]
    have hge : ¬ ry.toNat < k := by omega
    have hbi : bucketInitial rx.toNat ry.toNat = false := bucketInitial_cols012 (by omega) (by omega)
    simp [hge, hbi]; omega
  have hstep3 : CanPlay R (phase1Board P pad K st r (Function.update colState j f2)) [.LG]
      (phase1Board P pad K st r (Function.update (Function.update colState j f2) j (bucketCellFull (k + 4)))) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst (Function.update colState j f2) j
      .LG 3 1 1 (k + 3) (bucketCellFull (k + 4)) (by omega)
    · intro c hc; rw [cells_LG_3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc; rw [cells_LG_3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 2) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 2) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      have hrx : rx' = 1 := by omega
      subst hrx; rw [cells_LG_3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := k + 3) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k + 3) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 2) (ry := k + 3) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 2) (ry := k + 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hf2_f _ _ (by omega) (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 2, (baseY pad K r : ℤ) + k + 1), ?_, ?_⟩
      · simp only [translate]; rw [cells_LG_3]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right; right; ext <;> ring
      · exact phase1_occ_true (rx := 2) (ry := k + 1) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by
            rw [Function.update_self]
            have ht : ((k : ℤ) + 1).toNat = k + 1 := by omega
            simp [ht, f2])
    · intro rx hrx ry' hry'
      rw [Function.update_self, cells_LG_3]
      simp only [f2, f1, bucketCellFull, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      by_cases h1 : ry' < k
      · simp [h1, show ry' < k + 4 by omega]
      · by_cases h2 : ry' < k + 4
        · simp only [h1, h2, ↓reduceIte]
          by_cases hx3 : rx < 3
          · simp; omega
          · have hbi : bucketInitial rx ry' = true := by
              unfold bucketInitial
              have hm : rx % 6 = rx := Nat.mod_eq_of_lt hrx
              rw [hm]
              have h1' : ¬ rx < 2 := by omega
              have h2' : ¬ rx = 2 := by omega
              simp only [h1', h2', ↓reduceIte]
              split_ifs
              · simp; omega
              · rfl
            simp [hbi]
        · cases bucketInitial rx ry' <;> (simp [h1, h2]; try omega)
  rw [Function.update_idem] at hstep3
  have hstep45 := play_notch_fill hR P hs pad K st r hpad hst
    (Function.update colState j (bucketCellFull (k + 4))) j k (Function.update_self j _ _) hmod hk
  rw [Function.update_idem] at hstep45
  have h12 := CanPlay.append hstep1 hstep2
  have h123 := CanPlay.append h12 hstep3
  simpa [filler] using CanPlay.append h123 hstep45

/-- Play `a` copies of `filler` in bucket `j`. -/
private lemma play_fillers {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (a k : ℕ)
    (hcur : colState j = bucketCellFull k)
    (hmod : k % 6 = 0) (hk6 : 6 ≤ k) (hk : k + 6 * a ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) (List.replicate a filler).flatten
      (phase1Board P pad K st r (Function.update colState j (bucketCellFull (k + 6 * a)))) 0 := by
  induction a generalizing colState k with
  | zero =>
    have heq : Function.update colState j (bucketCellFull (k + 6 * 0)) = colState := by
      simp [hcur]
    rw [heq]
    exact CanPlay.nil R _
  | succ a ih =>
    have h1 := play_filler hR P hs pad K st r hpad hst colState j k hcur hmod hk6 (by omega)
    have h2 := ih (Function.update colState j (bucketCellFull (k + 6))) (k + 6)
      (Function.update_self j _ _) (by omega) (by omega) (by omega)
    rw [Function.update_idem] at h2
    have hsum : k + 6 + 6 * a = k + 6 * (a + 1) := by ring
    rw [hsum] at h2
    simpa [List.replicate_succ] using CanPlay.append h1 h2

/-- Play `terminator = [.Sq, .Sq]` in bucket `j`, turning `bucketCellFull k` into `bucketCellAt k`. -/
private lemma play_terminator {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (k : ℕ)
    (hcur : colState j = bucketCellFull k)
    (hmod : k % 6 = 0) (hk6 : 6 ≤ k) (hk : k + 4 ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) terminator
      (phase1Board P pad K st r (Function.update colState j (bucketCellAt k))) 0 := by
  have hst_ht : (baseHeight P : ℤ) + 5 ≤ (baseBoard P st).height := by
    have : 2 ≤ max R.radius 2 := le_max_right _ _
    simp only [baseBoard]; omega
  let t1 : ℕ → ℕ → Bool := fun rx ry =>
    bucketCellFull k rx ry ||
      decide ((rx = 0 ∧ ry = k + 1) ∨ (rx = 1 ∧ ry = k + 1) ∨
        (rx = 0 ∧ ry = k) ∨ (rx = 1 ∧ ry = k))
  have hcol_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 2 → (k : ℤ) ≤ ry → ry < baseHeight P →
      colState j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ _
    rw [hcur]; unfold bucketCellFull
    have hge : ¬ ry.toNat < k := by omega
    simp only [hge, ↓reduceIte]
    exact bucketInitial_cols012 (by omega) (by omega)
  -- Step 1: .Sq at (0, k + 1)
  have hstep1 : CanPlay R (phase1Board P pad K st r colState) [.Sq]
      (phase1Board P pad K st r (Function.update colState j t1)) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst colState j .Sq 0 0 0 (k + 1) t1 (by omega)
    · intro c hc; rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc; rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      have hrx : rx' = 0 := by omega
      subst hrx; rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := k + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k + 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := k) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (hcol_f _ _ (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 0, (baseY pad K r : ℤ) + k - 1), ?_, ?_⟩
      · simp only [translate]; rw [cells_Sq]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right; left; ext <;> ring
      · exact phase1_occ_true (rx := 0) (ry := k - 1) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [hcur]; unfold bucketCellFull; simp; left; omega)
    · intro rx hrx ry' hry'
      rw [hcur, cells_Sq]
      simp only [t1, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      congr 1; apply decide_eq_decide.mpr; omega
  -- Step 2: .Sq at (0, k + 3)
  have ht1_f : ∀ rx ry : ℤ, 0 ≤ rx → rx < 2 → (k : ℤ) + 2 ≤ ry → ry < baseHeight P →
      Function.update colState j t1 j rx.toNat ry.toNat = false := by
    intro rx ry _ _ _ _
    rw [Function.update_self]; simp only [t1, bucketCellFull]
    have hge : ¬ ry.toNat < k := by omega
    have hbi : bucketInitial rx.toNat ry.toNat = false := bucketInitial_cols012 (by omega) (by omega)
    simp [hge, hbi]; omega
  have hstep2 : CanPlay R (phase1Board P pad K st r (Function.update colState j t1)) [.Sq]
      (phase1Board P pad K st r (Function.update (Function.update colState j t1) j (bucketCellAt k))) 0 := by
    apply play_bucket_piece hR P hs pad K st r hpad hst (Function.update colState j t1) j
      .Sq 0 0 0 (k + 3) (bucketCellAt k) (by omega)
    · intro c hc; rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    · intro ry' hy1 hy2 c hc; rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry') (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := ry' - 1) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
    · intro rx' hx1 hx2 c hc
      have hrx : rx' = 0 := by omega
      subst hrx; rw [cells_Sq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact phase1_occ_false (rx := 0) (ry := k + 3) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k + 3) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 0) (ry := k + 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
      · exact phase1_occ_false (rx := 1) (ry := k + 2) (by ring) (by ring) (by omega) (by omega) (by omega) (by omega) (ht1_f _ _ (by omega) (by omega) (by omega))
    · refine ⟨(6 * (j.val : ℤ) + 0, (baseY pad K r : ℤ) + k + 1), ?_, ?_⟩
      · simp only [translate]; rw [cells_Sq]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right; left; ext <;> ring
      · exact phase1_occ_true (rx := 0) (ry := k + 1) (by ring) (by ring) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by
            rw [Function.update_self]
            have ht : ((k : ℤ) + 1).toNat = k + 1 := by omega
            simp [ht, t1])
    · intro rx hrx ry' hry'
      rw [Function.update_self, cells_Sq]
      simp only [t1, bucketCellFull, bucketCellAt, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq]
      by_cases h1 : ry' < k
      · simp [h1]
      · by_cases h2 : ry' < k + 4
        · simp only [h1, h2, ↓reduceIte]
          by_cases hx2 : rx < 2
          · have hne : rx ≠ 2 := by omega
            simp [hne]; omega
          · by_cases hx2' : rx = 2
            · subst hx2'
              have hbi : bucketInitial 2 ry' = false := bucketInitial_cols012 (by omega) (by omega)
              simp [hbi]
            · have hne : rx ≠ 2 := hx2'
              have hbi : bucketInitial rx ry' = true := by
                unfold bucketInitial
                have hm : rx % 6 = rx := Nat.mod_eq_of_lt hrx
                rw [hm]
                have h1' : ¬ rx < 2 := by omega
                have h2' : ¬ rx = 2 := by omega
                simp only [h1', h2', ↓reduceIte]
                split_ifs
                · simp; omega
                · rfl
              simp [hbi, hne]
        · cases bucketInitial rx ry' <;> (simp [h1, h2]; try omega)
  rw [Function.update_idem] at hstep2
  simpa [terminator] using CanPlay.append hstep1 hstep2

/-- Play an entire `integerBlock a` in bucket `j`, advancing `bucketCellAt h` to `bucketCellAt (h + 6 * (a + 1))`. -/
private lemma play_integerBlock {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st)
    (colState : Fin P.s → ℕ → ℕ → Bool) (j : Fin P.s) (h a : ℕ)
    (hcur : colState j = bucketCellAt h)
    (hmod : h % 6 = 0) (hbound : h + 6 * (a + 1) + 4 ≤ baseHeight P) :
    CanPlay R (phase1Board P pad K st r colState) (integerBlock a)
      (phase1Board P pad K st r (Function.update colState j (bucketCellAt (h + 6 * (a + 1))))) 0 := by
  have h1 := play_initiator hR P hs pad K st r hpad hst colState j h hcur hmod (by omega)
  have h2 := play_fillers hR P hs pad K st r hpad hst
    (Function.update colState j (bucketCellFull (h + 6))) j a (h + 6)
    (Function.update_self j _ _) (by omega) (by omega) (by omega)
  rw [Function.update_idem] at h2
  have h3 := play_terminator hR P hs pad K st r hpad hst
    (Function.update colState j (bucketCellFull (h + 6 + 6 * a))) j (h + 6 + 6 * a)
    (Function.update_self j _ _) (by omega) (by omega) (by omega)
  rw [Function.update_idem] at h3
  have hsum : h + 6 + 6 * a = h + 6 * (a + 1) := by ring
  rw [hsum] at h2 h3
  have h12 := CanPlay.append h1 h2
  simpa [integerBlock] using CanPlay.append h12 h3

/-- Phase 1a complete: playing `numberPieces P ++ List.replicate P.s .I` fills all `P.s` buckets completely! -/
private lemma play_phase1a {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hN : P.Normalized) (hs : 0 < P.s) (hyes : P.HasSolution)
    (pad K st r : ℕ) (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st) :
    CanPlay R (paddedReservoirBoard P pad K st r) (numberPieces P ++ List.replicate P.s .I)
      (phase1Board P pad K st r (fun _ _ _ => true)) 0 := by
  rcases hyes with ⟨assign, hassign⟩
  -- For each bucket j, the fiber has cardinality 3 and total weight 6 * P.target + 18
  have hfiber_sum : ∀ j : Fin P.s,
      ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j),
        6 * (P.entry i + 1) = 6 * P.target + 18 := by
    intro j
    have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j), P.entry i = P.target :=
      hassign j
    have hcard : (Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j)).card = 3 :=
      hN.1 _ hsum
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j), 6 * (P.entry i + 1)
        = 6 * ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j), (P.entry i + 1) := by
          rw [Finset.mul_sum]
      _ = 6 * ((∑ i ∈ Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j), P.entry i) +
            (Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j)).card) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = 6 * P.target + 18 := by rw [hsum, hcard]; ring
  let hpref : ℕ → Fin P.s → ℕ := fun n j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n ∧ assign i = j), 6 * (P.entry i + 1)
  have hpref_mod : ∀ n j, hpref n j % 6 = 0 := by
    intro n j
    have hdvd : 6 ∣ hpref n j := Finset.dvd_sum fun i _ => dvd_mul_right 6 _
    exact Nat.mod_eq_zero_of_dvd hdvd
  have hpref_le : ∀ n j, hpref n j ≤ 6 * P.target + 18 := by
    intro n j
    rw [← hfiber_sum j]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.2
    · intros; exact Nat.zero_le _
  -- Induction on n ≤ 3 * P.s for numberPieces P
  have hnum_ind : ∀ n ≤ 3 * P.s,
      CanPlay R (phase1Board P pad K st r (fun _ => bucketCellAt 0))
        ((List.ofFn P.entry |>.take n).flatMap integerBlock)
        (phase1Board P pad K st r (fun j => bucketCellAt (hpref n j))) 0 := by
    intro n hn
    induction n with
    | zero =>
      have h0 : (fun j => bucketCellAt (hpref 0 j)) = (fun _ => bucketCellAt 0) := by
        funext j; simp [hpref]
      rw [h0]
      exact CanPlay.nil R _
    | succ n ih =>
      have hih := ih (by omega)
      set idx : Fin (3 * P.s) := ⟨n, hn⟩
      set j : Fin P.s := assign idx
      have htake : (List.ofFn P.entry).take (n + 1) =
          (List.ofFn P.entry).take n ++ [P.entry idx] := by
        rw [List.take_add_one, List.getElem?_ofFn]
        simp [show n < 3 * P.s by omega, idx]
      rw [htake, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hupd_eq : Function.update (fun j' => bucketCellAt (hpref n j')) j
          (bucketCellAt (hpref n j + 6 * (P.entry idx + 1))) =
          (fun j' => bucketCellAt (hpref (n + 1) j')) := by
        funext j'
        by_cases hj' : j' = j
        · subst hj'
          rw [Function.update_self]
          congr 1
          have hset : Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n + 1 ∧ assign i = j) =
              insert idx (Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n ∧ assign i = j)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, ha⟩
              by_cases he : i.val = n
              · left; ext; exact he
              · right; exact ⟨by omega, ha⟩
            · rintro (rfl | ⟨hlt, ha⟩)
              · exact ⟨by simp [idx], rfl⟩
              · exact ⟨by omega, ha⟩
          have hnot : idx ∉ Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n ∧ assign i = j) := by
            simp [idx]
          simp only [hpref, hset, Finset.sum_insert hnot]
          omega
        · rw [Function.update_of_ne hj']
          congr 1
          have hset : Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n + 1 ∧ assign i = j') =
              Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n ∧ assign i = j') := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, ha⟩
              refine ⟨?_, ha⟩
              by_contra hge
              have hi_eq : i = idx := by ext; simp [idx]; omega
              subst hi_eq
              exact hj' ha.symm
            · rintro ⟨hlt, ha⟩; exact ⟨by omega, ha⟩
          simp only [hpref, hset]
      have hbd : hpref n j + 6 * (P.entry idx + 1) + 4 ≤ baseHeight P := by
        have hle := hpref_le (n + 1) j
        have heq : hpref (n + 1) j = hpref n j + 6 * (P.entry idx + 1) := by
          have hset : Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n + 1 ∧ assign i = j) =
              insert idx (Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n ∧ assign i = j)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, ha⟩
              by_cases he : i.val = n
              · left; ext; exact he
              · right; exact ⟨by omega, ha⟩
            · rintro (rfl | ⟨hlt, ha⟩)
              · exact ⟨by simp [idx], rfl⟩
              · exact ⟨by omega, ha⟩
          have hnot : idx ∉ Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < n ∧ assign i = j) := by
            simp [idx]
          simp only [hpref, hset, Finset.sum_insert hnot]
          omega
        unfold baseHeight; omega
      have hstep := play_integerBlock hR P hs pad K st r hpad hst
        (fun j' => bucketCellAt (hpref n j')) j (hpref n j) (P.entry idx) rfl (hpref_mod n j) hbd
      rw [hupd_eq] at hstep
      simpa using CanPlay.append hih hstep
  have hnum := hnum_ind (3 * P.s) le_rfl
  have htake_all : (List.ofFn P.entry).take (3 * P.s) = List.ofFn P.entry := by
    rw [List.take_of_length_le]; simp
  rw [htake_all] at hnum
  have hpref_end : (fun j => bucketCellAt (hpref (3 * P.s) j)) =
      (fun _ => bucketCellAt (6 * P.target + 18)) := by
    funext j
    congr 1
    have hset : Finset.univ.filter (fun i : Fin (3 * P.s) => i.val < 3 * P.s ∧ assign i = j) =
        Finset.univ.filter (fun i : Fin (3 * P.s) => assign i = j) := by
      ext i; simp
    simp only [hpref, hset]
    exact hfiber_sum j
  rw [hpref_end, phase1Board_init] at hnum
  -- Now play List.replicate P.s .I, filling col 2 of rows 6*T+18 .. 6*T+21 in each bucket
  have hfull_eq : ∀ rx ry, ry < baseHeight P → bucketCellFull (6 * P.target + 18 + 4) rx ry = true := by
    intro rx ry hry
    unfold baseHeight at hry
    unfold bucketCellFull
    simp [show ry < 6 * P.target + 18 + 4 by omega]
  have hfinal_ind : ∀ m ≤ P.s,
      CanPlay R (phase1Board P pad K st r (fun _ => bucketCellAt (6 * P.target + 18)))
        (List.replicate m .I)
        (phase1Board P pad K st r (fun j =>
          if j.val < m then bucketCellFull (6 * P.target + 18 + 4) else bucketCellAt (6 * P.target + 18))) 0 := by
    intro m hm
    induction m with
    | zero =>
      simpa using CanPlay.nil R _
    | succ m ih =>
      have hih := ih (by omega)
      set j : Fin P.s := ⟨m, hm⟩
      have hstep := play_slot_I hR P hs pad K st r hpad hst
        (fun j' => if j'.val < m then bucketCellFull (6 * P.target + 18 + 4)
          else bucketCellAt (6 * P.target + 18))
        j (6 * P.target + 18) (by simp [j]) (by unfold baseHeight; omega)
      have hupd : Function.update (fun j' : Fin P.s =>
          if j'.val < m then bucketCellFull (6 * P.target + 18 + 4)
          else bucketCellAt (6 * P.target + 18)) j (bucketCellFull (6 * P.target + 18 + 4)) =
          (fun j' : Fin P.s => if j'.val < m + 1 then bucketCellFull (6 * P.target + 18 + 4)
            else bucketCellAt (6 * P.target + 18)) := by
        funext j'
        by_cases hj' : j' = j
        · subst hj'; simp [j]
        · rw [Function.update_of_ne hj']
          have hne : j'.val ≠ m := fun h => hj' (Fin.ext h)
          by_cases hlt : j'.val < m
          · simp [hlt, show j'.val < m + 1 by omega]
          · simp [hlt, show ¬ j'.val < m + 1 by omega]
      rw [hupd] at hstep
      rw [List.replicate_succ']
      simpa using CanPlay.append hih hstep
  have hfin := hfinal_ind P.s le_rfl
  have hboard_eq : phase1Board P pad K st r (fun j =>
      if j.val < P.s then bucketCellFull (6 * P.target + 18 + 4) else bucketCellAt (6 * P.target + 18)) =
      phase1Board P pad K st r (fun _ _ _ => true) := by
    apply board_ext (by rfl) (by rfl)
    intro y hy1 hy2 x hx1 hx2
    simp only [phase1Board]
    by_cases h1 : y < r
    · simp [h1]
    by_cases h2 : y = r
    · simp [h2]
    by_cases h3 : y = r + 1
    · simp [h3]
    by_cases h4 : y < r + 2 + 4 * K
    · simp [h1, h2, h3, h4]
    by_cases h5 : y < baseY pad K r
    · simp [h1, h2, h3, h4, h5]
    by_cases h6 : y < baseY pad K r + baseHeight P
    · simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
      by_cases hx : x < 6 * P.s
      · simp only [hx, ↓reduceDIte]
        have hjlt : (⟨x / 6, by omega⟩ : Fin P.s).val < P.s := by dsimp; omega
        simp only [hjlt, ↓reduceIte]
        exact hfull_eq _ _ (by omega)
      · simp [hx]
    · simp [h1, h2, h3, h4, h5, h6]
  rw [hboard_eq] at hfin
  simpa [numberPieces] using CanPlay.append hnum hfin

/-! ### Section 4: Phases 1b, 1c+2, 3a, 3b, 4 and Main Completeness Theorem -/

/-- Phase 1b: drop `.RG` (`o = 1`) into the first lock cap, clearing rows `baseY + H - 2` and `baseY + H - 1`. -/
private lemma play_phase1b {R : Rotation} (hR : R.Admissible)
    (P : ThreePartition) (hs : 0 < P.s) (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad) (hst : 5 * max R.radius 2 + 12 ≤ st) :
    ∃ B1 : Board,
      CanPlay R (phase1Board P pad K st r (fun _ _ _ => true)) [.RG] B1 2 ∧
      B1.height = baseY pad K r + (baseBoard P st).height ∧
      B1.width = 6 * (P.s + pad) + 3 ∧
      ∀ (y : Fin B1.height) (x : Fin B1.width),
        B1.cell y x =
          if y.val < r then decide (x.val = 0)
          else if y.val = r then decide (x.val ≠ 6 * (P.s + pad))
          else if y.val = r + 1 then decide (x.val < 6 * (P.s + pad))
          else if y.val < r + 2 + 4 * K then decide (x.val ≠ 6 * (P.s + pad) - 1)
          else if y.val < baseY pad K r + baseHeight P - 2 then decide (x.val ≠ 6 * P.s + 2)
          else false := by
  set B := phase1Board P pad K st r (fun _ _ _ => true)
  let top : ℕ := baseY pad K r + baseHeight P
  have htop_def : top = baseY pad K r + baseHeight P := rfl
  have hby : r + 2 + 4 * K ≤ baseY pad K r := by unfold baseY; omega
  have hH_ge : 22 ≤ baseHeight P := by unfold baseHeight; omega
  have hW : 2 * max R.radius 2 + 9 ≤ B.width := by simp only [B, phase1Board]; omega
  have hH : top + 5 * max R.radius 2 + 12 ≤ B.height := by
    simp only [B, phase1Board, baseBoard, top]; omega
  set q : PieceState := PieceState.mk .RG 1 (6 * (P.s : ℤ) + 1, (top : ℤ) - 1) true
  have hocc_lock : ∀ (cx cy : ℤ),
      (cx = 6 * (P.s : ℤ) ∧ cy = (top : ℤ) - 2) ∨
      (6 * (P.s : ℤ) ≤ cx ∧ cx ≤ 6 * (P.s : ℤ) + 2 ∧ (top : ℤ) - 1 ≤ cy ∧ cy ≤ (top : ℤ) + 4) →
      B.occupied (cx, cy) = false := by
    intro cx cy hc
    have hy0 : 0 ≤ cy ∧ cy < B.height := by
      have : 2 ≤ max R.radius 2 := le_max_right _ _
      omega
    have hx0 : 0 ≤ cx ∧ cx < B.width := by simp only [B, phase1Board]; omega
    simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
    by_cases hlt : cy.toNat < top
    · simp only [B, phase1Board]
      have h1 : ¬ cy.toNat < r := by omega
      have h2 : ¬ cy.toNat = r := by omega
      have h3 : ¬ cy.toNat = r + 1 := by omega
      have h4 : ¬ cy.toNat < r + 2 + 4 * K := by omega
      have h5 : ¬ cy.toNat < baseY pad K r := by omega
      have hnx : ¬ cx.toNat < 6 * P.s := by omega
      have hlt' : cy.toNat < baseY pad K r + baseHeight P := hlt
      simp only [h1, h2, h3, h4, h5, hlt', hnx, ↓reduceIte, ↓reduceDIte]
      by_cases he0 : cx.toNat = 6 * P.s
      · simp [he0]; omega
      · by_cases he1 : cx.toNat = 6 * P.s + 1
        · simp [he1]; omega
        · have he2 : cx.toNat = 6 * P.s + 2 := by omega
          simp [he2]; omega
    · exact phase1Board_empty P pad K st r (fun _ _ _ => true)
        ⟨cy.toNat, hy0.2 |> fun h => by simpa [B] using Int.toNat_lt hy0.1 |>.mpr h⟩
        (by dsimp; omega)
        ⟨cx.toNat, hx0.2 |> fun h => by simpa [B] using Int.toNat_lt hx0.1 |>.mpr h⟩
  have htraj : Trajectory R B .RG q := by
    apply trajectory_of_drop_slide hR hW hH (phase1Board_empty P pad K st r (fun _ _ _ => true))
      (x_drop := 6 * (P.s : ℤ) + 1) (x_target := 6 * (P.s : ℤ) + 1) (y := (top : ℤ) - 1)
    · omega
    · intro y' hy1 hy2 c hc
      rw [cells_RG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · by_cases hy1' : y' = (top : ℤ) - 1
        · exact hocc_lock _ _ (Or.inl ⟨by omega, by omega⟩)
        · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
    · intro x' hx1 hx2 c hc
      have hx : x' = 6 * (P.s : ℤ) + 1 := by omega
      subst hx
      rw [cells_RG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inl ⟨by omega, by omega⟩)
    · intro hcl
      have hmem : (6 * (P.s : ℤ) + 1, (top : ℤ) - 2) ∈
          (translate (PieceState.mk .RG 1 (6 * (P.s : ℤ) + 1, (top : ℤ) - 1) false) 0 (-1)).cells := by
        simp only [translate]; rw [cells_RG_1]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; left; ext <;> ring
      have hf := hcl _ hmem
      have hy0 : 0 ≤ (top : ℤ) - 2 ∧ (top : ℤ) - 2 < B.height := by omega
      have hx0 : 0 ≤ 6 * (P.s : ℤ) + 1 ∧ 6 * (P.s : ℤ) + 1 < B.width := by
        simp only [B, phase1Board]; omega
      simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte] at hf
      have hxt : (6 * (P.s : ℤ) + 1).toNat = 6 * P.s + 1 := by omega
      have hyt : ((top : ℤ) - 2).toNat = top - 2 := by omega
      simp only [B, phase1Board, hxt, hyt] at hf
      have h1 : ¬ top - 2 < r := by omega
      have h2 : ¬ top - 2 = r := by omega
      have h3 : ¬ top - 2 = r + 1 := by omega
      have h4 : ¬ top - 2 < r + 2 + 4 * K := by omega
      have h5 : ¬ top - 2 < baseY pad K r := by omega
      have h6 : top - 2 < baseY pad K r + baseHeight P := by omega
      have hnx : ¬ 6 * P.s + 1 < 6 * P.s := by omega
      have hne0 : 6 * P.s + 1 ≠ 6 * P.s := by omega
      simp only [h1, h2, h3, h4, h5, h6, hnx, hne0, ↓reduceIte, ↓reduceDIte,
        decide_eq_false_iff_not] at hf
      omega
  -- Clear band [top - 2, top)
  have hcells_q : q.cells = [(6 * (P.s : ℤ) + 2, (top : ℤ) - 1),
      (6 * (P.s : ℤ) + 1, (top : ℤ) - 1),
      (6 * (P.s : ℤ), (top : ℤ) - 1),
      (6 * (P.s : ℤ), (top : ℤ) - 2)] := by
    dsimp only [q]; rw [cells_RG_1]; simp only [add_sub_cancel_right]; ring_nf
  have hclear := settle_clear_band B q (top - 2) top (by omega) (by omega)
    (fun y hy => by
      by_cases h1 : y.val < r
      · refine ⟨⟨1, by simp [B, phase1Board]⟩, ?_⟩
        have hnot : ((1 : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
        simp [Board.insert, B, phase1Board, h1, hnot]
      · by_cases h2 : y.val < r + 2
        · refine ⟨⟨6 * (P.s + pad), by simp [B, phase1Board]⟩, ?_⟩
          have hnot : ((6 * (P.s + pad) : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
          have hcell : B.cell y ⟨6 * (P.s + pad), by simp [B, phase1Board]⟩ = false := by
            by_cases he : y.val = r
            · simp [B, phase1Board, he]
            · have he1 : y.val = r + 1 := by omega
              simp [B, phase1Board, he1]
          simp only [Board.insert, hcell, Bool.false_or, decide_eq_false_iff_not]
          simpa using hnot
        · by_cases h3 : y.val < r + 2 + 4 * K
          · refine ⟨⟨6 * (P.s + pad) - 1, by simp [B, phase1Board]; omega⟩, ?_⟩
            have hnot : (((6 * (P.s + pad) - 1 : ℕ) : ℤ), (y.val : ℤ)) ∉ q.cells := by
              rw [hcells_q]; simp; omega
            have hne1 : ¬ y.val = r := by omega
            have hne2 : ¬ y.val = r + 1 := by omega
            simp [Board.insert, B, phase1Board, h1, hne1, hne2, h3, hnot]
          · refine ⟨⟨6 * P.s + 2, by simp [B, phase1Board]⟩, ?_⟩
            have hnot : (6 * (P.s : ℤ) + 2, (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
            have hne1 : ¬ y.val = r := by omega
            have hne2 : ¬ y.val = r + 1 := by omega
            have hcell : B.cell y ⟨6 * P.s + 2, by simp [B, phase1Board]⟩ = false := by
              by_cases h4 : y.val < baseY pad K r
              · simp [B, phase1Board, h1, hne1, hne2, h3, h4]
              · have h5 : y.val < baseY pad K r + baseHeight P := by omega
                have hnx : ¬ 6 * P.s + 2 < 6 * P.s := by omega
                have hne0 : 6 * P.s + 2 ≠ 6 * P.s := by omega
                have hne1' : 6 * P.s + 2 ≠ 6 * P.s + 1 := by omega
                simp only [B, phase1Board, h1, hne1, hne2, h3, h4, h5, hnx, hne0, hne1',
                  ↓reduceIte, ↓reduceDIte, decide_eq_false_iff_not]
                omega
            simp only [Board.insert, hcell, Bool.false_or, decide_eq_false_iff_not]
            simpa using hnot)
    (fun y hy1 hy2 x => by
      simp only [Board.insert, hcells_q, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
        Bool.or_eq_true, decide_eq_true_eq]
      have hy2' : y.val < baseY pad K r + baseHeight P := hy2
      by_cases hx : x.val < 6 * P.s ∨ 6 * P.s + 3 ≤ x.val
      · left
        simp only [B, phase1Board]
        have h1 : ¬ y.val < r := by omega
        have h2 : ¬ y.val = r := by omega
        have h3 : ¬ y.val = r + 1 := by omega
        have h4 : ¬ y.val < r + 2 + 4 * K := by omega
        have h5 : ¬ y.val < baseY pad K r := by omega
        simp only [h1, h2, h3, h4, h5, hy2', ↓reduceIte]
        rcases hx with hxl | hxr
        · simp [hxl]
        · have hnx : ¬ x.val < 6 * P.s := by omega
          have he0 : x.val ≠ 6 * P.s := by omega
          have he1 : x.val ≠ 6 * P.s + 1 := by omega
          have he2 : x.val ≠ 6 * P.s + 2 := by omega
          simp [hnx, he0, he1, he2]
      · by_cases hytop : y.val = top - 1
        · right; omega
        · have hytop2 : y.val = top - 2 := by omega
          by_cases hx0 : x.val = 6 * P.s
          · right; omega
          · left
            simp only [B, phase1Board]
            have h1 : ¬ y.val < r := by omega
            have h2 : ¬ y.val = r := by omega
            have h3 : ¬ y.val = r + 1 := by omega
            have h4 : ¬ y.val < r + 2 + 4 * K := by omega
            have h5 : ¬ y.val < baseY pad K r := by omega
            have hnx : ¬ x.val < 6 * P.s := by omega
            simp only [h1, h2, h3, h4, h5, hy2', hnx, hx0, ↓reduceIte, ↓reduceDIte]
            by_cases hx1 : x.val = 6 * P.s + 1
            · simp [hx1]; omega
            · have hx2 : x.val = 6 * P.s + 2 := by omega
              simp [hx2]; omega)
    (fun y hy => by
      refine ⟨⟨0, by simp [B, phase1Board]⟩, ?_⟩
      have hnot : ((0 : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
      have hcell : B.cell y ⟨0, by simp [B, phase1Board]⟩ = false :=
        phase1Board_empty P pad K st r (fun _ _ _ => true) y hy ⟨0, by simp [phase1Board]⟩
      simp [Board.insert, hcell, hnot])
  rcases hclear with ⟨hgain, hcell_eq⟩
  have hgain2 : B.gain q = 2 := by omega
  refine ⟨B.settle q, ?_, rfl, rfl, ?_⟩
  · simpa [hgain2] using CanPlay.single htraj
  · intro y x
    rw [hcell_eq y x]
    by_cases hy : y.val < top - 2
    · simp only [hy, ↓reduceDIte]
      have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
      simp only [Board.insert, hnot, decide_false, Bool.or_false, B, phase1Board]
      by_cases h1 : y.val < r
      · simp [h1]
      by_cases h2 : y.val = r
      · simp [h2]
      by_cases h3 : y.val = r + 1
      · simp [h3]
      by_cases h4 : y.val < r + 2 + 4 * K
      · simp [h1, h2, h3, h4]
      by_cases h5 : y.val < baseY pad K r
      · simp [h1, h2, h3, h4, h5, show y.val < baseY pad K r + baseHeight P - 2 by omega]
      · have h6 : y.val < baseY pad K r + baseHeight P := by omega
        have hy' : y.val < baseY pad K r + baseHeight P - 2 := hy
        simp only [h1, h2, h3, h4, h5, h6, hy', ↓reduceIte]
        by_cases hx : x.val < 6 * P.s
        · simp [hx]; omega
        · simp only [hx, ↓reduceDIte]
          by_cases he0 : x.val = 6 * P.s
          · simp [he0]; omega
          · by_cases he1 : x.val = 6 * P.s + 1
            · simp [he1]; omega
            · by_cases he2 : x.val = 6 * P.s + 2
              · simp [he2]; omega
              · simp [he0, he1, he2]
    · simp only [hy, ↓reduceDIte]
      have h1 : ¬ y.val < r := by omega
      have h2 : ¬ y.val = r := by omega
      have h3 : ¬ y.val = r + 1 := by omega
      have h4 : ¬ y.val < r + 2 + 4 * K := by omega
      have hy' : ¬ y.val < baseY pad K r + baseHeight P - 2 := hy
      simp only [h1, h2, h3, h4, hy', ↓reduceIte]
      split_ifs with hy2
      · have hnot : ((x.val : ℤ), ((y.val + (top - (top - 2)) : ℕ) : ℤ)) ∉ q.cells := by
          rw [hcells_q]; simp; omega
        have hem := phase1Board_empty P pad K st r (fun _ _ _ => true)
          ⟨y.val + (top - (top - 2)), hy2⟩ (by dsimp; omega) ⟨x.val, x.isLt⟩
        simp only [Board.insert, B, hem, Bool.false_or, decide_eq_false_iff_not]
        exact hnot
      · rfl

/-- General shaft-clearing lemma: `n` vertical `.I` pieces dropped into `col` clear `4 * n`
identical rows `decide (x ≠ col)` above `base`, leaving rows `< base` unchanged and rows `≥ base` false. -/
private lemma play_shaft_I {R : Rotation} (hR : R.Admissible)
    (n : ℕ) :
    ∀ (B : Board) (base col : ℕ)
      (_hbase : 1 ≤ base)
      (hcol : col < B.width)
      (_hW : 2 * max R.radius 2 + 9 ≤ B.width)
      (hH : base + 4 * n + 5 * max R.radius 2 + 12 ≤ B.height),
      (∀ y : Fin B.height, y.val < base → ∃ x : Fin B.width, B.cell y x = false) →
      B.cell ⟨base - 1, by omega⟩ ⟨col, hcol⟩ = true →
      (∀ y : Fin B.height, base ≤ y.val → y.val < base + 4 * n →
        ∀ x : Fin B.width, B.cell y x = decide (x.val ≠ col)) →
      (∀ y : Fin B.height, base + 4 * n ≤ y.val → ∀ x : Fin B.width, B.cell y x = false) →
      ∃ (B' : Board) (hH' : B'.height = B.height) (hW' : B'.width = B.width),
        CanPlay R B (List.replicate n .I) B' (4 * n) ∧
        (∀ (y : Fin B'.height) (x : Fin B'.width),
          y.val < base → B'.cell y x = B.cell ⟨y.val, hH' ▸ y.isLt⟩ ⟨x.val, hW' ▸ x.isLt⟩) ∧
        (∀ (y : Fin B'.height) (x : Fin B'.width),
          base ≤ y.val → B'.cell y x = false) := by
  induction n with
  | zero =>
    intro B base col _ _ _ _ _ _ _ hempty
    exact ⟨B, rfl, rfl, CanPlay.nil R B, fun _ _ _ => rfl, fun y x hy => hempty y (by omega) x⟩
  | succ n ih =>
    intro B base col hbase hcol hW hH hbelow hfloor hshaft hempty
    set q : PieceState := PieceState.mk .I 1 (col, base + 2) true
    have hocc_col : ∀ y' : ℤ, (base : ℤ) ≤ y' → y' < B.height →
        B.occupied (col, y') = false := by
      intro y' hy1 hy2
      have hy0 : 0 ≤ y' ∧ y' < B.height := by omega
      have hx0 : 0 ≤ (col : ℤ) ∧ (col : ℤ) < B.width := by omega
      simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
      by_cases hlt : y'.toNat < base + 4 * (n + 1)
      · rw [hshaft ⟨y'.toNat, by omega⟩ (by dsimp; omega) hlt ⟨(col : ℤ).toNat, by omega⟩]
        simp
      · exact hempty ⟨y'.toNat, by omega⟩ (by dsimp; omega) ⟨(col : ℤ).toNat, by omega⟩
    have htraj : Trajectory R B .I q := by
      apply trajectory_of_drop_slide hR hW hH hempty
        (x_drop := col) (x_target := col) (y := (base : ℤ) + 2)
      · omega
      · intro y' hy1 hy2 c hc
        rw [cells_I_1] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        have : 2 ≤ max R.radius 2 := le_max_right _ _
        rcases hc with rfl | rfl | rfl | rfl <;> exact hocc_col _ (by omega) (by omega)
      · intro x' hx1 hx2 c hc
        have hx : x' = col := by omega
        subst hx
        rw [cells_I_1] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact hocc_col _ (by omega) (by omega)
      · intro hcl
        have hmem : ((col : ℤ), (base : ℤ) - 1) ∈
            (translate (PieceState.mk .I 1 (col, base + 2) false) 0 (-1)).cells := by
          simp only [translate]; rw [cells_I_1]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          right; right; right; ext <;> ring
        have hf := hcl _ hmem
        have hy0 : 0 ≤ (base : ℤ) - 1 ∧ (base : ℤ) - 1 < B.height := by omega
        have hx0 : 0 ≤ (col : ℤ) ∧ (col : ℤ) < B.width := by omega
        simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte] at hf
        have hyt : ((base : ℤ) - 1).toNat = base - 1 := by omega
        have hxt : (col : ℤ).toNat = col := by omega
        have hfin1 : (⟨((base : ℤ) - 1).toNat, by omega⟩ : Fin B.height) = ⟨base - 1, by omega⟩ := by
          ext; exact hyt
        have hfin2 : (⟨(col : ℤ).toNat, by omega⟩ : Fin B.width) = ⟨col, hcol⟩ := by
          ext; exact hxt
        rw [hfin1, hfin2, hfloor] at hf
        simp at hf
    have hcells_q : q.cells = [((col : ℤ), (base : ℤ) + 3), ((col : ℤ), (base : ℤ) + 2),
        ((col : ℤ), (base : ℤ) + 1), ((col : ℤ), (base : ℤ))] := by
      dsimp only [q]; rw [cells_I_1]; ring_nf
    have hclear := settle_clear_band B q base (base + 4) (by omega) (by omega)
      (fun y hy => by
        obtain ⟨x, hx⟩ := hbelow y hy
        refine ⟨x, ?_⟩
        have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
        simp [Board.insert, hx, hnot])
      (fun y hy1 hy2 x => by
        simp only [Board.insert, hcells_q, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
          Bool.or_eq_true, decide_eq_true_eq]
        by_cases hx : x.val = col
        · right; omega
        · left
          rw [hshaft y hy1 (by omega) x]
          simp [hx])
      (fun y hy => by
        refine ⟨⟨col, hcol⟩, ?_⟩
        have hnot : ((col : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
        by_cases hlt : y.val < base + 4 * (n + 1)
        · have hc := hshaft y (by omega) hlt ⟨col, hcol⟩
          simp [Board.insert, hc, hnot]
        · have hc := hempty y (by omega) ⟨col, hcol⟩
          simp [Board.insert, hc, hnot])
    rcases hclear with ⟨hgain, hcell_eq⟩
    have hgain4 : B.gain q = 4 := by omega
    have hstep : CanPlay R B [.I] (B.settle q) 4 := by
      simpa [hgain4] using CanPlay.single htraj
    have hsub_eq : base + 4 - base = 4 := by omega
    have hsettle_below : ∀ (y : Fin (B.settle q).height) (x : Fin (B.settle q).width),
        y.val < base → (B.settle q).cell y x = B.cell ⟨y.val, y.isLt⟩ ⟨x.val, x.isLt⟩ := by
      intro y x hy
      rw [hcell_eq y x]
      simp only [hy, ↓reduceDIte]
      have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
      simp [Board.insert, hnot]
    have hsettle_shaft : ∀ y : Fin (B.settle q).height, base ≤ y.val → y.val < base + 4 * n →
        ∀ x : Fin (B.settle q).width, (B.settle q).cell y x = decide (x.val ≠ col) := by
      intro y hy1 hy2 x
      rw [hcell_eq y x]
      have h1 : ¬ y.val < base := by omega
      have h2 : y.val + (base + 4 - base) < B.height := by omega
      simp only [h1, h2, ↓reduceDIte]
      have hnot : ((x.val : ℤ), ((y.val + (base + 4 - base) : ℕ) : ℤ)) ∉ q.cells := by
        rw [hcells_q]; simp; omega
      simp only [Board.insert, hnot, decide_false, Bool.or_false]
      exact hshaft ⟨y.val + (base + 4 - base), h2⟩ (by dsimp; omega) (by dsimp; omega) ⟨x.val, x.isLt⟩
    have hsettle_empty : ∀ y : Fin (B.settle q).height, base + 4 * n ≤ y.val →
        ∀ x : Fin (B.settle q).width, (B.settle q).cell y x = false := by
      intro y hy x
      rw [hcell_eq y x]
      have h1 : ¬ y.val < base := by omega
      simp only [h1, ↓reduceDIte]
      split_ifs with h2
      · have hnot : ((x.val : ℤ), ((y.val + (base + 4 - base) : ℕ) : ℤ)) ∉ q.cells := by
          rw [hcells_q]; simp; omega
        simp only [Board.insert, hnot, decide_false, Bool.or_false]
        exact hempty ⟨y.val + (base + 4 - base), h2⟩ (by dsimp; omega) ⟨x.val, x.isLt⟩
      · rfl
    obtain ⟨B', hH', hW', hplay', hB'below, hB'empty⟩ := ih (B.settle q) base col hbase hcol hW
      (show base + 4 * n + 5 * max R.radius 2 + 12 ≤ B.height by omega)
      (fun y hy => by
        obtain ⟨x, hx⟩ := hbelow ⟨y.val, y.isLt⟩ hy
        exact ⟨⟨x.val, x.isLt⟩, by rw [hsettle_below y ⟨x.val, x.isLt⟩ hy]; exact hx⟩)
      (by
        rw [hsettle_below ⟨base - 1, show base - 1 < B.height by omega⟩ ⟨col, hcol⟩ (by dsimp; omega)]
        exact hfloor)
      hsettle_shaft hsettle_empty
    refine ⟨B', hH', hW', ?_, ?_, hB'empty⟩
    · have happ := CanPlay.append hstep hplay'
      rw [List.replicate_succ]
      simpa [Nat.mul_succ, Nat.add_comm] using happ
    · intro y x hy
      rw [hB'below y x hy, hsettle_below ⟨y.val, hH' ▸ y.isLt⟩ ⟨x.val, hW' ▸ x.isLt⟩ hy]

/-- Phase 3b: drop `.RG` (`o = 1`) into the second lock at rows `r, r + 1`, clearing both rows. -/
private lemma play_phase3b {R : Rotation} (hR : R.Admissible)
    (B : Board) (r S : ℕ)
    (hW_eq : B.width = 6 * S + 3)
    (hW : 2 * max R.radius 2 + 9 ≤ B.width)
    (hH : r + 2 + 5 * max R.radius 2 + 12 ≤ B.height)
    (hcell : ∀ (y : Fin B.height) (x : Fin B.width),
      B.cell y x =
        if y.val < r then decide (x.val = 0)
        else if y.val = r then decide (x.val ≠ 6 * S)
        else if y.val = r + 1 then decide (x.val < 6 * S)
        else false) :
    ∃ B' : Board,
      CanPlay R B [.RG] B' 2 ∧
      B'.height = B.height ∧ B'.width = B.width ∧
      ∀ (y : Fin B'.height) (x : Fin B'.width),
        B'.cell y x = if y.val < r then decide (x.val = 0) else false := by
  have hempty : ∀ y : Fin B.height, r + 2 ≤ y.val → ∀ x : Fin B.width, B.cell y x = false := by
    intro y hy x
    rw [hcell y x]
    have h1 : ¬ y.val < r := by omega
    have h2 : ¬ y.val = r := by omega
    have h3 : ¬ y.val = r + 1 := by omega
    simp [h1, h2, h3]
  set q : PieceState := PieceState.mk .RG 1 (6 * (S : ℤ) + 1, (r : ℤ) + 1) true
  have hocc_lock : ∀ (cx cy : ℤ),
      (cx = 6 * (S : ℤ) ∧ cy = (r : ℤ)) ∨
      (6 * (S : ℤ) ≤ cx ∧ cx ≤ 6 * (S : ℤ) + 2 ∧ (r : ℤ) + 1 ≤ cy ∧ cy ≤ (r : ℤ) + 6) →
      B.occupied (cx, cy) = false := by
    intro cx cy hc
    have : 2 ≤ max R.radius 2 := le_max_right _ _
    have hy0 : 0 ≤ cy ∧ cy < B.height := by omega
    have hx0 : 0 ≤ cx ∧ cx < B.width := by omega
    simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte]
    rw [hcell ⟨cy.toNat, by omega⟩ ⟨cx.toNat, by omega⟩]
    by_cases h1 : cy.toNat = r
    · simp [h1]; omega
    · by_cases h2 : cy.toNat = r + 1
      · simp [h2]; omega
      · have hn0 : ¬ cy.toNat < r := by omega
        simp [hn0, h1, h2]
  have htraj : Trajectory R B .RG q := by
    apply trajectory_of_drop_slide hR hW hH hempty
      (x_drop := 6 * (S : ℤ) + 1) (x_target := 6 * (S : ℤ) + 1) (y := (r : ℤ) + 1)
    · omega
    · intro y' hy1 hy2 c hc
      rw [cells_RG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · by_cases hy1' : y' = (r : ℤ) + 1
        · exact hocc_lock _ _ (Or.inl ⟨by omega, by omega⟩)
        · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
    · intro x' hx1 hx2 c hc
      have hx : x' = 6 * (S : ℤ) + 1 := by omega
      subst hx
      rw [cells_RG_1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact hocc_lock _ _ (Or.inl ⟨by omega, by omega⟩)
    · intro hcl
      have hmem : (6 * (S : ℤ) + 1, (r : ℤ)) ∈
          (translate (PieceState.mk .RG 1 (6 * (S : ℤ) + 1, (r : ℤ) + 1) false) 0 (-1)).cells := by
        simp only [translate]; rw [cells_RG_1]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; left; ext <;> ring
      have hf := hcl _ hmem
      have hy0 : 0 ≤ (r : ℤ) ∧ (r : ℤ) < B.height := by omega
      have hx0 : 0 ≤ 6 * (S : ℤ) + 1 ∧ 6 * (S : ℤ) + 1 < B.width := by omega
      simp only [Board.occupied, hy0, hx0, and_self, ↓reduceDIte] at hf
      rw [hcell ⟨(r : ℤ).toNat, by omega⟩ ⟨(6 * (S : ℤ) + 1).toNat, by omega⟩] at hf
      have hxt : (6 * (S : ℤ) + 1).toNat = 6 * S + 1 := by omega
      simp [hxt] at hf
  have hcells_q : q.cells = [(6 * (S : ℤ) + 2, (r : ℤ) + 1), (6 * (S : ℤ) + 1, (r : ℤ) + 1),
      (6 * (S : ℤ), (r : ℤ) + 1), (6 * (S : ℤ), (r : ℤ))] := by
    dsimp only [q]; rw [cells_RG_1]; ring_nf
  have hclear := settle_clear_band B q r (r + 2) (by omega) (by omega)
    (fun y hy => by
      refine ⟨⟨1, by omega⟩, ?_⟩
      have hnot : ((1 : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
      simp [Board.insert, hcell y ⟨1, by omega⟩, hy, hnot])
    (fun y hy1 hy2 x => by
      simp only [Board.insert, hcells_q, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
        Bool.or_eq_true, decide_eq_true_eq]
      by_cases hyr : y.val = r
      · by_cases hx : x.val = 6 * S
        · right; omega
        · left; rw [hcell y x]; simp [hyr, hx]
      · have hyr1 : y.val = r + 1 := by omega
        by_cases hx : x.val < 6 * S
        · left; rw [hcell y x]; simp [hyr1, hx]
        · right; omega)
    (fun y hy => by
      refine ⟨⟨0, by omega⟩, ?_⟩
      have hnot : ((0 : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
      simp [Board.insert, hempty y hy ⟨0, by omega⟩, hnot])
  rcases hclear with ⟨hgain, hcell_eq⟩
  have hgain2 : B.gain q = 2 := by omega
  refine ⟨B.settle q, by simpa [hgain2] using CanPlay.single htraj, rfl, rfl, ?_⟩
  intro y x
  rw [hcell_eq y x]
  by_cases hy : y.val < r
  · simp only [hy, ↓reduceDIte, ↓reduceIte]
    have hnot : ((x.val : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
    simp [Board.insert, hcell ⟨y.val, y.isLt⟩ ⟨x.val, x.isLt⟩, hy, hnot]
  · simp only [hy, ↓reduceDIte, ↓reduceIte]
    by_cases hy2 : y.val + (r + 2 - r) < B.height
    · simp only [hy2, ↓reduceDIte]
      have hnot : ((x.val : ℤ), ((y.val + (r + 2 - r) : ℕ) : ℤ)) ∉ q.cells := by
        rw [hcells_q]; simp; omega
      simp only [Board.insert, hempty ⟨y.val + (r + 2 - r), hy2⟩ (by dsimp; omega) ⟨x.val, x.isLt⟩,
        Bool.false_or, decide_eq_false_iff_not]
      exact hnot
    · simp only [hy2, ↓reduceDIte]

/-- Phase 4 (single pair of reservoir rows): `c` `.Sq` pieces clear the bottom 2 reservoir rows. -/
private lemma play_reservoir_pair {R : Rotation} (hR : R.Admissible)
    (B : Board) (k c : ℕ) (hc : 1 ≤ c)
    (hW_eq : B.width = 2 * c + 1)
    (hW : 2 * max R.radius 2 + 9 ≤ B.width)
    (hH : 2 * (k + 1) + 5 * max R.radius 2 + 12 ≤ B.height)
    (hcell : ∀ (y : Fin B.height) (x : Fin B.width),
      B.cell y x = if y.val < 2 * (k + 1) then decide (x.val = 0) else false) :
    ∃ B' : Board,
      CanPlay R B (List.replicate c .Sq) B' 2 ∧
      B'.height = B.height ∧ B'.width = B.width ∧
      ∀ (y : Fin B'.height) (x : Fin B'.width),
        B'.cell y x = if y.val < 2 * k then decide (x.val = 0) else false := by
  -- First place i ≤ c - 1 .Sq pieces in rows 0, 1 at x = 1, 3, ..., 2*i - 1 (0 rows cleared)
  have hfill : ∀ i ≤ c - 1,
      ∃ Bi : Board,
        CanPlay R B (List.replicate i .Sq) Bi 0 ∧
        Bi.height = B.height ∧ Bi.width = B.width ∧
        ∀ (y : Fin Bi.height) (x : Fin Bi.width),
          Bi.cell y x =
            if y.val < 2 then decide (x.val < 2 * i + 1)
            else if y.val < 2 * (k + 1) then decide (x.val = 0)
            else false := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨B, CanPlay.nil R B, rfl, rfl, fun y x => ?_⟩
      rw [hcell y x]
      by_cases h2 : y.val < 2
      · simp [h2, show y.val < 2 * (k + 1) by omega]
      · simp [h2]
    | succ i ih =>
      obtain ⟨Bi, hpi, hHi, hWi, hci⟩ := ih (by omega)
      have hempty_i : ∀ y : Fin Bi.height, 2 * (k + 1) ≤ y.val → ∀ x : Fin Bi.width, Bi.cell y x = false := by
        intro y hy x
        rw [hci y x]
        have h1 : ¬ y.val < 2 := by omega
        have h2 : ¬ y.val < 2 * (k + 1) := by omega
        simp [h1, h2]
      set q : PieceState := PieceState.mk .Sq 0 (2 * (i : ℤ) + 1, 1) true
      have hocc_f : ∀ (cx cy : ℤ), (2 * (i : ℤ) + 1 ≤ cx ∧ cx ≤ 2 * (i : ℤ) + 2) →
          0 ≤ cy → cy < Bi.height → Bi.occupied (cx, cy) = false := by
        intro cx cy hcx hcy0 hcyH
        have hx0 : 0 ≤ cx ∧ cx < Bi.width := by omega
        simp only [Board.occupied, hcy0, hcyH, hx0, and_self, ↓reduceDIte]
        rw [hci ⟨cy.toNat, by omega⟩ ⟨cx.toNat, by omega⟩]
        by_cases h2 : cy.toNat < 2
        · simp [h2]; omega
        · by_cases hk : cy.toNat < 2 * (k + 1)
          · simp [h2, hk]; omega
          · simp [h2, hk]
      have htraj : Trajectory R Bi .Sq q := by
        apply trajectory_of_drop_slide hR (by omega) (by omega) hempty_i
          (x_drop := 2 * (i : ℤ) + 1) (x_target := 2 * (i : ℤ) + 1) (y := 1)
        · omega
        · intro y' hy1 hy2 c hc
          rw [cells_Sq] at hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          have : 2 ≤ max R.radius 2 := le_max_right _ _
          rcases hc with rfl | rfl | rfl | rfl <;> exact hocc_f _ _ (by omega) (by omega) (by omega)
        · intro x' hx1 hx2 c hc
          have hx : x' = 2 * (i : ℤ) + 1 := by omega
          subst hx
          rw [cells_Sq] at hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl <;> exact hocc_f _ _ (by omega) (by omega) (by omega)
        · intro hcl
          have hmem : (2 * (i : ℤ) + 1, -1) ∈
              (translate (PieceState.mk .Sq 0 (2 * (i : ℤ) + 1, 1) false) 0 (-1)).cells := by
            simp only [translate]; rw [cells_Sq]
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            right; right; left; ext <;> ring
          have hf := hcl _ hmem
          simp [Board.occupied] at hf
      have hcells_q : q.cells = [(2 * (i : ℤ) + 1, 1), (2 * (i : ℤ) + 2, 1),
          (2 * (i : ℤ) + 1, 0), (2 * (i : ℤ) + 2, 0)] := by
        dsimp only [q]; rw [cells_Sq]; ring_nf
      have hnf : ∀ y : Fin Bi.height, ∃ x : Fin Bi.width, (Bi.insert q).cell y x = false := by
        intro y
        refine ⟨⟨2 * c, by omega⟩, ?_⟩
        have hnot : ((2 * c : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
        have hc0 : Bi.cell y ⟨2 * c, by omega⟩ = false := by
          rw [hci y ⟨2 * c, by omega⟩]
          by_cases h2 : y.val < 2
          · simp [h2]; omega
          · by_cases hk : y.val < 2 * (k + 1)
            · simp [h2, hk]; omega
            · simp [h2, hk]
        simp only [Board.insert, hc0, Bool.false_or, decide_eq_false_iff_not]
        simpa using hnot
      obtain ⟨hgain, hsettle⟩ := settle_eq_insert_of_not_full Bi q hnf
      have hstep : CanPlay R Bi [.Sq] (Bi.insert q) 0 := by
        have hp := CanPlay.single htraj
        rwa [hgain, hsettle] at hp
      refine ⟨Bi.insert q, ?_, hHi, hWi, ?_⟩
      · rw [List.replicate_succ']
        simpa using CanPlay.append hpi hstep
      · intro y x
        simp only [Board.insert, hci y x, hcells_q, List.mem_cons, List.not_mem_nil, or_false,
          Prod.mk.injEq]
        by_cases h2 : y.val < 2
        · simp only [h2, ↓reduceIte]
          by_cases hx : x.val < 2 * (i + 1) + 1
          · simp only [hx, decide_true, Bool.or_eq_true, decide_eq_true_eq]; omega
          · simp only [hx, decide_false, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
        · simp only [h2, ↓reduceIte]
          have hnot : ¬ (((x.val : ℤ) = 2 * (i : ℤ) + 1 ∧ (y.val : ℤ) = 1) ∨
              ((x.val : ℤ) = 2 * (i : ℤ) + 2 ∧ (y.val : ℤ) = 1) ∨
              ((x.val : ℤ) = 2 * (i : ℤ) + 1 ∧ (y.val : ℤ) = 0) ∨
              ((x.val : ℤ) = 2 * (i : ℤ) + 2 ∧ (y.val : ℤ) = 0)) := by omega
          simp only [hnot, decide_false, Bool.or_false]
  -- Now place the final c-th .Sq piece at x = 2 * (c - 1) + 1 = 2 * c - 1, clearing rows 0 and 1!
  obtain ⟨Bm, hpm, hHm, hWm, hcm⟩ := hfill (c - 1) le_rfl
  have hempty_m : ∀ y : Fin Bm.height, 2 * (k + 1) ≤ y.val → ∀ x : Fin Bm.width, Bm.cell y x = false := by
    intro y hy x
    rw [hcm y x]
    have h1 : ¬ y.val < 2 := by omega
    have h2 : ¬ y.val < 2 * (k + 1) := by omega
    simp [h1, h2]
  set q : PieceState := PieceState.mk .Sq 0 (2 * (c : ℤ) - 1, 1) true
  have hocc_f : ∀ (cx cy : ℤ), (2 * (c : ℤ) - 1 ≤ cx ∧ cx ≤ 2 * (c : ℤ)) →
      0 ≤ cy → cy < Bm.height → Bm.occupied (cx, cy) = false := by
    intro cx cy hcx hcy0 hcyH
    have hx0 : 0 ≤ cx ∧ cx < Bm.width := by omega
    simp only [Board.occupied, hcy0, hcyH, hx0, and_self, ↓reduceDIte]
    rw [hcm ⟨cy.toNat, by omega⟩ ⟨cx.toNat, by omega⟩]
    by_cases h2 : cy.toNat < 2
    · simp [h2]; omega
    · by_cases hk : cy.toNat < 2 * (k + 1)
      · simp [h2, hk]; omega
      · simp [h2, hk]
  have htraj : Trajectory R Bm .Sq q := by
    apply trajectory_of_drop_slide hR (by omega) (by omega) hempty_m
      (x_drop := 2 * (c : ℤ) - 1) (x_target := 2 * (c : ℤ) - 1) (y := 1)
    · omega
    · intro y' hy1 hy2 c' hc'
      rw [cells_Sq] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      have : 2 ≤ max R.radius 2 := le_max_right _ _
      rcases hc' with rfl | rfl | rfl | rfl <;> exact hocc_f _ _ (by omega) (by omega) (by omega)
    · intro x' hx1 hx2 c' hc'
      have hx : x' = 2 * (c : ℤ) - 1 := by omega
      subst hx
      rw [cells_Sq] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl <;> exact hocc_f _ _ (by omega) (by omega) (by omega)
    · intro hcl
      have hmem : (2 * (c : ℤ) - 1, -1) ∈
          (translate (PieceState.mk .Sq 0 (2 * (c : ℤ) - 1, 1) false) 0 (-1)).cells := by
        simp only [translate]; rw [cells_Sq]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right; left; ext <;> ring
      have hf := hcl _ hmem
      simp [Board.occupied] at hf
  have hcells_q : q.cells = [(2 * (c : ℤ) - 1, 1), (2 * (c : ℤ), 1),
      (2 * (c : ℤ) - 1, 0), (2 * (c : ℤ), 0)] := by
    dsimp only [q]; rw [cells_Sq]; ring_nf
  have hclear := settle_clear_band Bm q 0 2 (by omega) (by omega)
    (fun y hy => by omega)
    (fun y _ hy2 x => by
      simp only [Board.insert, hcm y x, hy2, ↓reduceIte, hcells_q, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq, Bool.or_eq_true, decide_eq_true_eq]
      omega)
    (fun y hy => by
      refine ⟨⟨1, by omega⟩, ?_⟩
      have hnot : ((1 : ℤ), (y.val : ℤ)) ∉ q.cells := by rw [hcells_q]; simp; omega
      have hc0 : Bm.cell y ⟨1, by omega⟩ = false := by
        rw [hcm y ⟨1, by omega⟩]
        have h1 : ¬ y.val < 2 := by omega
        by_cases hk : y.val < 2 * (k + 1)
        · simp [h1, hk]
        · simp [h1, hk]
      simp [Board.insert, hc0, hnot])
  rcases hclear with ⟨hgain, hcell_eq⟩
  have hgain2 : Bm.gain q = 2 := by omega
  have hstep : CanPlay R Bm [.Sq] (Bm.settle q) 2 := by
    simpa [hgain2] using CanPlay.single htraj
  refine ⟨Bm.settle q, ?_, hHm, hWm, ?_⟩
  · have hrep : List.replicate c Piece.Sq = List.replicate (c - 1) Piece.Sq ++ [Piece.Sq] := by
      have hc_eq : c = (c - 1) + 1 := by omega
      conv_lhs => rw [hc_eq, List.replicate_succ']
    rw [hrep]
    simpa using CanPlay.append hpm hstep
  · intro y x
    rw [hcell_eq y x]
    have hnot0 : ¬ y.val < 0 := by omega
    simp only [hnot0, ↓reduceDIte]
    by_cases hy2 : y.val + (2 - 0) < Bm.height
    · simp only [hy2, ↓reduceDIte]
      have hnot : ((x.val : ℤ), ((y.val + (2 - 0) : ℕ) : ℤ)) ∉ q.cells := by
        rw [hcells_q]; simp; omega
      simp only [Board.insert, hnot, decide_false, Bool.or_false]
      rw [hcm ⟨y.val + (2 - 0), hy2⟩ ⟨x.val, x.isLt⟩]
      have h1 : ¬ y.val + (2 - 0) < 2 := by omega
      by_cases hk : y.val < 2 * k
      · simp [h1, hk, show y.val + (2 - 0) < 2 * (k + 1) by omega]
      · simp [h1, hk, show ¬ y.val + (2 - 0) < 2 * (k + 1) by omega]
    · simp only [hy2, ↓reduceDIte]
      have hge : ¬ y.val < 2 * k := by omega
      simp [hge]

/-- Phase 4 (all `m` pairs of reservoir rows): `m * c` `.Sq` pieces clear `2 * m` rows. -/
private lemma play_phase4 {R : Rotation} (hR : R.Admissible)
    (m c : ℕ) (hc : 1 ≤ c) :
    ∀ B : Board,
      B.width = 2 * c + 1 →
      2 * max R.radius 2 + 9 ≤ B.width →
      2 * m + 5 * max R.radius 2 + 12 ≤ B.height →
      (∀ (y : Fin B.height) (x : Fin B.width),
        B.cell y x = if y.val < 2 * m then decide (x.val = 0) else false) →
      ∃ B' : Board, CanPlay R B (List.replicate (m * c) .Sq) B' (2 * m) := by
  induction m with
  | zero =>
    intro B _ _ _ _
    exact ⟨B, by simpa using CanPlay.nil R B⟩
  | succ m ih =>
    intro B hW_eq hW hH hcell
    obtain ⟨B1, hp1, hH1, hW1, hcell1⟩ := play_reservoir_pair hR B m c hc hW_eq hW hH hcell
    obtain ⟨B2, hp2⟩ := ih B1 (by omega) (by omega) (by omega) hcell1
    refine ⟨B2, ?_⟩
    have hrep : List.replicate ((m + 1) * c) Piece.Sq =
        List.replicate c Piece.Sq ++ List.replicate (m * c) Piece.Sq := by
      rw [← List.replicate_add]
      congr 1; ring
    rw [hrep]
    simpa [Nat.mul_succ, Nat.add_comm] using CanPlay.append hp1 hp2

/-! ### Main Completeness Theorem -/

theorem paddedReservoir_completeness
    (R : Rotation) (hR : R.Admissible)
    (P : ThreePartition) (_hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hyes : P.HasSolution)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : 1 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st)
    (hr : Even r) :
    ∃ w, r ≤ w ∧ Attainable R (paddedReservoirGame P pad K st r) w := by
  -- Phase 1a: fill all P.s buckets (0 rows cleared)
  have hp1a := play_phase1a hR P hN hs hyes pad K st r hpad hst
  -- Phase 1b: clear first lock cap (2 rows cleared)
  obtain ⟨B1, hp1b, hH1, hW1, hcell1⟩ := play_phase1b hR P hs pad K st r hpad hst
  -- Phase 1c + 2: clear (H - 2) + 12 * pad shaft rows in col 6 * P.s + 2
  set n1 : ℕ := 3 * P.target / 2 + 5 + 3 * pad
  have hT_even : Even P.target := hN.2.1
  have h4n1 : 4 * n1 = 12 * pad + baseHeight P - 2 := by
    rcases hT_even with ⟨t, ht⟩
    unfold baseHeight
    omega
  have hbase_sum : r + 2 + 4 * K + 4 * n1 = baseY pad K r + baseHeight P - 2 := by
    unfold baseY; omega
  have hW_ge : 2 * max R.radius 2 + 9 ≤ B1.width := by omega
  have hH_1c : (r + 2 + 4 * K) + 4 * n1 + 5 * max R.radius 2 + 12 ≤ B1.height := by
    rw [hH1]; unfold baseY; simp only [baseBoard]; omega
  obtain ⟨B2, hH2, hW2, hp2, hB2below, hB2empty⟩ :=
    play_shaft_I hR n1 B1 (r + 2 + 4 * K) (6 * P.s + 2) (by omega) (by omega) hW_ge hH_1c
      (fun y hy => by
        by_cases h1 : y.val < r
        · refine ⟨⟨1, by omega⟩, ?_⟩; rw [hcell1]; simp [h1]
        · by_cases h2 : y.val = r
          · refine ⟨⟨6 * (P.s + pad), by omega⟩, ?_⟩; rw [hcell1]; simp [h2]
          · by_cases h3 : y.val = r + 1
            · refine ⟨⟨6 * (P.s + pad), by omega⟩, ?_⟩; rw [hcell1]; simp [h3]
            · refine ⟨⟨6 * (P.s + pad) - 1, by omega⟩, ?_⟩; rw [hcell1]; simp [h1, h2, h3, hy])
      (by
        rw [hcell1]
        have h1 : ¬ (r + 2 + 4 * K - 1) < r := by omega
        have h2 : ¬ (r + 2 + 4 * K - 1) = r := by omega
        have h3 : ¬ (r + 2 + 4 * K - 1) = r + 1 := by omega
        have h4 : (r + 2 + 4 * K - 1) < r + 2 + 4 * K := by omega
        simp only [h1, h2, h3, h4, ↓reduceIte, decide_eq_true_eq]
        omega)
      (fun y hy1 hy2 x => by
        rw [hcell1]
        have h1 : ¬ y.val < r := by omega
        have h2 : ¬ y.val = r := by omega
        have h3 : ¬ y.val = r + 1 := by omega
        have h4 : ¬ y.val < r + 2 + 4 * K := by omega
        have h5 : y.val < baseY pad K r + baseHeight P - 2 := by omega
        simp [h1, h2, h3, h4, h5])
      (fun y hy x => by
        rw [hcell1]
        have h1 : ¬ y.val < r := by omega
        have h2 : ¬ y.val = r := by omega
        have h3 : ¬ y.val = r + 1 := by omega
        have h4 : ¬ y.val < r + 2 + 4 * K := by omega
        have h5 : ¬ y.val < baseY pad K r + baseHeight P - 2 := by omega
        simp [h1, h2, h3, h4, h5])
  -- Phase 3a: clear 4 * K chimney rows in col 6 * (P.s + pad) - 1
  obtain ⟨B3, hH3, hW3, hp3a, hB3below, hB3empty⟩ :=
    play_shaft_I hR K B2 (r + 2) (6 * (P.s + pad) - 1) (by omega) (by omega) (by omega) (by omega)
      (fun y hy => by
        by_cases h1 : y.val < r
        · refine ⟨⟨1, by omega⟩, ?_⟩
          rw [hB2below y ⟨1, by omega⟩ (by omega), hcell1]; simp [h1]
        · by_cases h2 : y.val = r
          · refine ⟨⟨6 * (P.s + pad), by omega⟩, ?_⟩
            rw [hB2below y ⟨6 * (P.s + pad), by omega⟩ (by omega), hcell1]; simp [h2]
          · have h3 : y.val = r + 1 := by omega
            refine ⟨⟨6 * (P.s + pad), by omega⟩, ?_⟩
            rw [hB2below y ⟨6 * (P.s + pad), by omega⟩ (by omega), hcell1]; simp [h3])
      (by
        rw [hB2below ⟨r + 2 - 1, by omega⟩ ⟨6 * (P.s + pad) - 1, by omega⟩ (by dsimp; omega), hcell1]
        have h3 : r + 2 - 1 = r + 1 := by omega
        simp [h3]; omega)
      (fun y hy1 hy2 x => by
        rw [hB2below y x (by omega), hcell1]
        have h1 : ¬ y.val < r := by omega
        have h2 : ¬ y.val = r := by omega
        have h3 : ¬ y.val = r + 1 := by omega
        simp [h1, h2, h3, hy2])
      (fun y hy x => hB2empty y x hy)
  -- Phase 3b: clear second lock (rows r and r + 1) with [.RG]
  have hcell3 : ∀ (y : Fin B3.height) (x : Fin B3.width),
      B3.cell y x =
        if y.val < r then decide (x.val = 0)
        else if y.val = r then decide (x.val ≠ 6 * (P.s + pad))
        else if y.val = r + 1 then decide (x.val < 6 * (P.s + pad))
        else false := by
    intro y x
    by_cases hy : y.val < r + 2
    · rw [hB3below y x hy, hB2below ⟨y.val, by omega⟩ ⟨x.val, by omega⟩ (by dsimp; omega), hcell1]
      by_cases h1 : y.val < r
      · simp [h1]
      by_cases h2 : y.val = r
      · simp [h2]
      have h3 : y.val = r + 1 := by omega
      simp [h3]
    · rw [hB3empty y x (by omega)]
      have h1 : ¬ y.val < r := by omega
      have h2 : ¬ y.val = r := by omega
      have h3 : ¬ y.val = r + 1 := by omega
      simp [h1, h2, h3]
  obtain ⟨B4, hp3b, hH4, hW4, hcell4⟩ :=
    play_phase3b hR B3 r (P.s + pad) (by omega) (by omega) (by omega) hcell3
  -- Phase 4: clear all r = 2 * m reservoir rows with .Sq pieces
  rcases hr with ⟨m, rfl⟩
  have hrm : m + m = 2 * m := by ring
  set c : ℕ := 3 * (P.s + pad) + 1
  obtain ⟨B5, hp4⟩ := play_phase4 hR m c (by omega) B4 (by omega) (by omega) (by omega)
    (fun y x => by rw [hcell4 y x, hrm])
  -- Chain all phases together
  have htotal :=
    CanPlay.append
      (CanPlay.append
        (CanPlay.append
          (CanPlay.append
            (CanPlay.append hp1a hp1b)
            hp2)
          hp3a)
        hp3b)
      hp4
  have hpieces_eq :
      numberPieces P ++ List.replicate P.s .I ++ [.RG] ++ List.replicate n1 .I ++
        List.replicate K .I ++ [.RG] ++ List.replicate (m * c) .Sq =
      (paddedReservoirGame P pad K st (m + m)).pieces := by
    simp only [paddedReservoirGame, basePieces, n1]
    have hrep : List.replicate (3 * P.target / 2 + 5 + 3 * pad) Piece.I =
        List.replicate (3 * P.target / 2 + 5) Piece.I ++ List.replicate (3 * pad) Piece.I :=
      List.replicate_add _ _ _
    have hsq : m * c = (m + m) * (6 * (P.s + pad) + 2) / 4 := by
      have : (m + m) * (6 * (P.s + pad) + 2) = 4 * (m * c) := by dsimp only [c]; ring
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    rw [hrep, hsq]
    simp only [List.append_assoc]
  rw [hpieces_eq] at htotal
  exact ⟨0 + 2 + 4 * n1 + 4 * K + 2 + 2 * m, by omega, htotal.toAttainable⟩

end TetrisHard.Rows.Padded

theorem solution
    (R : TetrisHard.Rows.Rotation) (hR : R.Admissible)
    (P : TetrisHard.Rows.ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hyes : P.HasSolution)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : 1 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st)
    (hr : Even r) :
    ∃ w, r ≤ w ∧ TetrisHard.Rows.Attainable R (TetrisHard.Rows.Padded.paddedReservoirGame P pad K st r) w :=
  TetrisHard.Rows.Padded.paddedReservoir_completeness R hR P hP hN hs hyes pad K st r hpad hK hst hr
