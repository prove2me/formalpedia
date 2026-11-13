-- Prove2me | solution 1 for PlanarMetricElections.Peer.empty_center
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:42.673512+00:00
-- url     : https://prove2.me/submissions/e70ae524-144f-4e7b-9bfc-9ff136b7ea10

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid
import Definitions.Def_PlanarMetricElections_Peer_ExtremePoints
import Definitions.Def_PlanarMetricElections_Peer_RectangularNet

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev
open PlanarMetricElections.Peer

/-! ## Mass -/

theorem mass_nonneg (V : Finset Plane) (X : Set Plane) : 0 ≤ mass V X := by
  unfold mass; positivity

theorem mass_le_card (V : Finset Plane) {X Y : Set Plane} (h : ∀ v ∈ V, v ∈ X → v ∈ Y) :
    mass V X ≤ mass V Y := by
  unfold mass
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun v hv => by
    simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, h v hv.1 hv.2⟩)

theorem mass_mono (V : Finset Plane) {X Y : Set Plane} (h : X ⊆ Y) : mass V X ≤ mass V Y :=
  mass_le_card V (fun _ _ hv => h hv)

theorem mass_union (V : Finset Plane) {X Y : Set Plane} (h : Disjoint X Y) :
    mass V (X ∪ Y) = mass V X + mass V Y := by
  unfold mass
  rw [← add_div]
  congr 1
  have : V.filter (fun v => v ∈ X ∪ Y) = V.filter (fun v => v ∈ X) ∪ V.filter (fun v => v ∈ Y) := by
    ext v; simp [Finset.mem_filter, Set.mem_union]; tauto
  have hd : Disjoint (V.filter (fun v => v ∈ X)) (V.filter (fun v => v ∈ Y)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact Set.disjoint_left.mp h h1.2 h2.2
  have e := Finset.card_union_of_disjoint hd
  rw [← this] at e
  have e2 := congrArg (Nat.cast : ℕ → ℝ) e
  push_cast at e2
  convert e2 using 2
  all_goals first | rfl | congr

/-- no voter of `V` lies in `X` -/
theorem mass_eq_zero (V : Finset Plane) {X : Set Plane} (h : ∀ v ∈ V, v ∉ X) : mass V X = 0 := by
  unfold mass
  have : V.filter (fun v => v ∈ X) = ∅ := by
    ext v; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    exact fun hv => h v hv.1 hv.2
  simp [this]

theorem mass_empty (V : Finset Plane) : mass V (∅ : Set Plane) = 0 :=
  mass_eq_zero V (fun _ _ => by simp)

/-- masses of finsets (as sets) -/
theorem mass_finset_union (V : Finset Plane) {X Y : Finset Plane} (h : Disjoint X Y) :
    mass V (↑(X ∪ Y) : Set Plane) = mass V (↑X : Set Plane) + mass V (↑Y : Set Plane) := by
  rw [Finset.coe_union]
  exact mass_union V (Finset.disjoint_coe.mpr h)

/-! ## Rectangles and nets -/

theorem isStrongRectNet_of_le {V Q : Finset Plane} (hQ : Q ⊆ V) (hc : Q.card ≤ 3)
    (h : ∀ R : Set Plane, IsRectangle R → Disjoint R (↑Q : Set Plane) → mass V R ≤ 1 / 2) :
    IsStrongRectNet V Q 3 (1 / 2) := by
  refine ⟨hQ, hc, fun R hR hε => ?_⟩
  by_contra hne
  push Not at hne
  have hd : Disjoint R (↑Q : Set Plane) := by
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hne x hxQ hx
  exact absurd (h R hR hd) (not_le.mpr hε)

theorem ordConn_side {I : Set ℝ} (h : Set.OrdConnected I) {t : ℝ} (ht : t ∉ I) :
    I ⊆ {x | x < t} ∨ I ⊆ {x | t < x} := by
  by_cases hex : ∃ a ∈ I, a < t
  · obtain ⟨a, ha, hat⟩ := hex
    left
    intro b hb
    rcases lt_trichotomy b t with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hb) ht
    · exact absurd (h.out ha hb ⟨hat.le, h1.le⟩) ht
  · right
    push Not at hex
    intro b hb
    rcases lt_trichotomy b t with h1 | h1 | h1
    · exact absurd h1 (not_lt.mpr (hex b hb))
    · exact absurd (h1 ▸ hb) ht
    · exact h1

/-- a rectangle missing `q` lies strictly on one side of it -/
theorem rect_avoid {R : Set Plane} (hR : IsRectangle R) {q : Plane} (hq : q ∉ R) :
    R ⊆ {x | x.1 < q.1} ∨ R ⊆ {x | q.1 < x.1} ∨ R ⊆ {x | x.2 < q.2} ∨ R ⊆ {x | q.2 < x.2} := by
  obtain ⟨I, J, hI, hJ, rfl⟩ := hR
  by_cases h1 : q.1 ∈ I
  · have h2 : q.2 ∉ J := fun h2 => hq ⟨h1, h2⟩
    rcases ordConn_side hJ h2 with h | h
    · right; right; left
      intro x hx; exact h hx.2
    · right; right; right
      intro x hx; exact h hx.2
  · rcases ordConn_side hI h1 with h | h
    · left; intro x hx; exact h hx.1
    · right; left; intro x hx; exact h hx.1

/-! ## The grid -/

section Grid
variable {V : Finset Plane} (g : QuartileGrid V)

theorem mem_cellVotes (i j : Fin 4) (v : Plane) :
    v ∈ g.cellVotes i j ↔ v ∈ V ∧ v ∈ g.cell i j := by
  unfold QuartileGrid.cellVotes; simp [Finset.mem_filter]

theorem cellVotes_subset (i j : Fin 4) : g.cellVotes i j ⊆ V := fun _ h =>
  ((mem_cellVotes g i j _).mp h).1

theorem mass_cellVotes (i j : Fin 4) : mass V (↑(g.cellVotes i j) : Set Plane) = g.cellMass i j := by
  unfold QuartileGrid.cellMass mass
  congr 3
  ext v
  simp [mem_cellVotes]

/-- band facts -/
theorem colBand_lt {c : Fin 3 → ℝ} (h01 : c 0 < c 1) (h12 : c 1 < c 2) {j j' : Fin 4} (hjj : j < j')
    {v w : Plane} (hv : v ∈ columnBand c j) (hw : w ∈ columnBand c j') : v.1 < w.1 := by
  fin_cases j <;> fin_cases j' <;> simp [columnBand] at hv hw hjj ⊢ <;> linarith

theorem rowBand_gt {c : Fin 3 → ℝ} (h01 : c 0 < c 1) (h12 : c 1 < c 2) {i i' : Fin 4} (hii : i < i')
    {v w : Plane} (hv : v ∈ rowBand c i) (hw : w ∈ rowBand c i') : w.2 < v.2 := by
  fin_cases i <;> fin_cases i' <;> simp [rowBand] at hv hw hii ⊢ <;> linarith

theorem colBand_unique {c : Fin 3 → ℝ} (h01 : c 0 < c 1) (h12 : c 1 < c 2) {j j' : Fin 4}
    {v : Plane} (hv : v ∈ columnBand c j) (hw : v ∈ columnBand c j') : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd (colBand_lt h01 h12 h hv hw) (lt_irrefl _)
  · exact h
  · exact absurd (colBand_lt h01 h12 h hw hv) (lt_irrefl _)

theorem rowBand_unique {c : Fin 3 → ℝ} (h01 : c 0 < c 1) (h12 : c 1 < c 2) {j j' : Fin 4}
    {v : Plane} (hv : v ∈ rowBand c j) (hw : v ∈ rowBand c j') : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd (rowBand_gt h01 h12 h hv hw) (lt_irrefl _)
  · exact h
  · exact absurd (rowBand_gt h01 h12 h hw hv) (lt_irrefl _)

theorem colBand_exists {c : Fin 3 → ℝ} {v : Plane} (h0 : v.1 ≠ c 0) (h1 : v.1 ≠ c 1) (h2 : v.1 ≠ c 2)
    (h01 : c 0 < c 1) (h12 : c 1 < c 2) : ∃ j, v ∈ columnBand c j := by
  by_cases a : v.1 < c 0
  · exact ⟨0, by simp [columnBand, a]⟩
  by_cases b : v.1 < c 1
  · exact ⟨1, by simp [columnBand]; exact ⟨lt_of_le_of_ne (not_lt.mp a) (Ne.symm h0), b⟩⟩
  by_cases d : v.1 < c 2
  · exact ⟨2, by simp [columnBand]; exact ⟨lt_of_le_of_ne (not_lt.mp b) (Ne.symm h1), d⟩⟩
  · exact ⟨3, by simp [columnBand]; exact lt_of_le_of_ne (not_lt.mp d) (Ne.symm h2)⟩

theorem rowBand_exists {c : Fin 3 → ℝ} {v : Plane} (h0 : v.2 ≠ c 0) (h1 : v.2 ≠ c 1) (h2 : v.2 ≠ c 2)
    (h01 : c 0 < c 1) (h12 : c 1 < c 2) : ∃ i, v ∈ rowBand c i := by
  by_cases a : c 2 < v.2
  · exact ⟨0, by simp [rowBand, a]⟩
  by_cases b : c 1 < v.2
  · exact ⟨1, by simp [rowBand]; exact ⟨b, lt_of_le_of_ne (not_lt.mp a) h2⟩⟩
  by_cases d : c 0 < v.2
  · exact ⟨2, by simp [rowBand]; exact ⟨d, lt_of_le_of_ne (not_lt.mp b) h1⟩⟩
  · exact ⟨3, by simp [rowBand]; exact lt_of_le_of_ne (not_lt.mp d) h0⟩

theorem xo (g : QuartileGrid V) : g.xCut 0 < g.xCut 1 ∧ g.xCut 1 < g.xCut 2 :=
  ⟨g.x_order (by decide), g.x_order (by decide)⟩
theorem yo (g : QuartileGrid V) : g.yCut 0 < g.yCut 1 ∧ g.yCut 1 < g.yCut 2 :=
  ⟨g.y_order (by decide), g.y_order (by decide)⟩

theorem cell_unique {i i' j j' : Fin 4} {v : Plane} (hv : v ∈ g.cell i j) (hw : v ∈ g.cell i' j') :
    i = i' ∧ j = j' :=
  ⟨rowBand_unique (yo g).1 (yo g).2 hv.1 hw.1, colBand_unique (xo g).1 (xo g).2 hv.2 hw.2⟩

theorem cell_exists {v : Plane} (hv : v ∈ V) : ∃ i j, v ∈ g.cell i j := by
  obtain ⟨j, hj⟩ := colBand_exists (g.x_avoids v hv 0) (g.x_avoids v hv 1) (g.x_avoids v hv 2)
    (xo g).1 (xo g).2
  obtain ⟨i, hi⟩ := rowBand_exists (g.y_avoids v hv 0) (g.y_avoids v hv 1) (g.y_avoids v hv 2)
    (yo g).1 (yo g).2
  exact ⟨i, j, hi, hj⟩

theorem cellVotes_disjoint {i j i' j' : Fin 4} (h : (i, j) ≠ (i', j')) :
    Disjoint (g.cellVotes i j) (g.cellVotes i' j') := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  rw [mem_cellVotes] at h1 h2
  obtain ⟨e1, e2⟩ := cell_unique g h1.2 h2.2
  exact h (by rw [e1, e2])

theorem cellMass_nonneg (i j : Fin 4) : 0 ≤ g.cellMass i j := mass_nonneg _ _

theorem cell_sum_one {v : Plane} (hv : v ∈ V) :
    ∑ i : Fin 4, ∑ j : Fin 4, (if v ∈ g.cell i j then 1 else 0 : ℕ) = 1 := by
  obtain ⟨i0, j0, h0⟩ := cell_exists g hv
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single j0]
    · simp [h0]
    · intro j _ hj
      have : v ∉ g.cell i0 j := fun h => hj (cell_unique g h h0).2
      simp [this]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have : v ∉ g.cell i j := fun h => hi (cell_unique g h h0).1
    simp [this]
  · simp

/-- the 16 cells partition the voters: a rectangle's (any set's) mass is the sum of its cell masses -/
theorem mass_eq_sum_cells (S : Set Plane) :
    mass V S = ∑ i : Fin 4, ∑ j : Fin 4, mass V (S ∩ g.cell i j) := by
  unfold mass
  simp_rw [← Finset.sum_div]
  congr 1
  have key : (V.filter (fun v => v ∈ S)).card =
      ∑ i : Fin 4, ∑ j : Fin 4, (V.filter (fun v => v ∈ S ∩ g.cell i j)).card := by
    calc (V.filter (fun v => v ∈ S)).card
        = ∑ v ∈ V, (if v ∈ S then 1 else 0 : ℕ) := Finset.card_filter _ _
      _ = ∑ v ∈ V, ∑ i : Fin 4, ∑ j : Fin 4, (if v ∈ S ∩ g.cell i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hS : v ∈ S
        · have := cell_sum_one g hv
          simpa [hS] using this.symm
        · simp [hS]
      _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ v ∈ V, (if v ∈ S ∩ g.cell i j then 1 else 0 : ℕ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by simp only [Finset.card_filter]
  have := congrArg (Nat.cast : ℕ → ℝ) key
  push_cast at this
  convert this using 4
  all_goals first | rfl | congr

theorem cellMass_row (i : Fin 4) : ∑ j : Fin 4, g.cellMass i j = 1 / 4 := by
  have h := mass_eq_sum_cells g (rowBand g.yCut i)
  rw [g.row_mass] at h
  rw [h]; symm; rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro j _
    unfold QuartileGrid.cellMass QuartileGrid.cell
    congr 1
    ext x; simp only [Set.mem_inter_iff]; tauto
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro j _
    apply mass_eq_zero
    intro v _ hv
    exact hi' (rowBand_unique (yo g).1 (yo g).2 hv.2.1 hv.1)
  · simp
theorem cellMass_col (j : Fin 4) : ∑ i : Fin 4, g.cellMass i j = 1 / 4 := by
  have h := mass_eq_sum_cells g (columnBand g.xCut j)
  rw [g.column_mass] at h
  rw [h]; symm; rw [Finset.sum_comm, Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro i _
    unfold QuartileGrid.cellMass QuartileGrid.cell
    congr 1
    ext x; simp only [Set.mem_inter_iff]; tauto
  · intro j' _ hj'
    apply Finset.sum_eq_zero
    intro i _
    apply mass_eq_zero
    intro v _ hv
    exact hj' (colBand_unique (xo g).1 (xo g).2 hv.2.2 hv.1)
  · simp
theorem mass_inter_cell_le (S : Set Plane) (i j : Fin 4) :
    mass V (S ∩ g.cell i j) ≤ g.cellMass i j :=
  mass_mono V Set.inter_subset_right

/-- positions of cells: columns increase to the east, rows increase to the south -/
theorem cell_x_lt {i i' j j' : Fin 4} {v w : Plane} (hv : v ∈ g.cell i j) (hw : w ∈ g.cell i' j')
    (h : j < j') : v.1 < w.1 := colBand_lt (xo g).1 (xo g).2 h hv.2 hw.2
theorem cell_y_gt {i i' j j' : Fin 4} {v w : Plane} (hv : v ∈ g.cell i j) (hw : w ∈ g.cell i' j')
    (h : i < i') : w.2 < v.2 := rowBand_gt (yo g).1 (yo g).2 h hv.1 hw.1
theorem cell_x_lt_middle {i j : Fin 4} {v : Plane} (hv : v ∈ g.cell i j) (hj : j ≤ 1) :
    v.1 < g.middle.1 := by
  have h := hv.2
  have := (xo g).1
  fin_cases j <;> simp [columnBand] at h hj ⊢ <;> unfold QuartileGrid.middle <;> simp <;> linarith
theorem middle_lt_cell_x {i j : Fin 4} {v : Plane} (hv : v ∈ g.cell i j) (hj : 2 ≤ j) :
    g.middle.1 < v.1 := by
  have h := hv.2
  have := (xo g).2
  fin_cases j <;> simp [columnBand] at h hj ⊢ <;> unfold QuartileGrid.middle <;> simp <;> linarith
theorem middle_lt_cell_y {i j : Fin 4} {v : Plane} (hv : v ∈ g.cell i j) (hi : i ≤ 1) :
    g.middle.2 < v.2 := by
  have h := hv.1
  have := (yo g).2
  fin_cases i <;> simp [rowBand] at h hi ⊢ <;> unfold QuartileGrid.middle <;> simp <;> linarith
theorem cell_y_lt_middle {i j : Fin 4} {v : Plane} (hv : v ∈ g.cell i j) (hi : 2 ≤ i) :
    v.2 < g.middle.2 := by
  have h := hv.1
  have := (yo g).1
  fin_cases i <;> simp [rowBand] at h hi ⊢ <;> unfold QuartileGrid.middle <;> simp <;> linarith

/-- a rectangle not containing the middle point lies in two rows or two columns: mass ≤ 1/2 -/
theorem safe_of_not_mem_middle {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∉ R) :
    mass V R ≤ 1 / 2 := by
  obtain ⟨I, J, hI, hJ, rfl⟩ := hR
  by_cases h1 : g.middle.1 ∈ I
  · have h2 : g.middle.2 ∉ J := fun h2 => hp ⟨h1, h2⟩
    rcases ordConn_side hJ h2 with h | h
    · -- y < yCut 1 : rows 2,3
      calc mass V (I ×ˢ J) ≤ mass V (rowBand g.yCut 2 ∪ rowBand g.yCut 3) := by
            apply mass_le_card
            intro v hv hvR
            have hv2 : v.2 < g.yCut 1 := h hvR.2
            obtain ⟨i, j, hij⟩ := cell_exists g hv
            have : 2 ≤ i := by
              by_contra hi
              have := middle_lt_cell_y g hij (by omega)
              simp [QuartileGrid.middle] at this; linarith
            have hrow := hij.1
            fin_cases i <;> simp at this <;> simp_all
        _ = 1 / 2 := by
            rw [mass_union, g.row_mass, g.row_mass]; norm_num
            rw [Set.disjoint_left]
            intro z h1 h2
            exact absurd (rowBand_unique (yo g).1 (yo g).2 h1 h2) (by decide)
    · calc mass V (I ×ˢ J) ≤ mass V (rowBand g.yCut 0 ∪ rowBand g.yCut 1) := by
            apply mass_le_card
            intro v hv hvR
            have hv2 : g.yCut 1 < v.2 := h hvR.2
            obtain ⟨i, j, hij⟩ := cell_exists g hv
            have : i ≤ 1 := by
              by_contra hi
              have := cell_y_lt_middle g hij (by omega)
              simp [QuartileGrid.middle] at this; linarith
            have hrow := hij.1
            fin_cases i <;> simp at this <;> simp_all
        _ = 1 / 2 := by
            rw [mass_union, g.row_mass, g.row_mass]; norm_num
            rw [Set.disjoint_left]
            intro z h1 h2
            exact absurd (rowBand_unique (yo g).1 (yo g).2 h1 h2) (by decide)
  · rcases ordConn_side hI h1 with h | h
    · calc mass V (I ×ˢ J) ≤ mass V (columnBand g.xCut 0 ∪ columnBand g.xCut 1) := by
            apply mass_le_card
            intro v hv hvR
            have hv2 : v.1 < g.xCut 1 := h hvR.1
            obtain ⟨i, j, hij⟩ := cell_exists g hv
            have : j ≤ 1 := by
              by_contra hi
              have := middle_lt_cell_x g hij (by omega)
              simp [QuartileGrid.middle] at this; linarith
            have hrow := hij.2
            fin_cases j <;> simp at this <;> simp_all
        _ = 1 / 2 := by
            rw [mass_union, g.column_mass, g.column_mass]; norm_num
            rw [Set.disjoint_left]
            intro z h1 h2
            exact absurd (colBand_unique (xo g).1 (xo g).2 h1 h2) (by decide)
    · calc mass V (I ×ˢ J) ≤ mass V (columnBand g.xCut 2 ∪ columnBand g.xCut 3) := by
            apply mass_le_card
            intro v hv hvR
            have hv2 : g.xCut 1 < v.1 := h hvR.1
            obtain ⟨i, j, hij⟩ := cell_exists g hv
            have : 2 ≤ j := by
              by_contra hi
              have := cell_x_lt_middle g hij (by omega)
              simp [QuartileGrid.middle] at this; linarith
            have hrow := hij.2
            fin_cases j <;> simp at this <;> simp_all
        _ = 1 / 2 := by
            rw [mass_union, g.column_mass, g.column_mass]; norm_num
            rw [Set.disjoint_left]
            intro z h1 h2
            exact absurd (colBand_unique (xo g).1 (xo g).2 h1 h2) (by decide)

/-! kill lemmas: a rectangle on one side of `q` has no voters in the cells on the other side
of `q`'s row / column (`q` need not be a voter). -/
theorem kill_east {R : Set Plane} {q : Plane} {i0 j0 : Fin 4} (hq : q ∈ g.cell i0 j0)
    (hR : R ⊆ {x | q.1 < x.1}) (i j : Fin 4) (hj : j < j0) : mass V (R ∩ g.cell i j) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := cell_x_lt g hv.2 hq hj
  simp only [Set.mem_setOf_eq] at h1; linarith
theorem kill_west {R : Set Plane} {q : Plane} {i0 j0 : Fin 4} (hq : q ∈ g.cell i0 j0)
    (hR : R ⊆ {x | x.1 < q.1}) (i j : Fin 4) (hj : j0 < j) : mass V (R ∩ g.cell i j) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := cell_x_lt g hq hv.2 hj
  simp only [Set.mem_setOf_eq] at h1; linarith
theorem kill_north {R : Set Plane} {q : Plane} {i0 j0 : Fin 4} (hq : q ∈ g.cell i0 j0)
    (hR : R ⊆ {x | q.2 < x.2}) (i j : Fin 4) (hi : i0 < i) : mass V (R ∩ g.cell i j) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := cell_y_gt g hq hv.2 hi
  simp only [Set.mem_setOf_eq] at h1; linarith
theorem kill_south {R : Set Plane} {q : Plane} {i0 j0 : Fin 4} (hq : q ∈ g.cell i0 j0)
    (hR : R ⊆ {x | x.2 < q.2}) (i j : Fin 4) (hi : i < i0) : mass V (R ∩ g.cell i j) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := cell_y_gt g hv.2 hq hi
  simp only [Set.mem_setOf_eq] at h1; linarith

end Grid

/-! ## Extreme points of a finite set -/

theorem exists_westmost (X : Finset Plane) (hX : X.Nonempty) : ∃ z ∈ X, ∀ x ∈ X, z.1 ≤ x.1 :=
  Finset.exists_min_image X Prod.fst hX
theorem exists_eastmost (X : Finset Plane) (hX : X.Nonempty) : ∃ z ∈ X, ∀ x ∈ X, x.1 ≤ z.1 :=
  Finset.exists_max_image X Prod.fst hX
theorem exists_southmost (X : Finset Plane) (hX : X.Nonempty) : ∃ z ∈ X, ∀ x ∈ X, z.2 ≤ x.2 :=
  Finset.exists_min_image X Prod.snd hX
theorem exists_northmost (X : Finset Plane) (hX : X.Nonempty) : ∃ z ∈ X, ∀ x ∈ X, x.2 ≤ z.2 :=
  Finset.exists_max_image X Prod.snd hX

/-- a set mass in a rectangle on the far side of an extreme point is zero; one lemma per side -/
theorem mass_inter_west_extreme {V : Finset Plane} {X : Finset Plane} {z : Plane} {R : Set Plane}
    (hz : ∀ x ∈ X, z.1 ≤ x.1) (hR : R ⊆ {x | x.1 < z.1}) : mass V (R ∩ ↑X) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := hz v hv.2
  simp only [Set.mem_setOf_eq] at h1; linarith
theorem mass_inter_east_extreme {V : Finset Plane} {X : Finset Plane} {z : Plane} {R : Set Plane}
    (hz : ∀ x ∈ X, x.1 ≤ z.1) (hR : R ⊆ {x | z.1 < x.1}) : mass V (R ∩ ↑X) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := hz v hv.2
  simp only [Set.mem_setOf_eq] at h1; linarith
theorem mass_inter_south_extreme {V : Finset Plane} {X : Finset Plane} {z : Plane} {R : Set Plane}
    (hz : ∀ x ∈ X, z.2 ≤ x.2) (hR : R ⊆ {x | x.2 < z.2}) : mass V (R ∩ ↑X) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := hz v hv.2
  simp only [Set.mem_setOf_eq] at h1; linarith
theorem mass_inter_north_extreme {V : Finset Plane} {X : Finset Plane} {z : Plane} {R : Set Plane}
    (hz : ∀ x ∈ X, x.2 ≤ z.2) (hR : R ⊆ {x | z.2 < x.2}) : mass V (R ∩ ↑X) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := hz v hv.2
  simp only [Set.mem_setOf_eq] at h1; linarith

end PlanarMetricElections.Peer.Dev
end
end

section
set_option autoImplicit false
open scoped Classical
namespace PlanarMetricElections.Peer.Dev.EmptyCenter
open PlanarMetricElections.Peer PlanarMetricElections.Peer.Dev

theorem cell_eq {V : Finset Plane} (g : QuartileGrid V) (S : Set Plane) (i j : Fin 4) :
    mass V (S ∩ g.cell i j) = mass V (S ∩ ↑(g.cellVotes i j)) := by
  unfold mass
  congr 3
  ext v
  simp only [Finset.mem_filter, Set.mem_inter_iff, Finset.mem_coe, QuartileGrid.cellVotes]
  tauto

theorem nonempty_of_mass_pos {V : Finset Plane} (X : Finset Plane)
    (h : 0 < mass V (↑X : Set Plane)) : X.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  rw [he] at h
  simp [mass_empty] at h

/-- an extreme point kills the cells contained in the finset -/
theorem ext_kill {V : Finset Plane} (g : QuartileGrid V) {R : Set Plane} {X : Finset Plane}
    (P : Fin 4 → Fin 4 → Prop) (hP : ∀ i j, P i j → g.cellVotes i j ⊆ X)
    (h : mass V (R ∩ ↑X) = 0) : ∀ i j : Fin 4, P i j → mass V (R ∩ g.cell i j) = 0 := by
  intro i j hij
  apply le_antisymm
  · rw [cell_eq, ← h]
    exact mass_mono V (Set.inter_subset_inter_right _ (by exact_mod_cast hP i j hij))
  · exact mass_nonneg _ _

theorem opt4 {V : Finset Plane} (g : QuartileGrid V) {R : Set Plane} (hR : IsRectangle R)
    {q : Plane} (hq : q ∉ R) {i0 j0 : Fin 4} (hqc : q ∈ g.cell i0 j0) :
    (R ⊆ {x | q.1 < x.1} ∧ ∀ i j : Fin 4, j < j0 → mass V (R ∩ g.cell i j) = 0) ∨
    (R ⊆ {x | x.1 < q.1} ∧ ∀ i j : Fin 4, j0 < j → mass V (R ∩ g.cell i j) = 0) ∨
    (R ⊆ {x | x.2 < q.2} ∧ ∀ i j : Fin 4, i < i0 → mass V (R ∩ g.cell i j) = 0) ∨
    (R ⊆ {x | q.2 < x.2} ∧ ∀ i j : Fin 4, i0 < i → mass V (R ∩ g.cell i j) = 0) := by
  rcases rect_avoid hR hq with h | h | h | h
  · exact Or.inr (Or.inl ⟨h, fun i j hj => kill_west g hqc h i j hj⟩)
  · exact Or.inl ⟨h, fun i j hj => kill_east g hqc h i j hj⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h, fun i j hj => kill_south g hqc h i j hj⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, fun i j hj => kill_north g hqc h i j hj⟩))


variable {V : Finset Plane} (g : QuartileGrid V)

/-- south extreme of the top-row union, point in B -/
theorem optB {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 0 1)
    (hz : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q.2 ≤ x.2) :
    (∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, (i = 0 ∧ (j = 1 ∨ j = 2)) → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exact Or.inl k
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · refine Or.inr (ext_kill g _ ?_ (mass_inter_south_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])

theorem optC {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 0 2)
    (hz : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q.2 ≤ x.2) :
    (∀ i j : Fin 4, 2 < j → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, (i = 0 ∧ (j = 1 ∨ j = 2)) → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inl k
  · refine Or.inr (ext_kill g _ ?_ (mass_inter_south_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])

theorem optN {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 3 1)
    (hz : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q.2) :
    (∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, (i = 3 ∧ (j = 1 ∨ j = 2)) → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exact Or.inl k
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · refine Or.inr (ext_kill g _ ?_ (mass_inter_north_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

theorem optO {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 3 2)
    (hz : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q.2) :
    (∀ i j : Fin 4, 2 < j → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, (i = 3 ∧ (j = 1 ∨ j = 2)) → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inl k
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · refine Or.inr (ext_kill g _ ?_ (mass_inter_north_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

/-- westmost point of the east-column union -/
theorem optH {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 1 3)
    (hz : ∀ x ∈ g.cellVotes 1 3 ∪ g.cellVotes 2 3, q.1 ≤ x.1) :
    (∀ i j : Fin 4, (j = 3 ∧ (i = 1 ∨ i = 2)) → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · refine Or.inl (ext_kill g _ ?_ (mass_inter_west_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exact Or.inr k
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])

theorem optL {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 2 3)
    (hz : ∀ x ∈ g.cellVotes 1 3 ∪ g.cellVotes 2 3, q.1 ≤ x.1) :
    (∀ i j : Fin 4, (j = 3 ∧ (i = 1 ∨ i = 2)) → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, 2 < i → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · refine Or.inl (ext_kill g _ ?_ (mass_inter_west_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inr k

/-- eastmost point of the west-column union -/
theorem optE {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 1 0)
    (hz : ∀ x ∈ g.cellVotes 1 0 ∪ g.cellVotes 2 0, x.1 ≤ q.1) :
    (∀ i j : Fin 4, (j = 0 ∧ (i = 1 ∨ i = 2)) → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · refine Or.inl (ext_kill g _ ?_ (mass_inter_east_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inr k
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])

theorem optI {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 2 0)
    (hz : ∀ x ∈ g.cellVotes 1 0 ∪ g.cellVotes 2 0, x.1 ≤ q.1) :
    (∀ i j : Fin 4, (j = 0 ∧ (i = 1 ∨ i = 2)) → mass V (R ∩ g.cell i j) = 0) ∨
    (∀ i j : Fin 4, 2 < i → mass V (R ∩ g.cell i j) = 0) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · refine Or.inl (ext_kill g _ ?_ (mass_inter_east_extreme hz h))
    rintro i j ⟨rfl, rfl | rfl⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inr k



theorem caseBNH (hA0 : g.cellMass 0 0 = 0) (hD0 : g.cellMass 0 3 = 0) (hM0 : g.cellMass 3 0 = 0)
    (hP0 : g.cellMass 3 3 = 0) {q1 q2 q3 : Plane}
    (hq1c : q1 ∈ g.cell 0 1) (hq2c : q2 ∈ g.cell 3 1) (hq3c : q3 ∈ g.cell 1 3)
    (hz1 : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q1.2 ≤ x.2) (hz2 : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q2.2)
    (hz3 : ∀ x ∈ g.cellVotes 1 3 ∪ g.cellVotes 2 3, q3.1 ≤ x.1)
    {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) (n1 : q1 ∉ R) (n2 : q2 ∉ R)
    (n3 : q3 ∉ R) : mass V R ≤ 1 / 2 := by
  have o1 := optB g hR hp n1 hq1c hz1
  have o2 := optN g hR hp n2 hq2c hz2
  have o3 := optH g hR hp n3 hq3c hz3
  rcases o1 with k1 | k1 <;> rcases o2 with k2 | k2 <;> rcases o3 with k3 | k3 <;> (focus
      have e := mass_eq_sum_cells g R
      simp only [Fin.sum_univ_four] at e
      have rw0 := cellMass_row g 0
      have rw1 := cellMass_row g 1
      have rw2 := cellMass_row g 2
      have rw3 := cellMass_row g 3
      have cl0 := cellMass_col g 0
      have cl1 := cellMass_col g 1
      have cl2 := cellMass_col g 2
      have cl3 := cellMass_col g 3
      simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
      have c00 := mass_inter_cell_le g R 0 0
      have c01 := mass_inter_cell_le g R 0 1
      have c02 := mass_inter_cell_le g R 0 2
      have c03 := mass_inter_cell_le g R 0 3
      have c10 := mass_inter_cell_le g R 1 0
      have c11 := mass_inter_cell_le g R 1 1
      have c12 := mass_inter_cell_le g R 1 2
      have c13 := mass_inter_cell_le g R 1 3
      have c20 := mass_inter_cell_le g R 2 0
      have c21 := mass_inter_cell_le g R 2 1
      have c22 := mass_inter_cell_le g R 2 2
      have c23 := mass_inter_cell_le g R 2 3
      have c30 := mass_inter_cell_le g R 3 0
      have c31 := mass_inter_cell_le g R 3 1
      have c32 := mass_inter_cell_le g R 3 2
      have c33 := mass_inter_cell_le g R 3 3
      have z00 := cellMass_nonneg g 0 0
      have z01 := cellMass_nonneg g 0 1
      have z02 := cellMass_nonneg g 0 2
      have z03 := cellMass_nonneg g 0 3
      have z10 := cellMass_nonneg g 1 0
      have z11 := cellMass_nonneg g 1 1
      have z12 := cellMass_nonneg g 1 2
      have z13 := cellMass_nonneg g 1 3
      have z20 := cellMass_nonneg g 2 0
      have z21 := cellMass_nonneg g 2 1
      have z22 := cellMass_nonneg g 2 2
      have z23 := cellMass_nonneg g 2 3
      have z30 := cellMass_nonneg g 3 0
      have z31 := cellMass_nonneg g 3 1
      have z32 := cellMass_nonneg g 3 2
      have z33 := cellMass_nonneg g 3 3
      first
      | (simp (disch := decide) only [k1, k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1, k2] at e; linarith))

theorem caseBNL (hA0 : g.cellMass 0 0 = 0) (hD0 : g.cellMass 0 3 = 0) (hM0 : g.cellMass 3 0 = 0)
    (hP0 : g.cellMass 3 3 = 0) {q1 q2 q3 : Plane}
    (hq1c : q1 ∈ g.cell 0 1) (hq2c : q2 ∈ g.cell 3 1) (hq3c : q3 ∈ g.cell 2 3)
    (hz1 : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q1.2 ≤ x.2) (hz2 : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q2.2)
    (hz3 : ∀ x ∈ g.cellVotes 1 3 ∪ g.cellVotes 2 3, q3.1 ≤ x.1)
    {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) (n1 : q1 ∉ R) (n2 : q2 ∉ R)
    (n3 : q3 ∉ R) : mass V R ≤ 1 / 2 := by
  have o1 := optB g hR hp n1 hq1c hz1
  have o2 := optN g hR hp n2 hq2c hz2
  have o3 := optL g hR hp n3 hq3c hz3
  rcases o1 with k1 | k1 <;> rcases o2 with k2 | k2 <;> rcases o3 with k3 | k3 <;> (focus
      have e := mass_eq_sum_cells g R
      simp only [Fin.sum_univ_four] at e
      have rw0 := cellMass_row g 0
      have rw1 := cellMass_row g 1
      have rw2 := cellMass_row g 2
      have rw3 := cellMass_row g 3
      have cl0 := cellMass_col g 0
      have cl1 := cellMass_col g 1
      have cl2 := cellMass_col g 2
      have cl3 := cellMass_col g 3
      simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
      have c00 := mass_inter_cell_le g R 0 0
      have c01 := mass_inter_cell_le g R 0 1
      have c02 := mass_inter_cell_le g R 0 2
      have c03 := mass_inter_cell_le g R 0 3
      have c10 := mass_inter_cell_le g R 1 0
      have c11 := mass_inter_cell_le g R 1 1
      have c12 := mass_inter_cell_le g R 1 2
      have c13 := mass_inter_cell_le g R 1 3
      have c20 := mass_inter_cell_le g R 2 0
      have c21 := mass_inter_cell_le g R 2 1
      have c22 := mass_inter_cell_le g R 2 2
      have c23 := mass_inter_cell_le g R 2 3
      have c30 := mass_inter_cell_le g R 3 0
      have c31 := mass_inter_cell_le g R 3 1
      have c32 := mass_inter_cell_le g R 3 2
      have c33 := mass_inter_cell_le g R 3 3
      have z00 := cellMass_nonneg g 0 0
      have z01 := cellMass_nonneg g 0 1
      have z02 := cellMass_nonneg g 0 2
      have z03 := cellMass_nonneg g 0 3
      have z10 := cellMass_nonneg g 1 0
      have z11 := cellMass_nonneg g 1 1
      have z12 := cellMass_nonneg g 1 2
      have z13 := cellMass_nonneg g 1 3
      have z20 := cellMass_nonneg g 2 0
      have z21 := cellMass_nonneg g 2 1
      have z22 := cellMass_nonneg g 2 2
      have z23 := cellMass_nonneg g 2 3
      have z30 := cellMass_nonneg g 3 0
      have z31 := cellMass_nonneg g 3 1
      have z32 := cellMass_nonneg g 3 2
      have z33 := cellMass_nonneg g 3 3
      first
      | (simp (disch := decide) only [k1, k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1, k2] at e; linarith))

theorem caseBO (hA0 : g.cellMass 0 0 = 0) (hD0 : g.cellMass 0 3 = 0) (hM0 : g.cellMass 3 0 = 0)
    (hP0 : g.cellMass 3 3 = 0) {q1 q2 : Plane}
    (hq1c : q1 ∈ g.cell 0 1) (hq2c : q2 ∈ g.cell 3 2)
    (hz1 : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q1.2 ≤ x.2) (hz2 : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q2.2)
    {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) (n1 : q1 ∉ R) (n2 : q2 ∉ R) :
    mass V R ≤ 1 / 2 := by
  have o1 := optB g hR hp n1 hq1c hz1
  have o2 := optO g hR hp n2 hq2c hz2
  rcases o1 with k1 | k1 <;> rcases o2 with k2 | k2 <;> (focus
      have e := mass_eq_sum_cells g R
      simp only [Fin.sum_univ_four] at e
      have rw0 := cellMass_row g 0
      have rw1 := cellMass_row g 1
      have rw2 := cellMass_row g 2
      have rw3 := cellMass_row g 3
      have cl0 := cellMass_col g 0
      have cl1 := cellMass_col g 1
      have cl2 := cellMass_col g 2
      have cl3 := cellMass_col g 3
      simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
      have c00 := mass_inter_cell_le g R 0 0
      have c01 := mass_inter_cell_le g R 0 1
      have c02 := mass_inter_cell_le g R 0 2
      have c03 := mass_inter_cell_le g R 0 3
      have c10 := mass_inter_cell_le g R 1 0
      have c11 := mass_inter_cell_le g R 1 1
      have c12 := mass_inter_cell_le g R 1 2
      have c13 := mass_inter_cell_le g R 1 3
      have c20 := mass_inter_cell_le g R 2 0
      have c21 := mass_inter_cell_le g R 2 1
      have c22 := mass_inter_cell_le g R 2 2
      have c23 := mass_inter_cell_le g R 2 3
      have c30 := mass_inter_cell_le g R 3 0
      have c31 := mass_inter_cell_le g R 3 1
      have c32 := mass_inter_cell_le g R 3 2
      have c33 := mass_inter_cell_le g R 3 3
      have z00 := cellMass_nonneg g 0 0
      have z01 := cellMass_nonneg g 0 1
      have z02 := cellMass_nonneg g 0 2
      have z03 := cellMass_nonneg g 0 3
      have z10 := cellMass_nonneg g 1 0
      have z11 := cellMass_nonneg g 1 1
      have z12 := cellMass_nonneg g 1 2
      have z13 := cellMass_nonneg g 1 3
      have z20 := cellMass_nonneg g 2 0
      have z21 := cellMass_nonneg g 2 1
      have z22 := cellMass_nonneg g 2 2
      have z23 := cellMass_nonneg g 2 3
      have z30 := cellMass_nonneg g 3 0
      have z31 := cellMass_nonneg g 3 1
      have z32 := cellMass_nonneg g 3 2
      have z33 := cellMass_nonneg g 3 3
      first
      | (simp (disch := decide) only [k1, k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1, k2] at e; linarith))

theorem caseCN (hA0 : g.cellMass 0 0 = 0) (hD0 : g.cellMass 0 3 = 0) (hM0 : g.cellMass 3 0 = 0)
    (hP0 : g.cellMass 3 3 = 0) {q1 q2 : Plane}
    (hq1c : q1 ∈ g.cell 0 2) (hq2c : q2 ∈ g.cell 3 1)
    (hz1 : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q1.2 ≤ x.2) (hz2 : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q2.2)
    {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) (n1 : q1 ∉ R) (n2 : q2 ∉ R) :
    mass V R ≤ 1 / 2 := by
  have o1 := optC g hR hp n1 hq1c hz1
  have o2 := optN g hR hp n2 hq2c hz2
  rcases o1 with k1 | k1 <;> rcases o2 with k2 | k2 <;> (focus
      have e := mass_eq_sum_cells g R
      simp only [Fin.sum_univ_four] at e
      have rw0 := cellMass_row g 0
      have rw1 := cellMass_row g 1
      have rw2 := cellMass_row g 2
      have rw3 := cellMass_row g 3
      have cl0 := cellMass_col g 0
      have cl1 := cellMass_col g 1
      have cl2 := cellMass_col g 2
      have cl3 := cellMass_col g 3
      simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
      have c00 := mass_inter_cell_le g R 0 0
      have c01 := mass_inter_cell_le g R 0 1
      have c02 := mass_inter_cell_le g R 0 2
      have c03 := mass_inter_cell_le g R 0 3
      have c10 := mass_inter_cell_le g R 1 0
      have c11 := mass_inter_cell_le g R 1 1
      have c12 := mass_inter_cell_le g R 1 2
      have c13 := mass_inter_cell_le g R 1 3
      have c20 := mass_inter_cell_le g R 2 0
      have c21 := mass_inter_cell_le g R 2 1
      have c22 := mass_inter_cell_le g R 2 2
      have c23 := mass_inter_cell_le g R 2 3
      have c30 := mass_inter_cell_le g R 3 0
      have c31 := mass_inter_cell_le g R 3 1
      have c32 := mass_inter_cell_le g R 3 2
      have c33 := mass_inter_cell_le g R 3 3
      have z00 := cellMass_nonneg g 0 0
      have z01 := cellMass_nonneg g 0 1
      have z02 := cellMass_nonneg g 0 2
      have z03 := cellMass_nonneg g 0 3
      have z10 := cellMass_nonneg g 1 0
      have z11 := cellMass_nonneg g 1 1
      have z12 := cellMass_nonneg g 1 2
      have z13 := cellMass_nonneg g 1 3
      have z20 := cellMass_nonneg g 2 0
      have z21 := cellMass_nonneg g 2 1
      have z22 := cellMass_nonneg g 2 2
      have z23 := cellMass_nonneg g 2 3
      have z30 := cellMass_nonneg g 3 0
      have z31 := cellMass_nonneg g 3 1
      have z32 := cellMass_nonneg g 3 2
      have z33 := cellMass_nonneg g 3 3
      first
      | (simp (disch := decide) only [k1, k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1, k2] at e; linarith))

theorem caseCOE (hA0 : g.cellMass 0 0 = 0) (hD0 : g.cellMass 0 3 = 0) (hM0 : g.cellMass 3 0 = 0)
    (hP0 : g.cellMass 3 3 = 0) {q1 q2 q3 : Plane}
    (hq1c : q1 ∈ g.cell 0 2) (hq2c : q2 ∈ g.cell 3 2) (hq3c : q3 ∈ g.cell 1 0)
    (hz1 : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q1.2 ≤ x.2) (hz2 : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q2.2)
    (hz3 : ∀ x ∈ g.cellVotes 1 0 ∪ g.cellVotes 2 0, x.1 ≤ q3.1)
    {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) (n1 : q1 ∉ R) (n2 : q2 ∉ R)
    (n3 : q3 ∉ R) : mass V R ≤ 1 / 2 := by
  have o1 := optC g hR hp n1 hq1c hz1
  have o2 := optO g hR hp n2 hq2c hz2
  have o3 := optE g hR hp n3 hq3c hz3
  rcases o1 with k1 | k1 <;> rcases o2 with k2 | k2 <;> rcases o3 with k3 | k3 <;> (focus
      have e := mass_eq_sum_cells g R
      simp only [Fin.sum_univ_four] at e
      have rw0 := cellMass_row g 0
      have rw1 := cellMass_row g 1
      have rw2 := cellMass_row g 2
      have rw3 := cellMass_row g 3
      have cl0 := cellMass_col g 0
      have cl1 := cellMass_col g 1
      have cl2 := cellMass_col g 2
      have cl3 := cellMass_col g 3
      simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
      have c00 := mass_inter_cell_le g R 0 0
      have c01 := mass_inter_cell_le g R 0 1
      have c02 := mass_inter_cell_le g R 0 2
      have c03 := mass_inter_cell_le g R 0 3
      have c10 := mass_inter_cell_le g R 1 0
      have c11 := mass_inter_cell_le g R 1 1
      have c12 := mass_inter_cell_le g R 1 2
      have c13 := mass_inter_cell_le g R 1 3
      have c20 := mass_inter_cell_le g R 2 0
      have c21 := mass_inter_cell_le g R 2 1
      have c22 := mass_inter_cell_le g R 2 2
      have c23 := mass_inter_cell_le g R 2 3
      have c30 := mass_inter_cell_le g R 3 0
      have c31 := mass_inter_cell_le g R 3 1
      have c32 := mass_inter_cell_le g R 3 2
      have c33 := mass_inter_cell_le g R 3 3
      have z00 := cellMass_nonneg g 0 0
      have z01 := cellMass_nonneg g 0 1
      have z02 := cellMass_nonneg g 0 2
      have z03 := cellMass_nonneg g 0 3
      have z10 := cellMass_nonneg g 1 0
      have z11 := cellMass_nonneg g 1 1
      have z12 := cellMass_nonneg g 1 2
      have z13 := cellMass_nonneg g 1 3
      have z20 := cellMass_nonneg g 2 0
      have z21 := cellMass_nonneg g 2 1
      have z22 := cellMass_nonneg g 2 2
      have z23 := cellMass_nonneg g 2 3
      have z30 := cellMass_nonneg g 3 0
      have z31 := cellMass_nonneg g 3 1
      have z32 := cellMass_nonneg g 3 2
      have z33 := cellMass_nonneg g 3 3
      first
      | (simp (disch := decide) only [k1, k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1, k2] at e; linarith))

theorem caseCOI (hA0 : g.cellMass 0 0 = 0) (hD0 : g.cellMass 0 3 = 0) (hM0 : g.cellMass 3 0 = 0)
    (hP0 : g.cellMass 3 3 = 0) {q1 q2 q3 : Plane}
    (hq1c : q1 ∈ g.cell 0 2) (hq2c : q2 ∈ g.cell 3 2) (hq3c : q3 ∈ g.cell 2 0)
    (hz1 : ∀ x ∈ g.cellVotes 0 1 ∪ g.cellVotes 0 2, q1.2 ≤ x.2) (hz2 : ∀ x ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2, x.2 ≤ q2.2)
    (hz3 : ∀ x ∈ g.cellVotes 1 0 ∪ g.cellVotes 2 0, x.1 ≤ q3.1)
    {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) (n1 : q1 ∉ R) (n2 : q2 ∉ R)
    (n3 : q3 ∉ R) : mass V R ≤ 1 / 2 := by
  have o1 := optC g hR hp n1 hq1c hz1
  have o2 := optO g hR hp n2 hq2c hz2
  have o3 := optI g hR hp n3 hq3c hz3
  rcases o1 with k1 | k1 <;> rcases o2 with k2 | k2 <;> rcases o3 with k3 | k3 <;> (focus
      have e := mass_eq_sum_cells g R
      simp only [Fin.sum_univ_four] at e
      have rw0 := cellMass_row g 0
      have rw1 := cellMass_row g 1
      have rw2 := cellMass_row g 2
      have rw3 := cellMass_row g 3
      have cl0 := cellMass_col g 0
      have cl1 := cellMass_col g 1
      have cl2 := cellMass_col g 2
      have cl3 := cellMass_col g 3
      simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
      have c00 := mass_inter_cell_le g R 0 0
      have c01 := mass_inter_cell_le g R 0 1
      have c02 := mass_inter_cell_le g R 0 2
      have c03 := mass_inter_cell_le g R 0 3
      have c10 := mass_inter_cell_le g R 1 0
      have c11 := mass_inter_cell_le g R 1 1
      have c12 := mass_inter_cell_le g R 1 2
      have c13 := mass_inter_cell_le g R 1 3
      have c20 := mass_inter_cell_le g R 2 0
      have c21 := mass_inter_cell_le g R 2 1
      have c22 := mass_inter_cell_le g R 2 2
      have c23 := mass_inter_cell_le g R 2 3
      have c30 := mass_inter_cell_le g R 3 0
      have c31 := mass_inter_cell_le g R 3 1
      have c32 := mass_inter_cell_le g R 3 2
      have c33 := mass_inter_cell_le g R 3 3
      have z00 := cellMass_nonneg g 0 0
      have z01 := cellMass_nonneg g 0 1
      have z02 := cellMass_nonneg g 0 2
      have z03 := cellMass_nonneg g 0 3
      have z10 := cellMass_nonneg g 1 0
      have z11 := cellMass_nonneg g 1 1
      have z12 := cellMass_nonneg g 1 2
      have z13 := cellMass_nonneg g 1 3
      have z20 := cellMass_nonneg g 2 0
      have z21 := cellMass_nonneg g 2 1
      have z22 := cellMass_nonneg g 2 2
      have z23 := cellMass_nonneg g 2 3
      have z30 := cellMass_nonneg g 3 0
      have z31 := cellMass_nonneg g 3 1
      have z32 := cellMass_nonneg g 3 2
      have z33 := cellMass_nonneg g 3 3
      first
      | (simp (disch := decide) only [k1, k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1, k2] at e; linarith))

end PlanarMetricElections.Peer.Dev.EmptyCenter

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev PlanarMetricElections.Peer.Dev.EmptyCenter in
theorem chk_empty_center (V : Finset Plane) (g : QuartileGrid V)
    (hF : g.cellMass 1 1 = 0) (hG : g.cellMass 1 2 = 0)
    (hJ : g.cellMass 2 1 = 0) (hK : g.cellMass 2 2 = 0) :
    ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2) := by
  have rw0 := cellMass_row g 0
  have rw1 := cellMass_row g 1
  have rw2 := cellMass_row g 2
  have rw3 := cellMass_row g 3
  have cl0 := cellMass_col g 0
  have cl1 := cellMass_col g 1
  have cl2 := cellMass_col g 2
  have cl3 := cellMass_col g 3
  simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
  have z10 := cellMass_nonneg g 1 0
  have z13 := cellMass_nonneg g 1 3
  have z20 := cellMass_nonneg g 2 0
  have z23 := cellMass_nonneg g 2 3
  have z12 := cellMass_nonneg g 1 2
  have z00 := cellMass_nonneg g 0 0
  have z03 := cellMass_nonneg g 0 3
  have z30 := cellMass_nonneg g 3 0
  have z33 := cellMass_nonneg g 3 3
  have hA0 : g.cellMass 0 0 = 0 := by linarith
  have hD0 : g.cellMass 0 3 = 0 := by linarith
  have hM0 : g.cellMass 3 0 = 0 := by linarith
  have hP0 : g.cellMass 3 3 = 0 := by linarith
  -- the four unions
  have mN : mass V (↑(g.cellVotes 0 1 ∪ g.cellVotes 0 2) : Set Plane) = 1 / 4 := by
    rw [mass_finset_union V (cellVotes_disjoint g (by decide)), mass_cellVotes, mass_cellVotes]
    linarith
  have mS : mass V (↑(g.cellVotes 3 1 ∪ g.cellVotes 3 2) : Set Plane) = 1 / 4 := by
    rw [mass_finset_union V (cellVotes_disjoint g (by decide)), mass_cellVotes, mass_cellVotes]
    linarith
  have mE : mass V (↑(g.cellVotes 1 3 ∪ g.cellVotes 2 3) : Set Plane) = 1 / 4 := by
    rw [mass_finset_union V (cellVotes_disjoint g (by decide)), mass_cellVotes, mass_cellVotes]
    linarith
  have mW : mass V (↑(g.cellVotes 1 0 ∪ g.cellVotes 2 0) : Set Plane) = 1 / 4 := by
    rw [mass_finset_union V (cellVotes_disjoint g (by decide)), mass_cellVotes, mass_cellVotes]
    linarith
  obtain ⟨q1, hq1N, hz1⟩ := exists_southmost _ (nonempty_of_mass_pos _ (by rw [mN]; norm_num))
  obtain ⟨q2, hq2S, hz2⟩ := exists_northmost _ (nonempty_of_mass_pos _ (by rw [mS]; norm_num))
  have hq1V : q1 ∈ V := by
    rcases Finset.mem_union.1 hq1N with h | h
    · exact cellVotes_subset g _ _ h
    · exact cellVotes_subset g _ _ h
  have hq2V : q2 ∈ V := by
    rcases Finset.mem_union.1 hq2S with h | h
    · exact cellVotes_subset g _ _ h
    · exact cellVotes_subset g _ _ h
  -- generic reduction: set up the rectangle
  have key : ∀ (Q : Finset Plane), Q ⊆ V → Q.card ≤ 3 →
      (∀ R : Set Plane, IsRectangle R → Disjoint R (↑Q : Set Plane) → g.middle ∈ R →
        mass V R ≤ 1 / 2) → ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2) := by
    intro Q h1 h2 h3
    refine ⟨Q, isStrongRectNet_of_le h1 h2 ?_⟩
    intro R hR hd
    by_cases hp : g.middle ∈ R
    · exact h3 R hR hd hp
    · exact safe_of_not_mem_middle g hR hp
  have hnot : ∀ {q : Plane} {Q : Finset Plane} {R : Set Plane}, Disjoint R (↑Q : Set Plane) →
      q ∈ Q → q ∉ R := fun hd hq => Set.disjoint_right.mp hd (by simpa using hq)
  rcases Finset.mem_union.1 hq1N with hq1B | hq1C <;>
  rcases Finset.mem_union.1 hq2S with hq2N | hq2O
  · have hq1c := ((mem_cellVotes g _ _ _).1 hq1B).2
    have hq2c := ((mem_cellVotes g _ _ _).1 hq2N).2
    obtain ⟨q3, hq3E, hz3⟩ := exists_westmost _ (nonempty_of_mass_pos _ (by rw [mE]; norm_num))
    have hq3V : q3 ∈ V := by
      rcases Finset.mem_union.1 hq3E with h | h
      · exact cellVotes_subset g _ _ h
      · exact cellVotes_subset g _ _ h
    refine key {q1, q2, q3} ?_ Finset.card_le_three ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    intro R hR hd hp
    rcases Finset.mem_union.1 hq3E with hq3H | hq3L
    · exact caseBNH g hA0 hD0 hM0 hP0 hq1c hq2c ((mem_cellVotes g _ _ _).1 hq3H).2 hz1 hz2 hz3 hR hp
        (hnot hd (by simp)) (hnot hd (by simp)) (hnot hd (by simp))
    · exact caseBNL g hA0 hD0 hM0 hP0 hq1c hq2c ((mem_cellVotes g _ _ _).1 hq3L).2 hz1 hz2 hz3 hR hp
        (hnot hd (by simp)) (hnot hd (by simp)) (hnot hd (by simp))
  · have hq1c := ((mem_cellVotes g _ _ _).1 hq1B).2
    have hq2c := ((mem_cellVotes g _ _ _).1 hq2O).2
    refine key {q1, q2} ?_ (le_trans Finset.card_le_two (by norm_num)) ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    intro R hR hd hp
    exact caseBO g hA0 hD0 hM0 hP0 hq1c hq2c hz1 hz2 hR hp (hnot hd (by simp)) (hnot hd (by simp))
  · have hq1c := ((mem_cellVotes g _ _ _).1 hq1C).2
    have hq2c := ((mem_cellVotes g _ _ _).1 hq2N).2
    refine key {q1, q2} ?_ (le_trans Finset.card_le_two (by norm_num)) ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    intro R hR hd hp
    exact caseCN g hA0 hD0 hM0 hP0 hq1c hq2c hz1 hz2 hR hp (hnot hd (by simp)) (hnot hd (by simp))
  · have hq1c := ((mem_cellVotes g _ _ _).1 hq1C).2
    have hq2c := ((mem_cellVotes g _ _ _).1 hq2O).2
    obtain ⟨q3, hq3E, hz3⟩ := exists_eastmost _ (nonempty_of_mass_pos _ (by rw [mW]; norm_num))
    have hq3V : q3 ∈ V := by
      rcases Finset.mem_union.1 hq3E with h | h
      · exact cellVotes_subset g _ _ h
      · exact cellVotes_subset g _ _ h
    refine key {q1, q2, q3} ?_ Finset.card_le_three ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    intro R hR hd hp
    rcases Finset.mem_union.1 hq3E with hq3H | hq3L
    · exact caseCOE g hA0 hD0 hM0 hP0 hq1c hq2c ((mem_cellVotes g _ _ _).1 hq3H).2 hz1 hz2 hz3 hR hp
        (hnot hd (by simp)) (hnot hd (by simp)) (hnot hd (by simp))
    · exact caseCOI g hA0 hD0 hM0 hP0 hq1c hq2c ((mem_cellVotes g _ _ _).1 hq3L).2 hz1 hz2 hz3 hR hp
        (hnot hd (by simp)) (hnot hd (by simp)) (hnot hd (by simp))
end PlanarMetricElections.Peer
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_empty_center := @PlanarMetricElections.Peer.chk_empty_center
