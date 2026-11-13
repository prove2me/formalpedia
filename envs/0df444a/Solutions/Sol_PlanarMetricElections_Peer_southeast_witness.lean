-- Prove2me | solution 1 for PlanarMetricElections.Peer.southeast_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:24:24.43038+00:00
-- url     : https://prove2.me/submissions/ed5bb584-125e-49e3-984b-e371bf3db488

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
theorem kill_south {R : Set Plane} {q : Plane} {i0 j0 : Fin 4} (hq : q ∈ g.cell i0 j0)
    (hR : R ⊆ {x | x.2 < q.2}) (i j : Fin 4) (hi : i < i0) : mass V (R ∩ g.cell i j) = 0 := by
  apply mass_eq_zero
  intro v _ hv
  have h1 := hR hv.1
  have h2 := cell_y_gt g hv.2 hq hi
  simp only [Set.mem_setOf_eq] at h1; linarith

end Grid

/-! ## Extreme points of a finite set -/

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

end PlanarMetricElections.Peer.Dev
end
end

section
set_option autoImplicit false
open scoped Classical
namespace PlanarMetricElections.Peer.Dev.SoutheastWitness
open PlanarMetricElections.Peer PlanarMetricElections.Peer.Dev

theorem cell_eq {V : Finset Plane} (g : QuartileGrid V) (S : Set Plane) (i j : Fin 4) :
    mass V (S ∩ g.cell i j) = mass V (S ∩ ↑(g.cellVotes i j)) := by
  unfold mass
  congr 3
  ext v
  simp only [Finset.mem_filter, Set.mem_inter_iff, Finset.mem_coe, QuartileGrid.cellVotes]
  tauto

theorem nonempty_of_pos {V : Finset Plane} (g : QuartileGrid V) (i j : Fin 4)
    (h : 0 < g.cellMass i j) : (g.cellVotes i j).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have := mass_cellVotes g i j
  rw [he] at this
  simp [mass_empty] at this
  linarith

/-- disjoint sets share a cell's mass -/
theorem pair_le {V : Finset Plane} (g : QuartileGrid V) {R Z : Set Plane} (h : Disjoint R Z)
    (i j : Fin 4) :
    mass V (R ∩ g.cell i j) + mass V (Z ∩ g.cell i j) ≤ g.cellMass i j := by
  rw [← mass_union V (Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left h)]
  exact mass_mono V (fun x hx => by rcases hx with hx | hx <;> exact hx.2) |>.trans
    (by unfold QuartileGrid.cellMass; exact le_refl _)

theorem zero_of_disj {V : Finset Plane} (g : QuartileGrid V) {Z T : Set Plane} (h : Disjoint Z T)
    {i j : Fin 4} (hc : g.cell i j ⊆ T) : mass V (Z ∩ g.cell i j) = 0 :=
  mass_eq_zero V (fun v _ hv => Set.disjoint_left.1 h hv.1 (hc hv.2))

/-- the final linear step -/
theorem final {V : Finset Plane} (g : QuartileGrid V) {R Z : Set Plane} (hRZ : Disjoint R Z)
    (hZrow : Disjoint Z (rowBand g.yCut 0)) (hZcol : Disjoint Z (columnBand g.xCut 0))
    (hZF : Disjoint Z (g.cell 1 1)) (hZm : g.tau ≤ mass V Z)
    (hc : ((∀ i, mass V (R ∩ g.cell i 0) = 0) ∧ mass V (R ∩ g.cell 1 1) = 0) ∨
          ((∀ j, mass V (R ∩ g.cell 0 j) = 0) ∧ mass V (R ∩ g.cell 1 1) = 0) ∨
          ((∀ j, mass V (R ∩ g.cell 0 j) = 0) ∧ (∀ i, mass V (R ∩ g.cell i 0) = 0))) :
    mass V R ≤ 1 / 2 := by
  have z0 : ∀ j, mass V (Z ∩ g.cell 0 j) = 0 := fun j =>
    zero_of_disj g hZrow (fun x hx => hx.1)
  have zc : ∀ i, mass V (Z ∩ g.cell i 0) = 0 := fun i =>
    zero_of_disj g hZcol (fun x hx => hx.2)
  have zF : mass V (Z ∩ g.cell 1 1) = 0 := zero_of_disj g hZF subset_rfl
  have eR := mass_eq_sum_cells g R
  have eZ := mass_eq_sum_cells g Z
  simp only [Fin.sum_univ_four] at eR eZ
  have rw0 := cellMass_row g 0
  have rw1 := cellMass_row g 1
  have rw2 := cellMass_row g 2
  have rw3 := cellMass_row g 3
  have cl0 := cellMass_col g 0
  have cl1 := cellMass_col g 1
  have cl2 := cellMass_col g 2
  have cl3 := cellMass_col g 3
  simp only [Fin.sum_univ_four] at rw0 rw1 rw2 rw3 cl0 cl1 cl2 cl3
  have hA : g.cellMass 0 0 ≤ g.tau := le_max_left _ _
  have hB : 1 / 4 - g.cellMass 1 1 ≤ g.tau := le_max_right _ _
  have p00 := pair_le g hRZ 0 0
  have p01 := pair_le g hRZ 0 1
  have p02 := pair_le g hRZ 0 2
  have p03 := pair_le g hRZ 0 3
  have p10 := pair_le g hRZ 1 0
  have p11 := pair_le g hRZ 1 1
  have p12 := pair_le g hRZ 1 2
  have p13 := pair_le g hRZ 1 3
  have p20 := pair_le g hRZ 2 0
  have p21 := pair_le g hRZ 2 1
  have p22 := pair_le g hRZ 2 2
  have p23 := pair_le g hRZ 2 3
  have p30 := pair_le g hRZ 3 0
  have p31 := pair_le g hRZ 3 1
  have p32 := pair_le g hRZ 3 2
  have p33 := pair_le g hRZ 3 3
  have n00 := mass_nonneg V (Z ∩ g.cell 0 0)
  have n01 := mass_nonneg V (Z ∩ g.cell 0 1)
  have n02 := mass_nonneg V (Z ∩ g.cell 0 2)
  have n03 := mass_nonneg V (Z ∩ g.cell 0 3)
  have n10 := mass_nonneg V (Z ∩ g.cell 1 0)
  have n11 := mass_nonneg V (Z ∩ g.cell 1 1)
  have n12 := mass_nonneg V (Z ∩ g.cell 1 2)
  have n13 := mass_nonneg V (Z ∩ g.cell 1 3)
  have n20 := mass_nonneg V (Z ∩ g.cell 2 0)
  have n21 := mass_nonneg V (Z ∩ g.cell 2 1)
  have n22 := mass_nonneg V (Z ∩ g.cell 2 2)
  have n23 := mass_nonneg V (Z ∩ g.cell 2 3)
  have n30 := mass_nonneg V (Z ∩ g.cell 3 0)
  have n31 := mass_nonneg V (Z ∩ g.cell 3 1)
  have n32 := mass_nonneg V (Z ∩ g.cell 3 2)
  have n33 := mass_nonneg V (Z ∩ g.cell 3 3)
  have m00 := mass_nonneg V (R ∩ g.cell 0 0)
  have m01 := mass_nonneg V (R ∩ g.cell 0 1)
  have m02 := mass_nonneg V (R ∩ g.cell 0 2)
  have m03 := mass_nonneg V (R ∩ g.cell 0 3)
  have m10 := mass_nonneg V (R ∩ g.cell 1 0)
  have m11 := mass_nonneg V (R ∩ g.cell 1 1)
  have m12 := mass_nonneg V (R ∩ g.cell 1 2)
  have m13 := mass_nonneg V (R ∩ g.cell 1 3)
  have m20 := mass_nonneg V (R ∩ g.cell 2 0)
  have m21 := mass_nonneg V (R ∩ g.cell 2 1)
  have m22 := mass_nonneg V (R ∩ g.cell 2 2)
  have m23 := mass_nonneg V (R ∩ g.cell 2 3)
  have m30 := mass_nonneg V (R ∩ g.cell 3 0)
  have m31 := mass_nonneg V (R ∩ g.cell 3 1)
  have m32 := mass_nonneg V (R ∩ g.cell 3 2)
  have m33 := mass_nonneg V (R ∩ g.cell 3 3)
  have z00 := z0 0
  have z01 := z0 1
  have z02 := z0 2
  have z03 := z0 3
  have y10 := zc 1
  have y20 := zc 2
  have y30 := zc 3
  rcases hc with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · have := k1 0; have := k1 1; have := k1 2; have := k1 3
    linarith
  · have := k1 0; have := k1 1; have := k1 2; have := k1 3
    linarith
  · have := k1 0; have := k1 1; have := k1 2; have := k1 3
    have := k2 0; have := k2 1; have := k2 2; have := k2 3
    linarith

end PlanarMetricElections.Peer.Dev.SoutheastWitness

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev PlanarMetricElections.Peer.Dev.SoutheastWitness in
theorem chk_southeast_witness (V : Finset Plane) (g : QuartileGrid V)
    (hG : g.cellMass 1 2 = 0) (hJ : g.cellMass 2 1 = 0)
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 0 0 ≤ g.cellMass 1 1 / 2)
    (q3 : Plane) (hq : q3 ∈ V)
    (hEast : g.middle.1 < q3.1) (hSouth : q3.2 < g.middle.2)
    (ZE ZS : Finset Plane) (hZE : ZE ⊆ V) (hZS : ZS ⊆ V)
    (hZErow : Disjoint (↑ZE : Set Plane) (rowBand g.yCut 0))
    (hZEcol : Disjoint (↑ZE : Set Plane) (columnBand g.xCut 0))
    (hZEF : Disjoint (↑ZE : Set Plane) (g.cell 1 1))
    (hZSrow : Disjoint (↑ZS : Set Plane) (rowBand g.yCut 0))
    (hZScol : Disjoint (↑ZS : Set Plane) (columnBand g.xCut 0))
    (hZSF : Disjoint (↑ZS : Set Plane) (g.cell 1 1))
    (hZEEast : ∀ z ∈ ZE, q3.1 ≤ z.1) (hZSSouth : ∀ z ∈ ZS, z.2 ≤ q3.2)
    (hZEmass : g.tau ≤ mass V (↑ZE : Set Plane))
    (hZSmass : g.tau ≤ mass V (↑ZS : Set Plane)) :
    IsStrongRectNet V {eastPoint (g.cellVotes 1 1), southPoint (g.cellVotes 1 1), q3}
      3 (1 / 2) := by
  have hFne := nonempty_of_pos g 1 1 hF
  obtain ⟨q1V, hq1E⟩ := eastPoint_spec _ hFne
  obtain ⟨q2V, hq2S⟩ := southPoint_spec _ hFne
  set q1 := eastPoint (g.cellVotes 1 1) with hq1def
  set q2 := southPoint (g.cellVotes 1 1) with hq2def
  have hq1c := ((mem_cellVotes g 1 1 q1).1 q1V).2
  have hq2c := ((mem_cellVotes g 1 1 q2).1 q2V).2
  apply isStrongRectNet_of_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact cellVotes_subset g 1 1 q1V
    · exact cellVotes_subset g 1 1 q2V
    · exact hq
  · exact Finset.card_le_three
  intro R hR hdisj
  by_cases hp : g.middle ∈ R
  swap
  · exact safe_of_not_mem_middle g hR hp
  have n1 : q1 ∉ R := Set.disjoint_right.mp hdisj (by simp)
  have n2 : q2 ∉ R := Set.disjoint_right.mp hdisj (by simp)
  have n3 : q3 ∉ R := Set.disjoint_right.mp hdisj (by simp)
  have a1 := cell_x_lt_middle g hq1c (by decide)
  have b1 := middle_lt_cell_y g hq1c (by decide)
  have a2 := cell_x_lt_middle g hq2c (by decide)
  have b2 := middle_lt_cell_y g hq2c (by decide)
  have o1 : ((∀ i, mass V (R ∩ g.cell i 0) = 0) ∧ mass V (R ∩ g.cell 1 1) = 0) ∨
      ((∀ j, mass V (R ∩ g.cell 0 j) = 0) ∧ R ⊆ {x | x.2 < q1.2}) := by
    rcases rect_avoid hR n1 with h | h | h | h
    · exfalso; have := h hp; simp only [Set.mem_ofPred_eq] at this; linarith
    · left
      refine ⟨fun i => kill_east g hq1c h i 0 (by decide), ?_⟩
      rw [cell_eq]; exact mass_inter_east_extreme hq1E h
    · right
      exact ⟨fun j => kill_south g hq1c h 0 j (by decide), h⟩
    · exfalso; have := h hp; simp only [Set.mem_ofPred_eq] at this; linarith
  have o2 : ((∀ i, mass V (R ∩ g.cell i 0) = 0) ∧ R ⊆ {x | q2.1 < x.1}) ∨
      ((∀ j, mass V (R ∩ g.cell 0 j) = 0) ∧ mass V (R ∩ g.cell 1 1) = 0) := by
    rcases rect_avoid hR n2 with h | h | h | h
    · exfalso; have := h hp; simp only [Set.mem_ofPred_eq] at this; linarith
    · left
      exact ⟨fun i => kill_east g hq2c h i 0 (by decide), h⟩
    · right
      refine ⟨fun j => kill_south g hq2c h 0 j (by decide), ?_⟩
      rw [cell_eq]; exact mass_inter_south_extreme hq2S h
    · exfalso; have := h hp; simp only [Set.mem_ofPred_eq] at this; linarith
  have o3 : Disjoint R (↑ZE : Set Plane) ∨ Disjoint R (↑ZS : Set Plane) := by
    rcases rect_avoid hR n3 with h | h | h | h
    · left
      refine Set.disjoint_left.2 fun x hxR hxZ => ?_
      have := h hxR; simp only [Set.mem_ofPred_eq] at this
      have := hZEEast x hxZ; linarith
    · exfalso; have := h hp; simp only [Set.mem_ofPred_eq] at this; linarith
    · exfalso; have := h hp; simp only [Set.mem_ofPred_eq] at this; linarith
    · right
      refine Set.disjoint_left.2 fun x hxR hxZ => ?_
      have := h hxR; simp only [Set.mem_ofPred_eq] at this
      have := hZSSouth x hxZ; linarith
  have key : ∀ Z : Set Plane, Disjoint R Z → Disjoint Z (rowBand g.yCut 0) →
      Disjoint Z (columnBand g.xCut 0) → Disjoint Z (g.cell 1 1) → g.tau ≤ mass V Z →
      mass V R ≤ 1 / 2 := by
    intro Z h1 h2 h3 h4 h5
    apply final g h1 h2 h3 h4 h5
    rcases o1 with ⟨k1, k2⟩ | ⟨k1, _⟩
    · exact Or.inl ⟨k1, k2⟩
    · rcases o2 with ⟨k3, _⟩ | ⟨k3, k4⟩
      · exact Or.inr (Or.inr ⟨k1, k3⟩)
      · exact Or.inr (Or.inl ⟨k1, k4⟩)
  rcases o3 with h | h
  · exact key _ h hZErow hZEcol hZEF hZEmass
  · exact key _ h hZSrow hZScol hZSF hZSmass

end PlanarMetricElections.Peer
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_southeast_witness := @PlanarMetricElections.Peer.chk_southeast_witness
