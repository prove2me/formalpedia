-- Prove2me | solution 1 for PlanarMetricElections.Peer.large_northwest_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:42.919545+00:00
-- url     : https://prove2.me/submissions/b16d11e0-bf5a-4f35-bdcc-0c244d44c8b1

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid
import Definitions.Def_PlanarMetricElections_Peer_ExtremePoints
import Definitions.Def_PlanarMetricElections_Peer_RectangularNet
import Definitions.Def_PlanarMetricElections_Peer_Mass
import Theorems.Thm_PlanarMetricElections_Peer_split_point

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

end PlanarMetricElections.Peer.Dev
end
end

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev
open PlanarMetricElections.Peer

/-- southeast split (the published Lemma A.1) -/
theorem split_SE (V X : Finset Plane) (hXV : X ⊆ V) (hX : X.Nonempty) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ mass V (↑X : Set Plane)) :
    ∃ z ∈ X, mass V ((↑X : Set Plane) ∩ {v | z.1 < v.1}) ≤ mass V (↑X : Set Plane) - a ∧
      mass V ((↑X : Set Plane) ∩ {v | v.2 < z.2}) ≤ mass V (↑X : Set Plane) - b :=
  PlanarMetricElections.Peer.split_point V X hXV hX a b ha hb hab

theorem mass_reflect (φ : Plane → Plane) (hφ : Function.Involutive φ) (V X : Finset Plane)
    (T : Set Plane) :
    mass (V.image φ) ((↑(X.image φ) : Set Plane) ∩ T) = mass V (↑X ∩ φ ⁻¹' T) := by
  unfold mass
  have hinj : Function.Injective φ := hφ.injective
  rw [Finset.card_image_of_injective _ hinj]
  have : (V.image φ).filter (fun v => v ∈ (↑(X.image φ) : Set Plane) ∩ T)
      = (V.filter (fun v => v ∈ (↑X : Set Plane) ∩ φ ⁻¹' T)).image φ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, Set.mem_inter_iff, Finset.coe_image,
      Set.mem_image, Finset.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, ⟨x, hx, hxv⟩, hT⟩
      have : x = v := hinj hxv
      subst this
      exact ⟨x, ⟨hv, hx, hT⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hx, hT⟩, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, ⟨v, hx, rfl⟩, hT⟩
  have hc := congrArg Finset.card this
  rw [Finset.card_image_of_injective _ hinj] at hc
  congr 2
  convert hc

theorem mass_reflect_self (φ : Plane → Plane) (hφ : Function.Involutive φ) (V X : Finset Plane) :
    mass (V.image φ) (↑(X.image φ) : Set Plane) = mass V (↑X : Set Plane) := by
  have := mass_reflect φ hφ V X Set.univ
  simpa using this

theorem split_NE (V X : Finset Plane) (hXV : X ⊆ V) (hX : X.Nonempty) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ mass V (↑X : Set Plane)) :
    ∃ z ∈ X, mass V ((↑X : Set Plane) ∩ {v | z.1 < v.1}) ≤ mass V (↑X : Set Plane) - a ∧
      mass V ((↑X : Set Plane) ∩ {v | z.2 < v.2}) ≤ mass V (↑X : Set Plane) - b := by
  let φ : Plane → Plane := fun x => (x.1, -x.2)
  have hφ : Function.Involutive φ := fun x => by simp [φ]
  have hX' : (X.image φ).Nonempty := hX.image _
  have hsub : X.image φ ⊆ V.image φ := Finset.image_subset_image hXV
  rw [← mass_reflect_self φ hφ V X] at hab
  obtain ⟨z', hz', h1, h2⟩ := split_SE (V.image φ) (X.image φ) hsub hX' a b ha hb hab
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
  rw [mass_reflect φ hφ, mass_reflect_self φ hφ] at h1 h2
  refine ⟨z, hz, ?_, ?_⟩
  · convert h1 using 3 <;> ext v <;> simp [φ]
  · convert h2 using 3 <;> ext v <;> simp [φ]

theorem split_SW (V X : Finset Plane) (hXV : X ⊆ V) (hX : X.Nonempty) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ mass V (↑X : Set Plane)) :
    ∃ z ∈ X, mass V ((↑X : Set Plane) ∩ {v | v.1 < z.1}) ≤ mass V (↑X : Set Plane) - a ∧
      mass V ((↑X : Set Plane) ∩ {v | v.2 < z.2}) ≤ mass V (↑X : Set Plane) - b := by
  let φ : Plane → Plane := fun x => (-x.1, x.2)
  have hφ : Function.Involutive φ := fun x => by simp [φ]
  have hX' : (X.image φ).Nonempty := hX.image _
  have hsub : X.image φ ⊆ V.image φ := Finset.image_subset_image hXV
  rw [← mass_reflect_self φ hφ V X] at hab
  obtain ⟨z', hz', h1, h2⟩ := split_SE (V.image φ) (X.image φ) hsub hX' a b ha hb hab
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
  rw [mass_reflect φ hφ, mass_reflect_self φ hφ] at h1 h2
  refine ⟨z, hz, ?_, ?_⟩
  · convert h1 using 3 <;> ext v <;> simp [φ]
  · convert h2 using 3 <;> ext v <;> simp [φ]

end PlanarMetricElections.Peer.Dev
end
end

section
set_option autoImplicit false
open scoped Classical
namespace PlanarMetricElections.Peer.Dev.LargeNW
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



theorem split_bound {V : Finset Plane} {R T : Set Plane} {X : Finset Plane} {c : ℝ}
    (hR : R ⊆ T) (h : mass V (↑X ∩ T) ≤ c) : mass V (R ∩ ↑X) ≤ c :=
  le_trans (mass_mono V (by
    intro x hx; exact ⟨hx.2, hR hx.1⟩)) h

theorem sum_two {V : Finset Plane} (g : QuartileGrid V) (R : Set Plane) {i j i' j' : Fin 4}
    (h : (i, j) ≠ (i', j')) :
    mass V (R ∩ g.cell i j) + mass V (R ∩ g.cell i' j') =
      mass V (R ∩ ↑(g.cellVotes i j ∪ g.cellVotes i' j')) := by
  rw [cell_eq, cell_eq, ← mass_union]
  · congr 1
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Finset.coe_union]
    tauto
  · exact Set.disjoint_left.2 fun x hx hy =>
      Finset.disjoint_left.1 (cellVotes_disjoint g h) hx.2 hy.2

variable {V : Finset Plane} (g : QuartileGrid V)




theorem optF {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqc : q ∈ g.cell 1 1) {c : ℝ} (hs1 : mass V (↑(g.cellVotes 1 1) ∩ {v | q.1 < v.1}) ≤ c)
    (hs2 : mass V (↑(g.cellVotes 1 1) ∩ {v | v.2 < q.2}) ≤ c) :
    ((∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∧ mass V (R ∩ g.cell 1 1) ≤ c) ∨
    ((∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) ∧ mass V (R ∩ g.cell 1 1) ≤ c) := by
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exact Or.inl ⟨k, by rw [cell_eq]; exact split_bound h hs1⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inr ⟨k, by rw [cell_eq]; exact split_bound h hs2⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])

/-- point of `H ∪ L` (southwest split): `west`/`south` bounds -/
theorem optX {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    {i0 : Fin 4} (hqc : q ∈ g.cell i0 3) (hi : i0 = 1 ∨ i0 = 2) {c : ℝ}
    (hs1 : mass V (↑(g.cellVotes 1 3 ∪ g.cellVotes 2 3) ∩ {v | v.1 < q.1}) ≤ c)
    (hs2 : mass V (↑(g.cellVotes 1 3 ∪ g.cellVotes 2 3) ∩ {v | v.2 < q.2}) ≤ c) :
    (mass V (R ∩ g.cell 1 3) + mass V (R ∩ g.cell 2 3) ≤ c) ∨
    ((∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) ∧
      mass V (R ∩ g.cell 1 3) + mass V (R ∩ g.cell 2 3) ≤ c) ∨
    (∀ i j : Fin 4, 2 < i → mass V (R ∩ g.cell i j) = 0) := by
  rw [sum_two g R (by decide)]
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inl (split_bound h hs1)
  · rcases hi with rfl | rfl
    · exact Or.inr (Or.inl ⟨k, split_bound h hs2⟩)
    · exfalso; (focus
        have hh := h hp
        simp only [Set.mem_ofPred_eq] at hh
        first
        | linarith [cell_x_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_x g hqc (by decide)]
        | linarith [cell_y_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_y g hqc (by decide)])
  · rcases hi with rfl | rfl
    · exfalso; (focus
        have hh := h hp
        simp only [Set.mem_ofPred_eq] at hh
        first
        | linarith [cell_x_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_x g hqc (by decide)]
        | linarith [cell_y_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_y g hqc (by decide)])
    · exact Or.inr (Or.inr k)

/-- point of `N ∪ O` (northeast split): `east`/`north` bounds -/
theorem optY {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    {j0 : Fin 4} (hqc : q ∈ g.cell 3 j0) (hj : j0 = 1 ∨ j0 = 2) {c : ℝ}
    (hs1 : mass V (↑(g.cellVotes 3 1 ∪ g.cellVotes 3 2) ∩ {v | q.1 < v.1}) ≤ c)
    (hs2 : mass V (↑(g.cellVotes 3 1 ∪ g.cellVotes 3 2) ∩ {v | q.2 < v.2}) ≤ c) :
    ((∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∧
      mass V (R ∩ g.cell 3 1) + mass V (R ∩ g.cell 3 2) ≤ c) ∨
    (mass V (R ∩ g.cell 3 1) + mass V (R ∩ g.cell 3 2) ≤ c) ∨
    (∀ i j : Fin 4, 2 < j → mass V (R ∩ g.cell i j) = 0) := by
  rw [sum_two g R (by decide)]
  rcases opt4 g hR hq hqc with ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩ | ⟨h, k⟩
  · rcases hj with rfl | rfl
    · exact Or.inl ⟨k, split_bound h hs1⟩
    · exfalso; (focus
        have hh := h hp
        simp only [Set.mem_ofPred_eq] at hh
        first
        | linarith [cell_x_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_x g hqc (by decide)]
        | linarith [cell_y_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_y g hqc (by decide)])
  · rcases hj with rfl | rfl
    · exfalso; (focus
        have hh := h hp
        simp only [Set.mem_ofPred_eq] at hh
        first
        | linarith [cell_x_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_x g hqc (by decide)]
        | linarith [cell_y_lt_middle g hqc (by decide)]
        | linarith [middle_lt_cell_y g hqc (by decide)])
    · exact Or.inr (Or.inr k)
  · exfalso; (focus
      have hh := h hp
      simp only [Set.mem_ofPred_eq] at hh
      first
      | linarith [cell_x_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_x g hqc (by decide)]
      | linarith [cell_y_lt_middle g hqc (by decide)]
      | linarith [middle_lt_cell_y g hqc (by decide)])
  · exact Or.inr (Or.inl (split_bound h hs2))

theorem core {R : Set Plane}
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 1 2 + g.cellMass 2 1 + g.cellMass 1 1 / 2 < g.cellMass 0 0)
    (o1 : ((∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∧
        mass V (R ∩ g.cell 1 1) ≤ g.cellMass 1 1 / 2) ∨
      ((∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) ∧
        mass V (R ∩ g.cell 1 1) ≤ g.cellMass 1 1 / 2))
    (o2 : (mass V (R ∩ g.cell 1 3) + mass V (R ∩ g.cell 2 3) ≤
        (g.cellMass 1 3 + g.cellMass 2 3) / 2) ∨
      ((∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) ∧
        mass V (R ∩ g.cell 1 3) + mass V (R ∩ g.cell 2 3) ≤
          (g.cellMass 1 3 + g.cellMass 2 3) / 2) ∨
      (∀ i j : Fin 4, 2 < i → mass V (R ∩ g.cell i j) = 0))
    (o3 : ((∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∧
        mass V (R ∩ g.cell 3 1) + mass V (R ∩ g.cell 3 2) ≤
          (g.cellMass 3 1 + g.cellMass 3 2) / 2) ∨
      (mass V (R ∩ g.cell 3 1) + mass V (R ∩ g.cell 3 2) ≤ (g.cellMass 3 1 + g.cellMass 3 2) / 2) ∨
      (∀ i j : Fin 4, 2 < j → mass V (R ∩ g.cell i j) = 0)) :
    mass V R ≤ 1 / 2 := by
  rcases o1 with ⟨k1, f1⟩ | ⟨k1, f1⟩ <;>
  rcases o2 with f2 | ⟨k2, f2⟩ | k2 <;>
  rcases o3 with ⟨k3, f3⟩ | f3 | k3 <;>
  (focus
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
      | (simp (disch := decide) only [k1, k2] at e; linarith)
      | (simp (disch := decide) only [k1, k3] at e; linarith)
      | (simp (disch := decide) only [k2, k3] at e; linarith)
      | (simp (disch := decide) only [k1] at e; linarith)
      | (simp (disch := decide) only [k2] at e; linarith)
      | (simp (disch := decide) only [k3] at e; linarith)
      | linarith)

theorem optXU {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqX : q ∈ g.cellVotes 1 3 ∪ g.cellVotes 2 3)
    (hs1 : mass V (↑(g.cellVotes 1 3 ∪ g.cellVotes 2 3) ∩ {v | v.1 < q.1}) ≤
      (g.cellMass 1 3 + g.cellMass 2 3) / 2)
    (hs2 : mass V (↑(g.cellVotes 1 3 ∪ g.cellVotes 2 3) ∩ {v | v.2 < q.2}) ≤
      (g.cellMass 1 3 + g.cellMass 2 3) / 2) :
    (mass V (R ∩ g.cell 1 3) + mass V (R ∩ g.cell 2 3) ≤
        (g.cellMass 1 3 + g.cellMass 2 3) / 2) ∨
      ((∀ i j : Fin 4, i < 1 → mass V (R ∩ g.cell i j) = 0) ∧
        mass V (R ∩ g.cell 1 3) + mass V (R ∩ g.cell 2 3) ≤
          (g.cellMass 1 3 + g.cellMass 2 3) / 2) ∨
      (∀ i j : Fin 4, 2 < i → mass V (R ∩ g.cell i j) = 0) := by
  rcases Finset.mem_union.1 hqX with h | h
  · exact optX g hR hp hq ((mem_cellVotes g _ _ _).1 h).2 (Or.inl rfl) hs1 hs2
  · exact optX g hR hp hq ((mem_cellVotes g _ _ _).1 h).2 (Or.inr rfl) hs1 hs2

theorem optYU {R : Set Plane} (hR : IsRectangle R) (hp : g.middle ∈ R) {q : Plane} (hq : q ∉ R)
    (hqY : q ∈ g.cellVotes 3 1 ∪ g.cellVotes 3 2)
    (hs1 : mass V (↑(g.cellVotes 3 1 ∪ g.cellVotes 3 2) ∩ {v | q.1 < v.1}) ≤
      (g.cellMass 3 1 + g.cellMass 3 2) / 2)
    (hs2 : mass V (↑(g.cellVotes 3 1 ∪ g.cellVotes 3 2) ∩ {v | q.2 < v.2}) ≤
      (g.cellMass 3 1 + g.cellMass 3 2) / 2) :
    ((∀ i j : Fin 4, j < 1 → mass V (R ∩ g.cell i j) = 0) ∧
        mass V (R ∩ g.cell 3 1) + mass V (R ∩ g.cell 3 2) ≤
          (g.cellMass 3 1 + g.cellMass 3 2) / 2) ∨
      (mass V (R ∩ g.cell 3 1) + mass V (R ∩ g.cell 3 2) ≤ (g.cellMass 3 1 + g.cellMass 3 2) / 2) ∨
      (∀ i j : Fin 4, 2 < j → mass V (R ∩ g.cell i j) = 0) := by
  rcases Finset.mem_union.1 hqY with h | h
  · exact optY g hR hp hq ((mem_cellVotes g _ _ _).1 h).2 (Or.inl rfl) hs1 hs2
  · exact optY g hR hp hq ((mem_cellVotes g _ _ _).1 h).2 (Or.inr rfl) hs1 hs2

end PlanarMetricElections.Peer.Dev.LargeNW

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev PlanarMetricElections.Peer.Dev.LargeNW in
theorem chk_large_northwest_corner (V : Finset Plane) (g : QuartileGrid V)
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 1 2 + g.cellMass 2 1 + g.cellMass 1 1 / 2 < g.cellMass 0 0) :
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
  have z01 := cellMass_nonneg g 0 1
  have z02 := cellMass_nonneg g 0 2
  have z03 := cellMass_nonneg g 0 3
  have z10 := cellMass_nonneg g 1 0
  have z12 := cellMass_nonneg g 1 2
  have z13 := cellMass_nonneg g 1 3
  have z20 := cellMass_nonneg g 2 0
  have z21 := cellMass_nonneg g 2 1
  have z23 := cellMass_nonneg g 2 3
  have z30 := cellMass_nonneg g 3 0
  have z31 := cellMass_nonneg g 3 1
  have z32 := cellMass_nonneg g 3 2
  have z33 := cellMass_nonneg g 3 3
  have hFne := nonempty_of_mass_pos _ (by rw [mass_cellVotes]; exact hF)
  have mX : mass V (↑(g.cellVotes 1 3 ∪ g.cellVotes 2 3) : Set Plane) =
      g.cellMass 1 3 + g.cellMass 2 3 := by
    rw [mass_finset_union V (cellVotes_disjoint g (by decide)), mass_cellVotes, mass_cellVotes]
  have mY : mass V (↑(g.cellVotes 3 1 ∪ g.cellVotes 3 2) : Set Plane) =
      g.cellMass 3 1 + g.cellMass 3 2 := by
    rw [mass_finset_union V (cellVotes_disjoint g (by decide)), mass_cellVotes, mass_cellVotes]
  have hXne := nonempty_of_mass_pos (g.cellVotes 1 3 ∪ g.cellVotes 2 3)
    (by rw [mX]; linarith)
  have hYne := nonempty_of_mass_pos (g.cellVotes 3 1 ∪ g.cellVotes 3 2)
    (by rw [mY]; linarith)
  have hXV : (g.cellVotes 1 3 ∪ g.cellVotes 2 3) ⊆ V :=
    Finset.union_subset (cellVotes_subset g _ _) (cellVotes_subset g _ _)
  have hYV : (g.cellVotes 3 1 ∪ g.cellVotes 3 2) ⊆ V :=
    Finset.union_subset (cellVotes_subset g _ _) (cellVotes_subset g _ _)
  obtain ⟨q1, hq1F, hs1, hs2⟩ := split_SE V (g.cellVotes 1 1) (cellVotes_subset g 1 1) hFne
    (g.cellMass 1 1 / 2) (g.cellMass 1 1 / 2) (by linarith) (by linarith)
    (by rw [mass_cellVotes]; linarith)
  rw [mass_cellVotes] at hs1 hs2
  obtain ⟨q2, hq2X, hs3, hs4⟩ := split_SW V _ hXV hXne
    ((g.cellMass 1 3 + g.cellMass 2 3) / 2) ((g.cellMass 1 3 + g.cellMass 2 3) / 2)
    (by linarith) (by linarith) (by rw [mX]; linarith)
  obtain ⟨q3, hq3Y, hs5, hs6⟩ := split_NE V _ hYV hYne
    ((g.cellMass 3 1 + g.cellMass 3 2) / 2) ((g.cellMass 3 1 + g.cellMass 3 2) / 2)
    (by linarith) (by linarith) (by rw [mY]; linarith)
  rw [mX] at hs3 hs4
  rw [mY] at hs5 hs6
  have hq1c := ((mem_cellVotes g _ _ _).1 hq1F).2
  have hq1V := cellVotes_subset g _ _ hq1F
  have hq2V := hXV hq2X
  have hq3V := hYV hq3Y
  refine ⟨{q1, q2, q3}, ?_⟩
  apply isStrongRectNet_of_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · exact Finset.card_le_three
  intro R hR hd
  by_cases hp : g.middle ∈ R
  swap
  · exact safe_of_not_mem_middle g hR hp
  have n1 : q1 ∉ R := Set.disjoint_right.mp hd (by simp)
  have n2 : q2 ∉ R := Set.disjoint_right.mp hd (by simp)
  have n3 : q3 ∉ R := Set.disjoint_right.mp hd (by simp)
  have o1 := optF g hR hp n1 hq1c (c := g.cellMass 1 1 / 2) (by linarith) (by linarith)
  have o2 := optXU g hR hp n2 hq2X (by linarith) (by linarith)
  have o3 := optYU g hR hp n3 hq3Y (by linarith) (by linarith)
  exact core g hK hF hA o1 o2 o3
end PlanarMetricElections.Peer
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_large_northwest_corner := @PlanarMetricElections.Peer.chk_large_northwest_corner
