-- Prove2me | solution 1 for PlanarMetricElections.Peer.rectangular_half_net
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:24:26.94419+00:00
-- url     : https://prove2.me/submissions/1563f889-a64f-4cf3-851c-9f8c38d7f64a

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid
import Definitions.Def_PlanarMetricElections_Peer_ExtremePoints
import Definitions.Def_PlanarMetricElections_Peer_RectangularNet
import Theorems.Thm_PlanarMetricElections_Peer_empty_center
import Theorems.Thm_PlanarMetricElections_Peer_four_center
import Theorems.Thm_PlanarMetricElections_Peer_opposite_center
import Theorems.Thm_PlanarMetricElections_Peer_large_northwest_corner
import Theorems.Thm_PlanarMetricElections_Peer_three_center
import Theorems.Thm_PlanarMetricElections_Peer_adjacent_center
import Theorems.Thm_PlanarMetricElections_Peer_one_center

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev
open PlanarMetricElections.Peer

/-! ## Mass -/

theorem mass_nonneg (V : Finset Plane) (X : Set Plane) : 0 ≤ mass V X := by
  unfold mass; positivity

/-! ## Rectangles and nets -/

/-- the good property: some `≤ 3` voters hit every rectangle of mass `> 1/2` -/
def Good (V : Finset Plane) : Prop := ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2)

/-! ## The grid -/

section Grid
variable {V : Finset Plane} (g : QuartileGrid V)

theorem cellMass_nonneg (i j : Fin 4) : 0 ≤ g.cellMass i j := mass_nonneg _ _

/-! kill lemmas: a rectangle on one side of `q` has no voters in the cells on the other side
of `q`'s row / column (`q` need not be a voter). -/

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

theorem cut_exists (S : Finset ℝ) (k : ℕ) (hk : k + 1 < S.card) :
    ∃ c : ℝ, c ∉ S ∧ (S.filter (· < c)).card = k + 1 := by
  set f := S.orderEmbOfFin rfl with hf
  have hk0 : k < S.card := by omega
  have hab : f ⟨k, hk0⟩ < f ⟨k+1, hk⟩ := f.strictMono (by simp [Fin.lt_def])
  set a := f ⟨k, hk0⟩
  set b := f ⟨k+1, hk⟩
  have hS : ∀ x, x ∈ S ↔ ∃ i, f i = x := by
    intro x
    have := Finset.range_orderEmbOfFin S (h := rfl)
    constructor
    · intro hx
      have : x ∈ Set.range f := by rw [hf, this]; exact hx
      exact this
    · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem S rfl i
  have key : ∀ i : Fin S.card, (f i < (a+b)/2 ↔ i.val < k+1) := by
    intro i
    constructor
    · intro h
      by_contra hn
      have : f ⟨k+1, hk⟩ ≤ f i := f.monotone (by simp [Fin.le_def]; omega)
      linarith
    · intro h
      have : f i ≤ f ⟨k, hk0⟩ := f.monotone (by simp [Fin.le_def]; omega)
      linarith
  refine ⟨(a+b)/2, ?_, ?_⟩
  · rw [hS]
    rintro ⟨i, hi⟩
    have := key i
    rw [hi] at this
    by_cases h : i.val < k+1
    · have := this.mpr h; linarith
    · have : f ⟨k+1, hk⟩ ≤ f i := f.monotone (by simp [Fin.le_def]; omega)
      rw [hi] at this; linarith
  · have : S.filter (· < (a+b)/2) = (Finset.univ.filter (fun i : Fin S.card => i.val < k+1)).image f := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hS]
      constructor
      · rintro ⟨⟨i, rfl⟩, h⟩
        exact ⟨i, (key i).mp h, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, rfl⟩, (key i).mpr hi⟩
    rw [this, Finset.card_image_of_injective _ f.injective]
    have : (Finset.univ.filter (fun i : Fin S.card => i.val < k+1)).image Fin.val = Finset.range (k+1) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
    have h2 := Finset.card_image_of_injective (Finset.univ.filter (fun i : Fin S.card => i.val < k+1)) Fin.val_injective
    rw [this, Finset.card_range] at h2
    exact h2.symm


theorem cnt_eq (f : Plane → ℝ) (W : Finset Plane) (hf : Set.InjOn f ↑W) (c : ℝ) :
    (W.filter (fun w => f w < c)).card = ((W.image f).filter (· < c)).card := by
  rw [Finset.filter_image]
  exact (Finset.card_image_of_injOn (hf.mono (by intro x hx; simp at hx ⊢; exact hx.1))).symm

theorem lt_of_cnt (f : Plane → ℝ) (W : Finset Plane) {a b : ℝ}
    (h : (W.filter (fun w => f w < a)).card < (W.filter (fun w => f w < b)).card) : a < b := by
  by_contra hn
  push Not at hn
  apply absurd h
  rw [not_lt]
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, by linarith [hw.2]⟩

theorem band_card (f : Plane → ℝ) (W : Finset Plane) {a b : ℝ} (hab : a < b)
    (ha : ∀ w ∈ W, f w ≠ a) :
    (W.filter (fun w => a < f w ∧ f w < b)).card + (W.filter (fun w => f w < a)).card
      = (W.filter (fun w => f w < b)).card := by
  have e : W.filter (fun w => f w < b) =
      W.filter (fun w => f w < a) ∪ W.filter (fun w => a < f w ∧ f w < b) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hw, h⟩
      rcases lt_or_gt_of_ne (ha w hw) with h1 | h1
      · exact Or.inl ⟨hw, h1⟩
      · exact Or.inr ⟨hw, h1, h⟩
    · rintro (⟨hw, h⟩ | ⟨hw, h1, h2⟩)
      · exact ⟨hw, by linarith⟩
      · exact ⟨hw, h2⟩
  have hd : Disjoint (W.filter (fun w => f w < a)) (W.filter (fun w => a < f w ∧ f w < b)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_filter] at h1 h2
    linarith [h1.2, h2.2.1]
  rw [e, Finset.card_union_of_disjoint hd]; ring

theorem upper_card (f : Plane → ℝ) (W : Finset Plane) {c : ℝ} (hc : ∀ w ∈ W, f w ≠ c) :
    (W.filter (fun w => c < f w)).card + (W.filter (fun w => f w < c)).card = W.card := by
  rw [add_comm]
  have := Finset.card_filter_add_card_filter_not (s := W) (fun w => f w < c)
  rw [← this]
  congr 2
  apply Finset.filter_congr
  intro w hw
  have := hc w hw
  constructor
  · intro h; exact not_lt.mpr h.le
  · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm this)

theorem cuts_exist (f : Plane → ℝ) (W : Finset Plane) (hf : Set.InjOn f ↑W) (m : ℕ) (hm : 0 < m)
    (hc : W.card = 4 * m) :
    ∃ c : Fin 3 → ℝ, StrictMono c ∧ (∀ w ∈ W, ∀ j, f w ≠ c j) ∧
      (W.filter (fun w => f w < c 0)).card = m ∧ (W.filter (fun w => f w < c 1)).card = 2 * m ∧
      (W.filter (fun w => f w < c 2)).card = 3 * m := by
  have hS : (W.image f).card = 4 * m := by
    rw [Finset.card_image_of_injOn hf, hc]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨c0, h0, k0⟩ := cut_exists (W.image f) m' (by omega)
  obtain ⟨c1, h1, k1⟩ := cut_exists (W.image f) (2 * m' + 1) (by omega)
  obtain ⟨c2, h2, k2⟩ := cut_exists (W.image f) (3 * m' + 2) (by omega)
  rw [← cnt_eq f W hf] at k0 k1 k2
  have l01 : c0 < c1 := lt_of_cnt f W (by omega)
  have l12 : c1 < c2 := lt_of_cnt f W (by omega)
  refine ⟨![c0, c1, c2], ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simpa
  · intro w hw j
    have hmem : f w ∈ W.image f := Finset.mem_image_of_mem f hw
    fin_cases j
    · intro h; exact h0 (by simpa [h] using hmem)
    · intro h; exact h1 (by simpa [h] using hmem)
    · intro h; exact h2 (by simpa [h] using hmem)
  · show (W.filter (fun w => f w < c0)).card = _
    omega
  · show (W.filter (fun w => f w < c1)).card = _
    omega
  · show (W.filter (fun w => f w < c2)).card = _
    omega

theorem mass_of_card (W : Finset Plane) (X : Set Plane) (m : ℕ) (hm : 0 < m) (hc : W.card = 4 * m)
    (h : (W.filter (fun v => v ∈ X)).card = m) : mass W X = 1 / 4 := by
  unfold mass
  rw [h, hc]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

theorem exists_grid (W : Finset Plane) (hne : W.Nonempty) (h4 : 4 ∣ W.card)
    (hx : Set.InjOn Prod.fst (↑W : Set Plane)) (hy : Set.InjOn Prod.snd (↑W : Set Plane)) :
    Nonempty (QuartileGrid W) := by
  obtain ⟨m, hmc⟩ := h4
  have hm : 0 < m := by
    have := hne.card_pos; omega
  obtain ⟨cx, mx, ax, x0, x1, x2⟩ := cuts_exist Prod.fst W hx m hm hmc
  obtain ⟨cy, my, ay, y0, y1, y2⟩ := cuts_exist Prod.snd W hy m hm hmc
  have ux0 := upper_card Prod.fst W (c := cx 2) (fun w hw => ax w hw 2)
  have uy2 := upper_card Prod.snd W (c := cy 2) (fun w hw => ay w hw 2)
  have bx1 := band_card Prod.fst W (mx (by decide : (0:Fin 3) < 1)) (fun w hw => ax w hw 0)
  have bx2 := band_card Prod.fst W (mx (by decide : (1:Fin 3) < 2)) (fun w hw => ax w hw 1)
  have by1 := band_card Prod.snd W (my (by decide : (0:Fin 3) < 1)) (fun w hw => ay w hw 0)
  have by2 := band_card Prod.snd W (my (by decide : (1:Fin 3) < 2)) (fun w hw => ay w hw 1)
  refine ⟨⟨hne, cx, cy, mx, my, ax, ay, hx, hy, ?_, ?_⟩⟩
  · intro j
    fin_cases j
    · refine mass_of_card W (columnBand cx 0) m hm hmc ?_
      rw [← x0]; apply congrArg; apply Finset.filter_congr; intro w _; simp [columnBand]
    · refine mass_of_card W (columnBand cx 1) m hm hmc ?_
      have : W.filter (fun v => v ∈ columnBand cx 1) =
          W.filter (fun w => cx 0 < w.1 ∧ w.1 < cx 1) := by
        apply Finset.filter_congr; intro w _; simp [columnBand]
      rw [this]; omega
    · refine mass_of_card W (columnBand cx 2) m hm hmc ?_
      have : W.filter (fun v => v ∈ columnBand cx 2) =
          W.filter (fun w => cx 1 < w.1 ∧ w.1 < cx 2) := by
        apply Finset.filter_congr; intro w _; simp [columnBand]
      rw [this]; omega
    · refine mass_of_card W (columnBand cx 3) m hm hmc ?_
      have : W.filter (fun v => v ∈ columnBand cx 3) =
          W.filter (fun w => cx 2 < w.1) := by
        apply Finset.filter_congr; intro w _; simp [columnBand]
      rw [this]; omega
  · intro i
    fin_cases i
    · refine mass_of_card W (rowBand cy 0) m hm hmc ?_
      have : W.filter (fun v => v ∈ rowBand cy 0) =
          W.filter (fun w => cy 2 < w.2) := by
        apply Finset.filter_congr; intro w _; simp [rowBand]
      rw [this]; omega
    · refine mass_of_card W (rowBand cy 1) m hm hmc ?_
      have : W.filter (fun v => v ∈ rowBand cy 1) =
          W.filter (fun w => cy 1 < w.2 ∧ w.2 < cy 2) := by
        apply Finset.filter_congr; intro w _; simp [rowBand]
      rw [this]; omega
    · refine mass_of_card W (rowBand cy 2) m hm hmc ?_
      have : W.filter (fun v => v ∈ rowBand cy 2) =
          W.filter (fun w => cy 0 < w.2 ∧ w.2 < cy 1) := by
        apply Finset.filter_congr; intro w _; simp [rowBand]
      rw [this]; omega
    · refine mass_of_card W (rowBand cy 3) m hm hmc ?_
      rw [← y0]; apply congrArg; apply Finset.filter_congr; intro w _; simp [rowBand]

/-! ## Perturbation -/

structure PD (V : Finset Plane) where
  ε : ℝ
  N : ℕ
  num : Plane × Fin 4 → ℕ
  hε : 0 < ε
  lt : ∀ x ∈ V ×ˢ (Finset.univ : Finset (Fin 4)), num x < N
  inj : Set.InjOn num ↑(V ×ˢ (Finset.univ : Finset (Fin 4)))
  gap1 : ∀ a ∈ V, ∀ b ∈ V, a.1 < b.1 → ε * N < b.1 - a.1
  gap2 : ∀ a ∈ V, ∀ b ∈ V, a.2 < b.2 → ε * N < b.2 - a.2

def PD.pt {V : Finset Plane} (d : PD V) (x : Plane × Fin 4) : Plane :=
  (x.1.1 + d.ε * d.num x, x.1.2 + d.ε * d.num x)

theorem exists_delta (s : Finset ℝ) (hs : ∀ g ∈ s, 0 < g) : ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ s, δ ≤ g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih (fun g hg => hs g (Finset.mem_insert_of_mem hg))
    refine ⟨min δ a, lt_min hδ (hs a (Finset.mem_insert_self _ _)), ?_⟩
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h g hg)

theorem exists_PD (V : Finset Plane) (hV : V.Nonempty) : Nonempty (PD V) := by
  have hn : 0 < V.card := hV.card_pos
  let idx : Plane → ℕ := fun v => if h : v ∈ V then (V.equivFin ⟨v, h⟩).val else 0
  have idx_lt : ∀ v ∈ V, idx v < V.card := by
    intro v hv; simp only [idx, dif_pos hv]; exact (V.equivFin ⟨v, hv⟩).isLt
  have idx_inj : ∀ v ∈ V, ∀ v' ∈ V, idx v = idx v' → v = v' := by
    intro v hv v' hv' h
    simp only [idx, dif_pos hv, dif_pos hv'] at h
    have := V.equivFin.injective (Fin.ext h)
    exact congrArg Subtype.val this
  set G : Finset ℝ := (((V ×ˢ V).image (fun p => p.2.1 - p.1.1)) ∪
      ((V ×ˢ V).image (fun p => p.2.2 - p.1.2))).filter (fun g => 0 < g) with hG
  obtain ⟨δ, hδ, hδG⟩ := exists_delta G (fun g hg => (Finset.mem_filter.mp hg).2)
  have hN : (0 : ℝ) < ((4 * V.card : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 4 * V.card)
  have hεN : δ / (2 * ((4 * V.card : ℕ) : ℝ)) * ((4 * V.card : ℕ) : ℝ) = δ / 2 := by
    field_simp
  refine ⟨⟨δ / (2 * ((4 * V.card : ℕ) : ℝ)), 4 * V.card, fun x => 4 * idx x.1 + x.2.val,
    by positivity, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hx
    have := idx_lt _ hx
    have := x.2.isLt
    omega
  · intro x hx x' hx' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true] at hx hx'
    have h1 : idx x.1 = idx x'.1 := by
      have := x.2.isLt; have := x'.2.isLt; simp only at h; omega
    have h2 : x.2.val = x'.2.val := by
      have := x.2.isLt; have := x'.2.isLt; simp only at h; omega
    exact Prod.ext (idx_inj _ hx _ hx' h1) (Fin.ext h2)
  · intro a ha b hb hab
    have : b.1 - a.1 ∈ G := by
      rw [hG, Finset.mem_filter]
      refine ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), by simp [ha, hb], rfl⟩), by linarith⟩
    have := hδG _ this
    rw [hεN]; linarith
  · intro a ha b hb hab
    have : b.2 - a.2 ∈ G := by
      rw [hG, Finset.mem_filter]
      refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), by simp [ha, hb], rfl⟩), by linarith⟩
    have := hδG _ this
    rw [hεN]; linarith

section
variable {V : Finset Plane} (d : PD V)

theorem PD.key1 {x x' : Plane × Fin 4} (hx : x ∈ V ×ˢ (Finset.univ : Finset (Fin 4)))
    (hx' : x' ∈ V ×ˢ (Finset.univ : Finset (Fin 4))) (h : (d.pt x).1 ≤ (d.pt x').1) :
    x.1.1 ≤ x'.1.1 := by
  by_contra hn
  push Not at hn
  have g := d.gap1 x'.1 (by simpa using hx') x.1 (by simpa using hx) hn
  have l := d.lt x' hx'
  have l' : (d.num x' : ℝ) ≤ d.N := by exact_mod_cast l.le
  have l0 : (0 : ℝ) ≤ d.num x := by positivity
  have := mul_le_mul_of_nonneg_left l' d.hε.le
  have := mul_nonneg d.hε.le l0
  simp only [PD.pt] at h
  linarith

theorem PD.key2 {x x' : Plane × Fin 4} (hx : x ∈ V ×ˢ (Finset.univ : Finset (Fin 4)))
    (hx' : x' ∈ V ×ˢ (Finset.univ : Finset (Fin 4))) (h : (d.pt x).2 ≤ (d.pt x').2) :
    x.1.2 ≤ x'.1.2 := by
  by_contra hn
  push Not at hn
  have g := d.gap2 x'.1 (by simpa using hx') x.1 (by simpa using hx) hn
  have l := d.lt x' hx'
  have l' : (d.num x' : ℝ) ≤ d.N := by exact_mod_cast l.le
  have l0 : (0 : ℝ) ≤ d.num x := by positivity
  have := mul_le_mul_of_nonneg_left l' d.hε.le
  have := mul_nonneg d.hε.le l0
  simp only [PD.pt] at h
  linarith

theorem PD.pt_inj1 {x x' : Plane × Fin 4} (hx : x ∈ V ×ˢ (Finset.univ : Finset (Fin 4)))
    (hx' : x' ∈ V ×ˢ (Finset.univ : Finset (Fin 4))) (h : (d.pt x).1 = (d.pt x').1) : x = x' := by
  have a := d.key1 hx hx' h.le
  have b := d.key1 hx' hx h.ge
  have e : x.1.1 = x'.1.1 := le_antisymm a b
  simp only [PD.pt] at h
  rw [e] at h
  have : d.ε * d.num x = d.ε * d.num x' := by linarith
  have := mul_left_cancel₀ d.hε.ne' this
  exact d.inj (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast this)

theorem PD.pt_inj2 {x x' : Plane × Fin 4} (hx : x ∈ V ×ˢ (Finset.univ : Finset (Fin 4)))
    (hx' : x' ∈ V ×ˢ (Finset.univ : Finset (Fin 4))) (h : (d.pt x).2 = (d.pt x').2) : x = x' := by
  have a := d.key2 hx hx' h.le
  have b := d.key2 hx' hx h.ge
  have e : x.1.2 = x'.1.2 := le_antisymm a b
  simp only [PD.pt] at h
  rw [e] at h
  have : d.ε * d.num x = d.ε * d.num x' := by linarith
  have := mul_left_cancel₀ d.hε.ne' this
  exact d.inj (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast this)

end

theorem exists_pert (V : Finset Plane) (hV : V.Nonempty) :
    ∃ (W : Finset Plane) (π : Plane → Plane), W.card = 4 * V.card ∧
      Set.InjOn Prod.fst (↑W : Set Plane) ∧ Set.InjOn Prod.snd (↑W : Set Plane) ∧
      (∀ w ∈ W, π w ∈ V) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w.1 ≤ w'.1 → (π w).1 ≤ (π w').1) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w.2 ≤ w'.2 → (π w).2 ≤ (π w').2) ∧
      (∀ X : Finset Plane, X ⊆ V → 4 * X.card ≤ (W.filter (fun w => π w ∈ X)).card) := by
  obtain ⟨d⟩ := exists_PD V hV
  set S : Finset (Plane × Fin 4) := V ×ˢ Finset.univ with hS
  set W : Finset Plane := S.image d.pt with hW
  let π : Plane → Plane := fun w =>
    if h : ∃ x ∈ S, d.pt x = w then (Classical.choose h).1 else 0
  have hπ : ∀ x ∈ S, π (d.pt x) = x.1 := by
    intro x hx
    have h : ∃ x' ∈ S, d.pt x' = d.pt x := ⟨x, hx, rfl⟩
    simp only [π, dif_pos h]
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    rw [d.pt_inj1 h1 hx (by rw [h2])]
  have hSV : ∀ x ∈ S, x.1 ∈ V := fun x hx => by simpa [hS] using hx
  have hmemW : ∀ w ∈ W, ∃ x ∈ S, d.pt x = w := fun w hw => Finset.mem_image.mp hw
  refine ⟨W, π, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW, Finset.card_image_of_injOn, hS, Finset.card_product]
    · simp; ring
    · intro x hx x' hx' h; exact d.pt_inj1 hx hx' (congrArg Prod.fst h)
  · intro w hw w' hw' h
    obtain ⟨x, hx, rfl⟩ := hmemW w hw
    obtain ⟨x', hx', rfl⟩ := hmemW w' hw'
    rw [d.pt_inj1 hx hx' h]
  · intro w hw w' hw' h
    obtain ⟨x, hx, rfl⟩ := hmemW w hw
    obtain ⟨x', hx', rfl⟩ := hmemW w' hw'
    rw [d.pt_inj2 hx hx' h]
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := hmemW w hw
    rw [hπ x hx]; exact hSV x hx
  · intro w hw w' hw' h
    obtain ⟨x, hx, rfl⟩ := hmemW w hw
    obtain ⟨x', hx', rfl⟩ := hmemW w' hw'
    rw [hπ x hx, hπ x' hx']
    exact d.key1 hx hx' h
  · intro w hw w' hw' h
    obtain ⟨x, hx, rfl⟩ := hmemW w hw
    obtain ⟨x', hx', rfl⟩ := hmemW w' hw'
    rw [hπ x hx, hπ x' hx']
    exact d.key2 hx hx' h
  · intro X hX
    have hsub : (X ×ˢ (Finset.univ : Finset (Fin 4))).image d.pt ⊆ W.filter (fun w => π w ∈ X) := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      have hxS : x ∈ S := by
        rw [Finset.mem_product] at hx; rw [hS, Finset.mem_product]; exact ⟨hX hx.1, hx.2⟩
      rw [Finset.mem_filter, hπ x hxS]
      exact ⟨Finset.mem_image_of_mem _ hxS, (Finset.mem_product.mp hx).1⟩
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_image_of_injOn, Finset.card_product]
    · simp; omega
    · intro x hx x' hx' h
      have hxS : ∀ y ∈ X ×ˢ (Finset.univ : Finset (Fin 4)), y ∈ S := by
        intro y hy
        rw [Finset.mem_product] at hy; rw [hS, Finset.mem_product]; exact ⟨hX hy.1, hy.2⟩
      exact d.pt_inj1 (hxS x hx) (hxS x' hx') (congrArg Prod.fst h)

/-- reduction of an arbitrary electorate to exact quartile grids (paper: proof of Theorem 3.1, last paragraph) -/
theorem perturb_good (V : Finset Plane) (hV : V.Nonempty)
    (H : ∀ (W : Finset Plane) (g : QuartileGrid W), Good W) : Good V := by
  obtain ⟨W, π, hWc, hx, hy, hπV, hπx, hπy, hcount⟩ := exists_pert V hV
  have hWne : W.Nonempty := by
    rw [← Finset.card_pos, hWc]; have := hV.card_pos; omega
  obtain ⟨g⟩ := exists_grid W hWne ⟨V.card, hWc⟩ hx hy
  obtain ⟨Q', hQ'W, hQ'c, hQ'net⟩ := H W g
  refine ⟨Q'.image π, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact hπV q' (hQ'W hq')
  · exact (Finset.card_image_le).trans hQ'c
  · intro R hR hmass
    obtain ⟨I, J, hI, hJ, rfl⟩ := hR
    have hn : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
    obtain ⟨X, hXV, hXmem, h1⟩ : ∃ X : Finset Plane, X ⊆ V ∧ (∀ v, v ∈ X ↔ v ∈ V ∧ v ∈ I ×ˢ J) ∧
        1 / 2 * (V.card : ℝ) < X.card := by
      refine ⟨V.filter (fun v => v ∈ I ×ˢ J), Finset.filter_subset _ _, fun v => by simp, ?_⟩
      unfold mass at hmass
      rw [lt_div_iff₀ hn] at hmass
      convert hmass using 2
      all_goals first | rfl | congr!
    set I' : Set ℝ := {t | ∃ w1 ∈ W, ∃ w2 ∈ W, π w1 ∈ X ∧ π w2 ∈ X ∧ w1.1 ≤ t ∧ t ≤ w2.1} with hI'
    set J' : Set ℝ := {t | ∃ w1 ∈ W, ∃ w2 ∈ W, π w1 ∈ X ∧ π w2 ∈ X ∧ w1.2 ≤ t ∧ t ≤ w2.2} with hJ'
    have hI'c : Set.OrdConnected I' := by
      refine ⟨fun s hs t ht u hu => ?_⟩
      obtain ⟨w1, hw1, _, _, h1, _, h3, _⟩ := hs
      obtain ⟨_, _, w2, hw2, _, h2, _, h4⟩ := ht
      exact ⟨w1, hw1, w2, hw2, h1, h2, h3.trans hu.1, hu.2.trans h4⟩
    have hJ'c : Set.OrdConnected J' := by
      refine ⟨fun s hs t ht u hu => ?_⟩
      obtain ⟨w1, hw1, _, _, h1, _, h3, _⟩ := hs
      obtain ⟨_, _, w2, hw2, _, h2, _, h4⟩ := ht
      exact ⟨w1, hw1, w2, hw2, h1, h2, h3.trans hu.1, hu.2.trans h4⟩
    have hmass' : 1 / 2 < mass W (I' ×ˢ J') := by
      have h2 : 4 * X.card ≤ (W.filter (fun w => (w ∈ I' ×ˢ J'))).card := by
        refine le_trans (hcount X hXV) (Finset.card_le_card ?_)
        intro w hw
        rw [Finset.mem_filter] at hw ⊢
        refine ⟨hw.1, ?_, ?_⟩
        · exact ⟨w, hw.1, w, hw.1, hw.2, hw.2, le_rfl, le_rfl⟩
        · exact ⟨w, hw.1, w, hw.1, hw.2, hw.2, le_rfl, le_rfl⟩
      have h3 : (4 : ℝ) * X.card ≤ (W.filter (fun w => (w ∈ I' ×ˢ J'))).card := by exact_mod_cast h2
      unfold mass
      rw [lt_div_iff₀ (by rw [hWc]; push_cast; positivity), hWc]
      push_cast
      linarith
    obtain ⟨q', hq'Q, hq'R⟩ := hQ'net (I' ×ˢ J') ⟨I', J', hI'c, hJ'c, rfl⟩ hmass'
    have hq'W := hQ'W hq'Q
    refine ⟨π q', Finset.mem_image_of_mem _ hq'Q, ?_, ?_⟩
    · obtain ⟨w1, hw1, w2, hw2, h1, h2, h3, h4⟩ := hq'R.1
      have a1 := ((hXmem _).mp h1).2.1
      have a2 := ((hXmem _).mp h2).2.1
      exact hI.out a1 a2 ⟨hπx _ hw1 _ hq'W h3, hπx _ hq'W _ hw2 h4⟩
    · obtain ⟨w1, hw1, w2, hw2, h1, h2, h3, h4⟩ := hq'R.2
      have a1 := ((hXmem _).mp h1).2.2
      have a2 := ((hXmem _).mp h2).2.2
      exact hJ.out a1 a2 ⟨hπy _ hw1 _ hq'W h3, hπy _ hq'W _ hw2 h4⟩

end PlanarMetricElections.Peer.Dev
end
end

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.Symmetry
open PlanarMetricElections.Peer PlanarMetricElections.Peer.Dev

/-- the three generating plane maps -/
def px (z : Plane) : Plane := (-z.1, z.2)
def py (z : Plane) : Plane := (z.1, -z.2)
def ps (z : Plane) : Plane := (z.2, z.1)

theorem px_inv : Function.Involutive px := fun z => by simp [px]
theorem py_inv : Function.Involutive py := fun z => by simp [py]
theorem ps_inv : Function.Involutive ps := fun z => by simp [ps]

theorem rect_px (R : Set Plane) (h : IsRectangle R) : IsRectangle (px ⁻¹' R) := by
  obtain ⟨I, J, hI, hJ, rfl⟩ := h
  refine ⟨Neg.neg ⁻¹' I, J, hI.preimage_anti (fun a b hab => neg_le_neg hab), hJ, ?_⟩
  ext z; simp [px]

theorem rect_py (R : Set Plane) (h : IsRectangle R) : IsRectangle (py ⁻¹' R) := by
  obtain ⟨I, J, hI, hJ, rfl⟩ := h
  refine ⟨I, Neg.neg ⁻¹' J, hI, hJ.preimage_anti (fun a b hab => neg_le_neg hab), ?_⟩
  ext z; simp [py]

theorem rect_ps (R : Set Plane) (h : IsRectangle R) : IsRectangle (ps ⁻¹' R) := by
  obtain ⟨I, J, hI, hJ, rfl⟩ := h
  refine ⟨J, I, hJ, hI, ?_⟩
  ext z; simp [ps, and_comm]

theorem mass_image (V : Finset Plane) (φ : Plane → Plane) (hφ : Function.Involutive φ)
    (X : Set Plane) : mass (V.image φ) X = mass V (φ ⁻¹' X) := by
  have hinj : Function.Injective φ := hφ.injective
  unfold mass
  rw [Finset.card_image_of_injective _ hinj, Finset.filter_image,
    Finset.card_image_of_injective _ hinj]
  rfl

theorem good_transport (V : Finset Plane) (φ : Plane → Plane) (hφ : Function.Involutive φ)
    (hrect : ∀ R, IsRectangle R → IsRectangle (φ ⁻¹' R)) (h : Good (V.image φ)) : Good V := by
  obtain ⟨Q', hsub, hcard, hnet⟩ := h
  refine ⟨Q'.image φ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hsub hq)
    simpa [hφ v] using hv
  · exact (Finset.card_image_le).trans hcard
  · intro R hR hm
    have hpre : φ ⁻¹' (φ ⁻¹' R) = R := by ext z; simp [hφ z]
    have hm' : 1 / 2 < mass (V.image φ) (φ ⁻¹' R) := by
      rw [mass_image V φ hφ, hpre]; exact hm
    obtain ⟨q, hq, hqR⟩ := hnet _ (hrect R hR) hm'
    exact ⟨φ q, Finset.mem_image_of_mem φ hq, hqR⟩

/-! ### Grid transport -/

theorem good_px (V : Finset Plane) (h : Good (V.image px)) : Good V :=
  good_transport V px px_inv rect_px h
theorem good_py (V : Finset Plane) (h : Good (V.image py)) : Good V :=
  good_transport V py py_inv rect_py h
theorem good_ps (V : Finset Plane) (h : Good (V.image ps)) : Good V :=
  good_transport V ps ps_inv rect_ps h

theorem mem_image_inv (V : Finset Plane) (φ : Plane → Plane) (hφ : Function.Involutive φ)
    {w : Plane} (hw : w ∈ V.image φ) : φ w ∈ V := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  simpa [hφ v] using hv

theorem cuts_rev (c : Fin 3 → ℝ) (h : StrictMono c) :
    StrictMono (![-c 2, -c 1, -c 0] : Fin 3 → ℝ) := by
  have h01 : c 0 < c 1 := h (by decide)
  have h12 : c 1 < c 2 := h (by decide)
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> linarith

def revCut (c : Fin 3 → ℝ) : Fin 3 → ℝ := ![-c 2, -c 1, -c 0]

theorem revCut_col (c : Fin 3 → ℝ) (j : Fin 4) :
    px ⁻¹' (columnBand (revCut c) j) = columnBand c (3 - j) := by
  fin_cases j <;> ext z <;> simp [px, columnBand, revCut] <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | (constructor <;> linarith [h.1, h.2]) | linarith

theorem revCut_row (c : Fin 3 → ℝ) (j : Fin 4) :
    py ⁻¹' (rowBand (revCut c) j) = rowBand c (3 - j) := by
  fin_cases j <;> ext z <;> simp [py, rowBand, revCut] <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | (constructor <;> linarith [h.1, h.2]) | linarith


theorem px_row (c : Fin 3 → ℝ) (i : Fin 4) : px ⁻¹' (rowBand c i) = rowBand c i := by
  fin_cases i <;> ext z <;> simp [px, rowBand]

theorem py_col (c : Fin 3 → ℝ) (i : Fin 4) : py ⁻¹' (columnBand c i) = columnBand c i := by
  fin_cases i <;> ext z <;> simp [py, columnBand]

theorem ps_row (c : Fin 3 → ℝ) (i : Fin 4) : ps ⁻¹' (rowBand c i) = columnBand c (3 - i) := by
  fin_cases i <;> ext z <;> simp [ps, rowBand, columnBand]

theorem ps_col (c : Fin 3 → ℝ) (i : Fin 4) : ps ⁻¹' (columnBand c i) = rowBand c (3 - i) := by
  fin_cases i <;> ext z <;> simp [ps, rowBand, columnBand]

variable {V : Finset Plane}

theorem revCut_apply_ne (c : Fin 3 → ℝ) (a : ℝ) (h : ∀ j : Fin 3, -a ≠ c j) (j : Fin 3) :
    a ≠ revCut c j := by
  intro e
  fin_cases j
  · exact h 2 (by simp [revCut] at e ⊢; linarith)
  · exact h 1 (by simp [revCut] at e ⊢; linarith)
  · exact h 0 (by simp [revCut] at e ⊢; linarith)

theorem grid_px (g : QuartileGrid V) :
    ∃ g' : QuartileGrid (V.image px), ∀ i j, g'.cellMass i j = g.cellMass i (3 - j) := by
  refine ⟨{ nonempty := g.nonempty.image px
            xCut := revCut g.xCut
            yCut := g.yCut
            x_order := cuts_rev _ g.x_order
            y_order := g.y_order
            x_avoids := ?_
            y_avoids := ?_
            x_distinct := ?_
            y_distinct := ?_
            column_mass := ?_
            row_mass := ?_ }, ?_⟩
  · intro v hv j
    have := g.x_avoids _ (mem_image_inv V px px_inv hv)
    exact revCut_apply_ne _ _ (fun k => by simpa [px] using this k) j
  · intro v hv i
    simpa [px] using g.y_avoids _ (mem_image_inv V px px_inv hv) i
  · intro v hv w hw h
    have := g.x_distinct (mem_image_inv V px px_inv hv) (mem_image_inv V px px_inv hw)
      (by simpa [px] using h)
    exact px_inv.injective this
  · intro v hv w hw h
    have := g.y_distinct (mem_image_inv V px px_inv hv) (mem_image_inv V px px_inv hw)
      (by simpa [px] using h)
    exact px_inv.injective this
  · intro j
    rw [mass_image V px px_inv, revCut_col]; exact g.column_mass _
  · intro i
    rw [mass_image V px px_inv, px_row]; exact g.row_mass _
  · intro i j
    unfold QuartileGrid.cellMass QuartileGrid.cell
    rw [mass_image V px px_inv, Set.preimage_inter, revCut_col, px_row]

theorem grid_py (g : QuartileGrid V) :
    ∃ g' : QuartileGrid (V.image py), ∀ i j, g'.cellMass i j = g.cellMass (3 - i) j := by
  refine ⟨{ nonempty := g.nonempty.image py
            xCut := g.xCut
            yCut := revCut g.yCut
            x_order := g.x_order
            y_order := cuts_rev _ g.y_order
            x_avoids := ?_
            y_avoids := ?_
            x_distinct := ?_
            y_distinct := ?_
            column_mass := ?_
            row_mass := ?_ }, ?_⟩
  · intro v hv i
    simpa [py] using g.x_avoids _ (mem_image_inv V py py_inv hv) i
  · intro v hv j
    have := g.y_avoids _ (mem_image_inv V py py_inv hv)
    exact revCut_apply_ne _ _ (fun k => by simpa [py] using this k) j
  · intro v hv w hw h
    have := g.x_distinct (mem_image_inv V py py_inv hv) (mem_image_inv V py py_inv hw)
      (by simpa [py] using h)
    exact py_inv.injective this
  · intro v hv w hw h
    have := g.y_distinct (mem_image_inv V py py_inv hv) (mem_image_inv V py py_inv hw)
      (by simpa [py] using h)
    exact py_inv.injective this
  · intro j
    rw [mass_image V py py_inv, py_col]; exact g.column_mass _
  · intro i
    rw [mass_image V py py_inv, revCut_row]; exact g.row_mass _
  · intro i j
    unfold QuartileGrid.cellMass QuartileGrid.cell
    rw [mass_image V py py_inv, Set.preimage_inter, revCut_row, py_col]

theorem grid_ps (g : QuartileGrid V) :
    ∃ g' : QuartileGrid (V.image ps), ∀ i j, g'.cellMass i j = g.cellMass (3 - j) (3 - i) := by
  refine ⟨{ nonempty := g.nonempty.image ps
            xCut := g.yCut
            yCut := g.xCut
            x_order := g.y_order
            y_order := g.x_order
            x_avoids := ?_
            y_avoids := ?_
            x_distinct := ?_
            y_distinct := ?_
            column_mass := ?_
            row_mass := ?_ }, ?_⟩
  · intro v hv i
    simpa [ps] using g.y_avoids _ (mem_image_inv V ps ps_inv hv) i
  · intro v hv i
    simpa [ps] using g.x_avoids _ (mem_image_inv V ps ps_inv hv) i
  · intro v hv w hw h
    have := g.y_distinct (mem_image_inv V ps ps_inv hv) (mem_image_inv V ps ps_inv hw)
      (by simpa [ps] using h)
    exact ps_inv.injective this
  · intro v hv w hw h
    have := g.x_distinct (mem_image_inv V ps ps_inv hv) (mem_image_inv V ps ps_inv hw)
      (by simpa [ps] using h)
    exact ps_inv.injective this
  · intro j
    rw [mass_image V ps ps_inv, ps_col]; exact g.row_mass _
  · intro i
    rw [mass_image V ps ps_inv, ps_row]; exact g.column_mass _
  · intro i j
    unfold QuartileGrid.cellMass QuartileGrid.cell
    rw [mass_image V ps ps_inv, Set.preimage_inter, ps_row, ps_col, Set.inter_comm]

/-- the grid property for a prescribed cell-mass matrix -/
def NetM (m : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ (V : Finset Plane) (g : QuartileGrid V), (∀ i j, g.cellMass i j = m i j) → Good V

theorem netM_x (m : Fin 4 → Fin 4 → ℝ) (h : NetM (fun i j => m i (3 - j))) : NetM m := by
  intro V g hg
  obtain ⟨g', hg'⟩ := grid_px g
  exact good_px V (h _ g' (fun i j => by rw [hg', hg]))

theorem netM_y (m : Fin 4 → Fin 4 → ℝ) (h : NetM (fun i j => m (3 - i) j)) : NetM m := by
  intro V g hg
  obtain ⟨g', hg'⟩ := grid_py g
  exact good_py V (h _ g' (fun i j => by rw [hg', hg]))

theorem netM_s (m : Fin 4 → Fin 4 → ℝ) (h : NetM (fun i j => m (3 - j) (3 - i))) : NetM m := by
  intro V g hg
  obtain ⟨g', hg'⟩ := grid_ps g
  exact good_ps V (h _ g' (fun i j => by rw [hg', hg]))

/-- reflection in the main diagonal -/
theorem netM_T (m : Fin 4 → Fin 4 → ℝ) (h : NetM (fun i j => m j i)) : NetM m := by
  apply netM_s
  apply netM_x
  apply netM_y
  convert h using 3 with i j
  simp

end PlanarMetricElections.Peer.Dev.Symmetry
end
end

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.Assembly
open PlanarMetricElections.Peer PlanarMetricElections.Peer.Dev PlanarMetricElections.Peer.Dev.Symmetry

/-- the base case: K = 0 < F -/
theorem base (m : Fin 4 → Fin 4 → ℝ) (hnn : ∀ i j, 0 ≤ m i j)
    (hK : m 2 2 = 0) (hF : 0 < m 1 1) : NetM m := by
  have adj : ∀ m : Fin 4 → Fin 4 → ℝ, m 2 2 = 0 → 0 < m 1 1 →
      m 0 0 ≤ m 1 2 + m 2 1 + m 1 1 / 2 → 0 < m 1 2 → m 2 1 = 0 → NetM m := by
    intro m hK hF hA hG hJ V g hg
    exact PlanarMetricElections.Peer.adjacent_center V g (by rw [hg]; exact hK)
      (by rw [hg]; exact hF) (by rw [hg, hg, hg, hg]; exact hA) (by rw [hg]; exact hG)
      (by rw [hg]; exact hJ)
  by_cases hA : m 1 2 + m 2 1 + m 1 1 / 2 < m 0 0
  · intro V g hg
    exact PlanarMetricElections.Peer.large_northwest_corner V g (by rw [hg]; exact hK)
      (by rw [hg]; exact hF) (by rw [hg, hg, hg, hg]; exact hA)
  · replace hA := not_lt.mp hA
    rcases (hnn 1 2).eq_or_lt with hG | hG
    · rcases (hnn 2 1).eq_or_lt with hJ | hJ
      · intro V g hg
        exact PlanarMetricElections.Peer.one_center V g (by rw [hg]; exact hG.symm)
          (by rw [hg]; exact hJ.symm) (by rw [hg]; exact hK) (by rw [hg]; exact hF)
          (by rw [hg, hg]; rw [← hG, ← hJ] at hA; linarith)
      · apply netM_T
        apply adj
        · simpa using hK
        · simpa using hF
        · show m 0 0 ≤ m 2 1 + m 1 2 + m 1 1 / 2
          linarith
        · simpa using hJ
        · simpa using hG.symm
    · rcases (hnn 2 1).eq_or_lt with hJ | hJ
      · exact adj m hK hF hA hG hJ.symm
      · intro V g hg
        exact PlanarMetricElections.Peer.three_center V g (by rw [hg]; exact hK)
          (by rw [hg]; exact hF) (by rw [hg, hg, hg, hg]; exact hA) (by rw [hg]; exact hG)
          (by rw [hg]; exact hJ)

theorem netM_rot (m : Fin 4 → Fin 4 → ℝ) (h : NetM (fun i j => m (3 - i) (3 - j))) : NetM m :=
  netM_y m (netM_x _ h)

theorem reduce (m : Fin 4 → Fin 4 → ℝ) (hnn : ∀ i j, 0 ≤ m i j)
    (h : (0 < m 1 1 ∧ m 2 2 = 0) ∨ (0 < m 2 2 ∧ m 1 1 = 0) ∨
      (0 < m 1 2 ∧ m 2 1 = 0) ∨ (0 < m 2 1 ∧ m 1 2 = 0)) : NetM m := by
  rcases h with ⟨hp, hz⟩ | ⟨hp, hz⟩ | ⟨hp, hz⟩ | ⟨hp, hz⟩
  · exact base m hnn hz hp
  · apply netM_rot
    exact base _ (fun i j => hnn _ _) (by simpa using hz) (by simpa using hp)
  · apply netM_x
    exact base _ (fun i j => hnn _ _) (by simpa using hz) (by simpa using hp)
  · apply netM_y
    exact base _ (fun i j => hnn _ _) (by simpa using hz) (by simpa using hp)

theorem netM_all (m : Fin 4 → Fin 4 → ℝ) (hnn : ∀ i j, 0 ≤ m i j) : NetM m := by
  rcases (hnn 1 1).eq_or_lt with hF | hF <;> rcases (hnn 1 2).eq_or_lt with hG | hG <;>
    rcases (hnn 2 1).eq_or_lt with hJ | hJ <;> rcases (hnn 2 2).eq_or_lt with hK | hK
  all_goals first
    | exact reduce m hnn (Or.inl ⟨hF, hK.symm⟩)
    | exact reduce m hnn (Or.inr (Or.inl ⟨hK, hF.symm⟩))
    | exact reduce m hnn (Or.inr (Or.inr (Or.inl ⟨hG, hJ.symm⟩)))
    | exact reduce m hnn (Or.inr (Or.inr (Or.inr ⟨hJ, hG.symm⟩)))
    | skip
  · intro V g hg
    exact PlanarMetricElections.Peer.empty_center V g (by rw [hg]; exact hF.symm)
      (by rw [hg]; exact hG.symm) (by rw [hg]; exact hJ.symm) (by rw [hg]; exact hK.symm)
  · intro V g hg
    exact PlanarMetricElections.Peer.opposite_center V g
      (Or.inr ⟨by rw [hg]; exact hG, by rw [hg]; exact hJ, by rw [hg]; exact hF.symm,
        by rw [hg]; exact hK.symm⟩)
  · intro V g hg
    exact PlanarMetricElections.Peer.opposite_center V g
      (Or.inl ⟨by rw [hg]; exact hF, by rw [hg]; exact hK, by rw [hg]; exact hG.symm,
        by rw [hg]; exact hJ.symm⟩)
  · intro V g hg
    exact PlanarMetricElections.Peer.four_center V g (by rw [hg]; exact hF)
      (by rw [hg]; exact hG) (by rw [hg]; exact hJ) (by rw [hg]; exact hK)

theorem grid_good (W : Finset Plane) (g : QuartileGrid W) : Good W :=
  netM_all (fun i j => g.cellMass i j) (fun i j => cellMass_nonneg g i j) W g (fun _ _ => rfl)

end PlanarMetricElections.Peer.Dev.Assembly
end
end

section
set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer.Dev.HalfNet
open PlanarMetricElections.Peer PlanarMetricElections.Peer.Dev

theorem rect_empty : IsRectangle (∅ : Set Plane) :=
  ⟨∅, ∅, Set.ordConnected_empty, Set.ordConnected_empty, by simp⟩

theorem worst_le (V Q : Finset Plane) (hnet : IsStrongRectNet V Q 3 (1 / 2)) :
    rectangularWorst V Q ≤ 1 / 2 := by
  unfold rectangularWorst
  apply csSup_le
  · exact ⟨mass V ∅, ∅, rect_empty, by simp, rfl⟩
  · rintro r ⟨R, hR, hd, rfl⟩
    by_contra hlt
    replace hlt := not_le.mp hlt
    obtain ⟨q, hq, hqR⟩ := hnet.2.2 R hR hlt
    exact Set.disjoint_left.mp hd hqR (Finset.mem_coe.mpr hq)

theorem worst_nonneg (V Q : Finset Plane) : 0 ≤ rectangularWorst V Q := by
  unfold rectangularWorst
  apply Real.sSup_nonneg
  rintro r ⟨R, _, _, rfl⟩
  exact mass_nonneg V R

theorem instance_le (V : Finset Plane) (hV : V.Nonempty) : rectangularInstance V 3 ≤ 1 / 2 := by
  obtain ⟨Q, hnet⟩ := perturb_good V hV (fun W g => Assembly.grid_good W g)
  refine le_trans ?_ (worst_le V Q hnet)
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨Q', _, _, rfl⟩
    exact worst_nonneg V Q'
  · exact ⟨Q, hnet.1, hnet.2.1, rfl⟩

end PlanarMetricElections.Peer.Dev.HalfNet

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev.HalfNet in
theorem chk_rectangular_half_net : rectangularFactor 3 ≤ 1 / 2 := by
  unfold rectangularFactor
  apply Real.sSup_le
  · rintro r ⟨V, hV, rfl⟩
    exact instance_le V hV
  · norm_num

end PlanarMetricElections.Peer
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_rectangular_half_net := @PlanarMetricElections.Peer.chk_rectangular_half_net
