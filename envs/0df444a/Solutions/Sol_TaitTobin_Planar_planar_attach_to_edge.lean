-- Prove2me | solution 1 for TaitTobin.Planar.planar_attach_to_edge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T15:02:42.511463+00:00
-- url     : https://prove2.me/submissions/2242d848-b825-4ac3-9988-e434a318313e

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

set_option autoImplicit false

namespace TTAE

open RobertsonSeymour1986.GM5

/-- `S` is the image of an injective path from `P` to `Q`. -/
def ArcImg (P Q : ℝ × ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∃ γ : Path P Q, Function.Injective γ ∧ Set.range γ = S

lemma ArcImg.symm {P Q : ℝ × ℝ} {S : Set (ℝ × ℝ)} (h : ArcImg P Q S) : ArcImg Q P S := by
  obtain ⟨γ, hi, hr⟩ := h
  refine ⟨γ.symm, ?_, by rw [Path.symm_range, hr]⟩
  intro s t hst
  simp only [Path.symm_apply] at hst
  exact unitInterval.symm_involutive.injective (hi hst)

lemma ArcImg.trans {P Q R : ℝ × ℝ} {S T : Set (ℝ × ℝ)} (h1 : ArcImg P Q S)
    (h2 : ArcImg Q R T) (h : ∀ z, z ∈ S → z ∈ T → z = Q) : ArcImg P R (S ∪ T) := by
  obtain ⟨γ, hγ, rγ⟩ := h1
  obtain ⟨δ, hδ, rδ⟩ := h2
  refine ⟨γ.trans δ, ?_, by rw [Path.trans_range, rγ, rδ]⟩
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have e := congrArg Subtype.val (hγ hst)
    simp only at e
    exact Subtype.ext (by linarith)
  · exfalso
    have hz := h _ (rγ ▸ Set.mem_range_self _) (by rw [hst, ← rδ]; exact Set.mem_range_self _)
    have e1 := congrArg Subtype.val (hγ (hz.trans γ.target.symm))
    have e2 := congrArg Subtype.val (hδ ((hst.symm.trans hz).trans δ.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at e1 e2
    linarith
  · exfalso
    have hz := h _ (rγ ▸ Set.mem_range_self _) (by rw [← hst, ← rδ]; exact Set.mem_range_self _)
    have e1 := congrArg Subtype.val (hγ (hz.trans γ.target.symm))
    have e2 := congrArg Subtype.val (hδ ((hst.trans hz).trans δ.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at e1 e2
    linarith
  · have e := congrArg Subtype.val (hδ hst)
    simp only at e
    exact Subtype.ext (by linarith)

/-- the straight segment from `P` to `Q` -/
def seg (P Q : ℝ × ℝ) : Set (ℝ × ℝ) := (fun t : ℝ => P + t • (Q - P)) '' Set.Icc 0 1

def segPath (P Q : ℝ × ℝ) : Path P Q where
  toFun t := P + (t : ℝ) • (Q - P)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

lemma arcImg_seg {P Q : ℝ × ℝ} (h : P ≠ Q) : ArcImg P Q (seg P Q) := by
  refine ⟨segPath P Q, ?_, ?_⟩
  · intro s t hst
    have h' : (s : ℝ) • (Q - P) = (t : ℝ) • (Q - P) := by
      have e : P + (s : ℝ) • (Q - P) = P + (t : ℝ) • (Q - P) := hst
      exact add_left_cancel e
    have hne : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    exact Subtype.ext (smul_left_injective ℝ hne h')
  · ext z
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩

lemma seg_symm (P Q : ℝ × ℝ) : seg P Q = seg Q P := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    ext <;> simp <;> ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    ext <;> simp <;> ring

lemma arcImg_sub {P Q : ℝ × ℝ} (γ : Path P Q) (hγ : Function.Injective γ) (a b : unitInterval)
    (hab : a < b) : ArcImg (γ a) (γ b) (γ '' Set.Icc a b) := by
  refine ⟨γ.subpath a b, ?_, Path.range_subpath_of_le γ a b hab.le⟩
  intro s t hst
  have e : γ (Set.Icc.convexComb a b s) = γ (Set.Icc.convexComb a b t) := hst
  have e2 := congrArg Subtype.val (hγ e)
  simp only [Set.Icc.coe_convexComb] at e2
  have hab' : (a : ℝ) < b := hab
  have : ((s : ℝ) - t) * ((b : ℝ) - a) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact Subtype.ext (by linarith)
  · exfalso; linarith

/-- Building a plane drawing from arc images. -/
theorem planar_of_imgs {V : Type} [LinearOrder V] (H : SimpleGraph V) (P : V → ℝ × ℝ)
    (hP : Function.Injective P) (S : V → V → Set (ℝ × ℝ))
    (hsymm : ∀ v w, S v w = S w v)
    (harc : ∀ v w, H.Adj v w → ArcImg (P v) (P w) (S v w))
    (havoid : ∀ v w, H.Adj v w → ∀ x, P x ∈ S v w → x = v ∨ x = w)
    (hmeet : ∀ v w x y, H.Adj v w → H.Adj x y → ¬ (s(v, w) = s(x, y)) →
      ∀ z, z ∈ S v w → z ∈ S x y → z = P v ∨ z = P w) :
    IsPlanar H := by
  classical
  let g : ∀ {v w : V}, H.Adj v w → Path (P v) (P w) := fun {v w} h =>
    if v < w then Classical.choose (harc v w h)
    else (Classical.choose (harc w v h.symm)).symm
  have gspec : ∀ {v w : V} (h : H.Adj v w),
      Function.Injective (g h) ∧ Set.range (g h) = S v w := by
    intro v w h
    by_cases hvw : v < w
    · simp only [g, if_pos hvw]; exact Classical.choose_spec (harc v w h)
    · simp only [g, if_neg hvw]
      obtain ⟨hi, hr⟩ := Classical.choose_spec (harc w v h.symm)
      refine ⟨?_, by rw [Path.symm_range, hr, hsymm]⟩
      intro s t hst
      simp only [Path.symm_apply] at hst
      exact unitInterval.symm_involutive.injective (hi hst)
  have grev : ∀ {v w : V} (h : H.Adj v w), g h.symm = (g h).symm := by
    intro v w h
    have hne : v ≠ w := H.ne_of_adj h
    rcases lt_or_gt_of_ne hne with hvw | hvw
    · simp only [g, if_pos hvw, if_neg (not_lt.mpr hvw.le)]
    · simp only [g, if_pos hvw, if_neg (not_lt.mpr hvw.le), Path.symm_symm]
  have hend : ∀ {v w : V} (h : H.Adj v w) (s : unitInterval),
      (g h s = P v ∨ g h s = P w) → (s = 0 ∨ s = 1) := by
    intro v w h s hs
    rcases hs with hs | hs
    · left; exact (gspec h).1 (hs.trans (g h).source.symm)
    · right; exact (gspec h).1 (hs.trans (g h).target.symm)
  refine ⟨PlaneDrawing.mk P hP g (fun h => (gspec h).1) (fun h => grev h) ?_ ?_⟩
  · intro v w h t x hx
    apply havoid v w h x
    rw [← (gspec h).2, ← hx]; exact Set.mem_range_self t
  · intro v w x y h k s t hst
    by_cases he : s(v, w) = s(x, y)
    · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, h2⟩
      · right; left; exact ⟨h1, h2⟩
    · right; right
      have hz1 : g h s ∈ S v w := (gspec h).2 ▸ Set.mem_range_self s
      have hz2 : g k t ∈ S x y := (gspec k).2 ▸ Set.mem_range_self t
      have he' : ¬ s(x, y) = s(v, w) := fun h' => he h'.symm
      refine ⟨hend h s (hmeet v w x y h k he _ hz1 (hst ▸ hz2)),
        hend k t (hmeet x y v w k h he' _ hz2 (hst ▸ hz1))⟩

/-- last exit time from a closed ball -/
lemma exit_time {A B : ℝ × ℝ} (γ : Path A B) {r : ℝ} (hr : 0 < r) (hB : r < dist B A) :
    ∃ τ : unitInterval, dist (γ τ) A = r ∧ ∀ t : unitInterval, τ < t → r < dist (γ t) A := by
  let S : Set unitInterval := {t | dist (γ t) A ≤ r}
  have hS : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have h0 : (0 : unitInterval) ∈ S := by
    show dist (γ 0) A ≤ r
    rw [γ.source, dist_self]; exact hr.le
  obtain ⟨τ, hτS, hmax⟩ := hS.isCompact.exists_isMaxOn ⟨0, h0⟩
    (continuous_subtype_val.continuousOn)
  have hgt : ∀ t : unitInterval, τ < t → r < dist (γ t) A := by
    intro t ht
    by_contra hle
    have hle' : t ∈ S := not_lt.mp hle
    have := isMaxOn_iff.mp hmax t hle'
    exact absurd ht (not_lt.mpr this)
  refine ⟨τ, ?_, hgt⟩
  apply le_antisymm hτS
  by_contra hlt
  have hlt' : dist (γ τ) A < r := not_le.mp hlt
  have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
  let f : ℝ → ℝ := fun s => dist (γ.extend s) A
  have hf : Continuous f := by fun_prop
  have hfτ : f τ = dist (γ τ) A := by
    show dist (γ.extend τ) A = _
    rw [Path.extend_extends']
  have hf1 : f 1 = dist B A := by
    show dist (γ.extend 1) A = _
    rw [Path.extend_one]
  have hrm : r ∈ Set.Icc (f τ) (f 1) := ⟨by rw [hfτ]; exact hlt'.le, by rw [hf1]; exact hB.le⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hτ1 hf.continuousOn hrm
  have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans τ.2.1 hs.1, hs.2⟩
  have hsτ : (τ : ℝ) < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · exfalso; rw [← h, hfτ] at hfs; linarith
    · exact h
  have h1 := hgt ⟨s, hs01⟩ hsτ
  have hfs' : f s = dist (γ ⟨s, hs01⟩) A := by
    show dist (γ.extend s) A = _
    rw [Path.extend_apply γ hs01]
  linarith




/-! Cells of the grid of mesh `h` (centred at `h • c`), local frames, and the two parallel
routes through one cell. -/

lemma ArcImg.map {P Q : ℝ × ℝ} {S : Set (ℝ × ℝ)} (h : ArcImg P Q S) (f : ℝ × ℝ → ℝ × ℝ)
    (hf : Continuous f) (hi : Function.Injective f) : ArcImg (f P) (f Q) (f '' S) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine ⟨γ.map hf, hi.comp hγ, ?_⟩
  rw [Path.map_coe, Set.range_comp]

lemma seg_coord {x y z : ℝ × ℝ} (h : z ∈ seg x y) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z.1 = x.1 + t * (y.1 - x.1) ∧ z.2 = x.2 + t * (y.2 - x.2) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht.1, ht.2, by simp, by simp⟩

lemma mem_seg_of {x y z : ℝ × ℝ} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (e1 : z.1 = x.1 + t * (y.1 - x.1)) (e2 : z.2 = x.2 + t * (y.2 - x.2)) : z ∈ seg x y := by
  refine ⟨t, ⟨h0, h1⟩, ?_⟩
  ext
  · simp [e1]
  · simp [e2]

/-- the four unit directions of the grid -/
def IsDir (d : ℤ × ℤ) : Prop := d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

/-- quarter turn to the left -/
def rotZ (d : ℤ × ℤ) : ℤ × ℤ := (-d.2, d.1)

lemma isDir_neg {d : ℤ × ℤ} (h : IsDir d) : IsDir (-d) := by
  unfold IsDir at *
  rcases h with rfl | rfl | rfl | rfl <;> simp

lemma isDir_rot {d : ℤ × ℤ} (h : IsDir d) : IsDir (rotZ d) := by
  unfold IsDir rotZ at *
  rcases h with rfl | rfl | rfl | rfl <;> simp

lemma dir_cases {d e : ℤ × ℤ} (hd : IsDir d) (he : IsDir e) :
    e = d ∨ e = rotZ d ∨ e = -d ∨ e = -rotZ d := by
  unfold IsDir at hd he
  unfold rotZ
  rcases hd with rfl | rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl <;> simp

lemma dir_sq {d : ℤ × ℤ} (h : IsDir d) :
    ((d.1 : ℝ) * d.1 + (d.2 : ℝ) * d.2 = 1) ∧ ((d.1 : ℝ) * d.2 = 0) := by
  unfold IsDir at h
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

lemma rot_ne {d : ℤ × ℤ} (h : IsDir d) : rotZ d ≠ d ∧ -rotZ d ≠ d ∧ -rotZ d ≠ rotZ d ∧
    rotZ d ≠ -d ∧ -rotZ d ≠ -d := by
  unfold IsDir at h
  unfold rotZ
  rcases h with rfl | rfl | rfl | rfl <;> simp

lemma neg_ne_self_dir {d : ℤ × ℤ} (h : IsDir d) : -d ≠ d := by
  unfold IsDir at h
  rcases h with rfl | rfl | rfl | rfl <;> simp

/-- local frame at cell `c` with first axis `d`, in units of `h` -/
def Lc (h : ℝ) (c d : ℤ × ℤ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (h * ((c.1 : ℝ) + z.1 * d.1 - z.2 * d.2), h * ((c.2 : ℝ) + z.1 * d.2 + z.2 * d.1))

lemma Lc_seg (h : ℝ) (c d : ℤ × ℤ) (x y : ℝ × ℝ) :
    Lc h c d '' seg x y = seg (Lc h c d x) (Lc h c d y) := by
  ext z
  constructor
  · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    ext <;> simp [Lc] <;> ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨x + t • (y - x), ⟨t, ht, rfl⟩, ?_⟩
    ext <;> simp [Lc] <;> ring

lemma Lc_cont (h : ℝ) (c d : ℤ × ℤ) : Continuous (Lc h c d) := by
  unfold Lc; fun_prop

lemma Lc_inj {h : ℝ} (hh : 0 < h) (c d : ℤ × ℤ) (hd : IsDir d) : Function.Injective (Lc h c d) := by
  intro z w e
  simp only [Lc, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  have f1 : z.1 * d.1 - z.2 * d.2 = w.1 * d.1 - w.2 * d.2 := by
    have := mul_left_cancel₀ hh.ne' e1; linarith
  have f2 : z.1 * d.2 + z.2 * d.1 = w.1 * d.2 + w.2 * d.1 := by
    have := mul_left_cancel₀ hh.ne' e2; linarith
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp at f1 f2 <;> ext <;> linarith

/-- closed and open cells -/
def cell (h : ℝ) (c : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | |z.1 - h * c.1| ≤ h / 2 ∧ |z.2 - h * c.2| ≤ h / 2}

def icell (h : ℝ) (c : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | |z.1 - h * c.1| < h / 2 ∧ |z.2 - h * c.2| < h / 2}

def ubox : Set (ℝ × ℝ) := {z | |z.1| ≤ 1 / 2 ∧ |z.2| ≤ 1 / 2}

def uibox : Set (ℝ × ℝ) := {z | |z.1| < 1 / 2 ∧ |z.2| < 1 / 2}

lemma scale_abs {h : ℝ} (hh : 0 < h) (X : ℝ) :
    (|h * X| ≤ h / 2 ↔ |X| ≤ 1 / 2) ∧ (|h * X| < h / 2 ↔ |X| < 1 / 2) := by
  rw [abs_mul, abs_of_pos hh]
  constructor
  · constructor
    · intro k; nlinarith
    · intro k; nlinarith
  · constructor
    · intro k; nlinarith
    · intro k; nlinarith

lemma Lc_cell {h : ℝ} (hh : 0 < h) (c d : ℤ × ℤ) (hd : IsDir d) (z : ℝ × ℝ) :
    (Lc h c d z ∈ cell h c ↔ z ∈ ubox) ∧ (Lc h c d z ∈ icell h c ↔ z ∈ uibox) := by
  have e1 : (Lc h c d z).1 - h * c.1 = h * (z.1 * d.1 - z.2 * d.2) := by simp [Lc]; ring
  have e2 : (Lc h c d z).2 - h * c.2 = h * (z.1 * d.2 + z.2 * d.1) := by simp [Lc]; ring
  simp only [cell, icell, ubox, uibox, Set.mem_setOf_eq, e1, e2, (scale_abs hh _).1,
    (scale_abs hh _).2]
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [abs_neg] <;> tauto

lemma int_of_abs_lt {k : ℤ} (h : |(k : ℝ)| < 1) : k = 0 := by
  rw [abs_lt] at h
  have h1 : (-1 : ℤ) < k := by exact_mod_cast h.1
  have h2 : k < 1 := by exact_mod_cast h.2
  omega

lemma icell_cell {h : ℝ} (hh : 0 < h) {c c' : ℤ × ℤ} {z : ℝ × ℝ} (h1 : z ∈ icell h c)
    (h2 : z ∈ cell h c') : c = c' := by
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  have k1 : |((c.1 - c'.1 : ℤ) : ℝ)| < 1 := by
    have : |h * ((c.1 : ℝ) - c'.1)| < h := by
      have := abs_sub_le (h * (c.1 : ℝ)) z.1 (h * c'.1)
      rw [abs_sub_comm] at a1
      calc |h * ((c.1 : ℝ) - c'.1)| = |h * c.1 - h * c'.1| := by ring_nf
        _ ≤ |h * c.1 - z.1| + |z.1 - h * c'.1| := abs_sub_le _ _ _
        _ < h / 2 + h / 2 + 0 := by linarith
        _ = h := by ring
    rw [abs_mul, abs_of_pos hh] at this
    push_cast
    nlinarith [abs_nonneg ((c.1 : ℝ) - c'.1)]
  have k2 : |((c.2 - c'.2 : ℤ) : ℝ)| < 1 := by
    have : |h * ((c.2 : ℝ) - c'.2)| < h := by
      rw [abs_sub_comm] at a2
      calc |h * ((c.2 : ℝ) - c'.2)| = |h * c.2 - h * c'.2| := by ring_nf
        _ ≤ |h * c.2 - z.2| + |z.2 - h * c'.2| := abs_sub_le _ _ _
        _ < h / 2 + h / 2 + 0 := by linarith
        _ = h := by ring
    rw [abs_mul, abs_of_pos hh] at this
    push_cast
    nlinarith [abs_nonneg ((c.2 : ℝ) - c'.2)]
  have := int_of_abs_lt k1
  have := int_of_abs_lt k2
  ext <;> omega

/-- midpoint of the side of cell `c` in direction `d` -/
noncomputable def mid (h : ℝ) (c d : ℤ × ℤ) : ℝ × ℝ :=
  (h * ((c.1 : ℝ) + d.1 / 2), h * ((c.2 : ℝ) + d.2 / 2))

/-- the point a quarter to the left of that midpoint -/
noncomputable def quarter (h : ℝ) (c d : ℤ × ℤ) : ℝ × ℝ :=
  (h * ((c.1 : ℝ) + d.1 / 2 - d.2 / 4), h * ((c.2 : ℝ) + d.2 / 2 + d.1 / 4))

/-- an integer plus a fixed offset in `(-1/2, 1/2]` -/
lemma int_half {k : ℤ} {o : ℝ} (h : |(k : ℝ) + o| ≤ 1 / 2) (ho : |o| < 1 / 2) : k = 0 := by
  rw [abs_le] at h
  rw [abs_lt] at ho
  have h1 : (-1 : ℤ) < k := by
    have : (-1 : ℝ) < k := by linarith
    exact_mod_cast this
  have h2 : k < 1 := by
    have : (k : ℝ) < 1 := by linarith
    exact_mod_cast this
  omega

lemma int_half' {k : ℤ} {o : ℝ} (h : |(k : ℝ) + o| ≤ 1 / 2) (ho : o = 1 / 2) : k = 0 ∨ k = -1 := by
  rw [abs_le] at h
  subst ho
  have h1 : (-1 : ℤ) ≤ k := by
    have : (-1 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have h2 : k ≤ 0 := by
    have : (k : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  omega

lemma int_half'' {k : ℤ} {o : ℝ} (h : |(k : ℝ) + o| ≤ 1 / 2) (ho : o = -1 / 2) : k = 0 ∨ k = 1 := by
  rw [abs_le] at h
  subst ho
  have h1 : (0 : ℤ) ≤ k := by
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have h2 : k ≤ 1 := by
    have : (k : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  omega

lemma cell_coord {h : ℝ} (hh : 0 < h) {c' : ℤ × ℤ} {z : ℝ × ℝ} (hz : z ∈ cell h c') (c : ℤ × ℤ)
    (o1 o2 : ℝ) (e1 : z.1 = h * ((c.1 : ℝ) + o1)) (e2 : z.2 = h * ((c.2 : ℝ) + o2)) :
    |((c.1 - c'.1 : ℤ) : ℝ) + o1| ≤ 1 / 2 ∧ |((c.2 - c'.2 : ℤ) : ℝ) + o2| ≤ 1 / 2 := by
  obtain ⟨b1, b2⟩ := hz
  rw [e1] at b1
  rw [e2] at b2
  have f1 : h * ((c.1 : ℝ) + o1) - h * c'.1 = h * (((c.1 - c'.1 : ℤ) : ℝ) + o1) := by push_cast; ring
  have f2 : h * ((c.2 : ℝ) + o2) - h * c'.2 = h * (((c.2 - c'.2 : ℤ) : ℝ) + o2) := by push_cast; ring
  rw [f1, (scale_abs hh _).1] at b1
  rw [f2, (scale_abs hh _).1] at b2
  exact ⟨b1, b2⟩

lemma mid_cell {h : ℝ} (hh : 0 < h) {c d c' : ℤ × ℤ} (hd : IsDir d) (hz : mid h c d ∈ cell h c') :
    c' = c ∨ c' = c + d := by
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c (1 / 2) 0 (by unfold mid; dsimp only; push_cast; ring) (by unfold mid; dsimp only; push_cast; ring)
    have a2 := int_half k2 (by norm_num)
    rcases int_half' k1 rfl with a1 | a1
    · left; ext <;> omega
    · right; ext <;> simp <;> omega
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c (-1 / 2) 0 (by unfold mid; dsimp only; push_cast; ring) (by unfold mid; dsimp only; push_cast; ring)
    have a2 := int_half k2 (by norm_num)
    rcases int_half'' k1 rfl with a1 | a1
    · left; ext <;> omega
    · right; ext <;> simp <;> omega
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c 0 (1 / 2) (by unfold mid; dsimp only; push_cast; ring) (by unfold mid; dsimp only; push_cast; ring)
    have a1 := int_half k1 (by norm_num)
    rcases int_half' k2 rfl with a2 | a2
    · left; ext <;> omega
    · right; ext <;> simp <;> omega
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c 0 (-1 / 2) (by unfold mid; dsimp only; push_cast; ring) (by unfold mid; dsimp only; push_cast; ring)
    have a1 := int_half k1 (by norm_num)
    rcases int_half'' k2 rfl with a2 | a2
    · left; ext <;> omega
    · right; ext <;> simp <;> omega

lemma quarter_cell {h : ℝ} (hh : 0 < h) {c d c' : ℤ × ℤ} (hd : IsDir d)
    (hz : quarter h c d ∈ cell h c') : c' = c ∨ c' = c + d := by
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c (1 / 2) (1 / 4) (by unfold quarter; dsimp only; push_cast; ring) (by unfold quarter; dsimp only; push_cast; ring)
    have a2 := int_half k2 (by norm_num [abs_of_pos])
    rcases int_half' k1 rfl with a1 | a1
    · left; ext <;> omega
    · right; ext <;> simp <;> omega
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c (-1 / 2) (-1 / 4) (by unfold quarter; dsimp only; push_cast; ring)
      (by unfold quarter; dsimp only; push_cast; ring)
    have a2 := int_half k2 (by norm_num [abs_of_neg])
    rcases int_half'' k1 rfl with a1 | a1
    · left; ext <;> omega
    · right; ext <;> simp <;> omega
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c (-1 / 4) (1 / 2) (by unfold quarter; dsimp only; push_cast; ring)
      (by unfold quarter; dsimp only; push_cast; ring)
    have a1 := int_half k1 (by norm_num [abs_of_neg])
    rcases int_half' k2 rfl with a2 | a2
    · left; ext <;> omega
    · right; ext <;> simp <;> omega
  · obtain ⟨k1, k2⟩ := cell_coord hh hz c (1 / 4) (-1 / 2) (by unfold quarter; dsimp only; push_cast; ring)
      (by unfold quarter; dsimp only; push_cast; ring)
    have a1 := int_half k1 (by norm_num [abs_of_pos])
    rcases int_half'' k2 rfl with a2 | a2
    · left; ext <;> omega
    · right; ext <;> simp <;> omega

lemma mid_ne_quarter {h : ℝ} (hh : 0 < h) {c d c' d' : ℤ × ℤ} (hd : IsDir d) (hd' : IsDir d') :
    mid h c d ≠ quarter h c' d' := by
  intro e
  simp only [mid, quarter, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  have f1 := mul_left_cancel₀ hh.ne' e1
  have f2 := mul_left_cancel₀ hh.ne' e2
  have i1 : ((4 * c.1 + 2 * d.1 - 4 * c'.1 - 2 * d'.1 + d'.2 : ℤ) : ℝ) = 0 := by
    push_cast; linarith
  have i2 : ((4 * c.2 + 2 * d.2 - 4 * c'.2 - 2 * d'.2 - d'.1 : ℤ) : ℝ) = 0 := by
    push_cast; linarith
  have j1 : (4 * c.1 + 2 * d.1 - 4 * c'.1 - 2 * d'.1 + d'.2 : ℤ) = 0 := by exact_mod_cast i1
  have j2 : (4 * c.2 + 2 * d.2 - 4 * c'.2 - 2 * d'.2 - d'.1 : ℤ) = 0 := by exact_mod_cast i2
  obtain ⟨p1, p2⟩ := d'
  simp only [IsDir, Prod.mk.injEq] at hd'
  dsimp only at j1 j2
  omega


/-! The two routes through one cell (in local units), and along a chain of cells. -/

inductive Turn
  | straight
  | left
  | right

noncomputable def eA : Turn → ℝ × ℝ
  | .straight => (1 / 2, 0)
  | .left => (0, 1 / 2)
  | .right => (0, -1 / 2)

noncomputable def kB : Turn → ℝ × ℝ
  | .straight => (0, 1 / 4)
  | .left => (-1 / 4, 1 / 4)
  | .right => (1 / 4, 1 / 4)

noncomputable def eB : Turn → ℝ × ℝ
  | .straight => (1 / 2, 1 / 4)
  | .left => (-1 / 4, 1 / 2)
  | .right => (1 / 4, -1 / 2)

def stdA (t : Turn) : Set (ℝ × ℝ) := seg (-1 / 2, 0) (0, 0) ∪ seg (0, 0) (eA t)

def stdB (t : Turn) : Set (ℝ × ℝ) := seg (-1 / 2, 1 / 4) (kB t) ∪ seg (kB t) (eB t)

lemma stdA_arc (t : Turn) : ArcImg (-1 / 2, 0) (eA t) (stdA t) := by
  have h1 : ArcImg ((-1 / 2 : ℝ), (0 : ℝ)) (0, 0) (seg (-1 / 2, 0) (0, 0)) :=
    arcImg_seg (by norm_num [Prod.ext_iff])
  have h2 : ArcImg ((0 : ℝ), (0 : ℝ)) (eA t) (seg (0, 0) (eA t)) :=
    arcImg_seg (by cases t <;> norm_num [eA, Prod.ext_iff])
  refine h1.trans h2 ?_
  intro z hz1 hz2
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz1
  obtain ⟨u, u0, u1, b1, b2⟩ := seg_coord hz2
  cases t <;> simp only [eA] at b1 b2 <;> ext <;> simp at a1 a2 b1 b2 ⊢ <;> linarith

lemma stdB_arc (t : Turn) : ArcImg (-1 / 2, 1 / 4) (eB t) (stdB t) := by
  have h1 : ArcImg ((-1 / 2 : ℝ), (1 / 4 : ℝ)) (kB t) (seg (-1 / 2, 1 / 4) (kB t)) :=
    arcImg_seg (by cases t <;> simp [kB] <;> norm_num)
  have h2 : ArcImg (kB t) (eB t) (seg (kB t) (eB t)) :=
    arcImg_seg (by cases t <;> simp [kB, eB] <;> norm_num)
  refine h1.trans h2 ?_
  intro z hz1 hz2
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz1
  obtain ⟨u, u0, u1, b1, b2⟩ := seg_coord hz2
  cases t <;> simp only [kB, eB] at a1 a2 b1 b2 ⊢ <;> ext <;> simp at a1 a2 b1 b2 ⊢ <;> linarith

lemma stdAB (t : Turn) (z : ℝ × ℝ) (h1 : z ∈ stdA t) (h2 : z ∈ stdB t) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  · obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord h1
    obtain ⟨u, u0, u1, b1, b2⟩ := seg_coord h2
    cases t <;> simp only [eA, kB, eB] at a1 a2 b1 b2 <;> simp at a1 a2 b1 b2 <;> linarith

lemma conv_abs {a b s r : ℝ} (s0 : 0 ≤ s) (s1 : s ≤ 1) (ha : |a| ≤ r) (hb : |b| ≤ r) :
    |a + s * (b - a)| ≤ r := by
  have e : a + s * (b - a) = (1 - s) * a + s * b := by ring
  rw [e]
  calc |(1 - s) * a + s * b| ≤ |(1 - s) * a| + |s * b| := abs_add_le _ _
    _ = (1 - s) * |a| + s * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith only [s1] : (0 : ℝ) ≤ 1 - s), abs_of_nonneg s0]
    _ ≤ (1 - s) * r + s * r := add_le_add
      (mul_le_mul_of_nonneg_left ha (by linarith only [s1])) (mul_le_mul_of_nonneg_left hb s0)
    _ = r := by ring

lemma conv_abs_lt {a b s r : ℝ} (s0 : 0 < s) (s1 : s ≤ 1) (ha : |a| ≤ r) (hb : |b| < r) :
    |a + s * (b - a)| < r := by
  have e : a + s * (b - a) = (1 - s) * a + s * b := by ring
  rw [e]
  calc |(1 - s) * a + s * b| ≤ |(1 - s) * a| + |s * b| := abs_add_le _ _
    _ = (1 - s) * |a| + s * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith only [s1] : (0 : ℝ) ≤ 1 - s), abs_of_pos s0]
    _ < (1 - s) * r + s * r := add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left ha (by linarith only [s1])) (mul_lt_mul_of_pos_left hb s0)
    _ = r := by ring

lemma conv_abs_lt' {a b s r : ℝ} (s0 : 0 ≤ s) (s1 : s < 1) (ha : |a| < r) (hb : |b| ≤ r) :
    |a + s * (b - a)| < r := by
  have e : a + s * (b - a) = b + (1 - s) * (a - b) := by ring
  rw [e]
  exact conv_abs_lt (by linarith only [s1]) (by linarith only [s0]) hb ha

lemma seg_ubox {x y z : ℝ × ℝ} (hx : x ∈ ubox) (hy : y ∈ ubox) (hz : z ∈ seg x y) : z ∈ ubox := by
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
  show |z.1| ≤ 1 / 2 ∧ |z.2| ≤ 1 / 2
  rw [a1, a2]
  exact ⟨conv_abs s0 s1 hx.1 hy.1, conv_abs s0 s1 hx.2 hy.2⟩

lemma seg_uibox_r {x y z : ℝ × ℝ} (hx : x ∈ ubox) (hy : y ∈ uibox) (hz : z ∈ seg x y) :
    z = x ∨ z ∈ uibox := by
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
  rcases eq_or_lt_of_le s0 with e | e
  · left; ext
    · rw [a1, ← e]; ring
    · rw [a2, ← e]; ring
  · right
    show |z.1| < 1 / 2 ∧ |z.2| < 1 / 2
    rw [a1, a2]
    exact ⟨conv_abs_lt e s1 hx.1 hy.1, conv_abs_lt e s1 hx.2 hy.2⟩

lemma seg_uibox_l {x y z : ℝ × ℝ} (hx : x ∈ uibox) (hy : y ∈ ubox) (hz : z ∈ seg x y) :
    z = y ∨ z ∈ uibox := by
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
  rcases eq_or_lt_of_le s1 with e | e
  · left; ext
    · rw [a1, e]; ring
    · rw [a2, e]; ring
  · right
    show |z.1| < 1 / 2 ∧ |z.2| < 1 / 2
    rw [a1, a2]
    exact ⟨conv_abs_lt' s0 e hx.1 hy.1, conv_abs_lt' s0 e hx.2 hy.2⟩

lemma ubox_of_uibox {x : ℝ × ℝ} (h : x ∈ uibox) : x ∈ ubox := ⟨h.1.le, h.2.le⟩

lemma stdA_box (t : Turn) (z : ℝ × ℝ) (hz : z ∈ stdA t) :
    z ∈ ubox ∧ (z ∈ uibox ∨ z = (-1 / 2, 0) ∨ z = eA t) := by
  have p1 : ((-1 / 2 : ℝ), (0 : ℝ)) ∈ ubox := by norm_num [ubox]
  have p2 : ((0 : ℝ), (0 : ℝ)) ∈ uibox := by norm_num [uibox]
  have p3 : eA t ∈ ubox := by cases t <;> norm_num [eA, ubox]
  rcases hz with hz | hz
  · refine ⟨seg_ubox p1 (ubox_of_uibox p2) hz, ?_⟩
    rcases seg_uibox_r p1 p2 hz with h | h
    · right; left; exact h
    · left; exact h
  · refine ⟨seg_ubox (ubox_of_uibox p2) p3 hz, ?_⟩
    rcases seg_uibox_l p2 p3 hz with h | h
    · right; right; exact h
    · left; exact h

lemma stdB_box (t : Turn) (z : ℝ × ℝ) (hz : z ∈ stdB t) :
    z ∈ ubox ∧ (z ∈ uibox ∨ z = (-1 / 2, 1 / 4) ∨ z = eB t) := by
  have p1 : ((-1 / 2 : ℝ), (1 / 4 : ℝ)) ∈ ubox := by norm_num [ubox]
  have p2 : kB t ∈ uibox := by cases t <;> norm_num [kB, uibox]
  have p3 : eB t ∈ ubox := by cases t <;> norm_num [eB, ubox]
  rcases hz with hz | hz
  · refine ⟨seg_ubox p1 (ubox_of_uibox p2) hz, ?_⟩
    rcases seg_uibox_r p1 p2 hz with h | h
    · right; left; exact h
    · left; exact h
  · refine ⟨seg_ubox (ubox_of_uibox p2) p3 hz, ?_⟩
    rcases seg_uibox_l p2 p3 hz with h | h
    · right; right; exact h
    · left; exact h

/-- the turn made at a cell entered in direction `din` and left in direction `dout` -/
def turnOf (din dout : ℤ × ℤ) : Turn :=
  if dout = din then .straight else if dout = rotZ din then .left else .right

def pieceA (h : ℝ) (c din dout : ℤ × ℤ) : Set (ℝ × ℝ) := Lc h c din '' stdA (turnOf din dout)

def pieceB (h : ℝ) (c din dout : ℤ × ℤ) : Set (ℝ × ℝ) := Lc h c din '' stdB (turnOf din dout)

lemma Lc_entryA (h : ℝ) (c din : ℤ × ℤ) : Lc h c din (-1 / 2, 0) = mid h c (-din) := by
  unfold Lc mid; ext <;> dsimp only <;> (try simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, rotZ]) <;> push_cast <;> ring

lemma Lc_entryB (h : ℝ) (c din : ℤ × ℤ) : Lc h c din (-1 / 2, 1 / 4) = quarter h (c - din) din := by
  unfold Lc quarter; ext <;> dsimp only <;> (try simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, rotZ]) <;> push_cast <;> ring

lemma Lc_exit (h : ℝ) (c din dout : ℤ × ℤ) (hd : IsDir din) (hd' : IsDir dout)
    (hne : dout ≠ -din) :
    Lc h c din (eA (turnOf din dout)) = mid h c dout ∧
      Lc h c din (eB (turnOf din dout)) = quarter h c dout := by
  obtain ⟨r1, r2, r3, -, -⟩ := rot_ne hd
  rcases dir_cases hd hd' with e | e | e | e
  · subst e
    simp only [turnOf, if_pos rfl, eA, eB]
    unfold Lc mid quarter
    constructor <;> ext <;> dsimp only <;> (try simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, rotZ]) <;> push_cast <;> ring
  · subst e
    simp only [turnOf, if_neg r1, if_pos rfl, eA, eB]
    unfold Lc mid quarter rotZ
    constructor <;> ext <;> dsimp only <;> (try simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, rotZ]) <;> push_cast <;> ring
  · exact absurd e hne
  · subst e
    simp only [turnOf, if_neg r2, if_neg r3, eA, eB]
    unfold Lc mid quarter rotZ
    constructor <;> ext <;> dsimp only <;> (try simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, rotZ]) <;> push_cast <;> ring

lemma piece_props {h : ℝ} (hh : 0 < h) {c din dout : ℤ × ℤ} (hd : IsDir din) (hd' : IsDir dout)
    (hne : dout ≠ -din) :
    ArcImg (mid h c (-din)) (mid h c dout) (pieceA h c din dout) ∧
    ArcImg (quarter h (c - din) din) (quarter h c dout) (pieceB h c din dout) ∧
    (∀ z, z ∈ pieceA h c din dout → z ∈ pieceB h c din dout → False) ∧
    (∀ z ∈ pieceA h c din dout, z ∈ cell h c ∧
      (z ∈ icell h c ∨ z = mid h c (-din) ∨ z = mid h c dout)) ∧
    (∀ z ∈ pieceB h c din dout, z ∈ cell h c ∧
      (z ∈ icell h c ∨ z = quarter h (c - din) din ∨ z = quarter h c dout)) := by
  obtain ⟨x1, x2⟩ := Lc_exit h c din dout hd hd' hne
  have hinj := Lc_inj hh c din hd
  have hcont := Lc_cont h c din
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (stdA_arc (turnOf din dout)).map _ hcont hinj
    rw [Lc_entryA, x1] at this; exact this
  · have := (stdB_arc (turnOf din dout)).map _ hcont hinj
    rw [Lc_entryB, x2] at this; exact this
  · rintro z ⟨w1, hw1, rfl⟩ ⟨w2, hw2, e⟩
    have := hinj e
    subst this
    exact stdAB _ _ hw1 hw2
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨b1, b2⟩ := stdA_box _ w hw
    refine ⟨(Lc_cell hh c din hd w).1.mpr b1, ?_⟩
    rcases b2 with b2 | b2 | b2
    · left; exact (Lc_cell hh c din hd w).2.mpr b2
    · right; left; rw [b2, Lc_entryA]
    · right; right; rw [b2, x1]
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨b1, b2⟩ := stdB_box _ w hw
    refine ⟨(Lc_cell hh c din hd w).1.mpr b1, ?_⟩
    rcases b2 with b2 | b2 | b2
    · left; exact (Lc_cell hh c din hd w).2.mpr b2
    · right; left; rw [b2, Lc_entryB]
    · right; right; rw [b2, x2]

/-- the route along a chain of cells -/
def chainA (h : ℝ) : ℤ × ℤ → List (ℤ × ℤ) → ℤ × ℤ → Set (ℝ × ℝ)
  | _, [], _ => ∅
  | din, [c], dout => pieceA h c din dout
  | din, c :: c' :: rest, dout => pieceA h c din (c' - c) ∪ chainA h (c' - c) (c' :: rest) dout

def chainB (h : ℝ) : ℤ × ℤ → List (ℤ × ℤ) → ℤ × ℤ → Set (ℝ × ℝ)
  | _, [], _ => ∅
  | din, [c], dout => pieceB h c din dout
  | din, c :: c' :: rest, dout => pieceB h c din (c' - c) ∪ chainB h (c' - c) (c' :: rest) dout

def IsMid (h : ℝ) (z : ℝ × ℝ) : Prop := ∃ c d, IsDir d ∧ z = mid h c d

def IsQuarter (h : ℝ) (z : ℝ × ℝ) : Prop := ∃ c d, IsDir d ∧ z = quarter h c d

lemma mid_shift (h : ℝ) (c c' : ℤ × ℤ) : mid h c' (-(c' - c)) = mid h c (c' - c) := by
  unfold mid; ext <;> dsimp only <;> (try simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, rotZ]) <;> push_cast <;> ring

theorem chain_props {h : ℝ} (hh : 0 < h) : ∀ (cs : List (ℤ × ℤ)) (din dout c0 cl : ℤ × ℤ),
    cs.head? = some c0 → cs.getLast? = some cl → cs.Nodup →
    cs.IsChain (fun c c' => IsDir (c' - c)) → IsDir din → IsDir dout →
    c0 - din ∉ cs → cl + dout ∉ cs → cl + dout ≠ c0 - din →
    ArcImg (mid h c0 (-din)) (mid h cl dout) (chainA h din cs dout) ∧
    ArcImg (quarter h (c0 - din) din) (quarter h cl dout) (chainB h din cs dout) ∧
    (∀ z, z ∈ chainA h din cs dout → z ∈ chainB h din cs dout → False) ∧
    (∀ z ∈ chainA h din cs dout, ∃ c ∈ cs, z ∈ cell h c ∧ (z ∈ icell h c ∨ IsMid h z)) ∧
    (∀ z ∈ chainB h din cs dout, ∃ c ∈ cs, z ∈ cell h c ∧ (z ∈ icell h c ∨ IsQuarter h z)) := by
  intro cs
  induction cs with
  | nil => intro din dout c0 cl h0; simp at h0
  | cons c tl ih =>
    intro din dout c0 cl h0 hl hnd hch hdin hdout hpre hpost hpp
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    cases tl with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      have hne : dout ≠ -din := by
        intro e; apply hpp; rw [e, sub_eq_add_neg]
      obtain ⟨hA, hB, hAB, hAc, hBc⟩ := piece_props (c := c) hh hdin hdout hne
      refine ⟨hA, hB, hAB, ?_, ?_⟩
      · intro z hz
        obtain ⟨h1, h2⟩ := hAc z hz
        refine ⟨c, List.mem_singleton_self _, h1, ?_⟩
        rcases h2 with h2 | h2 | h2
        · left; exact h2
        · right; exact ⟨c, -din, isDir_neg hdin, h2⟩
        · right; exact ⟨c, dout, hdout, h2⟩
      · intro z hz
        obtain ⟨h1, h2⟩ := hBc z hz
        refine ⟨c, List.mem_singleton_self _, h1, ?_⟩
        rcases h2 with h2 | h2 | h2
        · left; exact h2
        · right; exact ⟨c - din, din, hdin, h2⟩
        · right; exact ⟨c, dout, hdout, h2⟩
    | cons c' rest =>
      have hl' : (c' :: rest).getLast? = some cl := by
        rw [List.getLast?_cons_cons] at hl; exact hl
      have hd1 : IsDir (c' - c) := (List.isChain_cons_cons.mp hch).1
      have hch' := (List.isChain_cons_cons.mp hch).2
      have hnd' : (c' :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hc_notin : c ∉ c' :: rest := (List.nodup_cons.mp hnd).1
      have hne1 : c' - c ≠ -din := by
        intro e
        apply hpre
        have : c' = c - din := by rw [sub_eq_add_neg, ← e]; abel
        rw [← this]; exact List.mem_cons_of_mem _ List.mem_cons_self
      have hpre' : c' - (c' - c) ∉ c' :: rest := by rw [sub_sub_cancel]; exact hc_notin
      have hpost' : cl + dout ∉ c' :: rest := fun hm => hpost (List.mem_cons_of_mem _ hm)
      have hpp' : cl + dout ≠ c' - (c' - c) := by
        rw [sub_sub_cancel]; intro e; exact hpost (e ▸ List.mem_cons_self)
      obtain ⟨iA, iB, iAB, iAc, iBc⟩ := ih (c' - c) dout c' cl rfl hl' hnd' hch' hd1 hdout
        hpre' hpost' hpp'
      obtain ⟨pA, pB, pAB, pAc, pBc⟩ := piece_props (c := c) hh hdin hd1 hne1
      rw [mid_shift] at iA
      rw [sub_sub_cancel] at iB
      have cross : ∀ z c'', c'' ∈ c' :: rest → z ∈ cell h c'' → z ∈ cell h c →
          ¬ z ∈ icell h c ∧ ¬ z ∈ icell h c'' := by
        intro z c'' hc'' h1 h2
        have hcc : c'' ≠ c := fun e => hc_notin (e ▸ hc'')
        exact ⟨fun h3 => hcc (icell_cell hh h3 h1).symm, fun h3 => hcc (icell_cell hh h3 h2)⟩
      have jA : ∀ z, z ∈ pieceA h c din (c' - c) → z ∈ chainA h (c' - c) (c' :: rest) dout →
          z = mid h c (c' - c) := by
        intro z hz1 hz2
        obtain ⟨c'', hc'', hz3, -⟩ := iAc z hz2
        obtain ⟨hzc, hz4⟩ := pAc z hz1
        have hcc : c'' ≠ c := fun e => hc_notin (e ▸ hc'')
        rcases hz4 with hz4 | hz4 | hz4
        · exact absurd hz4 (cross z c'' hc'' hz3 hzc).1
        · exfalso
          rw [hz4] at hz3
          rcases mid_cell hh (isDir_neg hdin) hz3 with e | e
          · exact hcc e
          · apply hpre
            rw [← sub_eq_add_neg] at e
            rw [← e]; exact List.mem_cons_of_mem _ hc''
        · exact hz4
      have jB : ∀ z, z ∈ pieceB h c din (c' - c) → z ∈ chainB h (c' - c) (c' :: rest) dout →
          z = quarter h c (c' - c) := by
        intro z hz1 hz2
        obtain ⟨c'', hc'', hz3, -⟩ := iBc z hz2
        obtain ⟨hzc, hz4⟩ := pBc z hz1
        have hcc : c'' ≠ c := fun e => hc_notin (e ▸ hc'')
        rcases hz4 with hz4 | hz4 | hz4
        · exact absurd hz4 (cross z c'' hc'' hz3 hzc).1
        · exfalso
          rw [hz4] at hz3
          rcases quarter_cell hh hdin hz3 with e | e
          · apply hpre; rw [← e]; exact List.mem_cons_of_mem _ hc''
          · rw [sub_add_cancel] at e; exact hcc e
        · exact hz4
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show ArcImg _ _ (pieceA h c din (c' - c) ∪ chainA h (c' - c) (c' :: rest) dout)
        exact pA.trans iA jA
      · show ArcImg _ _ (pieceB h c din (c' - c) ∪ chainB h (c' - c) (c' :: rest) dout)
        exact pB.trans iB jB
      · show ∀ z, z ∈ pieceA h c din (c' - c) ∪ chainA h (c' - c) (c' :: rest) dout →
          z ∈ pieceB h c din (c' - c) ∪ chainB h (c' - c) (c' :: rest) dout → False
        intro z hz1 hz2
        rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
        · exact pAB z hz1 hz2
        · obtain ⟨c'', hc'', hz3, hz4⟩ := iBc z hz2
          obtain ⟨hzc, hz5⟩ := pAc z hz1
          obtain ⟨n1, n2⟩ := cross z c'' hc'' hz3 hzc
          rcases hz4 with hz4 | ⟨q1, q2, hq, hq'⟩
          · exact n2 hz4
          · rcases hz5 with hz5 | hz5 | hz5
            · exact n1 hz5
            · exact mid_ne_quarter hh (isDir_neg hdin) hq (hz5.symm.trans hq')
            · exact mid_ne_quarter hh hd1 hq (hz5.symm.trans hq')
        · obtain ⟨c'', hc'', hz3, hz4⟩ := iAc z hz1
          obtain ⟨hzc, hz5⟩ := pBc z hz2
          obtain ⟨n1, n2⟩ := cross z c'' hc'' hz3 hzc
          rcases hz4 with hz4 | ⟨q1, q2, hq, hq'⟩
          · exact n2 hz4
          · rcases hz5 with hz5 | hz5 | hz5
            · exact n1 hz5
            · exact mid_ne_quarter hh hq hdin (hq'.symm.trans hz5)
            · exact mid_ne_quarter hh hq hd1 (hq'.symm.trans hz5)
        · exact iAB z hz1 hz2
      · show ∀ z ∈ pieceA h c din (c' - c) ∪ chainA h (c' - c) (c' :: rest) dout, _
        intro z hz
        rcases hz with hz | hz
        · obtain ⟨h1, h2⟩ := pAc z hz
          refine ⟨c, List.mem_cons_self, h1, ?_⟩
          rcases h2 with h2 | h2 | h2
          · left; exact h2
          · right; exact ⟨c, -din, isDir_neg hdin, h2⟩
          · right; exact ⟨c, c' - c, hd1, h2⟩
        · obtain ⟨c'', hc'', h1, h2⟩ := iAc z hz
          exact ⟨c'', List.mem_cons_of_mem _ hc'', h1, h2⟩
      · show ∀ z ∈ pieceB h c din (c' - c) ∪ chainB h (c' - c) (c' :: rest) dout, _
        intro z hz
        rcases hz with hz | hz
        · obtain ⟨h1, h2⟩ := pBc z hz
          refine ⟨c, List.mem_cons_self, h1, ?_⟩
          rcases h2 with h2 | h2 | h2
          · left; exact h2
          · right; exact ⟨c - din, din, hdin, h2⟩
          · right; exact ⟨c, c' - c, hd1, h2⟩
        · obtain ⟨c'', hc'', h1, h2⟩ := iBc z hz
          exact ⟨c'', List.mem_cons_of_mem _ hc'', h1, h2⟩


/-- grid adjacency -/
def gAdj (a b : ℤ × ℤ) : Prop :=
  b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1)

/-- the grid graph on `ℤ × ℤ` -/
def gridG : SimpleGraph (ℤ × ℤ) where
  Adj a b := gAdj a b
  symm := ⟨by
    intro a b h
    unfold gAdj at *
    rcases h with h | h | h | h
    · right; left; exact h
    · left; exact h
    · right; right; right; exact h
    · right; right; left; exact h⟩
  loopless := ⟨by
    intro a h
    unfold gAdj at h
    obtain ⟨a1, a2⟩ := a
    simp only [Prod.mk.injEq] at h
    omega⟩

lemma gridG_adj {a b : ℤ × ℤ} : gridG.Adj a b ↔ gAdj a b := Iff.rfl

/-- the cell containing `x` -/
noncomputable def cellOf (h : ℝ) (x : ℝ × ℝ) : ℤ × ℤ := (⌊x.1 / h⌋, ⌊x.2 / h⌋)

/-- lower-left corner of a cell -/
def corner (h : ℝ) (c : ℤ × ℤ) : ℝ × ℝ := ((c.1 : ℝ) * h, (c.2 : ℝ) * h)

lemma floor_close {h a : ℝ} (hh : 0 < h) : |(⌊a / h⌋ : ℝ) * h - a| < h := by
  have h1 := Int.floor_le (a / h)
  have h2 := Int.lt_floor_add_one (a / h)
  have e : a / h * h = a := div_mul_cancel₀ a hh.ne'
  rw [abs_lt]
  constructor
  · nlinarith
  · nlinarith

lemma dist_corner_cellOf {h : ℝ} (hh : 0 < h) (x : ℝ × ℝ) : dist (corner h (cellOf h x)) x < h := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨floor_close hh, floor_close hh⟩

lemma floor_step {h a b : ℝ} (hh : 0 < h) (hab : |a - b| < h) : |⌊a / h⌋ - ⌊b / h⌋| ≤ 1 := by
  have h1 := Int.floor_le (a / h)
  have h2 := Int.lt_floor_add_one (a / h)
  have h3 := Int.floor_le (b / h)
  have h4 := Int.lt_floor_add_one (b / h)
  have hd : |a / h - b / h| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh]; exact hab
  rw [abs_lt] at hd
  have k1 : ((⌊a / h⌋ - ⌊b / h⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have k2 : ((⌊b / h⌋ - ⌊a / h⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have k1' : ⌊a / h⌋ - ⌊b / h⌋ < 2 := by exact_mod_cast k1
  have k2' : ⌊b / h⌋ - ⌊a / h⌋ < 2 := by exact_mod_cast k2
  rw [abs_le]; constructor <;> omega

lemma walk_x (c1 c2 a : ℤ) (h : |a - c1| ≤ 1) :
    ∃ w : gridG.Walk (c1, c2) (a, c2), ∀ y ∈ w.support, y = (c1, c2) ∨ y = (a, c2) := by
  rcases (show a = c1 ∨ a = c1 + 1 ∨ a = c1 - 1 by rw [abs_le] at h; omega) with rfl | rfl | rfl
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by left; rfl)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by right; left; simp)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto

lemma walk_y (c1 c2 b : ℤ) (h : |b - c2| ≤ 1) :
    ∃ w : gridG.Walk (c1, c2) (c1, b), ∀ y ∈ w.support, y = (c1, c2) ∨ y = (c1, b) := by
  rcases (show b = c2 ∨ b = c2 + 1 ∨ b = c2 - 1 by rw [abs_le] at h; omega) with rfl | rfl | rfl
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by right; right; left; rfl)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by right; right; right; simp)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto

lemma step_walk (c c' : ℤ × ℤ) (h1 : |c'.1 - c.1| ≤ 1) (h2 : |c'.2 - c.2| ≤ 1) :
    ∃ w : gridG.Walk c c', ∀ y ∈ w.support, y = c ∨ y = (c'.1, c.2) ∨ y = c' := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := c'
  obtain ⟨w1, hw1⟩ := walk_x c1 c2 d1 h1
  obtain ⟨w2, hw2⟩ := walk_y d1 c2 d2 h2
  refine ⟨w1.append w2, ?_⟩
  intro y hy
  rw [SimpleGraph.Walk.mem_support_append_iff] at hy
  rcases hy with hy | hy
  · rcases hw1 y hy with h | h
    · left; exact h
    · right; left; exact h
  · rcases hw2 y hy with h | h
    · right; left; exact h
    · right; right; exact h

/-- the walk of cells along an arc -/
theorem arc_walk {x y : ℝ × ℝ} (γ : Path x y) {h : ℝ} (hh : 0 < h) :
    ∃ w : gridG.Walk (cellOf h x) (cellOf h y),
      (∀ c ∈ w.support, ∃ t : unitInterval, dist (corner h c) (γ t) < 2 * h) ∧
      w.support.Pairwise (fun a b => ∃ ta tb : unitInterval, ta ≤ tb ∧
        dist (corner h a) (γ ta) < 2 * h ∧ dist (corner h b) (γ tb) < 2 * h) := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) h hh
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN' : (1 : ℝ) / N < δ := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hδ] at hN; linarith
  let T : ℕ → unitInterval := fun k => Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)
  have hTval : ∀ k, k ≤ N → (T k : ℝ) = (k : ℝ) / N := by
    intro k hk
    simp only [T]
    rw [Set.projIcc_of_mem]
    constructor
    · positivity
    · rw [div_le_one hNpos]; exact_mod_cast hk
  have hTmono : ∀ k, k + 1 ≤ N → T k ≤ T (k + 1) := by
    intro k hk
    show (T k : ℝ) ≤ T (k + 1)
    rw [hTval k (by omega), hTval (k + 1) hk]
    apply div_le_div_of_nonneg_right _ hNpos.le
    push_cast; linarith
  have hTclose : ∀ k, k + 1 ≤ N → dist (γ (T k)) (γ (T (k + 1))) < h := by
    intro k hk
    apply hU
    rw [Subtype.dist_eq, hTval k (by omega), hTval (k + 1) hk, Real.dist_eq]
    rw [show (k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N = -(1 / N) by push_cast; ring, abs_neg,
      abs_of_pos (by positivity)]
    exact hN'
  -- induction over the samples
  have key : ∀ k, k ≤ N → ∃ w : gridG.Walk (cellOf h (γ 0)) (cellOf h (γ (T k))),
      (∀ c ∈ w.support, ∃ t : unitInterval, t ≤ T k ∧ dist (corner h c) (γ t) < 2 * h) ∧
      w.support.Pairwise (fun a b => ∃ ta tb : unitInterval, ta ≤ tb ∧
        dist (corner h a) (γ ta) < 2 * h ∧ dist (corner h b) (γ tb) < 2 * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hT0 : T 0 = 0 := by
        apply Subtype.ext; rw [hTval 0 (Nat.zero_le _)]; simp
      rw [hT0]
      refine ⟨SimpleGraph.Walk.nil, ?_, by simp⟩
      intro c hc
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hc
      subst hc
      exact ⟨0, le_refl _, lt_trans (dist_corner_cellOf hh _) (by linarith)⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hwn, hwp⟩ := ih (by omega)
      have hcl := hTclose k hk
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hcl
      have hs1 : |(cellOf h (γ (T (k + 1)))).1 - (cellOf h (γ (T k))).1| ≤ 1 := by
        rw [abs_sub_comm]; exact floor_step hh hcl.1
      have hs2 : |(cellOf h (γ (T (k + 1)))).2 - (cellOf h (γ (T k))).2| ≤ 1 := by
        rw [abs_sub_comm]; exact floor_step hh hcl.2
      obtain ⟨w', hw'⟩ := step_walk (cellOf h (γ (T k))) (cellOf h (γ (T (k + 1)))) hs1 hs2
      -- every new cell is near γ (T k)
      have hnear : ∀ y ∈ w'.support, dist (corner h y) (γ (T k)) < 2 * h := by
        intro y hy
        have dc := dist_corner_cellOf hh (γ (T k))
        have dc' := dist_corner_cellOf hh (γ (T (k + 1)))
        have hcl2 := hTclose k hk
        rcases hw' y hy with rfl | rfl | rfl
        · linarith
        · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at dc dc' hcl2
          simp only [corner] at dc dc' ⊢
          constructor
          · calc |((cellOf h (γ (T (k + 1)))).1 : ℝ) * h - (γ (T k)).1|
                ≤ |((cellOf h (γ (T (k + 1)))).1 : ℝ) * h - (γ (T (k + 1))).1| + |(γ (T k)).1 - (γ (T (k + 1))).1| := by
                  rw [abs_sub_comm (γ (T k)).1]; exact abs_sub_le _ _ _
              _ < h + h := add_lt_add dc'.1 hcl2.1
              _ = 2 * h := by ring
          · linarith [dc.2]
        · calc dist (corner h (cellOf h (γ (T (k + 1))))) (γ (T k))
              ≤ dist (corner h (cellOf h (γ (T (k + 1))))) (γ (T (k + 1))) + dist (γ (T (k + 1))) (γ (T k)) :=
                dist_triangle _ _ _
            _ < h + h := add_lt_add dc' (by rw [dist_comm]; exact hcl2)
            _ = 2 * h := by ring
      refine ⟨w.append w', ?_, ?_⟩
      · intro y hy
        rw [SimpleGraph.Walk.mem_support_append_iff] at hy
        rcases hy with hy | hy
        · obtain ⟨t, ht, hd⟩ := hwn y hy
          exact ⟨t, le_trans ht (hTmono k hk), hd⟩
        · exact ⟨T k, hTmono k hk, hnear y hy⟩
      · rw [SimpleGraph.Walk.support_append, List.pairwise_append]
        refine ⟨hwp, ?_, ?_⟩
        · apply List.Pairwise.imp_of_mem (R := fun _ _ => True)
          · intro a b ha hb _
            exact ⟨T k, T k, le_refl _, hnear a (List.mem_of_mem_tail ha),
              hnear b (List.mem_of_mem_tail hb)⟩
          · exact List.pairwise_of_forall (fun _ _ => trivial)
        · intro a ha b hb
          obtain ⟨t, ht, hd⟩ := hwn a ha
          exact ⟨t, T k, ht, hd, hnear b (List.mem_of_mem_tail hb)⟩
  obtain ⟨w, hwn, hwp⟩ := key N le_rfl
  have hTN : T N = 1 := by
    apply Subtype.ext; rw [hTval N le_rfl]; simp [hNpos.ne']
  refine ⟨w.copy (by rw [Path.source]) (by rw [hTN, Path.target]), ?_, ?_⟩
  · intro c hc
    rw [SimpleGraph.Walk.support_copy] at hc
    obtain ⟨t, _, hd⟩ := hwn c hc
    exact ⟨t, hd⟩
  · rw [SimpleGraph.Walk.support_copy]; exact hwp



/-! Walks of cells: grid steps are unit directions, straight rows, the lattice point's cell. -/

lemma gAdj_dir {a b : ℤ × ℤ} (h : gAdj a b) : IsDir (b - a) := by
  unfold gAdj at h
  unfold IsDir
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left; ext <;> simp <;> omega
  · right; left; ext <;> simp <;> omega
  · right; right; left; ext <;> simp <;> omega
  · right; right; right; ext <;> simp <;> omega

lemma dir_gAdj {a b : ℤ × ℤ} (h : IsDir (b - a)) : gridG.Adj a b := by
  rw [gridG_adj]
  unfold gAdj
  unfold IsDir at h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk_sub_mk, Prod.mk.injEq] at h ⊢
  omega

lemma row_walk (c d : ℤ × ℤ) (hd : IsDir d) : ∀ n : ℕ, ∃ w : gridG.Walk c (c + (n : ℤ) • d),
    ∀ x ∈ w.support, ∃ j : ℕ, j ≤ n ∧ x = c + (j : ℤ) • d
  | 0 => ⟨SimpleGraph.Walk.nil.copy rfl (by simp), by
      intro x hx
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      exact ⟨0, le_rfl, by simp [hx]⟩⟩
  | n + 1 => by
    obtain ⟨w, hw⟩ := row_walk c d hd n
    have hadj : gridG.Adj (c + (n : ℤ) • d) (c + ((n + 1 : ℕ) : ℤ) • d) := by
      apply dir_gAdj
      have : c + ((n + 1 : ℕ) : ℤ) • d - (c + (n : ℤ) • d) = d := by
        push_cast; rw [add_smul, one_smul]; abel
      rw [this]; exact hd
    refine ⟨w.concat hadj, ?_⟩
    intro x hx
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · obtain ⟨j, hj, e⟩ := hw x hx; exact ⟨j, by omega, e⟩
    · exact ⟨n + 1, le_rfl, hx⟩

lemma floor_int_add_half (m : ℤ) : ⌊(m : ℝ) + 1 / 2⌋ = m := by
  rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

/-- facts about the support of a path, as a list -/
lemma path_list {c0 cl : ℤ × ℤ} (p : gridG.Walk c0 cl) (hp : p.IsPath) :
    p.support.head? = some c0 ∧ p.support.getLast? = some cl ∧ p.support.Nodup ∧
      p.support.IsChain (fun c c' => IsDir (c' - c)) := by
  refine ⟨?_, ?_, hp.support_nodup, ?_⟩
  · rw [SimpleGraph.Walk.support_eq_cons]; rfl
  · rw [List.getLast?_eq_getLast (SimpleGraph.Walk.support_ne_nil p),
      SimpleGraph.Walk.getLast_support]
  · exact (SimpleGraph.Walk.isChain_adj_support p).imp (fun a b hab => gAdj_dir hab)


/-! Image drawings, obstacles, frames at a vertex, port regions. -/

open RobertsonSeymour1986.GM5 in
lemma ArcImg.left_mem {P Q : ℝ × ℝ} {S : Set (ℝ × ℝ)} (h : ArcImg P Q S) : P ∈ S := by
  obtain ⟨γ, -, rfl⟩ := h; exact ⟨0, γ.source⟩

lemma ArcImg.right_mem {P Q : ℝ × ℝ} {S : Set (ℝ × ℝ)} (h : ArcImg P Q S) : Q ∈ S := by
  obtain ⟨γ, -, rfl⟩ := h; exact ⟨1, γ.target⟩

lemma ArcImg.compact {P Q : ℝ × ℝ} {S : Set (ℝ × ℝ)} (h : ArcImg P Q S) : IsCompact S := by
  obtain ⟨γ, -, rfl⟩ := h; exact isCompact_range γ.continuous

/-- a drawing given by arc images -/
structure ImgDr {V : Type} (H : SimpleGraph V) where
  P : V → ℝ × ℝ
  inj : Function.Injective P
  S : V → V → Set (ℝ × ℝ)
  symm : ∀ v w, S v w = S w v
  arc : ∀ v w, H.Adj v w → ArcImg (P v) (P w) (S v w)
  avoid : ∀ v w, H.Adj v w → ∀ x, P x ∈ S v w → x = v ∨ x = w
  meet : ∀ v w x y, H.Adj v w → H.Adj x y → ¬ s(v, w) = s(x, y) →
    ∀ z, z ∈ S v w → z ∈ S x y → z = P v ∨ z = P w

open RobertsonSeymour1986.GM5 in
theorem ImgDr.planar {V : Type} [LinearOrder V] {H : SimpleGraph V} (D : ImgDr H) :
    IsPlanar H :=
  planar_of_imgs H D.P D.inj D.S D.symm D.arc D.avoid D.meet

/-- everything already drawn, except the (isolated) vertex `u` -/
def Obs {V : Type} {H : SimpleGraph V} (D : ImgDr H) (u : V) : Set (ℝ × ℝ) :=
  {z | (∃ v w, H.Adj v w ∧ z ∈ D.S v w) ∨ (∃ v, v ≠ u ∧ z = D.P v)}

lemma Obs_compact {n : ℕ} {H : SimpleGraph (Fin n)} (D : ImgDr H) (u : Fin n) :
    IsCompact (Obs D u) := by
  classical
  have e : Obs D u = (⋃ p : Fin n × Fin n, {z | H.Adj p.1 p.2 ∧ z ∈ D.S p.1 p.2}) ∪
      Set.range (fun v : {v : Fin n // v ≠ u} => D.P v) := by
    ext z
    simp only [Obs, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_range,
      Prod.exists, Subtype.exists]
    constructor
    · rintro (⟨v, w, h1, h2⟩ | ⟨v, hv, rfl⟩)
      · left; exact ⟨v, w, h1, h2⟩
      · right; exact ⟨v, hv, rfl⟩
    · rintro (⟨v, w, h1, h2⟩ | ⟨v, hv, rfl⟩)
      · left; exact ⟨v, w, h1, h2⟩
      · right; exact ⟨v, hv, rfl⟩
  rw [e]
  refine IsCompact.union (isCompact_iUnion fun p => ?_) (Set.finite_range _).isCompact
  by_cases hp : H.Adj p.1 p.2
  · have : {z | H.Adj p.1 p.2 ∧ z ∈ D.S p.1 p.2} = D.S p.1 p.2 := by
      ext z; simp [hp]
    rw [this]; exact (D.arc _ _ hp).compact
  · have : {z | H.Adj p.1 p.2 ∧ z ∈ D.S p.1 p.2} = ∅ := by
      ext z; simp [hp]
    rw [this]; exact isCompact_empty

lemma sep_path_set {P Q : ℝ × ℝ} (γ : Path P Q) (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (h : ∀ t, γ t ∉ S) : ∃ δ > 0, ∀ t, ∀ z ∈ S, δ ≤ dist (γ t) z := by
  rcases S.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, by simp [hE]⟩
  · have hpos : ∀ t, 0 < Metric.infDist (γ t) S := fun t =>
      (hS.isClosed.notMem_iff_infDist_pos hne).mp (h t)
    obtain ⟨t0, -, ht0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (((Metric.continuous_infDist_pt S).comp γ.continuous).continuousOn)
    refine ⟨Metric.infDist (γ t0) S, hpos t0, fun t z hz => ?_⟩
    exact (isMinOn_iff.mp ht0 t (Set.mem_univ t)).trans (Metric.infDist_le_dist_of_mem hz)

lemma pos_min_pt {P Q : ℝ × ℝ} (γ : Path P Q) (A : ℝ × ℝ) (h : ∀ t, γ t ≠ A) :
    ∃ c > 0, ∀ t, c ≤ dist (γ t) A := by
  obtain ⟨t0, -, ht0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (Continuous.continuousOn (by fun_prop : Continuous fun t => dist (γ t) A))
  exact ⟨dist (γ t0) A, dist_pos.mpr (h t0), fun t => isMinOn_iff.mp ht0 t (Set.mem_univ t)⟩

/-- frame coordinates at the lattice point `k`, first axis `d` -/
def fa (k d : ℤ × ℤ) (z : ℝ × ℝ) : ℝ := (z.1 - k.1) * d.1 + (z.2 - k.2) * d.2

def fb (k d : ℤ × ℤ) (z : ℝ × ℝ) : ℝ := -(z.1 - k.1) * d.2 + (z.2 - k.2) * d.1

def kR (k : ℤ × ℤ) : ℝ × ℝ := ((k.1 : ℝ), (k.2 : ℝ))

lemma frame_Lc (k d : ℤ × ℤ) (hd : IsDir d) (α β : ℝ) :
    fa k d (Lc 1 k d (α, β)) = α ∧ fb k d (Lc 1 k d (α, β)) = β := by
  obtain ⟨s1, s2⟩ := dir_sq hd
  simp only [fa, fb, Lc]
  constructor
  · linear_combination α * s1
  · linear_combination β * s1

lemma Lc_frame (k d : ℤ × ℤ) (hd : IsDir d) (z : ℝ × ℝ) : Lc 1 k d (fa k d z, fb k d z) = z := by
  obtain ⟨s1, s2⟩ := dir_sq hd
  simp only [fa, fb, Lc]
  ext
  · simp only; linear_combination (z.1 - k.1) * s1
  · simp only; linear_combination (z.2 - k.2) * s1

lemma Lc_zero (k d : ℤ × ℤ) : Lc 1 k d (0, 0) = kR k := by
  simp [Lc, kR]

lemma Lc_id (z : ℝ × ℝ) : Lc 1 (0, 0) (1, 0) z = z := by
  simp [Lc]

lemma fa_id (z : ℝ × ℝ) : fa (0, 0) (1, 0) z = z.1 := by simp [fa]

lemma fb_id (z : ℝ × ℝ) : fb (0, 0) (1, 0) z = z.2 := by simp [fb]

lemma frame_dist (k d : ℤ × ℤ) (hd : IsDir d) (z : ℝ × ℝ) :
    dist z (kR k) = max |fa k d z| |fb k d z| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [kR]
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl
  · have ha : fa k (1, 0) z = z.1 - k.1 := by simp only [fa]; push_cast; ring
    have hb : fb k (1, 0) z = z.2 - k.2 := by simp only [fb]; push_cast; ring
    rw [ha, hb]
  · have ha : fa k (-1, 0) z = -(z.1 - k.1) := by simp only [fa]; push_cast; ring
    have hb : fb k (-1, 0) z = -(z.2 - k.2) := by simp only [fb]; push_cast; ring
    rw [ha, hb, abs_neg, abs_neg]
  · have ha : fa k (0, 1) z = z.2 - k.2 := by simp only [fa]; push_cast; ring
    have hb : fb k (0, 1) z = -(z.1 - k.1) := by simp only [fb]; push_cast; ring
    rw [ha, hb, abs_neg, max_comm]
  · have ha : fa k (0, -1) z = -(z.2 - k.2) := by simp only [fa]; push_cast; ring
    have hb : fb k (0, -1) z = z.1 - k.1 := by simp only [fb]; push_cast; ring
    rw [ha, hb, abs_neg, max_comm]

lemma cell_sm {h : ℝ} (N : ℕ) (hN : h * N = 1) (k d : ℤ × ℤ) (j : ℤ) :
    h * ((((N : ℤ) • k + j • d).1 : ℤ) : ℝ) = k.1 + j * h * d.1 ∧
      h * ((((N : ℤ) • k + j • d).2 : ℤ) : ℝ) = k.2 + j * h * d.2 := by
  constructor
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; push_cast
    linear_combination (k.1 : ℝ) * hN
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; push_cast
    linear_combination (k.2 : ℝ) * hN

lemma dir_abs {d : ℤ × ℤ} (hd : IsDir d) : |(d.1 : ℝ)| + |(d.2 : ℝ)| = 1 := by
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl <;> norm_num

lemma l1_bound {a b x y r : ℝ} (ha : |a| ≤ r) (hb : |b| ≤ r) (hxy : |x| + |y| = 1) :
    |a * x + b * y| ≤ r := by
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = |a| * |x| + |b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ r * |x| + r * |y| := add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    _ = r := by rw [← mul_add, hxy, mul_one]

lemma frame_cell {h : ℝ} (N : ℕ) (hN : h * N = 1) (k d : ℤ × ℤ) (hd : IsDir d) (j : ℤ)
    (z : ℝ × ℝ) (hz : z ∈ cell h ((N : ℤ) • k + j • d)) :
    |fa k d z - j * h| ≤ h / 2 ∧ |fb k d z| ≤ h / 2 := by
  obtain ⟨b1, b2⟩ := hz
  obtain ⟨e1, e2⟩ := cell_sm N hN k d j
  rw [e1] at b1
  rw [e2] at b2
  obtain ⟨s1, -⟩ := dir_sq hd
  have habs := dir_abs hd
  have hA : fa k d z - j * h = (z.1 - (k.1 + j * h * d.1)) * d.1 + (z.2 - (k.2 + j * h * d.2)) * d.2 := by
    simp only [fa]; linear_combination ((j : ℝ) * h) * s1
  have hB : fb k d z = (z.1 - (k.1 + j * h * d.1)) * (-(d.2 : ℝ)) +
      (z.2 - (k.2 + j * h * d.2)) * d.1 := by
    simp only [fb]; ring
  refine ⟨by rw [hA]; exact l1_bound b1 b2 habs, ?_⟩
  rw [hB]; exact l1_bound b1 b2 (by rw [abs_neg, add_comm]; exact habs)

lemma cell_of_frame {h : ℝ} (N : ℕ) (hN : h * N = 1) (k d : ℤ × ℤ) (hd : IsDir d)
    (j : ℤ) (α β : ℝ) (h1 : |α - j * h| ≤ h / 2) (h2 : |β| ≤ h / 2) :
    Lc 1 k d (α, β) ∈ cell h ((N : ℤ) • k + j • d) := by
  obtain ⟨e1, e2⟩ := cell_sm N hN k d j
  have habs := dir_abs hd
  refine ⟨?_, ?_⟩
  · rw [e1]
    have : (Lc 1 k d (α, β)).1 - (k.1 + j * h * d.1) = (α - j * h) * d.1 + β * (-(d.2 : ℝ)) := by
      simp only [Lc]; ring
    rw [this]; exact l1_bound h1 h2 (by rw [abs_neg]; exact habs)
  · rw [e2]
    have : (Lc 1 k d (α, β)).2 - (k.2 + j * h * d.2) = (α - j * h) * d.2 + β * d.1 := by
      simp only [Lc]; ring
    rw [this]; exact l1_bound h1 h2 (by rw [add_comm]; exact habs)

/-- the port region at `k`: a thin wedge of length `L` around the first axis -/
def Rg (h L : ℝ) (k d : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ fa k d z ∧ fa k d z ≤ L ∧ |fb k d z| ≤ fa k d z * (h / 4) / L}

lemma seg_frame (k d : ℤ × ℤ) (hd : IsDir d) (L β : ℝ) (z : ℝ × ℝ)
    (hz : z ∈ seg (kR k) (Lc 1 k d (L, β))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ fa k d z = t * L ∧ fb k d z = t * β := by
  rw [← Lc_zero k d, ← Lc_seg] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨t, t0, t1, a1, a2⟩ := seg_coord hw
  have hw' : w = (t * L, t * β) := by ext <;> simp [a1, a2]
  rw [hw']
  obtain ⟨f1, f2⟩ := frame_Lc k d hd (t * L) (t * β)
  exact ⟨t, t0, t1, f1, f2⟩

lemma seg_Rg {h L : ℝ} (hL : 0 < L) (k d : ℤ × ℤ) (hd : IsDir d) {β : ℝ} (hβ : |β| ≤ h / 4) :
    seg (kR k) (Lc 1 k d (L, β)) ⊆ Rg h L k d := by
  intro z hz
  obtain ⟨t, t0, t1, f1, f2⟩ := seg_frame k d hd L β z hz
  refine ⟨by rw [f1]; positivity, by rw [f1]; nlinarith, ?_⟩
  rw [f1, f2, abs_mul, abs_of_nonneg t0]
  have : t * L * (h / 4) / L = t * (h / 4) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hβ t0

lemma Rg_dist {h L : ℝ} (hh : 0 < h) (hL : 0 < L) (hhL : h / 4 ≤ L) (k d : ℤ × ℤ) (hd : IsDir d) (z : ℝ × ℝ)
    (hz : z ∈ Rg h L k d) : dist z (kR k) ≤ L := by
  obtain ⟨a0, a1, a2⟩ := hz
  rw [frame_dist k d hd, max_le_iff]
  refine ⟨by rw [abs_of_nonneg a0]; exact a1, a2.trans ?_⟩
  rw [mul_div_assoc]
  calc fa k d z * (h / 4 / L) ≤ L * 1 := by
        apply mul_le_mul a1 _ (div_nonneg (by linarith) hL.le) hL.le
        rw [div_le_one hL]; exact hhL
    _ = L := mul_one L

lemma Rg_obs {n : ℕ} {H : SimpleGraph (Fin n)} (D : ImgDr H) (u : Fin n) {h L ρ μ : ℝ}
    (_hL : 0 < L) (hLρ : L ≤ ρ) (hhμ : h / 4 / L ≤ μ) (k d : ℤ × ℤ) (hd : IsDir d)
    (cone : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 k d (α, β) ∉ Obs D u)
    (z : ℝ × ℝ) (hz : z ∈ Rg h L k d) (hzo : z ∈ Obs D u) : z = kR k := by
  obtain ⟨a0, a1, a2⟩ := hz
  rcases eq_or_lt_of_le a0 with e | e
  · have hb : fb k d z = 0 := by
      rw [← e] at a2; simp at a2; exact a2
    rw [← Lc_frame k d hd z, ← e, hb, Lc_zero]
  · exfalso
    apply cone (fa k d z) (fb k d z) e (a1.trans hLρ) _ (by rw [Lc_frame k d hd z]; exact hzo)
    calc |fb k d z| ≤ fa k d z * (h / 4) / L := a2
      _ = (h / 4 / L) * fa k d z := by ring
      _ ≤ μ * fa k d z := mul_le_mul_of_nonneg_right hhμ e.le

/-- a cell of the straight row in front of a vertex -/
lemma row_cell {n : ℕ} {H : SimpleGraph (Fin n)} (D : ImgDr H) (u : Fin n) {h ρ μ : ℝ} {J : ℕ}
    (hh : 0 < h) (N : ℕ) (hN : h * N = 1) (hJμ : 1 ≤ μ * J) (hμ : 0 < μ)
    (k d : ℤ × ℤ) (hd : IsDir d)
    (cone : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 k d (α, β) ∉ Obs D u)
    (j : ℤ) (hj : (J : ℤ) + 1 ≤ j) (hjρ : ((j : ℝ) + 1 / 2) * h ≤ ρ)
    (z : ℝ × ℝ) (hz : z ∈ cell h ((N : ℤ) • k + j • d)) :
    z ∉ Obs D u ∧ (z ∈ Rg h ((J + 1 / 2) * h) k d → j = J + 1 ∧ fa k d z = (J + 1 / 2) * h) := by
  obtain ⟨c1, c2⟩ := frame_cell N hN k d hd j z hz
  rw [abs_le] at c1
  have hjR : ((J : ℝ) + 1) ≤ j := by exact_mod_cast hj
  have hjh : ((J : ℝ) + 1 / 2) * h ≤ ((j : ℝ) - 1 / 2) * h :=
    mul_le_mul_of_nonneg_right (by linarith) hh.le
  have hfa : ((J : ℝ) + 1 / 2) * h ≤ fa k d z := by linarith [c1.1]
  have hfa0 : 0 < fa k d z := lt_of_lt_of_le (by positivity) hfa
  constructor
  · intro hzo
    apply cone (fa k d z) (fb k d z) hfa0 (by linarith [c1.2]) _ (by rw [Lc_frame k d hd z]; exact hzo)
    have e1 : μ * (((J : ℝ) + 1 / 2) * h) ≤ μ * fa k d z := mul_le_mul_of_nonneg_left hfa hμ.le
    have e2 : 1 * h ≤ μ * J * h := mul_le_mul_of_nonneg_right hJμ hh.le
    have e3 : 0 ≤ μ * h := by positivity
    linarith
  · rintro ⟨-, r1, -⟩
    have hfaL : fa k d z = (J + 1 / 2) * h := le_antisymm r1 hfa
    refine ⟨?_, hfaL⟩
    have : (j : ℝ) ≤ J + 1 := by
      have : ((j : ℝ) - 1 / 2) * h ≤ ((J : ℝ) + 1 / 2) * h := by linarith [c1.1]
      have := le_of_mul_le_mul_right this hh
      linarith
    have : j ≤ (J : ℤ) + 1 := by exact_mod_cast this
    omega


/-! The core construction: a corridor path between two cones gives the new edges. -/

lemma dist_kR_ge {k : ℤ × ℤ} (hk : k ≠ 0) : 1 ≤ dist (kR (0, 0)) (kR k) := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [kR, Int.cast_zero, zero_sub, abs_neg]
  by_cases h1 : k.1 = 0
  · have h2 : k.2 ≠ 0 := fun h2 => hk (Prod.ext h1 h2)
    have : (1 : ℝ) ≤ |(k.2 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h2
    exact le_trans this (le_max_right _ _)
  · have : (1 : ℝ) ≤ |(k.1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h1
    exact le_trans this (le_max_left _ _)

lemma floor_half_zero : ⌊(1 / 2 : ℝ)⌋ = 0 := by
  rw [Int.floor_eq_iff]; norm_num

lemma cellOf_frame {N : ℕ} (hN0 : (0 : ℝ) < N) (k d : ℤ × ℤ) (hd : IsDir d) (s : ℝ) :
    ∃ j : ℤ, cellOf (1 / N) (Lc 1 k d (s, 0) + ((1 / (N : ℝ) / 2, 1 / (N : ℝ) / 2) : ℝ × ℝ)) = (N : ℤ) • k + j • d ∧
      |(j : ℝ) - s * N| ≤ 1 / 2 := by
  have key : ∀ m : ℤ, ∀ y : ℝ,
      ⌊((m : ℝ) + y + 1 / N / 2) / (1 / N)⌋ = m * N + ⌊y * N + 1 / 2⌋ := by
    intro m y
    have e : ((m : ℝ) + y + 1 / N / 2) / (1 / N) = ((m * N : ℤ) : ℝ) + (y * N + 1 / 2) := by
      push_cast; field_simp; ring
    rw [e, Int.floor_intCast_add]
  have fl : ∀ y : ℝ, |(⌊y + 1 / 2⌋ : ℝ) - y| ≤ 1 / 2 := by
    intro y
    have h1 := Int.floor_le (y + 1 / 2)
    have h2 := Int.lt_floor_add_one (y + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  have hc1 : (Lc 1 k d (s, 0) + ((1 / (N : ℝ) / 2, 1 / (N : ℝ) / 2) : ℝ × ℝ)).1 = (k.1 : ℝ) + s * d.1 + 1 / N / 2 := by
    simp only [Lc, Prod.fst_add]; ring
  have hc2 : (Lc 1 k d (s, 0) + ((1 / (N : ℝ) / 2, 1 / (N : ℝ) / 2) : ℝ × ℝ)).2 = (k.2 : ℝ) + s * d.2 + 1 / N / 2 := by
    simp only [Lc, Prod.snd_add]; ring
  have hc : cellOf (1 / N) (Lc 1 k d (s, 0) + ((1 / (N : ℝ) / 2, 1 / (N : ℝ) / 2) : ℝ × ℝ)) =
      (k.1 * N + ⌊s * d.1 * N + 1 / 2⌋, k.2 * N + ⌊s * d.2 * N + 1 / 2⌋) := by
    show (⌊_ / _⌋, ⌊_ / _⌋) = _
    rw [hc1, hc2, key, key]
  rw [hc]
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl
  · refine ⟨⌊s * N + 1 / 2⌋, ?_, fl (s * N)⟩
    have e2 : ⌊s * (((1, 0) : ℤ × ℤ).2 : ℝ) * N + 1 / 2⌋ = 0 := by
      simp only [Int.cast_zero, mul_zero, zero_mul, zero_add]; exact floor_half_zero
    have e1 : ⌊s * (((1, 0) : ℤ × ℤ).1 : ℝ) * N + 1 / 2⌋ = ⌊s * N + 1 / 2⌋ := by
      simp only [Int.cast_one, mul_one]
    rw [e1, e2]; ext <;> simp <;> ring
  · refine ⟨-⌊-(s * N) + 1 / 2⌋, ?_, ?_⟩
    · have e2 : ⌊s * ((((-1 : ℤ), (0 : ℤ)) : ℤ × ℤ).2 : ℝ) * N + 1 / 2⌋ = 0 := by
        simp only [Int.cast_zero, mul_zero, zero_mul, zero_add]; exact floor_half_zero
      have e1 : ⌊s * ((((-1 : ℤ), (0 : ℤ)) : ℤ × ℤ).1 : ℝ) * N + 1 / 2⌋ = ⌊-(s * N) + 1 / 2⌋ := by
        congr 1; push_cast; ring
      rw [e1, e2]; ext <;> simp <;> ring
    · have := fl (-(s * N)); push_cast; rw [abs_le] at this ⊢; constructor <;> linarith
  · refine ⟨⌊s * N + 1 / 2⌋, ?_, fl (s * N)⟩
    have e1 : ⌊s * (((0, 1) : ℤ × ℤ).1 : ℝ) * N + 1 / 2⌋ = 0 := by
      simp only [Int.cast_zero, mul_zero, zero_mul, zero_add]; exact floor_half_zero
    have e2 : ⌊s * (((0, 1) : ℤ × ℤ).2 : ℝ) * N + 1 / 2⌋ = ⌊s * N + 1 / 2⌋ := by
      simp only [Int.cast_one, mul_one]
    rw [e1, e2]; ext <;> simp <;> ring
  · refine ⟨-⌊-(s * N) + 1 / 2⌋, ?_, ?_⟩
    · have e1 : ⌊s * ((((0 : ℤ), (-1 : ℤ)) : ℤ × ℤ).1 : ℝ) * N + 1 / 2⌋ = 0 := by
        simp only [Int.cast_zero, mul_zero, zero_mul, zero_add]; exact floor_half_zero
      have e2 : ⌊s * ((((0 : ℤ), (-1 : ℤ)) : ℤ × ℤ).2 : ℝ) * N + 1 / 2⌋ = ⌊-(s * N) + 1 / 2⌋ := by
        congr 1; push_cast; ring
      rw [e1, e2]; ext <;> simp <;> ring
    · have := fl (-(s * N)); push_cast; rw [abs_le] at this ⊢; constructor <;> linarith

lemma row_walk2 (N : ℕ) (k d : ℤ × ℤ) (hd : IsDir d) (j1 j2 : ℤ) (h12 : j1 ≤ j2) :
    ∃ w : gridG.Walk ((N : ℤ) • k + j1 • d) ((N : ℤ) • k + j2 • d),
      ∀ x ∈ w.support, ∃ j : ℤ, j1 ≤ j ∧ j ≤ j2 ∧ x = (N : ℤ) • k + j • d := by
  obtain ⟨w, hw⟩ := row_walk ((N : ℤ) • k + j1 • d) d hd (j2 - j1).toNat
  have e : (N : ℤ) • k + j1 • d + (((j2 - j1).toNat : ℕ) : ℤ) • d = (N : ℤ) • k + j2 • d := by
    rw [Int.toNat_of_nonneg (by omega), add_assoc, ← add_smul]; congr 2; ring
  refine ⟨w.copy rfl e, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_copy] at hx
  obtain ⟨j, hj, rfl⟩ := hw x hx
  refine ⟨j1 + j, by omega, ?_, by rw [add_assoc, ← add_smul]⟩
  have := Int.toNat_of_nonneg (show 0 ≤ j2 - j1 by omega)
  omega


/-! Assembly: three new arc images with the right meeting pattern give a drawing of `G'`. -/

theorem assemble {n : ℕ} (H0 G' : SimpleGraph (Fin n)) (D0 : ImgDr H0) (a b u : Fin n)
    (hab : a ≠ b) (hua : u ≠ a) (hub : u ≠ b)
    (hu0 : ∀ q, ¬ H0.Adj u q) (hab0 : ¬ H0.Adj a b)
    (hG' : ∀ p q, G'.Adj p q ↔
      (H0.Adj p q ∨ s(p, q) = s(a, b) ∨ s(p, q) = s(u, a) ∨ s(p, q) = s(u, b)))
    (U : ℝ × ℝ) (Af Bf C : Set (ℝ × ℝ))
    (FA : ArcImg (D0.P a) (D0.P b) Af) (FB : ArcImg U (D0.P b) Bf) (FC : ArcImg (D0.P a) U C)
    (FAo : ∀ z ∈ Af, z ∈ Obs D0 u → z = D0.P a ∨ z = D0.P b)
    (FBo : ∀ z ∈ Bf, z ∈ Obs D0 u → z = D0.P b)
    (FCo : ∀ z ∈ C, z ∈ Obs D0 u → z = D0.P a)
    (FAB : ∀ z ∈ Af, z ∈ Bf → z = D0.P b)
    (FAC : ∀ z ∈ Af, z ∈ C → z = D0.P a)
    (FBC : ∀ z ∈ Bf, z ∈ C → z = U)
    (FU : U ∉ Obs D0 u) (FUA : U ∉ Af) :
    RobertsonSeymour1986.GM5.IsPlanar G' := by
  classical
  let P' : Fin n → ℝ × ℝ := Function.update D0.P u U
  have hP'u : P' u = U := Function.update_self u U D0.P
  have hP'v : ∀ v, v ≠ u → P' v = D0.P v := fun v hv => Function.update_of_ne hv U D0.P
  have hvu : ∀ v w, H0.Adj v w → v ≠ u := fun v w h e => hu0 w (e ▸ h)
  have hobsE : ∀ v w, H0.Adj v w → ∀ z ∈ D0.S v w, z ∈ Obs D0 u :=
    fun v w h z hz => Or.inl ⟨v, w, h, hz⟩
  have hobsV : ∀ v, v ≠ u → D0.P v ∈ Obs D0 u := fun v hv => Or.inr ⟨v, hv, rfl⟩
  have hP'inj : Function.Injective P' := by
    intro v w e
    by_cases hv : v = u <;> by_cases hw : w = u
    · rw [hv, hw]
    · exfalso; rw [hv, hP'u, hP'v w hw] at e; exact FU (e ▸ hobsV w hw)
    · exfalso; rw [hw, hP'u, hP'v v hv] at e; exact FU (e ▸ hobsV v hv)
    · rw [hP'v v hv, hP'v w hw] at e; exact D0.inj e
  have n1 : s(a, b) ≠ s(u, a) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hua h1.symm
    · exact hub h2.symm
  have n2 : s(a, b) ≠ s(u, b) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hua h1.symm
    · exact hab h1
  have n3 : s(u, a) ≠ s(u, b) := by
    intro e; rcases Sym2.eq_iff.mp e with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hab h2
    · exact hub h1
  have nH : ∀ v w, H0.Adj v w → s(v, w) ≠ s(a, b) ∧ s(v, w) ≠ s(u, a) ∧ s(v, w) ≠ s(u, b) := by
    intro v w h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab0 h
      · exact hab0 h.symm
    · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu0 _ h
      · exact hu0 _ h.symm
    · rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu0 _ h
      · exact hu0 _ h.symm
  let S' : Fin n → Fin n → Set (ℝ × ℝ) := fun v w =>
    if s(v, w) = s(a, b) then Af
    else if s(v, w) = s(u, a) then C
    else if s(v, w) = s(u, b) then Bf
    else D0.S v w
  have hSab : ∀ v w, s(v, w) = s(a, b) → S' v w = Af := fun v w e => if_pos e
  have hSua : ∀ v w, s(v, w) = s(u, a) → S' v w = C := fun v w e => by
    simp only [S', if_pos e, if_neg (fun e' : s(v, w) = s(a, b) => n1 (e'.symm.trans e))]
  have hSub : ∀ v w, s(v, w) = s(u, b) → S' v w = Bf := fun v w e => by
    simp only [S', if_pos e, if_neg (fun e' : s(v, w) = s(a, b) => n2 (e'.symm.trans e)),
      if_neg (fun e' : s(v, w) = s(u, a) => n3 (e'.symm.trans e))]
  have hS0 : ∀ v w, H0.Adj v w → S' v w = D0.S v w := fun v w h => by
    obtain ⟨m1, m2, m3⟩ := nH v w h
    simp only [S', if_neg m1, if_neg m2, if_neg m3]
  have hsymm : ∀ v w, S' v w = S' w v := by
    intro v w
    simp only [S', Sym2.eq_swap (a := w) (b := v), D0.symm w v]
  have hcls : ∀ v w, G'.Adj v w → H0.Adj v w ∨ s(v, w) = s(a, b) ∨ s(v, w) = s(u, a) ∨
      s(v, w) = s(u, b) := fun v w h => (hG' v w).mp h
  have hPa : P' a = D0.P a := hP'v a hua.symm
  have hPb : P' b = D0.P b := hP'v b hub.symm
  -- endpoints of the new edges
  have eab : ∀ v w, s(v, w) = s(a, b) →
      (P' v = D0.P a ∧ P' w = D0.P b) ∨ (P' v = D0.P b ∧ P' w = D0.P a) := by
    intro v w e
    rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨hPa, hPb⟩
    · right; exact ⟨hPb, hPa⟩
  have eua : ∀ v w, s(v, w) = s(u, a) → (P' v = U ∧ P' w = D0.P a) ∨ (P' v = D0.P a ∧ P' w = U) := by
    intro v w e
    rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨hP'u, hPa⟩
    · right; exact ⟨hPa, hP'u⟩
  have eub : ∀ v w, s(v, w) = s(u, b) → (P' v = U ∧ P' w = D0.P b) ∨ (P' v = D0.P b ∧ P' w = U) := by
    intro v w e
    rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨hP'u, hPb⟩
    · right; exact ⟨hPb, hP'u⟩
  refine ImgDr.planar ⟨P', hP'inj, S', hsymm, ?_, ?_, ?_⟩
  · -- arcs
    intro v w h
    rcases hcls v w h with h0 | e | e | e
    · rw [hS0 v w h0, hP'v v (hvu v w h0), hP'v w (hvu w v h0.symm)]; exact D0.arc v w h0
    · rw [hSab v w e]
      rcases eab v w e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact FA
      · exact FA.symm
    · rw [hSua v w e]
      rcases eua v w e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact FC.symm
      · exact FC
    · rw [hSub v w e]
      rcases eub v w e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact FB
      · exact FB.symm
  · -- vertices
    intro v w h x hx
    rcases hcls v w h with h0 | e | e | e
    · rw [hS0 v w h0] at hx
      by_cases hxu : x = u
      · exfalso; rw [hxu, hP'u] at hx; exact FU (hobsE v w h0 _ hx)
      · rw [hP'v x hxu] at hx; exact D0.avoid v w h0 x hx
    · rw [hSab v w e] at hx
      by_cases hxu : x = u
      · exfalso; rw [hxu, hP'u] at hx; exact FUA hx
      · rw [hP'v x hxu] at hx
        rcases FAo _ hx (hobsV x hxu) with e' | e'
        · have := D0.inj e'; subst this
          rcases Sym2.eq_iff.mp e with ⟨h1, -⟩ | ⟨-, h2⟩
          · left; exact h1.symm
          · right; exact h2.symm
        · have := D0.inj e'; subst this
          rcases Sym2.eq_iff.mp e with ⟨-, h2⟩ | ⟨h1, -⟩
          · right; exact h2.symm
          · left; exact h1.symm
    · rw [hSua v w e] at hx
      by_cases hxu : x = u
      · subst hxu
        rcases Sym2.eq_iff.mp e with ⟨h1, -⟩ | ⟨-, h2⟩
        · left; exact h1.symm
        · right; exact h2.symm
      · rw [hP'v x hxu] at hx
        have := D0.inj (FCo _ hx (hobsV x hxu)); subst this
        rcases Sym2.eq_iff.mp e with ⟨-, h2⟩ | ⟨h1, -⟩
        · right; exact h2.symm
        · left; exact h1.symm
    · rw [hSub v w e] at hx
      by_cases hxu : x = u
      · subst hxu
        rcases Sym2.eq_iff.mp e with ⟨h1, -⟩ | ⟨-, h2⟩
        · left; exact h1.symm
        · right; exact h2.symm
      · rw [hP'v x hxu] at hx
        have := D0.inj (FBo _ hx (hobsV x hxu)); subst this
        rcases Sym2.eq_iff.mp e with ⟨-, h2⟩ | ⟨h1, -⟩
        · right; exact h2.symm
        · left; exact h1.symm
  · -- meetings
    intro v w x y h k hne z hz1 hz2
    -- endpoint helpers for the first edge
    have endA : s(v, w) = s(a, b) → (z = D0.P a ∨ z = D0.P b) → z = P' v ∨ z = P' w := by
      intro e hz
      rcases eab v w e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with hz | hz <;> rw [hz] <;>
        first | (left; exact h1.symm) | (right; exact h2.symm)
    have endC : s(v, w) = s(u, a) → (z = U ∨ z = D0.P a) → z = P' v ∨ z = P' w := by
      intro e hz
      rcases eua v w e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with hz | hz <;> rw [hz] <;>
        first | (left; exact h1.symm) | (right; exact h2.symm)
    have endB : s(v, w) = s(u, b) → (z = U ∨ z = D0.P b) → z = P' v ∨ z = P' w := by
      intro e hz
      rcases eub v w e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with hz | hz <;> rw [hz] <;>
        first | (left; exact h1.symm) | (right; exact h2.symm)
    have endO : H0.Adj v w → (∃ q, z = D0.P q ∧ D0.P q ∈ D0.S v w ∧ q ≠ u) →
        z = P' v ∨ z = P' w := by
      rintro h0 ⟨q, rfl, hq, hqu⟩
      rcases D0.avoid v w h0 q hq with rfl | rfl
      · left; exact (hP'v _ hqu).symm
      · right; exact (hP'v _ hqu).symm
    rcases hcls v w h with h0 | e | e | e <;> rcases hcls x y k with k0 | f | f | f
    -- old / old
    · rw [hS0 v w h0] at hz1; rw [hS0 x y k0] at hz2
      rw [hP'v v (hvu v w h0), hP'v w (hvu w v h0.symm)]
      exact D0.meet v w x y h0 k0 hne z hz1 hz2
    -- old / ab
    · rw [hS0 v w h0] at hz1; rw [hSab x y f] at hz2
      apply endO h0
      rcases FAo z hz2 (hobsE v w h0 z hz1) with rfl | rfl
      · exact ⟨a, rfl, hz1, hua.symm⟩
      · exact ⟨b, rfl, hz1, hub.symm⟩
    · rw [hS0 v w h0] at hz1; rw [hSua x y f] at hz2
      apply endO h0
      have := FCo z hz2 (hobsE v w h0 z hz1); subst this
      exact ⟨a, rfl, hz1, hua.symm⟩
    · rw [hS0 v w h0] at hz1; rw [hSub x y f] at hz2
      apply endO h0
      have := FBo z hz2 (hobsE v w h0 z hz1); subst this
      exact ⟨b, rfl, hz1, hub.symm⟩
    -- ab / *
    · rw [hSab v w e] at hz1; rw [hS0 x y k0] at hz2
      exact endA e (FAo z hz1 (hobsE x y k0 z hz2))
    · exact absurd (e.trans f.symm) hne
    · rw [hSab v w e] at hz1; rw [hSua x y f] at hz2
      exact endA e (Or.inl (FAC z hz1 hz2))
    · rw [hSab v w e] at hz1; rw [hSub x y f] at hz2
      exact endA e (Or.inr (FAB z hz1 hz2))
    -- ua / *
    · rw [hSua v w e] at hz1; rw [hS0 x y k0] at hz2
      exact endC e (Or.inr (FCo z hz1 (hobsE x y k0 z hz2)))
    · rw [hSua v w e] at hz1; rw [hSab x y f] at hz2
      exact endC e (Or.inr (FAC z hz2 hz1))
    · exact absurd (e.trans f.symm) hne
    · rw [hSua v w e] at hz1; rw [hSub x y f] at hz2
      exact endC e (Or.inl (FBC z hz2 hz1))
    -- ub / *
    · rw [hSub v w e] at hz1; rw [hS0 x y k0] at hz2
      exact endB e (Or.inr (FBo z hz1 (hobsE x y k0 z hz2)))
    · rw [hSub v w e] at hz1; rw [hSab x y f] at hz2
      exact endB e (Or.inr (FAB z hz2 hz1))
    · rw [hSub v w e] at hz1; rw [hSua x y f] at hz2
      exact endB e (Or.inl (FBC z hz1 hz2))
    · exact absurd (e.trans f.symm) hne


/-! The core: cones at both ends and a corridor path give the drawing of `G'`. -/

lemma dir10 : IsDir (1, 0) := Or.inl rfl

lemma seg_param_X (L β : ℝ) (z : ℝ × ℝ) (hz : z ∈ seg (kR (0, 0)) (Lc 1 (0, 0) (1, 0) (L, β))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t * L, t * β) := by
  obtain ⟨t, t0, t1, f1, f2⟩ := seg_frame (0, 0) (1, 0) dir10 L β z hz
  rw [fa_id] at f1; rw [fb_id] at f2
  exact ⟨t, t0, t1, Prod.ext f1 f2⟩

set_option maxHeartbeats 1000000 in
/-- the walk of cells along the corridor, with the facts the assembly needs -/
theorem core_cells {n : ℕ} {H0 : SimpleGraph (Fin n)} (D0 : ImgDr H0) (u : Fin n)
    (kW dW : ℤ × ℤ) (hkW : kW ≠ 0) (hdW : IsDir dW)
    (ρ μ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hμ : 0 < μ)
    (coneX : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 (0, 0) (1, 0) (α, β) ∉ Obs D0 u)
    (coneW : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 kW dW (α, β) ∉ Obs D0 u)
    (sX sW : ℝ) (hsX' : sX ≤ ρ / 2) (hsW' : sW ≤ ρ / 2)
    (K : Path (Lc 1 (0, 0) (1, 0) (sX, 0)) (Lc 1 kW dW (sW, 0)))
    (ρ' δ : ℝ) (hδK : ∀ t, ∀ z ∈ Obs D0 u, δ ≤ dist (K t) z)
    (hKfar : ∀ t, ρ' ≤ dist (K t) (kR (0, 0)) ∧ ρ' ≤ dist (K t) (kR kW))
    (J N : ℕ) (hN0 : (0 : ℝ) < N) (hJμ : 1 ≤ μ * J) (h : ℝ) (hh_def : h = 1 / (N : ℝ))
    (sδ : ((J : ℝ) + 10) * h < δ) (sρ' : ((J : ℝ) + 10) * h < ρ')
    (ssX : ((J : ℝ) + 10) * h < sX) (ssW : ((J : ℝ) + 10) * h < sW)
    (sρ : ((J : ℝ) + 10) * h < ρ) :
    ∃ cs : List (ℤ × ℤ),
      cs.head? = some ((N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ))) ∧
      cs.getLast? = some ((N : ℤ) • kW + ((J : ℤ) + 1) • dW) ∧ cs.Nodup ∧
      cs.IsChain (fun c c' => IsDir (c' - c)) ∧
      ∀ x ∈ cs, ∀ z ∈ cell h x, z ∉ Obs D0 u ∧
        (z ∈ Rg h (((J : ℝ) + 1 / 2) * h) (0, 0) (1, 0) →
          x = (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ)) ∧
          fa (0, 0) (1, 0) z = ((J : ℝ) + 1 / 2) * h) ∧
        (z ∈ Rg h (((J : ℝ) + 1 / 2) * h) kW dW → x = (N : ℤ) • kW + ((J : ℤ) + 1) • dW ∧
          fa kW dW z = ((J : ℝ) + 1 / 2) * h) := by
  classical
  have hh : 0 < h := by rw [hh_def]; positivity
  have hN : h * N = 1 := by rw [hh_def]; field_simp
  have hJh : 0 ≤ (J : ℝ) * h := by positivity
  set L : ℝ := ((J : ℝ) + 1 / 2) * h with hL_def
  have hL : 0 < L := by positivity
  have hLs : h / 4 ≤ L := by rw [hL_def]; linarith only [hJh, hh]
  have hLρ : L ≤ ρ := by rw [hL_def]; linarith only [hJh, hh, sρ]
  have h10 : 10 * h < ρ := by linarith only [hJh, sρ]
  -- the two end cells of the corridor walk
  obtain ⟨iX, hiXc, hiXb⟩ := cellOf_frame hN0 (0, 0) (1, 0) dir10 sX
  obtain ⟨jW, hjWc, hjWb⟩ := cellOf_frame hN0 kW dW hdW sW
  rw [abs_le] at hiXb hjWb
  have hsXN : ((J : ℝ) + 10) < sX * N := by
    have := ssX; rw [hh_def, mul_one_div, div_lt_iff₀ hN0] at this; linarith only [this]
  have hsWN : ((J : ℝ) + 10) < sW * N := by
    have := ssW; rw [hh_def, mul_one_div, div_lt_iff₀ hN0] at this; linarith only [this]
  have hiX1 : (J : ℤ) + 1 ≤ iX := by
    have : ((J : ℝ) + 1) ≤ iX := by linarith only [hiXb.1, hsXN]
    exact_mod_cast this
  have hjW1 : (J : ℤ) + 1 ≤ jW := by
    have : ((J : ℝ) + 1) ≤ jW := by linarith only [hjWb.1, hsWN]
    exact_mod_cast this
  have hiXρ : ((iX : ℝ) + 1 / 2) * h ≤ ρ := by
    have e : sX * N * h = sX := by rw [mul_assoc, mul_comm (N : ℝ) h, hN, mul_one]
    have m : ((iX : ℝ) + 1 / 2) * h ≤ (sX * N + 1) * h :=
      mul_le_mul_of_nonneg_right (by linarith only [hiXb.2]) hh.le
    have e2 : (sX * N + 1) * h = sX + h := by rw [add_mul, e, one_mul]
    linarith only [m, e2, hsX', h10, hh]
  have hjWρ : ((jW : ℝ) + 1 / 2) * h ≤ ρ := by
    have e : sW * N * h = sW := by rw [mul_assoc, mul_comm (N : ℝ) h, hN, mul_one]
    have m : ((jW : ℝ) + 1 / 2) * h ≤ (sW * N + 1) * h :=
      mul_le_mul_of_nonneg_right (by linarith only [hjWb.2]) hh.le
    have e2 : (sW * N + 1) * h = sW + h := by rw [add_mul, e, one_mul]
    linarith only [m, e2, hsW', h10, hh]
  -- the walk of cells
  obtain ⟨rX, hrX⟩ := row_walk2 N (0, 0) (1, 0) dir10 (J + 1) iX hiX1
  obtain ⟨rW, hrW⟩ := row_walk2 N kW dW hdW (J + 1) jW hjW1
  let f : ℝ × ℝ → ℝ × ℝ := fun z => z + ((1 / (N : ℝ) / 2, 1 / (N : ℝ) / 2) : ℝ × ℝ)
  have hf : Continuous f := by fun_prop
  obtain ⟨wK, hwK, -⟩ := arc_walk (K.map hf) (show 0 < 1 / (N : ℝ) by positivity)
  let wK' : gridG.Walk ((N : ℤ) • ((0 : ℤ), (0 : ℤ)) + iX • ((1 : ℤ), (0 : ℤ)))
      ((N : ℤ) • kW + jW • dW) := wK.copy hiXc hjWc
  let total := rX.append (wK'.append rW.reverse)
  obtain ⟨hhead, hlast, hnd, hch⟩ := path_list total.bypass (SimpleGraph.Walk.bypass_isPath total)
  -- classification of the cells
  have hcls : ∀ x ∈ total.bypass.support, (∃ j : ℤ, (J : ℤ) + 1 ≤ j ∧ j ≤ iX ∧
        x = (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + j • ((1 : ℤ), (0 : ℤ))) ∨
      (∃ j : ℤ, (J : ℤ) + 1 ≤ j ∧ j ≤ jW ∧ x = (N : ℤ) • kW + j • dW) ∨
      (∃ t, dist (corner (1 / (N : ℝ)) x) (f (K t)) < 2 * (1 / (N : ℝ))) := by
    intro x hx
    have hx' : x ∈ (rX.append ((wK.copy hiXc hjWc).append rW.reverse)).support :=
      SimpleGraph.Walk.support_bypass_subset_support _ hx
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx'
    rcases hx' with hx' | hx' | hx'
    · left; exact hrX x hx'
    · right; right
      rw [SimpleGraph.Walk.support_copy] at hx'
      obtain ⟨t, ht⟩ := hwK x hx'
      exact ⟨t, ht⟩
    · right; left; exact hrW x hx'
  -- facts about every cell of the walk
  have hXW := dist_kR_ge hkW
  have Q : ∀ x ∈ total.bypass.support, ∀ z ∈ cell h x, z ∉ Obs D0 u ∧
      (z ∈ Rg h L (0, 0) (1, 0) → x = ((N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ))) ∧ fa (0, 0) (1, 0) z = L) ∧
      (z ∈ Rg h L kW dW → x = ((N : ℤ) • kW + ((J : ℤ) + 1) • dW) ∧ fa kW dW z = L) := by
    intro x hx z hz
    rcases hcls x hx with ⟨j, hj1, hj2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩ | ⟨t, ht⟩
    · have hjρ : ((j : ℝ) + 1 / 2) * h ≤ ρ := by
        have : (j : ℝ) ≤ iX := by exact_mod_cast hj2
        exact le_trans (mul_le_mul_of_nonneg_right (by linarith only [this]) hh.le) hiXρ
      obtain ⟨r1, r2⟩ := row_cell D0 u hh N hN hJμ hμ (0, 0) (1, 0) dir10 coneX j hj1 hjρ z hz
      refine ⟨r1, fun hr => ?_, fun hr => ?_⟩
      · obtain ⟨e1, e2⟩ := r2 hr
        exact ⟨by rw [e1], e2⟩
      · exfalso
        have d1 := Rg_dist hh hL hLs kW dW hdW z hr
        obtain ⟨c1, c2⟩ := frame_cell N hN (0, 0) (1, 0) dir10 j z hz
        have d2 : dist z (kR (0, 0)) ≤ ρ := by
          rw [frame_dist (0, 0) (1, 0) dir10 z, max_le_iff]
          rw [abs_le] at c1 c2
          have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (by
            have : (0 : ℤ) ≤ j := by omega
            exact_mod_cast this) hh.le
          constructor <;> rw [abs_le] <;> constructor <;>
            linarith only [c1.1, c1.2, c2.1, c2.2, hjh, hjρ, hh]
        have := dist_triangle_left (kR (0, 0)) (kR kW) z
        linarith only [d1, d2, this, hXW, hLρ, hρ4]
    · have hjρ : ((j : ℝ) + 1 / 2) * h ≤ ρ := by
        have : (j : ℝ) ≤ jW := by exact_mod_cast hj2
        exact le_trans (mul_le_mul_of_nonneg_right (by linarith only [this]) hh.le) hjWρ
      obtain ⟨r1, r2⟩ := row_cell D0 u hh N hN hJμ hμ kW dW hdW coneW j hj1 hjρ z hz
      refine ⟨r1, fun hr => ?_, fun hr => ?_⟩
      · exfalso
        have d1 := Rg_dist hh hL hLs (0, 0) (1, 0) dir10 z hr
        obtain ⟨c1, c2⟩ := frame_cell N hN kW dW hdW j z hz
        have d2 : dist z (kR kW) ≤ ρ := by
          rw [frame_dist kW dW hdW z, max_le_iff]
          rw [abs_le] at c1 c2
          have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (by
            have : (0 : ℤ) ≤ j := by omega
            exact_mod_cast this) hh.le
          constructor <;> rw [abs_le] <;> constructor <;>
            linarith only [c1.1, c1.2, c2.1, c2.2, hjh, hjρ, hh]
        have := dist_triangle_left (kR (0, 0)) (kR kW) z
        linarith only [d1, d2, this, hXW, hLρ, hρ4]
      · obtain ⟨e1, e2⟩ := r2 hr
        exact ⟨by rw [e1], e2⟩
    · -- a cell close to the corridor
      have hzK : dist z (K t) < 3 * h := by
        obtain ⟨b1, b2⟩ := hz
        have e1 : dist (f (K t)) (K t) = h / 2 := by
          simp only [f, dist_eq_norm, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs]
          rw [← hh_def]
          rw [abs_of_pos (by positivity : (0 : ℝ) < h / 2), max_self]
        have e2 : dist z (corner h x) ≤ h / 2 := by
          rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
          simp only [corner]
          rw [mul_comm (x.1 : ℝ) h, mul_comm (x.2 : ℝ) h]
          exact ⟨b1, b2⟩
        rw [← hh_def] at ht
        have := dist_triangle4 z (corner h x) (f (K t)) (K t)
        linarith only [e1, e2, ht, this]
      have hK1 := hKfar t
      refine ⟨fun hzo => ?_, fun hr => ?_, fun hr => ?_⟩
      · have := hδK t z hzo
        rw [dist_comm] at this
        linarith only [this, hzK, sδ, hJh, hh]
      · exfalso
        have d1 := Rg_dist hh hL hLs (0, 0) (1, 0) dir10 z hr
        have := dist_triangle (K t) z (kR (0, 0))
        rw [dist_comm] at hzK
        linarith only [d1, this, hzK, hK1.1, sρ', hL_def, hJh, hh]
      · exfalso
        have d1 := Rg_dist hh hL hLs kW dW hdW z hr
        have := dist_triangle (K t) z (kR kW)
        rw [dist_comm] at hzK
        linarith only [d1, this, hzK, hK1.2, sρ', hL_def, hJh, hh]
  refine ⟨total.bypass.support, hhead, hlast, hnd, hch, ?_⟩
  intro x hx z hz
  obtain ⟨q1, q2, q3⟩ := Q x hx z hz
  exact ⟨q1, q2, q3⟩


/-! The three new arcs, from the chain of cells, and the final drawing. -/

lemma kR00 : kR (0, 0) = ((0 : ℝ), (0 : ℝ)) := by simp [kR]

lemma seg_Rg0 {h L β : ℝ} (hL : 0 < L) (hβ : |β| ≤ h / 4) :
    seg (0, 0) (L, β) ⊆ Rg h L (0, 0) (1, 0) := by
  have := seg_Rg (h := h) hL (0, 0) (1, 0) dir10 hβ
  rwa [Lc_id, kR00] at this

lemma seg_coord0 {L β : ℝ} {z : ℝ × ℝ} (hz : z ∈ seg (0, 0) (L, β)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t * L, t * β) := by
  obtain ⟨t, t0, t1, a1, a2⟩ := seg_coord hz
  refine ⟨t, t0, t1, ?_⟩
  ext <;> simp [a1, a2]

lemma seg_end {k d : ℤ × ℤ} (hd : IsDir d) {L β : ℝ} (hL : 0 < L) {z : ℝ × ℝ}
    (hz : z ∈ seg (kR k) (Lc 1 k d (L, β))) (h : fa k d z = L) : z = Lc 1 k d (L, β) := by
  obtain ⟨t, t0, t1, f1, f2⟩ := seg_frame k d hd L β z hz
  have ht : t = 1 := by
    rw [h] at f1
    have : (t - 1) * L = 0 := by linarith
    rcases mul_eq_zero.mp this with e | e
    · linarith
    · linarith
  rw [← Lc_frame k d hd z, f1, f2, ht, one_mul, one_mul]

lemma xB1c {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (z : ℝ × ℝ)
    (hz : z ∈ seg ((L / 2, h / 8) : ℝ × ℝ) (L, h / 4)) : h / 8 ≤ z.2 ∧ L / 2 ≤ z.1 := by
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
  dsimp only at a1 a2
  have e1 : 0 ≤ s * (L - L / 2) := mul_nonneg s0 (by linarith)
  have e2 : 0 ≤ s * (h / 4 - h / 8) := mul_nonneg s0 (by linarith)
  constructor
  · linarith only [a2, e2]
  · linarith only [a1, e1]

lemma xCc {L h : ℝ} (hL : 0 < L) (z : ℝ × ℝ)
    (hz : z ∈ seg ((0 : ℝ), (0 : ℝ)) ((L / 2, h / 8) : ℝ × ℝ)) :
    z.1 ≤ L / 2 ∧ z.2 = z.1 * (h / 4) / L := by
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
  dsimp only at a1 a2
  have e1 : s * (L / 2 - 0) ≤ 1 * (L / 2 - 0) := mul_le_mul_of_nonneg_right s1 (by linarith)
  refine ⟨by rw [a1]; linarith only [e1], ?_⟩
  rw [a1, a2]; field_simp; ring

lemma xBC {L h : ℝ} (hL : 0 < L) (z : ℝ × ℝ)
    (h1 : z ∈ seg ((L / 2, h / 8) : ℝ × ℝ) (L, h / 4))
    (h2 : z ∈ seg ((0 : ℝ), (0 : ℝ)) ((L / 2, h / 8) : ℝ × ℝ)) : z = (L / 2, h / 8) := by
  obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord h1
  obtain ⟨s', s0', s1', b1, b2⟩ := seg_coord h2
  dsimp only at a1 a2 b1 b2
  have k : (1 + s - s') * (L / 2) = 0 := by linarith only [a1, b1]
  rcases mul_eq_zero.mp k with k | k
  · have hs : s = 0 := by linarith only [k, s0, s1']
    rw [hs] at a1 a2
    ext
    · rw [a1]; ring
    · rw [a2]; ring
  · linarith only [k, hL]

set_option maxHeartbeats 2000000 in
theorem core_finish {n : ℕ} (H0 G' : SimpleGraph (Fin n)) (D0 : ImgDr H0) (a b u : Fin n)
    (hab : a ≠ b) (hua : u ≠ a) (hub : u ≠ b)
    (hu0 : ∀ q, ¬ H0.Adj u q) (hab0 : ¬ H0.Adj a b)
    (hG' : ∀ p q, G'.Adj p q ↔
      (H0.Adj p q ∨ s(p, q) = s(a, b) ∨ s(p, q) = s(u, a) ∨ s(p, q) = s(u, b)))
    (kW dW : ℤ × ℤ) (hkW : kW ≠ 0) (hdW : IsDir dW)
    (hX : D0.P a = kR (0, 0)) (hW : D0.P b = kR kW)
    (ρ μ : ℝ) (hρ4 : ρ ≤ 1 / 4)
    (coneX : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 (0, 0) (1, 0) (α, β) ∉ Obs D0 u)
    (coneW : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 kW dW (α, β) ∉ Obs D0 u)
    (J N : ℕ) (h : ℝ) (hh : 0 < h) (hN : h * N = 1)
    (hLρ : ((J : ℝ) + 1 / 2) * h ≤ ρ) (hslope : h / 4 / (((J : ℝ) + 1 / 2) * h) ≤ μ)
    (cs : List (ℤ × ℤ))
    (hhead : cs.head? = some ((N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ))))
    (hlast : cs.getLast? = some ((N : ℤ) • kW + ((J : ℤ) + 1) • dW)) (hnd : cs.Nodup)
    (hch : cs.IsChain (fun c c' => IsDir (c' - c)))
    (Q : ∀ x ∈ cs, ∀ z ∈ cell h x, z ∉ Obs D0 u ∧
        (z ∈ Rg h (((J : ℝ) + 1 / 2) * h) (0, 0) (1, 0) →
          x = (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ)) ∧
          fa (0, 0) (1, 0) z = ((J : ℝ) + 1 / 2) * h) ∧
        (z ∈ Rg h (((J : ℝ) + 1 / 2) * h) kW dW → x = (N : ℤ) • kW + ((J : ℤ) + 1) • dW ∧
          fa kW dW z = ((J : ℝ) + 1 / 2) * h)) :
    IsPlanar G' := by
  classical
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = ((J : ℝ) + 1 / 2) * h := ⟨_, rfl⟩
  rw [← hL_def] at hLρ hslope Q
  have hJh : 0 ≤ (J : ℝ) * h := by positivity
  have hL : 0 < L := by rw [hL_def]; positivity
  have hLs : h / 4 ≤ L := by rw [hL_def]; linarith only [hJh, hh]
  have hXW := dist_kR_ge hkW
  -- the two port regions
  have hRR : ∀ z, z ∈ Rg h L (0, 0) (1, 0) → z ∈ Rg h L kW dW → False := by
    intro z h1 h2
    have d1 := Rg_dist hh hL hLs (0, 0) (1, 0) dir10 z h1
    have d2 := Rg_dist hh hL hLs kW dW hdW z h2
    have := dist_triangle_left (kR (0, 0)) (kR kW) z
    linarith only [d1, d2, this, hXW, hLρ, hρ4]
  have hRXo : ∀ z ∈ Rg h L (0, 0) (1, 0), z ∈ Obs D0 u → z = (0, 0) := by
    intro z hz hzo
    rw [← kR00]; exact Rg_obs D0 u hL hLρ hslope (0, 0) (1, 0) dir10 coneX z hz hzo
  have hRWo : ∀ z ∈ Rg h L kW dW, z ∈ Obs D0 u → z = kR kW :=
    Rg_obs D0 u hL hLρ hslope kW dW hdW coneW
  have hRX : ∀ z : ℝ × ℝ, z ∈ Rg h L (0, 0) (1, 0) → 0 ≤ z.1 ∧ z.1 ≤ L := by
    intro z hz; obtain ⟨a0, a1, -⟩ := hz; rw [fa_id] at a0 a1; exact ⟨a0, a1⟩
  -- test points next to the first and the last cell
  have hc0' : (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ)) - (1, 0) =
      (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + (J : ℤ) • ((1 : ℤ), (0 : ℤ)) := by
    ext <;> simp
  have hcl' : (N : ℤ) • kW + ((J : ℤ) + 1) • dW + -dW = (N : ℤ) • kW + (J : ℤ) • dW := by
    rw [add_smul, one_smul]; abel
  have zcell : ∀ (k d : ℤ × ℤ), IsDir d →
      Lc 1 k d ((J : ℝ) * h, 0) ∈ cell h ((N : ℤ) • k + (J : ℤ) • d) := by
    intro k d hd
    refine cell_of_frame N hN k d hd J _ _ ?_ ?_
    · push_cast; rw [sub_self, abs_zero]; positivity
    · rw [abs_zero]; positivity
  have zRg : ∀ (k d : ℤ × ℤ), IsDir d → Lc 1 k d ((J : ℝ) * h, 0) ∈ Rg h L k d := by
    intro k d hd
    obtain ⟨f1, f2⟩ := frame_Lc k d hd ((J : ℝ) * h) 0
    refine ⟨by rw [f1]; positivity, by rw [f1, hL_def]; linarith only [hh], ?_⟩
    rw [f1, f2, abs_zero]; positivity
  have zfa : ∀ (k d : ℤ × ℤ), IsDir d → fa k d (Lc 1 k d ((J : ℝ) * h, 0)) ≠ L := by
    intro k d hd e
    rw [(frame_Lc k d hd _ 0).1, hL_def] at e
    linarith only [e, hh]
  have hpre : (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ)) - (1, 0) ∉ cs := by
    intro hm; rw [hc0'] at hm
    exact zfa _ _ dir10 ((Q _ hm _ (zcell _ _ dir10)).2.1 (zRg _ _ dir10)).2
  have hpost : (N : ℤ) • kW + ((J : ℤ) + 1) • dW + -dW ∉ cs := by
    intro hm; rw [hcl'] at hm
    exact zfa _ _ hdW ((Q _ hm _ (zcell _ _ hdW)).2.2 (zRg _ _ hdW)).2
  have hpp : (N : ℤ) • kW + ((J : ℤ) + 1) • dW + -dW ≠
      (N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ)) - (1, 0) := by
    intro e
    rw [hcl', hc0'] at e
    have hz := zcell kW dW hdW
    rw [e] at hz
    obtain ⟨c1, c2⟩ := frame_cell N hN (0, 0) (1, 0) dir10 J _ hz
    have d1 : dist (Lc 1 kW dW ((J : ℝ) * h, 0)) (kR (0, 0)) ≤ L := by
      rw [frame_dist (0, 0) (1, 0) dir10, max_le_iff]
      rw [abs_le] at c1 c2
      push_cast at c1
      constructor <;> rw [abs_le] <;> constructor <;>
        linarith only [c1.1, c1.2, c2.1, c2.2, hL_def, hJh, hh]
    have d2 : dist (Lc 1 kW dW ((J : ℝ) * h, 0)) (kR kW) ≤ L := by
      rw [frame_dist kW dW hdW, (frame_Lc kW dW hdW _ 0).1, (frame_Lc kW dW hdW _ 0).2, abs_zero,
        max_le_iff]
      exact ⟨by rw [abs_of_nonneg hJh, hL_def]; linarith only [hh], hL.le⟩
    have := dist_triangle_left (kR (0, 0)) (kR kW) (Lc 1 kW dW ((J : ℝ) * h, 0))
    linarith only [d1, d2, this, hXW, hLρ, hρ4]
  obtain ⟨cA, cB, cAB, cAc, cBc⟩ := chain_props hh cs (1, 0) (-dW) _ _ hhead hlast hnd hch dir10
    (isDir_neg hdW) hpre hpost hpp
  -- the end points of the two chains
  have pA0 : mid h ((N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ))) (-(1, 0)) =
      (L, 0) := by
    rw [hL_def]; unfold mid; ext <;> simp <;> ring
  have pB0 : quarter h ((N : ℤ) • ((0 : ℤ), (0 : ℤ)) + ((J : ℤ) + 1) • ((1 : ℤ), (0 : ℤ)) - (1, 0))
      (1, 0) = (L, h / 4) := by
    rw [hc0', hL_def]; unfold quarter; ext <;> simp <;> ring
  obtain ⟨e1, e2⟩ := cell_sm N hN kW dW ((J : ℤ) + 1)
  push_cast at e1 e2
  have pA1 : mid h ((N : ℤ) • kW + ((J : ℤ) + 1) • dW) (-dW) = Lc 1 kW dW (L, 0) := by
    unfold mid Lc
    ext
    · simp only [Prod.fst_neg, Int.cast_neg]; rw [hL_def]; linear_combination e1
    · simp only [Prod.snd_neg, Int.cast_neg]; rw [hL_def]; linear_combination e2
  have pB1 : quarter h ((N : ℤ) • kW + ((J : ℤ) + 1) • dW) (-dW) = Lc 1 kW dW (L, -(h / 4)) := by
    unfold quarter Lc
    ext
    · simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; rw [hL_def]; linear_combination e1
    · simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; rw [hL_def]; linear_combination e2
  rw [pA0, pA1] at cA
  rw [pB0, pB1] at cB
  -- names
  set A2 := chainA h (1, 0) cs (-dW) with hA2
  set B2 := chainB h (1, 0) cs (-dW) with hB2
  set QW := Lc 1 kW dW (L, 0) with hQW
  set QWB := Lc 1 kW dW (L, -(h / 4)) with hQWB
  set W := kR kW with hWdef
  set U : ℝ × ℝ := (L / 2, h / 8) with hU
  -- cells of the chains
  have hA2f : ∀ z ∈ A2, z ∉ Obs D0 u ∧ (z ∈ Rg h L (0, 0) (1, 0) → z.1 = L) ∧
      (z ∈ Rg h L kW dW → fa kW dW z = L) := by
    intro z hz
    obtain ⟨c, hc, hzc, -⟩ := cAc z hz
    obtain ⟨q1, q2, q3⟩ := Q c hc z hzc
    exact ⟨q1, fun r => by rw [← fa_id]; exact (q2 r).2, fun r => (q3 r).2⟩
  have hB2f : ∀ z ∈ B2, z ∉ Obs D0 u ∧ (z ∈ Rg h L (0, 0) (1, 0) → z.1 = L) ∧
      (z ∈ Rg h L kW dW → fa kW dW z = L) := by
    intro z hz
    obtain ⟨c, hc, hzc, -⟩ := cBc z hz
    obtain ⟨q1, q2, q3⟩ := Q c hc z hzc
    exact ⟨q1, fun r => by rw [← fa_id]; exact (q2 r).2, fun r => (q3 r).2⟩
  -- the pieces near X
  have hA1R : seg (0, 0) (L, 0) ⊆ Rg h L (0, 0) (1, 0) := seg_Rg0 hL (by rw [abs_zero]; positivity)
  have hBXR : seg (0, 0) (L, h / 4) ⊆ Rg h L (0, 0) (1, 0) :=
    seg_Rg0 hL (by rw [abs_of_pos (by positivity)])
  have hB1X : seg U (L, h / 4) ⊆ seg (0, 0) (L, h / 4) := by
    intro z hz
    obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
    exact mem_seg_of ((1 + s) / 2) (by linarith only [s0]) (by linarith only [s1])
      (by rw [a1, hU]; simp; ring)
      (by rw [a2, hU]; simp; ring)
  have hCX : seg (0, 0) U ⊆ seg (0, 0) (L, h / 4) := by
    intro z hz
    obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
    exact mem_seg_of (s / 2) (by linarith only [s0]) (by linarith only [s1])
      (by rw [a1, hU]; simp; ring)
      (by rw [a2, hU]; simp; ring)
  have hB1c : ∀ z ∈ seg U (L, h / 4), h / 8 ≤ z.2 ∧ L / 2 ≤ z.1 := by
    intro z hz; rw [hU] at hz; exact xB1c hL hh z hz
  have hCc : ∀ z ∈ seg (0, 0) U, z.1 ≤ L / 2 ∧ z.2 = z.1 * (h / 4) / L := by
    intro z hz; rw [hU] at hz; exact xCc hL z hz
  have hA1c : ∀ z ∈ seg (0, 0) (L, 0), z.2 = 0 := by
    intro z hz
    obtain ⟨s, s0, s1, a1, a2⟩ := seg_coord hz
    simp at a2; exact a2
  have endA1 : ∀ z ∈ seg (0, 0) (L, 0), z.1 = L → z = (L, 0) := by
    intro z hz e
    have := seg_end dir10 hL (by rwa [Lc_id, kR00]) (by rw [fa_id]; exact e)
    rwa [Lc_id] at this
  have endBX : ∀ z ∈ seg (0, 0) (L, h / 4), z.1 = L → z = (L, h / 4) := by
    intro z hz e
    have := seg_end dir10 hL (by rwa [Lc_id, kR00]) (by rw [fa_id]; exact e)
    rwa [Lc_id] at this
  -- the pieces near W
  have hA3R : seg QW W ⊆ Rg h L kW dW := by
    rw [seg_symm]; exact seg_Rg hL kW dW hdW (by rw [abs_zero]; positivity)
  have hB3R : seg QWB W ⊆ Rg h L kW dW := by
    rw [seg_symm]; exact seg_Rg hL kW dW hdW (by rw [abs_neg, abs_of_pos (by positivity)])
  have endA3 : ∀ z ∈ seg QW W, fa kW dW z = L → z = QW := by
    intro z hz e; rw [seg_symm] at hz; exact seg_end hdW hL hz e
  have endB3 : ∀ z ∈ seg QWB W, fa kW dW z = L → z = QWB := by
    intro z hz e; rw [seg_symm] at hz; exact seg_end hdW hL hz e
  have hA3B3 : ∀ z, z ∈ seg QW W → z ∈ seg QWB W → z = W := by
    intro z h1 h2
    rw [seg_symm] at h1 h2
    obtain ⟨t, t0, t1, f1, f2⟩ := seg_frame kW dW hdW L 0 z h1
    obtain ⟨t', t0', t1', f1', f2'⟩ := seg_frame kW dW hdW L (-(h / 4)) z h2
    have ht' : t' = 0 := by
      rw [f2] at f2'
      have : t' * (h / 4) = 0 := by linarith only [f2']
      rcases mul_eq_zero.mp this with e | e
      · exact e
      · linarith only [e, hh]
    rw [← Lc_frame kW dW hdW z, f1', f2, ht', zero_mul, mul_zero, Lc_zero]
  have hQWne : QW ≠ W := by
    intro e
    have := (frame_Lc kW dW hdW L 0).1
    rw [← hQW, e, hWdef, ← Lc_zero kW dW, (frame_Lc kW dW hdW 0 0).1] at this
    linarith only [this, hL]
  have hQWBne : QWB ≠ W := by
    intro e
    have := (frame_Lc kW dW hdW L (-(h / 4))).1
    rw [← hQWB, e, hWdef, ← Lc_zero kW dW, (frame_Lc kW dW hdW 0 0).1] at this
    linarith only [this, hL]
  -- the new arcs
  set Af := seg (0, 0) (L, 0) ∪ A2 ∪ seg QW W with hAf
  set Bf := seg U (L, h / 4) ∪ B2 ∪ seg QWB W with hBf
  set C := seg (0, 0) U with hC
  have FA : ArcImg (0, 0) W Af := by
    have a1 : ArcImg (0, 0) (L, 0) (seg (0, 0) (L, 0)) :=
      arcImg_seg (by intro e; have := congrArg Prod.fst e; simp at this; linarith only [this, hL])
    refine (a1.trans cA ?_).trans (arcImg_seg hQWne) ?_
    · intro z h1 h2
      exact endA1 z h1 ((hA2f z h2).2.1 (hA1R h1))
    · intro z h1 h2
      rcases h1 with h1 | h1
      · exact (hRR z (hA1R h1) (hA3R h2)).elim
      · exact endA3 z h2 ((hA2f z h1).2.2 (hA3R h2))
  have FB : ArcImg U W Bf := by
    have b1 : ArcImg U (L, h / 4) (seg U (L, h / 4)) :=
      arcImg_seg (by intro e; have := congrArg Prod.fst e; simp [hU] at this; linarith only [this, hL])
    refine (b1.trans cB ?_).trans (arcImg_seg hQWBne) ?_
    · intro z h1 h2
      exact endBX z (hB1X h1) ((hB2f z h2).2.1 (hBXR (hB1X h1)))
    · intro z h1 h2
      rcases h1 with h1 | h1
      · exact (hRR z (hBXR (hB1X h1)) (hB3R h2)).elim
      · exact endB3 z h2 ((hB2f z h1).2.2 (hB3R h2))
  have FC : ArcImg (0, 0) U C :=
    arcImg_seg (by intro e; have := congrArg Prod.fst e; simp [hU] at this; linarith only [this, hL])
  -- U is free
  have hURX : U ∈ Rg h L (0, 0) (1, 0) := hBXR (hCX (by rw [hC]; exact FC.right_mem))
  have hU1 : U.1 = L / 2 := by rw [hU]
  have FU : U ∉ Obs D0 u := by
    intro hm
    have := congrArg Prod.fst (hRXo U hURX hm)
    rw [hU1] at this; simp at this; linarith only [this, hL]
  have FUA : U ∉ Af := by
    rintro ((h1 | h1) | h1)
    · have := hA1c U h1; rw [hU] at this; simp at this; linarith only [this, hh]
    · have := (hA2f U h1).2.1 hURX; rw [hU1] at this; linarith only [this, hL]
    · exact hRR U hURX (hA3R h1)
  -- obstacles
  have FAo : ∀ z ∈ Af, z ∈ Obs D0 u → z = (0, 0) ∨ z = W := by
    rintro z ((h1 | h1) | h1) hz
    · left; exact hRXo z (hA1R h1) hz
    · exact ((hA2f z h1).1 hz).elim
    · right; exact hRWo z (hA3R h1) hz
  have FBo : ∀ z ∈ Bf, z ∈ Obs D0 u → z = W := by
    rintro z ((h1 | h1) | h1) hz
    · exfalso
      have e := hRXo z (hBXR (hB1X h1)) hz
      have := (hB1c z h1).1
      rw [e] at this; simp at this; linarith only [this, hh]
    · exact ((hB2f z h1).1 hz).elim
    · exact hRWo z (hB3R h1) hz
  have FCo : ∀ z ∈ C, z ∈ Obs D0 u → z = (0, 0) := fun z h1 hz => hRXo z (hBXR (hCX h1)) hz
  -- the new arcs meet only at their common ends
  have FAB : ∀ z ∈ Af, z ∈ Bf → z = W := by
    rintro z ((h1 | h1) | h1) ((h2 | h2) | h2)
    · exfalso; have e1 := hA1c z h1; have e2 := (hB1c z h2).1; linarith only [e1, e2, hh]
    · exfalso
      have e := endA1 z h1 ((hB2f z h2).2.1 (hA1R h1))
      exact cAB z (e ▸ cA.left_mem) h2
    · exact (hRR z (hA1R h1) (hB3R h2)).elim
    · exfalso
      have e := endBX z (hB1X h2) ((hA2f z h1).2.1 (hBXR (hB1X h2)))
      exact cAB z h1 (e ▸ cB.left_mem)
    · exact (cAB z h1 h2).elim
    · exfalso
      have e := endB3 z h2 ((hA2f z h1).2.2 (hB3R h2))
      exact cAB z h1 (e ▸ cB.right_mem)
    · exact (hRR z (hBXR (hB1X h2)) (hA3R h1)).elim
    · exfalso
      have e := endA3 z h1 ((hB2f z h2).2.2 (hA3R h1))
      exact cAB z (e ▸ cA.right_mem) h2
    · exact hA3B3 z h1 h2
  have FAC : ∀ z ∈ Af, z ∈ C → z = (0, 0) := by
    rintro z ((h1 | h1) | h1) h2
    · obtain ⟨c1, c2⟩ := hCc z h2
      have e := hA1c z h1
      rw [e] at c2
      have : z.1 = 0 := by
        have hpos : 0 < h / 4 / L := by positivity
        have : z.1 * (h / 4 / L) = 0 := by rw [mul_div_assoc']; linarith only [c2]
        rcases mul_eq_zero.mp this with e' | e'
        · exact e'
        · linarith only [e', hpos]
      ext
      · exact this
      · exact e
    · exfalso
      have e1 := (hA2f z h1).2.1 (hBXR (hCX h2))
      have e2 := (hCc z h2).1
      linarith only [e1, e2, hL]
    · exact (hRR z (hBXR (hCX h2)) (hA3R h1)).elim
  have FBC : ∀ z ∈ Bf, z ∈ C → z = U := by
    rintro z ((h1 | h1) | h1) h2
    · rw [hC] at h2; rw [hU] at h1 h2 ⊢; exact xBC hL z h1 h2
    · exfalso
      have e1 := (hB2f z h1).2.1 (hBXR (hCX h2))
      have e2 := (hCc z h2).1
      linarith only [e1, e2, hL]
    · exact (hRR z (hBXR (hCX h2)) (hB3R h1)).elim
  rw [kR00] at hX
  exact assemble H0 G' D0 a b u hab hua hub hu0 hab0 hG' U Af Bf C (hX ▸ hW ▸ FA) (hW ▸ FB)
    (hX ▸ FC) (by rw [hX, hW]; exact FAo) (by rw [hW]; exact FBo) (by rw [hX]; exact FCo)
    (by rw [hW]; exact FAB) (by rw [hX]; exact FAC) FBC FU FUA


/-! Radial straightening of all arcs at one vertex, for image drawings. -/

lemma fin_min {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c > 0, ∀ i, c ≤ f i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  | inr _ =>
    obtain ⟨i0, hi0⟩ := Finite.exists_min f
    exact ⟨f i0, hf i0, hi0⟩

lemma dist_smul_add (A v : ℝ × ℝ) {t : ℝ} (ht : 0 ≤ t) : dist (A + t • v) A = t * ‖v‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]

lemma seg_dist_le {A p z : ℝ × ℝ} (hz : z ∈ seg A p) : dist z A ≤ dist p A := by
  obtain ⟨t, ht, rfl⟩ := hz
  rw [dist_smul_add A _ ht.1, dist_eq_norm p A]
  calc t * ‖p - A‖ ≤ 1 * ‖p - A‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ = ‖p - A‖ := one_mul _

lemma seg_dist_eq {A p z : ℝ × ℝ} (hp : p ≠ A) (hz : z ∈ seg A p) (h : dist z A = dist p A) :
    z = p := by
  obtain ⟨t, ht, rfl⟩ := hz
  rw [dist_smul_add A _ ht.1, dist_eq_norm p A] at h
  have hn : 0 < ‖p - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  have ht1 : t = 1 := by
    have h2 : (t - 1) * ‖p - A‖ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · linarith
    · linarith
  subst ht1; simp

lemma seg_seg {A p q z : ℝ × ℝ} (hpq : p ≠ q) (hd : dist p A = dist q A) (hz1 : z ∈ seg A p)
    (hz2 : z ∈ seg A q) : z = A := by
  obtain ⟨s, hs, rfl⟩ := hz1
  obtain ⟨t, ht, e⟩ := hz2
  have hd1 := congrArg (fun z => dist z A) e
  simp only at hd1
  rw [dist_smul_add A _ ht.1, dist_smul_add A _ hs.1, ← dist_eq_norm, ← dist_eq_norm, hd] at hd1
  by_cases hq : dist q A = 0
  · exfalso; apply hpq
    rw [hq, dist_eq_zero] at hd
    rw [dist_eq_zero] at hq
    rw [hd, hq]
  · have hts : t = s := mul_right_cancel₀ hq hd1
    subst hts
    by_cases ht0 : t = 0
    · subst ht0; simp
    · exfalso; apply hpq
      have e2 : t • (q - A) = t • (p - A) := add_left_cancel e
      have e3 : q - A = p - A := smul_right_injective (ℝ × ℝ) ht0 e2
      exact (sub_left_injective e3).symm

set_option maxHeartbeats 2000000 in
theorem straighten {n : ℕ} {H : SimpleGraph (Fin n)} (D : ImgDr H) (a : Fin n) (rmax : ℝ)
    (hrmax : 0 < rmax) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rmax ∧ ∃ D' : ImgDr H, D'.P = D.P ∧
      (∀ v, v ≠ a → r < dist (D.P v) (D.P a)) ∧
      (∀ v w, H.Adj v w → v ≠ a → w ≠ a → D'.S v w = D.S v w ∧
        ∀ z ∈ D.S v w, r < dist z (D.P a)) ∧
      (∀ c, H.Adj a c → ∃ pc : ℝ × ℝ, ∃ Oc : Set (ℝ × ℝ), dist pc (D.P a) = r ∧ pc ∈ D.S a c ∧
        D'.S a c = seg (D.P a) pc ∪ Oc ∧ Oc ⊆ D.S a c ∧
        ∀ z ∈ Oc, r ≤ dist z (D.P a) ∧ (dist z (D.P a) = r → z = pc)) := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A, A = D.P a := ⟨_, rfl⟩
  rw [← hAdef]
  -- a path for every edge
  have hpath : ∀ p : Fin n × Fin n, ∃ γ : Path (D.P p.1) (D.P p.2),
      H.Adj p.1 p.2 → Function.Injective γ ∧ Set.range γ = D.S p.1 p.2 := by
    intro p
    by_cases hp : H.Adj p.1 p.2
    · obtain ⟨γ, h1, h2⟩ := D.arc _ _ hp
      exact ⟨γ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨segPath _ _, fun h => absurd h hp⟩
  choose γ hγ using hpath
  obtain ⟨γa, hγa⟩ : ∃ γa : ∀ b, Path (D.P a) (D.P b),
      ∀ b, H.Adj a b → Function.Injective (γa b) ∧ Set.range (γa b) = D.S a b :=
    ⟨fun b => γ (a, b), fun b h => hγ (a, b) h⟩
  have hvert : ∀ v : Fin n, ∃ c > 0, v ≠ a → c ≤ dist (D.P v) A := by
    intro v
    by_cases hv : v = a
    · exact ⟨1, one_pos, fun h => absurd hv h⟩
    · exact ⟨_, dist_pos.mpr (fun e => hv (D.inj (e.trans hAdef))), fun _ => le_rfl⟩
  have hedge : ∀ p : Fin n × Fin n, ∃ c > 0, H.Adj p.1 p.2 → p.1 ≠ a → p.2 ≠ a →
      ∀ z ∈ D.S p.1 p.2, c ≤ dist z A := by
    intro p
    by_cases hp : H.Adj p.1 p.2 ∧ p.1 ≠ a ∧ p.2 ≠ a
    · obtain ⟨hinj, hran⟩ := hγ p hp.1
      obtain ⟨c, hc, hle⟩ := pos_min_pt (γ p) A (by
        intro t ht
        have hm : D.P a ∈ D.S p.1 p.2 := by rw [← hAdef, ← hran, ← ht]; exact Set.mem_range_self t
        rcases D.avoid _ _ hp.1 a hm with h | h
        · exact hp.2.1 h.symm
        · exact hp.2.2 h.symm)
      refine ⟨c, hc, fun _ _ _ z hz => ?_⟩
      rw [← hran] at hz
      obtain ⟨t, rfl⟩ := hz
      exact hle t
    · exact ⟨1, one_pos, fun h h1 h2 => absurd ⟨h, h1, h2⟩ hp⟩
  choose cv hcv0 hcv using hvert
  choose ce hce0 hce using hedge
  obtain ⟨c1, hc1, hc1le⟩ := fin_min cv hcv0
  obtain ⟨c2, hc2, hc2le⟩ := fin_min ce hce0
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min (min c1 c2) rmax / 2 := ⟨_, rfl⟩
  have hm0 : 0 < min (min c1 c2) rmax := lt_min (lt_min hc1 hc2) hrmax
  have hr : 0 < r := by rw [hrdef]; exact half_pos hm0
  have hrm : r ≤ rmax := by
    rw [hrdef]; have := min_le_right (min c1 c2) rmax; linarith
  have hrv : ∀ v, v ≠ a → r < dist (D.P v) A := by
    intro v hv
    have h1 := hcv v hv
    have h2 := hc1le v
    have h3 : min (min c1 c2) rmax ≤ c1 := (min_le_left _ _).trans (min_le_left _ _)
    rw [hrdef]; linarith
  have hre : ∀ v w, H.Adj v w → v ≠ a → w ≠ a → ∀ z ∈ D.S v w, r < dist z A := by
    intro v w h hv hw z hz
    have h1 := hce (v, w) h hv hw z hz
    have h2 := hc2le (v, w)
    have h3 : min (min c1 c2) rmax ≤ c2 := (min_le_left _ _).trans (min_le_right _ _)
    rw [hrdef]; linarith
  -- exit times at the arcs of `a`
  have hex : ∀ b : Fin n, ∃ τ : unitInterval, H.Adj a b →
      dist (γa b τ) A = r ∧ ∀ t : unitInterval, τ < t → r < dist (γa b t) A := by
    intro b
    by_cases h : H.Adj a b
    · have hb : r < dist (D.P b) A := hrv b (H.ne_of_adj h).symm
      obtain ⟨τ, h1, h2⟩ := exit_time (γa b) hr (show r < dist (D.P b) (D.P a) by rw [← hAdef]; exact hb)
      exact ⟨τ, fun _ => ⟨by rw [hAdef]; exact h1, by rw [hAdef]; exact h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose τ hτ using hex
  have hτ1 : ∀ b (h : H.Adj a b), τ b < 1 := by
    intro b h
    refine lt_of_le_of_ne (unitInterval.le_one _) (fun e => ?_)
    have h1 := (hτ b h).1
    rw [e, (γa b).target] at h1
    have := hrv b (H.ne_of_adj h).symm
    linarith
  have hτ0 : ∀ b (h : H.Adj a b), τ b ≠ 0 := by
    intro b h e
    have h1 := (hτ b h).1
    rw [e, (γa b).source] at h1
    rw [hAdef, dist_self] at h1
    linarith
  obtain ⟨p, hp⟩ : ∃ p : Fin n → ℝ × ℝ, ∀ b, p b = γa b (τ b) := ⟨_, fun b => rfl⟩
  have hpd : ∀ b, H.Adj a b → dist (p b) A = r := fun b h => by rw [hp b]; exact (hτ b h).1
  have hpA : ∀ b, H.Adj a b → p b ≠ A := fun b h e => by
    have := hpd b h; rw [e, dist_self] at this; linarith
  have hpS : ∀ b, H.Adj a b → p b ∈ D.S a b := fun b h => by
    rw [← (hγa b h).2, hp b]; exact Set.mem_range_self _
  obtain ⟨Out, hOut⟩ : ∃ Out : Fin n → Set (ℝ × ℝ), ∀ b, Out b = (γa b) '' Set.Icc (τ b) 1 :=
    ⟨_, fun b => rfl⟩
  have hOutS : ∀ b, H.Adj a b → Out b ⊆ D.S a b := by
    intro b h z hz
    rw [hOut b] at hz
    obtain ⟨t, -, rfl⟩ := hz
    rw [← (hγa b h).2]; exact Set.mem_range_self t
  have hOut_ge : ∀ b, H.Adj a b → ∀ z ∈ Out b, r ≤ dist z A ∧ (dist z A = r → z = p b) := by
    intro b h z hz
    rw [hOut b] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rcases eq_or_lt_of_le ht.1 with e | e
    · rw [← e, ← hp b]; exact ⟨(hpd b h).ge, fun _ => rfl⟩
    · have := (hτ b h).2 t e; exact ⟨this.le, fun h' => absurd h' (ne_of_gt this)⟩
  have hOut_arc : ∀ b (h : H.Adj a b), ∀ z ∈ Out b, ∃ s : unitInterval, s ≠ 0 ∧ γa b s = z := by
    intro b h z hz
    rw [hOut b] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    refine ⟨s, fun e => hτ0 b h ?_, rfl⟩
    exact le_antisymm (e ▸ hs.1) unitInterval.nonneg'
  obtain ⟨Str, hStr⟩ : ∃ Str : Fin n → Set (ℝ × ℝ), ∀ b, Str b = seg A (p b) ∪ Out b :=
    ⟨_, fun b => rfl⟩
  have hStr_arc : ∀ b, H.Adj a b → ArcImg A (D.P b) (Str b) := by
    intro b h
    have h1 : ArcImg A (p b) (seg A (p b)) := arcImg_seg (hpA b h).symm
    have h2 : ArcImg (p b) (D.P b) (Out b) := by
      have := arcImg_sub (γa b) (hγa b h).1 (τ b) 1 (hτ1 b h)
      rw [(γa b).target, ← hp b, ← hOut b] at this; exact this
    rw [hStr b]
    refine h1.trans h2 ?_
    intro z hz1 hz2
    obtain ⟨hge, heq⟩ := hOut_ge b h z hz2
    have hle := seg_dist_le hz1; rw [hpd b h] at hle
    exact heq (le_antisymm hle hge)
  -- meetings at `a`
  have hγeq : ∀ v w (h : H.Adj v w) (s : unitInterval), γ (v, w) s ∈ D.S v w := fun v w h s => by
    rw [← (hγ (v, w) h).2]; exact Set.mem_range_self s
  have hγend : ∀ v w (h : H.Adj v w) (s : unitInterval), (γ (v, w) s = D.P v ∨ γ (v, w) s = D.P w) →
      s = 0 ∨ s = 1 := by
    intro v w h s hs
    rcases hs with hs | hs
    · left; exact (hγ (v, w) h).1 (hs.trans (γ (v, w)).source.symm)
    · right; exact (hγ (v, w) h).1 (hs.trans (γ (v, w)).target.symm)
  have hpp : ∀ b c, H.Adj a b → H.Adj a c → b ≠ c → p b ≠ p c := by
    intro b c hb hc hbc e
    have hne : ¬ s(a, b) = s(a, c) := by
      intro e'; rcases Sym2.eq_iff.mp e' with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact hbc h2
      · exact H.ne_of_adj hb h2.symm
    rcases D.meet a b a c hb hc hne (p b) (hpS b hb) (e ▸ hpS c hc) with h1 | h1
    · exact hpA b hb (h1.trans hAdef.symm)
    · have := hpd b hb; rw [h1] at this; have := hrv b (H.ne_of_adj hb).symm; linarith
  have M22 : ∀ b c, H.Adj a b → H.Adj a c → b ≠ c → ∀ z, z ∈ Str b → z ∈ Str c → z = A := by
    intro b c hb hc hbc z hz1 hz2
    rw [hStr b] at hz1
    rw [hStr c] at hz2
    rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
    · exact seg_seg (hpp b c hb hc hbc) ((hpd b hb).trans (hpd c hc).symm) hz1 hz2
    · exfalso
      obtain ⟨hge, heq⟩ := hOut_ge c hc z hz2
      have hle := seg_dist_le hz1; rw [hpd b hb] at hle
      have e1 := heq (le_antisymm hle hge)
      have e2 := seg_dist_eq (hpA b hb) hz1 (by rw [hpd b hb]; exact le_antisymm hle hge)
      exact hpp b c hb hc hbc (e2.symm.trans e1)
    · exfalso
      obtain ⟨hge, heq⟩ := hOut_ge b hb z hz1
      have hle := seg_dist_le hz2; rw [hpd c hc] at hle
      have e1 := heq (le_antisymm hle hge)
      have e2 := seg_dist_eq (hpA c hc) hz2 (by rw [hpd c hc]; exact le_antisymm hle hge)
      exact hpp b c hb hc hbc (e1.symm.trans e2)
    · exfalso
      have hne : ¬ s(a, b) = s(a, c) := by
        intro e'; rcases Sym2.eq_iff.mp e' with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact hbc h2
        · exact H.ne_of_adj hb h2.symm
      rcases D.meet a b a c hb hc hne z (hOutS b hb hz1) (hOutS c hc hz2) with h1 | h1
      · obtain ⟨hge, -⟩ := hOut_ge b hb z hz1
        rw [h1, ← hAdef, dist_self] at hge; linarith
      · have hd := (hOut_ge c hc z hz2).1
        have hz3 := hOutS c hc hz2
        rcases D.meet a c a b hc hb (fun e => hne e.symm) z hz3 (hOutS b hb hz1) with h2 | h2
        · rw [h2, ← hAdef, dist_self] at hd; linarith
        · exact hbc (D.inj (h1.symm.trans h2))
  have M23 : ∀ b, H.Adj a b → ∀ v w, H.Adj v w → v ≠ a → w ≠ a → ∀ z, z ∈ Str b →
      z ∈ D.S v w → z = D.P b ∧ (z = D.P v ∨ z = D.P w) := by
    intro b hb v w h hv hw z hz1 hz2
    rw [hStr b] at hz1
    rcases hz1 with hz1 | hz1
    · exfalso
      have := seg_dist_le hz1; rw [hpd b hb] at this
      have := hre v w h hv hw z hz2
      linarith
    · have hne : ¬ s(a, b) = s(v, w) := by
        intro e'; rcases Sym2.eq_iff.mp e' with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hv h1.symm
        · exact hw h1.symm
      have hzS := hOutS b hb hz1
      rcases D.meet a b v w hb h hne z hzS hz2 with h1 | h1
      · exfalso; have := (hOut_ge b hb z hz1).1; rw [h1, ← hAdef, dist_self] at this; linarith
      · exact ⟨h1, D.meet v w a b h hb (fun e => hne e.symm) z hz2 hzS⟩
  -- the new image drawing
  let S' : Fin n → Fin n → Set (ℝ × ℝ) := fun v w =>
    if v = a then Str w else if w = a then Str v else D.S v w
  have hSa : ∀ w, S' a w = Str w := fun w => if_pos rfl
  have hSa' : ∀ v, v ≠ a → S' v a = Str v := fun v hv => by
    simp only [S', if_neg hv, ↓reduceIte]
  have hSo : ∀ v w, v ≠ a → w ≠ a → S' v w = D.S v w := fun v w hv hw => by
    simp only [S', if_neg hv, if_neg hw]
  have hsymm : ∀ v w, S' v w = S' w v := by
    intro v w
    by_cases hv : v = a <;> by_cases hw : w = a
    · rw [hv, hw]
    · rw [hv, hSa, hSa' w hw]
    · rw [hw, hSa, hSa' v hv]
    · rw [hSo v w hv hw, hSo w v hw hv, D.symm]
  have hcls : ∀ v w, H.Adj v w → (v = a ∧ H.Adj a w) ∨ (w = a ∧ H.Adj a v) ∨ (v ≠ a ∧ w ≠ a) := by
    intro v w h
    by_cases hv : v = a
    · left; exact ⟨hv, hv ▸ h⟩
    · by_cases hw : w = a
      · right; left; exact ⟨hw, hw ▸ h.symm⟩
      · right; right; exact ⟨hv, hw⟩
  refine ⟨r, hr, hrm, ⟨D.P, D.inj, S', hsymm, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · -- arcs
    intro v w h
    rcases hcls v w h with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ | ⟨hv, hw⟩
    · rw [hSa, ← hAdef]; exact hStr_arc w hg
    · rw [hSa' v (H.ne_of_adj h), ← hAdef]; exact (hStr_arc v hg).symm
    · rw [hSo v w hv hw]; exact D.arc v w h
  · -- vertices
    intro v w h x hx
    rcases hcls v w h with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ | ⟨hv, hw⟩
    · rw [hSa, hStr w] at hx
      rcases hx with hx | hx
      · left
        by_contra hxa
        have := seg_dist_le hx; rw [hpd w hg] at this
        have := hrv x hxa; linarith
      · exact D.avoid _ _ hg x (hOutS w hg hx)
    · rw [hSa' v (H.ne_of_adj h), hStr v] at hx
      rcases hx with hx | hx
      · right
        by_contra hxa
        have := seg_dist_le hx; rw [hpd v hg] at this
        have := hrv x hxa; linarith
      · rcases D.avoid _ _ hg x (hOutS v hg hx) with e | e
        · right; exact e
        · left; exact e
    · rw [hSo v w hv hw] at hx; exact D.avoid v w h x hx
  · -- meetings
    intro v w x y h k hne z hz1 hz2
    rcases hcls v w h with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ | ⟨hv, hw⟩ <;>
    rcases hcls x y k with ⟨rfl, kg⟩ | ⟨rfl, kg⟩ | ⟨hx, hy⟩
    · rw [hSa] at hz1 hz2
      have hwy : w ≠ y := fun e => hne (by rw [e])
      left; rw [← hAdef] at *; exact M22 w y hg kg hwy z hz1 hz2
    · rw [hSa] at hz1; rw [hSa' x (H.ne_of_adj k)] at hz2
      have hwx : w ≠ x := fun e => hne (by rw [e, Sym2.eq_swap])
      left; exact (M22 w x hg kg hwx z hz1 hz2).trans hAdef
    · rw [hSa] at hz1; rw [hSo x y hx hy] at hz2
      right; exact (M23 w hg x y k hx hy z hz1 hz2).1
    · rw [hSa' v (H.ne_of_adj h)] at hz1; rw [hSa] at hz2
      have hvy : v ≠ y := fun e => hne (by rw [e, Sym2.eq_swap])
      right; exact (M22 v y hg kg hvy z hz1 hz2).trans hAdef
    · rw [hSa' v (H.ne_of_adj h)] at hz1; rw [hSa' x (H.ne_of_adj k)] at hz2
      have hvx : v ≠ x := fun e => hne (by rw [e])
      right; exact (M22 v x hg kg hvx z hz1 hz2).trans hAdef
    · rw [hSa' v (H.ne_of_adj h)] at hz1; rw [hSo x y hx hy] at hz2
      left; exact (M23 v hg x y k hx hy z hz1 hz2).1
    · rw [hSo v w hv hw] at hz1; rw [hSa] at hz2
      exact (M23 y kg v w h hv hw z hz2 hz1).2
    · rw [hSo v w hv hw] at hz1; rw [hSa' x (H.ne_of_adj k)] at hz2
      exact (M23 x kg v w h hv hw z hz2 hz1).2
    · rw [hSo v w hv hw] at hz1; rw [hSo x y hx hy] at hz2
      exact D.meet v w x y h k hne z hz1 hz2
  · intro v hv; exact hrv v hv
  · intro v w h hv hw
    exact ⟨by show S' v w = _; exact hSo v w hv hw, hre v w h hv hw⟩
  · intro c hc
    refine ⟨p c, Out c, hpd c hc, hpS c hc, ?_, hOutS c hc, hOut_ge c hc⟩
    show S' a c = _
    rw [hSa, hStr c]


/-! The core statement: cones at both ends plus a corridor path. -/

theorem core {n : ℕ} (H0 G' : SimpleGraph (Fin n)) (D0 : ImgDr H0) (a b u : Fin n)
    (hab : a ≠ b) (hua : u ≠ a) (hub : u ≠ b)
    (hu0 : ∀ q, ¬ H0.Adj u q) (hab0 : ¬ H0.Adj a b)
    (hG' : ∀ p q, G'.Adj p q ↔
      (H0.Adj p q ∨ s(p, q) = s(a, b) ∨ s(p, q) = s(u, a) ∨ s(p, q) = s(u, b)))
    (kW dW : ℤ × ℤ) (hkW : kW ≠ 0) (hdW : IsDir dW)
    (hX : D0.P a = kR (0, 0)) (hW : D0.P b = kR kW)
    (ρ μ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hμ : 0 < μ)
    (coneX : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 (0, 0) (1, 0) (α, β) ∉ Obs D0 u)
    (coneW : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 kW dW (α, β) ∉ Obs D0 u)
    (sX sW : ℝ) (hsX : 0 < sX) (hsX' : sX ≤ ρ / 2) (hsW : 0 < sW) (hsW' : sW ≤ ρ / 2)
    (K : Path (Lc 1 (0, 0) (1, 0) (sX, 0)) (Lc 1 kW dW (sW, 0)))
    (hK : ∀ t, K t ∉ Obs D0 u) (ρ' : ℝ) (hρ' : 0 < ρ')
    (hKfar : ∀ t, ρ' ≤ dist (K t) (kR (0, 0)) ∧ ρ' ≤ dist (K t) (kR kW)) :
    IsPlanar G' := by
  obtain ⟨δ, hδ, hδK⟩ := sep_path_set K (Obs D0 u) (Obs_compact D0 u) hK
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 1 / μ ≤ J := ⟨⌈1 / μ⌉₊, Nat.le_ceil _⟩
  have hJμ : 1 ≤ μ * J := by
    rw [div_le_iff₀ hμ] at hJ; linarith only [hJ]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 / δ + 1 / ρ' + 1 / sX + 1 / sW + 1 / ρ + 1 := ⟨_, rfl⟩
  have p1 : 0 < 1 / δ := by positivity
  have p2 : 0 < 1 / ρ' := by positivity
  have p3 : 0 < 1 / sX := by positivity
  have p4 : 0 < 1 / sW := by positivity
  have p5 : 0 < 1 / ρ := by positivity
  have hTpos : 0 < T := by rw [hT]; positivity
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, ((J : ℝ) + 10) * T < N := exists_nat_gt _
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hNB
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = 1 / (N : ℝ) := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; positivity
  have hN : h * N = 1 := by rw [hh_def]; field_simp
  have small : ∀ x : ℝ, 0 < x → 1 / x ≤ T → ((J : ℝ) + 10) * h < x := by
    intro x hx hxT
    have h1 : 1 ≤ x * T := by rw [div_le_iff₀ hx] at hxT; linarith only [hxT]
    have h2 : ((J : ℝ) + 10) ≤ ((J : ℝ) + 10) * (x * T) := le_mul_of_one_le_right (by positivity) h1
    have h3 : x * (((J : ℝ) + 10) * T) < x * N := mul_lt_mul_of_pos_left hNB hx
    rw [hh_def, mul_one_div, div_lt_iff₀ hN0]
    linarith only [h2, h3]
  have sδ := small δ hδ (by linarith only [hT, p2, p3, p4, p5])
  have sρ' := small ρ' hρ' (by linarith only [hT, p1, p3, p4, p5])
  have ssX := small sX hsX (by linarith only [hT, p1, p2, p4, p5])
  have ssW := small sW hsW (by linarith only [hT, p1, p2, p3, p5])
  have sρ := small ρ hρ (by linarith only [hT, p1, p2, p3, p4])
  obtain ⟨cs, hhead, hlast, hnd, hch, Q⟩ := core_cells D0 u kW dW hkW hdW ρ μ hρ hρ4 hμ coneX coneW
    sX sW hsX' hsW' K ρ' δ hδK hKfar J N hN0 hJμ h hh_def sδ sρ' ssX ssW sρ
  have hJh : 0 ≤ (J : ℝ) * h := by positivity
  have hLρ : ((J : ℝ) + 1 / 2) * h ≤ ρ := by linarith only [hJh, sρ, hh]
  have hslope : h / 4 / (((J : ℝ) + 1 / 2) * h) ≤ μ := by
    rw [div_le_iff₀ (by positivity)]
    have e1 : 1 * h ≤ μ * J * h := mul_le_mul_of_nonneg_right hJμ hh.le
    have e2 : 0 ≤ μ * h := by positivity
    linarith only [e1, e2, hh]
  exact core_finish H0 G' D0 a b u hab hua hub hu0 hab0 hG' kW dW hkW hdW hX hW ρ μ hρ4 coneX coneW
    J N h hh hN hLρ hslope cs hhead hlast hnd hch Q


/-! From a plane drawing: image drawings, linear changes of coordinates, cones. -/

noncomputable def ofDrawing {V : Type} {G H : SimpleGraph V} (D : PlaneDrawing G) (hle : H ≤ G) :
    ImgDr H := by
  classical
  refine ⟨D.vertex, D.vertex_injective,
    fun v w => if h : G.Adj v w then Set.range (D.arc h) else ∅, ?_, ?_, ?_, ?_⟩
  · intro v w
    by_cases h : G.Adj v w
    · rw [dif_pos h, dif_pos h.symm, D.arc_reverse h, Path.symm_range]
    · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
  · intro v w h
    rw [dif_pos (hle h)]
    exact ⟨D.arc _, D.arc_injective _, rfl⟩
  · intro v w h x hx
    rw [dif_pos (hle h)] at hx
    obtain ⟨t, ht⟩ := hx
    exact D.arc_avoids_vertices _ t x ht
  · intro v w x y h k hne z hz1 hz2
    rw [dif_pos (hle h)] at hz1
    rw [dif_pos (hle k)] at hz2
    obtain ⟨s, rfl⟩ := hz1
    obtain ⟨t, e⟩ := hz2
    rcases D.arcs_meet_only_at_endpoints (hle h) (hle k) s t e.symm with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact absurd (by rw [h1, h2]) hne
    · exact absurd (by rw [h1, h2, Sym2.eq_swap]) hne
    · rcases h1 with h1 | h1
      · left; rw [h1, Path.source]
      · right; rw [h1, Path.target]

lemma ofDrawing_P {V : Type} {G H : SimpleGraph V} (D : PlaneDrawing G) (hle : H ≤ G) :
    (ofDrawing D hle).P = D.vertex := rfl

lemma ofDrawing_S {V : Type} {G H : SimpleGraph V} (D : PlaneDrawing G) (hle : H ≤ G) (v w : V)
    (h : G.Adj v w) : (ofDrawing D hle).S v w = Set.range (D.arc h) := by
  classical
  show (if h : G.Adj v w then Set.range (D.arc h) else ∅) = _
  rw [dif_pos h]

def ImgDr.map {V : Type} {H : SimpleGraph V} (D : ImgDr H) (Φ : ℝ × ℝ → ℝ × ℝ)
    (hc : Continuous Φ) (hi : Function.Injective Φ) : ImgDr H where
  P := Φ ∘ D.P
  inj := hi.comp D.inj
  S := fun v w => Φ '' D.S v w
  symm := fun v w => by rw [D.symm]
  arc := fun v w h => (D.arc v w h).map Φ hc hi
  avoid := fun v w h x hx => by
    obtain ⟨y, hy, e⟩ := hx
    have e' : y = D.P x := hi e
    exact D.avoid v w h x (e' ▸ hy)
  meet := fun v w x y h k hne z hz1 hz2 => by
    obtain ⟨y1, hy1, rfl⟩ := hz1
    obtain ⟨y2, hy2, e⟩ := hz2
    have e' : y2 = y1 := hi e
    rw [e'] at hy2
    rcases D.meet v w x y h k hne y1 hy1 hy2 with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]; rfl

lemma Obs_map {V : Type} {H : SimpleGraph V} (D : ImgDr H) (Φ : ℝ × ℝ → ℝ × ℝ)
    (hc : Continuous Φ) (hi : Function.Injective Φ) (u : V) :
    Obs (D.map Φ hc hi) u = Φ '' Obs D u := by
  ext z
  constructor
  · rintro (⟨v, w, h, y, hy, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨y, Or.inl ⟨v, w, h, hy⟩, rfl⟩
    · exact ⟨D.P v, Or.inr ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨y, (⟨v, w, h, hy⟩ | ⟨v, hv, rfl⟩), rfl⟩
    · exact Or.inl ⟨v, w, h, y, hy, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩

/-- a linear map of the plane, by its matrix entries -/
def mapM (m : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (m.1 * z.1 + m.2.1 * z.2, m.2.2.1 * z.1 + m.2.2.2 * z.2)

def detM (m : ℝ × ℝ × ℝ × ℝ) : ℝ := m.1 * m.2.2.2 - m.2.1 * m.2.2.1

lemma mapM_sub (m : ℝ × ℝ × ℝ × ℝ) (x y : ℝ × ℝ) : mapM m (x - y) = mapM m x - mapM m y := by
  ext <;> simp [mapM] <;> ring

lemma mapM_add (m : ℝ × ℝ × ℝ × ℝ) (x y : ℝ × ℝ) : mapM m (x + y) = mapM m x + mapM m y := by
  ext <;> simp [mapM] <;> ring

lemma mapM_smul (m : ℝ × ℝ × ℝ × ℝ) (t : ℝ) (x : ℝ × ℝ) : mapM m (t • x) = t • mapM m x := by
  ext <;> simp [mapM] <;> ring

lemma mapM_zero (m : ℝ × ℝ × ℝ × ℝ) : mapM m 0 = 0 := by
  ext <;> simp [mapM]

lemma mapM_cont (m : ℝ × ℝ × ℝ × ℝ) : Continuous (mapM m) := by
  unfold mapM; fun_prop

lemma mapM_inj (m : ℝ × ℝ × ℝ × ℝ) (h : detM m ≠ 0) : Function.Injective (mapM m) := by
  intro x y e
  simp only [mapM, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  have k1 : detM m * (x.1 - y.1) = 0 := by
    unfold detM; linear_combination m.2.2.2 * e1 - m.2.1 * e2
  have k2 : detM m * (x.2 - y.2) = 0 := by
    unfold detM; linear_combination -m.2.2.1 * e1 + m.1 * e2
  rcases mul_eq_zero.mp k1 with h1 | h1
  · exact absurd h1 h
  rcases mul_eq_zero.mp k2 with h2 | h2
  · exact absurd h2 h
  ext <;> linarith

lemma mapM_lower (m : ℝ × ℝ × ℝ × ℝ) (h : detM m ≠ 0) :
    ∃ c > 0, ∀ z, c * ‖z‖ ≤ ‖mapM m z‖ := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |m.1| + |m.2.1| + |m.2.2.1| + |m.2.2.2| + 1 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hdet : 0 < |detM m| := abs_pos.mpr h
  refine ⟨|detM m| / K, by positivity, fun z => ?_⟩
  set x := mapM m z with hx
  have hx1 : |x.1| ≤ ‖x‖ := by
    have := norm_fst_le x; rwa [Real.norm_eq_abs] at this
  have hx2 : |x.2| ≤ ‖x‖ := by
    have := norm_snd_le x; rwa [Real.norm_eq_abs] at this
  have i1 : detM m * z.1 = m.2.2.2 * x.1 - m.2.1 * x.2 := by
    rw [hx]; simp only [mapM, detM]; ring
  have i2 : detM m * z.2 = -m.2.2.1 * x.1 + m.1 * x.2 := by
    rw [hx]; simp only [mapM, detM]; ring
  have bound : ∀ (p q : ℝ), |p * x.1 + q * x.2| ≤ (|p| + |q|) * ‖x‖ := by
    intro p q
    have a1 : |p * x.1| ≤ |p| * ‖x‖ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg p)
    have a2 : |q * x.2| ≤ |q| * ‖x‖ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx2 (abs_nonneg q)
    calc |p * x.1 + q * x.2| ≤ |p * x.1| + |q * x.2| := abs_add_le _ _
      _ ≤ |p| * ‖x‖ + |q| * ‖x‖ := add_le_add a1 a2
      _ = (|p| + |q|) * ‖x‖ := by ring
  have hxn : 0 ≤ ‖x‖ := norm_nonneg x
  have b1 : |detM m| * |z.1| ≤ K * ‖x‖ := by
    rw [← abs_mul, i1, sub_eq_add_neg, ← neg_mul]
    refine (bound _ _).trans ?_
    rw [abs_neg]
    apply mul_le_mul_of_nonneg_right _ hxn
    rw [hK]; linarith [abs_nonneg m.1, abs_nonneg m.2.2.1]
  have b2 : |detM m| * |z.2| ≤ K * ‖x‖ := by
    rw [← abs_mul, i2]
    refine (bound _ _).trans ?_
    rw [abs_neg]
    apply mul_le_mul_of_nonneg_right _ hxn
    rw [hK]; linarith [abs_nonneg m.2.1, abs_nonneg m.2.2.2]
  have hzn : ‖z‖ = max |z.1| |z.2| := by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [div_mul_eq_mul_div, div_le_iff₀ hKpos, hzn, mul_comm (‖x‖) K]
  rcases le_total |z.1| |z.2| with hz | hz
  · rw [max_eq_right hz]; exact b2
  · rw [max_eq_left hz]; exact b1


/-! Aligning both end rays with grid axes, and the free cones. -/

lemma exists_M0 (v w : ℝ × ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ m0 : ℝ × ℝ × ℝ × ℝ, detM m0 ≠ 0 ∧ mapM m0 v = (1, 0) ∧
      ((∃ κ : ℝ, 0 < κ ∧ mapM m0 w = (0, κ)) ∨ (∃ κ : ℝ, κ ≠ 0 ∧ mapM m0 w = (κ, 0))) := by
  by_cases hcr : v.1 * w.2 - v.2 * w.1 = 0
  · obtain ⟨nv, hnv⟩ : ∃ nv : ℝ, nv = v.1 ^ 2 + v.2 ^ 2 := ⟨_, rfl⟩
    have hnv0 : 0 < nv := by
      rw [hnv]
      by_contra hle
      have hle' : v.1 ^ 2 + v.2 ^ 2 ≤ 0 := not_lt.mp hle
      have q1 := sq_nonneg v.1
      have q2 := sq_nonneg v.2
      have h1 : v.1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith only [hle', q1, q2])
      have h2 : v.2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith only [hle', q1, q2])
      exact hv (Prod.ext h1 h2)
    refine ⟨(v.1 / nv, v.2 / nv, -v.2 / nv, v.1 / nv), ?_, ?_,
      Or.inr ⟨(v.1 * w.1 + v.2 * w.2) / nv, ?_, ?_⟩⟩
    · unfold detM
      dsimp only
      have : v.1 / nv * (v.1 / nv) - v.2 / nv * (-v.2 / nv) = (v.1 ^ 2 + v.2 ^ 2) / nv ^ 2 := by
        ring
      rw [this, ← hnv]
      positivity
    · ext
      · show v.1 / nv * v.1 + v.2 / nv * v.2 = 1
        have : v.1 / nv * v.1 + v.2 / nv * v.2 = (v.1 ^ 2 + v.2 ^ 2) / nv := by ring
        rw [this, ← hnv, div_self hnv0.ne']
      · show -v.2 / nv * v.1 + v.1 / nv * v.2 = 0
        ring
    · intro hκ
      rcases div_eq_zero_iff.mp hκ with hnum | hnum
      · have e1 : nv * w.1 = 0 := by rw [hnv]; linear_combination v.1 * hnum - v.2 * hcr
        have e2 : nv * w.2 = 0 := by rw [hnv]; linear_combination v.2 * hnum + v.1 * hcr
        rcases mul_eq_zero.mp e1 with h | h
        · linarith
        rcases mul_eq_zero.mp e2 with h' | h'
        · linarith
        exact hw (Prod.ext h h')
      · linarith
    · ext
      · show v.1 / nv * w.1 + v.2 / nv * w.2 = (v.1 * w.1 + v.2 * w.2) / nv
        ring
      · show -v.2 / nv * w.1 + v.1 / nv * w.2 = 0
        have : -v.2 / nv * w.1 + v.1 / nv * w.2 = (v.1 * w.2 - v.2 * w.1) / nv := by ring
        rw [this, hcr, zero_div]
  · obtain ⟨cr, hcrd⟩ : ∃ cr : ℝ, cr = v.1 * w.2 - v.2 * w.1 := ⟨_, rfl⟩
    rw [← hcrd] at hcr
    refine ⟨(w.2 / cr, -w.1 / cr, -v.2 / cr, v.1 / cr), ?_, ?_, Or.inl ⟨1, one_pos, ?_⟩⟩
    · unfold detM
      dsimp only
      have : w.2 / cr * (v.1 / cr) - -w.1 / cr * (-v.2 / cr) = (v.1 * w.2 - v.2 * w.1) / cr ^ 2 := by
        ring
      rw [this, ← hcrd]
      exact div_ne_zero hcr (pow_ne_zero 2 hcr)
    · ext
      · show w.2 / cr * v.1 + -w.1 / cr * v.2 = 1
        have : w.2 / cr * v.1 + -w.1 / cr * v.2 = (v.1 * w.2 - v.2 * w.1) / cr := by ring
        rw [this, ← hcrd, div_self hcr]
      · show -v.2 / cr * v.1 + v.1 / cr * v.2 = 0
        ring
    · ext
      · show w.2 / cr * w.1 + -w.1 / cr * w.2 = 0
        ring
      · show -v.2 / cr * w.1 + v.1 / cr * w.2 = 1
        have : -v.2 / cr * w.1 + v.1 / cr * w.2 = (v.1 * w.2 - v.2 * w.1) / cr := by ring
        rw [this, ← hcrd, div_self hcr]

lemma exists_M (v w e : ℝ × ℝ) (hv : v ≠ 0) (hw : w ≠ 0) (he : e ≠ 0) :
    ∃ m : ℝ × ℝ × ℝ × ℝ, detM m ≠ 0 ∧ (∃ s1 : ℝ, 0 < s1 ∧ mapM m v = (s1, 0)) ∧
      (∃ dW : ℤ × ℤ, IsDir dW ∧ ∃ s2 : ℝ, 0 < s2 ∧ mapM m w = s2 • kR dW) ∧
      ∃ kW : ℤ × ℤ, kW ≠ 0 ∧ mapM m e = kR kW := by
  obtain ⟨m0, hdet, hv0, hw0⟩ := exists_M0 v w hv hw
  obtain ⟨α, hα⟩ : ∃ α, α = (mapM m0 e).1 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = (mapM m0 e).2 := ⟨_, rfl⟩
  have hαβ : ¬ (α = 0 ∧ β = 0) := by
    rintro ⟨h1, h2⟩
    apply he
    apply mapM_inj m0 hdet
    rw [mapM_zero]
    ext
    · rw [← hα, h1]; rfl
    · rw [← hβ, h2]; rfl
  have sc : ∀ x : ℝ, ∃ s : ℝ, 0 < s ∧ ∃ k : ℤ, (k : ℝ) = s * x ∧ (k = 0 → x = 0) := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · refine ⟨-1 / x, div_pos_of_neg_of_neg (by norm_num) hx, -1, ?_, fun h => by norm_num at h⟩
      push_cast; rw [div_mul_cancel₀ _ hx.ne]
    · exact ⟨1, one_pos, 0, by simp [hx], fun _ => hx⟩
    · refine ⟨1 / x, by positivity, 1, ?_, fun h => by norm_num at h⟩
      push_cast; rw [div_mul_cancel₀ _ hx.ne']
  obtain ⟨s1, hs1, k1, hk1, hk10⟩ := sc α
  obtain ⟨s2, hs2, k2, hk2, hk20⟩ := sc β
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ × ℝ × ℝ × ℝ,
      m = (s1 * m0.1, s1 * m0.2.1, s2 * m0.2.2.1, s2 * m0.2.2.2) := ⟨_, rfl⟩
  have hm : ∀ z, mapM m z = (s1 * (mapM m0 z).1, s2 * (mapM m0 z).2) := by
    intro z; rw [hmdef]; simp only [mapM]; ext <;> ring
  refine ⟨m, ?_, ⟨s1, hs1, ?_⟩, ?_, ⟨(k1, k2), ?_, ?_⟩⟩
  · have : detM m = s1 * s2 * detM m0 := by rw [hmdef]; simp only [detM]; ring
    rw [this]; exact mul_ne_zero (mul_ne_zero hs1.ne' hs2.ne') hdet
  · rw [hm, hv0]; ext <;> simp
  · rcases hw0 with ⟨κ, hκ, hκw⟩ | ⟨κ, hκ, hκw⟩
    · refine ⟨(0, 1), Or.inr (Or.inr (Or.inl rfl)), s2 * κ, by positivity, ?_⟩
      rw [hm, hκw]; ext <;> simp [kR]
    · rcases lt_or_gt_of_ne hκ with hneg | hpos
      · refine ⟨(-1, 0), Or.inr (Or.inl rfl), -(s1 * κ), neg_pos.mpr (mul_neg_of_pos_of_neg hs1 hneg), ?_⟩
        rw [hm, hκw]; ext <;> simp [kR]
      · refine ⟨(1, 0), Or.inl rfl, s1 * κ, by positivity, ?_⟩
        rw [hm, hκw]; ext <;> simp [kR]
  · intro h0
    have e1 : k1 = 0 := congrArg Prod.fst h0
    have e2 : k2 = 0 := congrArg Prod.snd h0
    exact hαβ ⟨hk10 e1, hk20 e2⟩
  · rw [hm]; ext
    · simp only [kR]; rw [hk1, hα]
    · simp only [kR]; rw [hk2, hβ]

/-- coordinates of a vector in the frame of a grid direction -/
def va (d : ℤ × ℤ) (x : ℝ × ℝ) : ℝ := x.1 * d.1 + x.2 * d.2

def vb (d : ℤ × ℤ) (x : ℝ × ℝ) : ℝ := -x.1 * d.2 + x.2 * d.1

lemma Lc_sub_kR (k d : ℤ × ℤ) (α β : ℝ) :
    Lc 1 k d (α, β) - kR k = (α * d.1 - β * d.2, α * d.2 + β * d.1) := by
  ext <;> simp [Lc, kR] <;> ring

lemma va_vb_rot (d : ℤ × ℤ) (hd : IsDir d) (α β : ℝ) :
    va d (α * d.1 - β * d.2, α * d.2 + β * d.1) = α ∧
      vb d (α * d.1 - β * d.2, α * d.2 + β * d.1) = β := by
  obtain ⟨s1, -⟩ := dir_sq hd
  simp only [va, vb]
  constructor
  · linear_combination α * s1
  · linear_combination β * s1

lemma vec_frame (d : ℤ × ℤ) (hd : IsDir d) (x : ℝ × ℝ) :
    x = (va d x * d.1 - vb d x * d.2, va d x * d.2 + vb d x * d.1) := by
  obtain ⟨s1, -⟩ := dir_sq hd
  simp only [va, vb]
  ext
  · simp only; linear_combination -x.1 * s1
  · simp only; linear_combination -x.2 * s1

lemma norm_rot (d : ℤ × ℤ) (hd : IsDir d) (α β : ℝ) :
    ‖((α * d.1 - β * d.2, α * d.2 + β * d.1) : ℝ × ℝ)‖ = max |α| |β| := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [abs_neg, max_comm]

lemma cone_gen (m : ℝ × ℝ × ℝ × ℝ) (c : ℝ) (hc : 0 < c) (hlow : ∀ z, c * ‖z‖ ≤ ‖mapM m z‖)
    (A V : ℝ × ℝ) (k d : ℤ × ℤ) (hd : IsDir d) (hV : mapM m (V - A) = kR k)
    (O : Set (ℝ × ℝ)) (r : ℝ) (hr : 0 < r) {I : Type} [Finite I] (P : I → ℝ × ℝ)
    (hnear : ∀ y ∈ O, dist y V < r → y = V ∨ ∃ i, y ∈ seg V (P i))
    (hpar : ∀ i, ¬ (0 < va d (mapM m (P i - V)) ∧ vb d (mapM m (P i - V)) = 0))
    (ρmax : ℝ) (hρmax : 0 < ρmax) :
    ∃ ρ > 0, ρ ≤ ρmax ∧ ∃ μ > 0, μ ≤ 1 ∧ ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α →
      Lc 1 k d (α, β) ∉ (fun z => mapM m (z - A)) '' O := by
  classical
  obtain ⟨e1, he1⟩ : ∃ e1 : I → ℝ, e1 = fun i => va d (mapM m (P i - V)) := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : I → ℝ, e2 = fun i => vb d (mapM m (P i - V)) := ⟨_, rfl⟩
  have hpar' : ∀ i, 0 < e1 i → e2 i ≠ 0 := by
    intro i h1 h2; rw [he1] at h1; rw [he2] at h2; exact hpar i ⟨h1, h2⟩
  obtain ⟨f, hfdef⟩ : ∃ f : I → ℝ, f = fun i => if 0 < e1 i then |e2 i| / e1 i else 1 :=
    ⟨_, rfl⟩
  have hf : ∀ i, 0 < f i := by
    intro i; rw [hfdef]; dsimp only
    split_ifs with h
    · have := hpar' i h
      positivity
    · exact one_pos
  obtain ⟨μ0, hμ0, hμle⟩ := fin_min f hf
  have hρ0 : 0 < min (c * r) ρmax := lt_min (by positivity) hρmax
  have hμm : 0 < min μ0 1 := lt_min hμ0 one_pos
  refine ⟨min (c * r) ρmax / 2, by positivity, by linarith [min_le_right (c * r) ρmax],
    min μ0 1 / 2, by positivity, by linarith [min_le_right μ0 1], ?_⟩
  rintro α β hα hαρ hβ ⟨y, hy, hΦ⟩
  simp only at hΦ
  have hμ1 : min μ0 1 / 2 ≤ 1 := by linarith [min_le_right μ0 1]
  have hβα : |β| ≤ α := le_trans hβ (by
    have := mul_le_mul_of_nonneg_right hμ1 hα.le
    linarith only [this])
  have hyV : mapM m (y - V) = (α * d.1 - β * d.2, α * d.2 + β * d.1) := by
    have : y - V = (y - A) - (V - A) := by abel
    rw [this, mapM_sub, hΦ, hV, Lc_sub_kR]
  have hnorm : ‖mapM m (y - V)‖ ≤ α := by
    rw [hyV, norm_rot d hd]; exact max_le (by rw [abs_of_pos hα]) hβα
  have hyVr : dist y V < r := by
    rw [dist_eq_norm]
    have h1 := hlow (y - V)
    have h2 : α ≤ c * r / 2 := by linarith [min_le_left (c * r) ρmax]
    by_contra hcon
    have h3 : r ≤ ‖y - V‖ := not_lt.mp hcon
    have h4 : c * r ≤ c * ‖y - V‖ := mul_le_mul_of_nonneg_left h3 hc.le
    linarith
  obtain ⟨r1, r2⟩ := va_vb_rot d hd α β
  rcases hnear y hy hyVr with hyv | ⟨i, hi⟩
  · rw [hyv, sub_self, mapM_zero] at hyV
    rw [← hyV] at r1; simp [va] at r1; linarith
  · obtain ⟨t, ht, rfl⟩ := hi
    rw [add_sub_cancel_left, mapM_smul] at hyV
    have hva : va d (t • mapM m (P i - V)) = t * e1 i := by
      rw [he1]; simp only [va, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hvb : vb d (t • mapM m (P i - V)) = t * e2 i := by
      rw [he2]; simp only [vb, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [← hyV, hva] at r1
    rw [← hyV, hvb] at r2
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le ht.1 with e | e
      · rw [← e] at r1; linarith
      · exact e
    have hpos : 0 < e1 i := by
      by_contra hneg
      have : t * e1 i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0.le (not_lt.mp hneg)
      linarith
    have hfi : f i = |e2 i| / e1 i := by rw [hfdef]; dsimp only; rw [if_pos hpos]
    have hμf : μ0 ≤ |e2 i| / e1 i := hfi ▸ hμle i
    have hb : |β| = t * |e2 i| := by rw [← r2, abs_mul, abs_of_pos ht0]
    have key : t * |e2 i| ≤ min μ0 1 / 2 * (t * e1 i) := by rw [← hb, r1]; exact hβ
    have k2 : |e2 i| ≤ min μ0 1 / 2 * e1 i := by
      have : t * |e2 i| ≤ t * (min μ0 1 / 2 * e1 i) := by linarith
      exact le_of_mul_le_mul_left this ht0
    have k3 : min μ0 1 / 2 * e1 i ≤ |e2 i| / 2 := by
      have : min μ0 1 ≤ |e2 i| / e1 i := (min_le_left _ _).trans hμf
      have := mul_le_mul_of_nonneg_right this hpos.le
      rw [div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    have : |e2 i| = 0 := by linarith [abs_nonneg (e2 i)]
    exact hpar' i hpos (abs_eq_zero.mp this)


/-! Straightening at both ends of the edge `ab` (which is removed from the drawing). -/

lemma range_segPath (P Q : ℝ × ℝ) : Set.range (segPath P Q) = seg P Q := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩

lemma dist_seg_far {A B P y : ℝ × ℝ} (hy : y ∈ seg A P) :
    dist B A - dist P A ≤ dist y B := by
  have h1 := seg_dist_le hy
  have h2 := dist_triangle B y A
  rw [dist_comm B y] at h2
  linarith

set_option maxHeartbeats 4000000 in
theorem attach_straight {n : ℕ} (G : SimpleGraph (Fin n)) (D : PlaneDrawing G) (a b u : Fin n)
    (hab : G.Adj a b) (H0 : SimpleGraph (Fin n))
    (hH0 : ∀ p q, H0.Adj p q ↔ G.Adj p q ∧ ¬ s(p, q) = s(a, b)) :
    ∃ D2 : ImgDr H0, ∃ ra rb : ℝ, ∃ pa qb : Fin n → ℝ × ℝ,
      D2.P = D.vertex ∧ 0 < ra ∧ 0 < rb ∧ ra + rb < dist (D.vertex b) (D.vertex a) ∧
      (∀ c, H0.Adj a c → dist (pa c) (D.vertex a) = ra ∧
        (pa c ∈ Set.range (D.arc hab) → pa c = D.vertex a ∨ pa c = D.vertex b)) ∧
      (∀ d, H0.Adj b d → dist (qb d) (D.vertex b) = rb ∧
        (qb d ∈ Set.range (D.arc hab) → qb d = D.vertex a ∨ qb d = D.vertex b)) ∧
      (∀ y ∈ Obs D2 u, dist y (D.vertex a) < ra →
        y = D.vertex a ∨ ∃ c : {c // H0.Adj a c}, y ∈ seg (D.vertex a) (pa c)) ∧
      (∀ y ∈ Obs D2 u, dist y (D.vertex b) < rb →
        y = D.vertex b ∨ ∃ d : {d // H0.Adj b d}, y ∈ seg (D.vertex b) (qb d)) ∧
      (∀ y ∈ Set.range (D.arc hab), y ≠ D.vertex a → y ≠ D.vertex b →
        ra ≤ dist y (D.vertex a) → rb ≤ dist y (D.vertex b) → y ∉ Obs D2 u) := by
  classical
  have hle : H0 ≤ G := fun p q h => ((hH0 p q).mp h).1
  have hab' : a ≠ b := G.ne_of_adj hab
  have hab0 : ¬ H0.Adj a b := fun h => ((hH0 a b).mp h).2 rfl
  obtain ⟨D0, hD0⟩ : ∃ D0 : ImgDr H0, D0 = ofDrawing D hle := ⟨_, rfl⟩
  have hD0P : D0.P = D.vertex := by rw [hD0]; rfl
  have hD0S : ∀ v w (h : G.Adj v w), D0.S v w = Set.range (D.arc h) := by
    intro v w h; rw [hD0]; exact ofDrawing_S D hle v w h
  obtain ⟨A, hA⟩ : ∃ A, A = D.vertex a := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = D.vertex b := ⟨_, rfl⟩
  -- an old arc meets the arc of `ab` only at `A` or `B`
  have G0 : ∀ v w, H0.Adj v w → ∀ y ∈ D0.S v w, y ∈ Set.range (D.arc hab) → y = A ∨ y = B := by
    intro v w h y hy hyg
    rw [hD0S v w (hle h)] at hy
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨t, ht⟩ := hyg
    have hne := ((hH0 v w).mp h).2
    rcases D.arcs_meet_only_at_endpoints (hle h) hab s t ht.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨-, h2⟩
    · exact absurd (by rw [h1, h2]) hne
    · exact absurd (by rw [h1, h2, Sym2.eq_swap]) hne
    · rw [← ht]
      rcases h2 with h2 | h2
      · left; rw [h2, Path.source, hA]
      · right; rw [h2, Path.target, hB]
  -- straighten at a, then at b
  obtain ⟨ra, hra, -, D1, hD1P, hD1v, hD1o, hD1a⟩ := straighten D0 a 1 one_pos
  rw [hD0P, ← hA] at hD1v hD1o hD1a
  rw [hD0P] at hD1P
  have hdAB : ra < dist B A := by rw [hB]; exact hD1v b hab'.symm
  obtain ⟨rb, hrb, hrbm, D2, hD2P, hD2v, hD2o, hD2b⟩ :=
    straighten D1 b ((dist B A - ra) / 2) (by linarith)
  rw [hD1P, ← hB] at hD2v hD2o hD2b
  rw [hD1P] at hD2P
  choose! pa Oa hpa using hD1a
  choose! qb Ob hqb using hD2b
  have hbna : ∀ d, H0.Adj b d → d ≠ a := fun d h e => hab0 (e ▸ h.symm)
  have hanb : ∀ c, H0.Adj a c → c ≠ b := fun c h e => hab0 (e ▸ h)
  -- the images of the twice straightened drawing
  have CL : ∀ v w, H0.Adj v w → ∀ y ∈ D2.S v w,
      (∃ c, H0.Adj a c ∧ y ∈ seg A (pa c)) ∨ (∃ d, H0.Adj b d ∧ y ∈ seg B (qb d)) ∨
      ((∃ v' w', H0.Adj v' w' ∧ y ∈ D0.S v' w') ∧ ra ≤ dist y A ∧ rb ≤ dist y B) := by
    -- edges at `a`
    have hA' : ∀ c, H0.Adj a c → ∀ y ∈ D2.S a c, (∃ c, H0.Adj a c ∧ y ∈ seg A (pa c)) ∨
        (∃ d, H0.Adj b d ∧ y ∈ seg B (qb d)) ∨
        ((∃ v' w', H0.Adj v' w' ∧ y ∈ D0.S v' w') ∧ ra ≤ dist y A ∧ rb ≤ dist y B) := by
      intro c hc y hy
      obtain ⟨e2, f2⟩ := hD2o a c hc hab' (hanb c hc)
      rw [e2, (hpa c hc).2.2.1] at hy
      rcases hy with hy | hy
      · left; exact ⟨c, hc, hy⟩
      · right; right
        refine ⟨⟨a, c, hc, (hpa c hc).2.2.2.1 hy⟩, ((hpa c hc).2.2.2.2 y hy).1, ?_⟩
        have : y ∈ D1.S a c := by rw [(hpa c hc).2.2.1]; exact Or.inr hy
        exact (f2 y this).le
    have hB' : ∀ d, H0.Adj b d → ∀ y ∈ D2.S b d, (∃ c, H0.Adj a c ∧ y ∈ seg A (pa c)) ∨
        (∃ d, H0.Adj b d ∧ y ∈ seg B (qb d)) ∨
        ((∃ v' w', H0.Adj v' w' ∧ y ∈ D0.S v' w') ∧ ra ≤ dist y A ∧ rb ≤ dist y B) := by
      intro d hd y hy
      rw [(hqb d hd).2.2.1] at hy
      rcases hy with hy | hy
      · right; left; exact ⟨d, hd, hy⟩
      · right; right
        have hy1 : y ∈ D1.S b d := (hqb d hd).2.2.2.1 hy
        obtain ⟨e1, f1⟩ := hD1o b d hd hab'.symm (hbna d hd)
        rw [e1] at hy1
        exact ⟨⟨b, d, hd, hy1⟩, (f1 y hy1).le, ((hqb d hd).2.2.2.2 y hy).1⟩
    intro v w h y hy
    by_cases hva : v = a
    · subst hva; exact hA' w h y hy
    by_cases hwa : w = a
    · subst hwa; rw [D2.symm] at hy; exact hA' v h.symm y hy
    by_cases hvb : v = b
    · subst hvb; exact hB' w h y hy
    by_cases hwb : w = b
    · subst hwb; rw [D2.symm] at hy; exact hB' v h.symm y hy
    right; right
    obtain ⟨e2, f2⟩ := hD2o v w h hvb hwb
    obtain ⟨e1, f1⟩ := hD1o v w h hva hwa
    rw [e2] at hy
    rw [e1] at hy f2
    exact ⟨⟨v, w, h, hy⟩, (f1 y hy).le, (f2 y hy).le⟩
  have hfarA : ∀ y, (∃ d, H0.Adj b d ∧ y ∈ seg B (qb d)) → ra < dist y A := by
    rintro y ⟨d, hd, hy⟩
    have := dist_seg_far (B := A) hy
    rw [(hqb d hd).1, dist_comm A B] at this
    linarith
  have hfarB : ∀ y, (∃ c, H0.Adj a c ∧ y ∈ seg A (pa c)) → rb < dist y B := by
    rintro y ⟨c, hc, hy⟩
    have := dist_seg_far (B := B) hy
    rw [(hpa c hc).1] at this
    linarith
  refine ⟨D2, ra, rb, pa, qb, hD2P, hra, hrb, by rw [← hA, ← hB]; linarith, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    refine ⟨by rw [← hA]; exact (hpa c hc).1, fun hm => ?_⟩
    rw [← hA, ← hB]
    exact G0 a c hc _ (hpa c hc).2.1 hm
  · intro d hd
    refine ⟨by rw [← hB]; exact (hqb d hd).1, fun hm => ?_⟩
    rw [← hA, ← hB]
    have hm1 := (hqb d hd).2.1
    rw [(hD1o b d hd hab'.symm (hbna d hd)).1] at hm1
    exact G0 b d hd _ hm1 hm
  · rw [← hA]
    rintro y (⟨v, w, h, hy⟩ | ⟨v, hv, rfl⟩) hyA
    · rcases CL v w h y hy with ⟨c, hc, hy'⟩ | hy' | ⟨-, hy', -⟩
      · right; exact ⟨⟨c, hc⟩, hy'⟩
      · exact absurd hyA (not_lt.mpr (hfarA y hy').le)
      · exact absurd hyA (not_lt.mpr hy')
    · rw [hD2P]
      by_cases hva : v = a
      · left; rw [hva, hA]
      · exfalso; have := hD1v v hva; rw [hD2P] at hyA; linarith
  · rw [← hB]
    rintro y (⟨v, w, h, hy⟩ | ⟨v, hv, rfl⟩) hyB
    · rcases CL v w h y hy with hy' | ⟨d, hd, hy'⟩ | ⟨-, -, hy'⟩
      · exact absurd hyB (not_lt.mpr (hfarB y hy').le)
      · right; exact ⟨⟨d, hd⟩, hy'⟩
      · exact absurd hyB (not_lt.mpr hy')
    · rw [hD2P]
      by_cases hvb : v = b
      · left; rw [hvb, hB]
      · exfalso; have := hD2v v hvb; rw [hD2P] at hyB; linarith
  · intro y hyg
    rw [← hA, ← hB]
    intro hyA hyB hdA hdB hy
    rcases hy with ⟨v, w, h, hy⟩ | ⟨v, hv, rfl⟩
    · rcases CL v w h y hy with ⟨c, hc, hy'⟩ | ⟨d, hd, hy'⟩ | ⟨⟨v', w', h', hy'⟩, -, -⟩
      · have hle' := seg_dist_le hy'
        rw [(hpa c hc).1] at hle'
        have e := seg_dist_eq (by intro e; have := (hpa c hc).1; rw [e, dist_self] at this; linarith)
          hy' (by rw [(hpa c hc).1]; linarith)
        rcases G0 a c hc _ (e ▸ (hpa c hc).2.1) hyg with h1 | h1
        · exact hyA h1
        · exact hyB h1
      · have hle' := seg_dist_le hy'
        rw [(hqb d hd).1] at hle'
        have e := seg_dist_eq (by intro e; have := (hqb d hd).1; rw [e, dist_self] at this; linarith)
          hy' (by rw [(hqb d hd).1]; linarith)
        have hm1 := (hqb d hd).2.1
        rw [(hD1o b d hd hab'.symm (hbna d hd)).1] at hm1
        rcases G0 b d hd _ (e ▸ hm1) hyg with h1 | h1
        · exact hyA h1
        · exact hyB h1
      · rcases G0 v' w' h' y hy' hyg with h1 | h1
        · exact hyA h1
        · exact hyB h1
    · rw [hD2P] at hyg hyA hyB
      obtain ⟨t, ht⟩ := hyg
      rcases D.arc_avoids_vertices hab t v ht with rfl | rfl
      · exact hyA hA.symm
      · exact hyB hB.symm


/-! The main construction. -/

lemma norm_kR_dir (d : ℤ × ℤ) (hd : IsDir d) : ‖kR d‖ = 1 := by
  unfold IsDir at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [kR, Prod.norm_def]

set_option maxHeartbeats 8000000 in
theorem attach_main {n : ℕ} (G : SimpleGraph (Fin n)) (D : PlaneDrawing G) (a b u : Fin n)
    (hab : G.Adj a b) (hu : ∀ q, ¬ G.Adj u q) (G' : SimpleGraph (Fin n))
    (hG' : ∀ p q, G'.Adj p q ↔
      (G.Adj p q ∨ (p = u ∧ (q = a ∨ q = b)) ∨ (q = u ∧ (p = a ∨ p = b)))) :
    IsPlanar G' := by
  classical
  obtain ⟨H0, hH0def⟩ : ∃ H0 : SimpleGraph (Fin n), H0 = G.deleteEdges {s(a, b)} := ⟨_, rfl⟩
  have hH0 : ∀ p q, H0.Adj p q ↔ G.Adj p q ∧ ¬ s(p, q) = s(a, b) := by
    intro p q; rw [hH0def, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  have hle : H0 ≤ G := fun p q h => ((hH0 p q).mp h).1
  have hab' : a ≠ b := G.ne_of_adj hab
  have hua : u ≠ a := fun e => hu b (e ▸ hab)
  have hub : u ≠ b := fun e => hu a (e ▸ hab.symm)
  have hu0 : ∀ q, ¬ H0.Adj u q := fun q h => hu q (hle h)
  have hab0 : ¬ H0.Adj a b := fun h => ((hH0 a b).mp h).2 rfl
  have hG'' : ∀ p q, G'.Adj p q ↔
      (H0.Adj p q ∨ s(p, q) = s(a, b) ∨ s(p, q) = s(u, a) ∨ s(p, q) = s(u, b)) := by
    intro p q
    rw [hG' p q, hH0]
    constructor
    · rintro (h | ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
      · by_cases e : s(p, q) = s(a, b)
        · right; left; exact e
        · left; exact ⟨h, e⟩
      · right; right; left; rw [h1, h2]
      · right; right; right; rw [h1, h2]
      · right; right; left; rw [h1, h2, Sym2.eq_swap]
      · right; right; right; rw [h1, h2, Sym2.eq_swap]
    · rintro (⟨h, -⟩ | e | e | e)
      · left; exact h
      · left
        rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hab
        · rw [h1, h2]; exact hab.symm
      · right
        rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, Or.inl h2⟩
        · right; exact ⟨h2, Or.inl h1⟩
      · right
        rcases Sym2.eq_iff.mp e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, Or.inr h2⟩
        · right; exact ⟨h2, Or.inr h1⟩
  obtain ⟨D2, ra, rb, pa, qb, hD2P, hra, hrb, hrab, hpa, hqb, NA, NB, GM⟩ :=
    attach_straight G D a b u hab H0 hH0
  set A := D.vertex a with hA
  set B := D.vertex b with hB
  -- leaving the ball at `A`
  obtain ⟨τ, hτ1, hτ2⟩ := exit_time (D.arc hab) hra (by linarith only [hrab, hrb] : ra < dist B A)
  set p := D.arc hab τ with hpdef
  have hpA : p ≠ A := by intro e; rw [e, dist_self] at hτ1; linarith only [hτ1, hra]
  have hpB : rb < dist p B := by
    have := dist_triangle B p A
    rw [dist_comm B p] at this
    linarith only [this, hτ1, hrab]
  have hpR : p ∈ Set.range (D.arc hab) := Set.mem_range_self τ
  -- the reversed tail and its exit from the ball at `B`
  obtain ⟨γ2, hγ2⟩ : ∃ γ2 : Path B p,
      γ2 = (((D.arc hab).subpath τ 1).symm).cast (D.arc hab).target.symm rfl := ⟨_, rfl⟩
  have hγ2v : ∀ s, ∃ t : unitInterval, τ ≤ t ∧ γ2 s = D.arc hab t := by
    intro s
    refine ⟨Set.Icc.convexComb τ 1 (unitInterval.symm s), ?_, ?_⟩
    · show (τ : ℝ) ≤ (Set.Icc.convexComb τ 1 (unitInterval.symm s) : ℝ)
      rw [Set.Icc.coe_convexComb]
      have h1 : (τ : ℝ) ≤ 1 := τ.2.2
      have h2 : 0 ≤ ((unitInterval.symm s : unitInterval) : ℝ) := (unitInterval.symm s).2.1
      have h3 : ((unitInterval.symm s : unitInterval) : ℝ) ≤ 1 := (unitInterval.symm s).2.2
      simp only [Set.Icc.coe_one]
      have := mul_nonneg h2 (by linarith only [h1] : 0 ≤ 1 - (τ : ℝ))
      linarith only [this]
    · rw [hγ2]; rfl
  have hγ2A : ∀ s, ra ≤ dist (γ2 s) A := by
    intro s
    obtain ⟨t, ht, e⟩ := hγ2v s
    rw [e]
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hτ1]
    · exact (hτ2 t h).le
  have hγ2R : ∀ s, γ2 s ∈ Set.range (D.arc hab) := by
    intro s; obtain ⟨t, -, e⟩ := hγ2v s; rw [e]; exact Set.mem_range_self t
  obtain ⟨τ', hτ1', hτ2'⟩ := exit_time γ2 hrb hpB
  set q := γ2 τ' with hqdef
  have hqB : q ≠ B := by intro e; rw [e, dist_self] at hτ1'; linarith only [hτ1', hrb]
  have hqA : ra ≤ dist q A := hγ2A τ'
  have hqA' : q ≠ A := by intro e; rw [e, dist_self] at hqA; linarith only [hqA, hra]
  have hqR : q ∈ Set.range (D.arc hab) := hγ2R τ'
  have hp1 : p = γ2 1 := by rw [γ2.target]
  obtain ⟨mid, hmid⟩ : ∃ mid : Path p q, mid = ((γ2.subpath τ' 1).symm).cast hp1 rfl := ⟨_, rfl⟩
  have hmidR : Set.range mid = γ2 '' Set.Icc τ' 1 := by
    rw [hmid]
    show Set.range ((γ2.subpath τ' 1).symm) = _
    rw [Path.symm_range, Path.range_subpath_of_le γ2 τ' 1 (unitInterval.le_one _)]
  -- different exit points
  have hppa : ∀ c, H0.Adj a c → p ≠ pa c := by
    intro c hc e
    rcases (hpa c hc).2 (e ▸ hpR) with h | h
    · exact hpA (e.trans h)
    · rw [← e] at h; rw [h] at hτ1; linarith only [hτ1, hrab, hrb]
  have hqqb : ∀ d, H0.Adj b d → q ≠ qb d := by
    intro d hd e
    rcases (hqb d hd).2 (e ▸ hqR) with h | h
    · exact hqA' (e.trans h)
    · exact hqB (e.trans h)
  -- the linear change of coordinates
  have hpA0 : p - A ≠ 0 := sub_ne_zero.mpr hpA
  have hqB0 : q - B ≠ 0 := sub_ne_zero.mpr hqB
  have hBA0 : B - A ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; rw [e, dist_self] at hrab; linarith only [hrab, hra, hrb]
  obtain ⟨m, hdet, ⟨s1, hs1, hmv⟩, ⟨dW, hdW, s2, hs2, hmw⟩, ⟨kW, hkW, hme⟩⟩ :=
    exists_M (p - A) (q - B) (B - A) hpA0 hqB0 hBA0
  obtain ⟨c, hc, hlow⟩ := mapM_lower m hdet
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ × ℝ → ℝ × ℝ, Φ = fun z => mapM m (z - A) := ⟨_, rfl⟩
  have hΦc : Continuous Φ := by rw [hΦ]; exact (mapM_cont m).comp (by fun_prop)
  have hΦi : Function.Injective Φ := by
    intro x y e; rw [hΦ] at e; exact sub_left_injective (mapM_inj m hdet e)
  have hΦsub : ∀ y z, Φ y - Φ z = mapM m (y - z) := by
    intro y z; rw [hΦ]; simp only; rw [← mapM_sub]; congr 1; abel
  have hΦA : Φ A = kR (0, 0) := by rw [hΦ]; simp only [sub_self, mapM_zero]; rw [kR00]; rfl
  have hΦB : Φ B = kR kW := by rw [hΦ]; exact hme
  obtain ⟨D3, hD3⟩ : ∃ D3 : ImgDr H0, D3 = D2.map Φ hΦc hΦi := ⟨_, rfl⟩
  have hObs3 : Obs D3 u = Φ '' Obs D2 u := by rw [hD3]; exact Obs_map D2 Φ hΦc hΦi u
  -- the two cones
  have hs1c : c * ra ≤ s1 := by
    have h1 := hlow (p - A)
    rw [hmv, ← dist_eq_norm, hτ1] at h1
    have : ‖((s1, 0) : ℝ × ℝ)‖ = s1 := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs1, abs_zero,
        max_eq_left hs1.le]
    rw [this] at h1; exact h1
  have hs2c : c * rb ≤ s2 := by
    have h1 := hlow (q - B)
    rw [hmw, ← dist_eq_norm, hτ1', norm_smul, norm_kR_dir dW hdW, Real.norm_eq_abs,
      abs_of_pos hs2, mul_one] at h1
    exact h1
  obtain ⟨ρm, hρm⟩ : ∃ ρm : ℝ, ρm = min (1 / 4) (min (c * ra / 2) (c * rb / 2)) := ⟨_, rfl⟩
  have hρm0 : 0 < ρm := by rw [hρm]; positivity
  have hparA : ∀ i : {c // H0.Adj a c}, ¬ (0 < va (1, 0) (mapM m (pa i - A)) ∧
      vb (1, 0) (mapM m (pa i - A)) = 0) := by
    rintro ⟨i, hi⟩ ⟨h1, h2⟩
    simp only [va, vb, Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero, neg_zero,
      zero_add] at h1 h2
    set x := mapM m (pa i - A) with hx
    have ex : mapM m ((x.1 / s1) • (p - A)) = mapM m (pa i - A) := by
      rw [mapM_smul, hmv, ← hx]; ext
      · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
      · simp only [Prod.smul_snd, smul_eq_mul, mul_zero]; exact h2.symm
    have e2 := mapM_inj m hdet ex
    have hn := congrArg norm e2
    rw [norm_smul, ← dist_eq_norm, ← dist_eq_norm, hτ1, (hpa i hi).1, Real.norm_eq_abs,
      abs_of_pos (div_pos h1 hs1)] at hn
    have hk : x.1 / s1 = 1 := by
      have : (x.1 / s1 - 1) * ra = 0 := by linarith only [hn]
      rcases mul_eq_zero.mp this with h | h
      · linarith only [h]
      · linarith only [h, hra]
    rw [hk, one_smul] at e2
    exact hppa i hi (sub_left_injective e2)
  have hparB : ∀ i : {d // H0.Adj b d}, ¬ (0 < va dW (mapM m (qb i - B)) ∧
      vb dW (mapM m (qb i - B)) = 0) := by
    rintro ⟨i, hi⟩ ⟨h1, h2⟩
    have hs2' : s2 ≠ 0 := hs2.ne'
    set x := mapM m (qb i - B) with hx
    obtain ⟨e, he⟩ : ∃ e, e = va dW x := ⟨_, rfl⟩
    have hxf := vec_frame dW hdW x
    rw [h2, ← he] at hxf
    rw [← he] at h1
    have hsd : (e / s2) • (s2 • kR dW) = x := by
      rw [smul_smul, div_mul_cancel₀ e hs2', hxf]; ext <;> simp [kR]
    have ex : mapM m ((e / s2) • (q - B)) = mapM m (qb i - B) := by
      rw [mapM_smul, hmw, hsd]
    have e2 := mapM_inj m hdet ex
    have hn := congrArg norm e2
    rw [norm_smul, ← dist_eq_norm, ← dist_eq_norm, hτ1', (hqb i hi).1, Real.norm_eq_abs,
      abs_of_pos (div_pos h1 hs2)] at hn
    have hk : e / s2 = 1 := by
      have : (e / s2 - 1) * rb = 0 := by linarith only [hn]
      rcases mul_eq_zero.mp this with h | h
      · linarith only [h]
      · linarith only [h, hrb]
    rw [hk, one_smul] at e2
    exact hqqb i hi (sub_left_injective e2)
  obtain ⟨ρA, hρA, hρAm, μA, hμA, hμA1, coneA⟩ := cone_gen m c hc hlow A A (0, 0) (1, 0) dir10
    (by simp only [sub_self, mapM_zero]; rw [kR00]; rfl) (Obs D2 u) ra hra
    (fun i : {c // H0.Adj a c} => pa i) (fun y hy hd => NA y hy hd) hparA ρm hρm0
  obtain ⟨ρB, hρB, hρBm, μB, hμB, hμB1, coneB⟩ := cone_gen m c hc hlow A B kW dW hdW hme
    (Obs D2 u) rb hrb (fun i : {d // H0.Adj b d} => qb i) (fun y hy hd => NB y hy hd) hparB ρm hρm0
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min ρA ρB := ⟨_, rfl⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = min μA μB := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min hρA hρB
  have hμ : 0 < μ := by rw [hμdef]; exact lt_min hμA hμB
  have hρA' : ρ ≤ ρA := by rw [hρdef]; exact min_le_left _ _
  have hρB' : ρ ≤ ρB := by rw [hρdef]; exact min_le_right _ _
  have hμA' : μ ≤ μA := by rw [hμdef]; exact min_le_left _ _
  have hμB' : μ ≤ μB := by rw [hμdef]; exact min_le_right _ _
  have hρ4 : ρ ≤ 1 / 4 := by
    have := min_le_left (1 / 4 : ℝ) (min (c * ra / 2) (c * rb / 2)); rw [← hρm] at this
    linarith only [this, hρA', hρAm]
  have hρa : ρ ≤ c * ra / 2 := by
    have h1 := min_le_right (1 / 4 : ℝ) (min (c * ra / 2) (c * rb / 2))
    have h2 := min_le_left (c * ra / 2) (c * rb / 2)
    rw [← hρm] at h1; linarith only [h1, h2, hρA', hρAm]
  have hρb : ρ ≤ c * rb / 2 := by
    have h1 := min_le_right (1 / 4 : ℝ) (min (c * ra / 2) (c * rb / 2))
    have h2 := min_le_right (c * ra / 2) (c * rb / 2)
    rw [← hρm] at h1; linarith only [h1, h2, hρA', hρAm]
  have coneX : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α →
      Lc 1 (0, 0) (1, 0) (α, β) ∉ Obs D3 u := by
    intro α β hα hαρ hβ
    rw [hObs3, hΦ]
    exact coneA α β hα (hαρ.trans hρA') (hβ.trans (mul_le_mul_of_nonneg_right hμA' hα.le))
  have coneW : ∀ α β : ℝ, 0 < α → α ≤ ρ → |β| ≤ μ * α → Lc 1 kW dW (α, β) ∉ Obs D3 u := by
    intro α β hα hαρ hβ
    rw [hObs3, hΦ]
    exact coneB α β hα (hαρ.trans hρB') (hβ.trans (mul_le_mul_of_nonneg_right hμB' hα.le))
  -- the corridor path
  obtain ⟨sX, hsXd⟩ : ∃ sX : ℝ, sX = ρ / 2 := ⟨_, rfl⟩
  have hsX : 0 < sX := by rw [hsXd]; positivity
  obtain ⟨l1, hl1⟩ : ∃ l1 : ℝ, l1 = sX / s1 := ⟨_, rfl⟩
  obtain ⟨l2, hl2⟩ : ∃ l2 : ℝ, l2 = sX / s2 := ⟨_, rfl⟩
  have hl1p : 0 < l1 := by rw [hl1]; positivity
  have hl2p : 0 < l2 := by rw [hl2]; positivity
  have hl11 : l1 ≤ 1 := by
    rw [hl1, div_le_one hs1]; rw [hsXd]; linarith only [hρa, hs1c, hρ]
  have hl21 : l2 ≤ 1 := by
    rw [hl2, div_le_one hs2]; rw [hsXd]; linarith only [hρb, hs2c, hρ]
  obtain ⟨P0, hP0⟩ : ∃ P0 : ℝ × ℝ, P0 = A + l1 • (p - A) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ × ℝ, P1 = B + l2 • (q - B) := ⟨_, rfl⟩
  obtain ⟨Ko, hKo⟩ : ∃ Ko : Path P0 P1, Ko = (segPath P0 p).trans (mid.trans (segPath q P1)) :=
    ⟨_, rfl⟩
  have hKoR : Set.range Ko = seg P0 p ∪ (Set.range mid ∪ seg q P1) := by
    rw [hKo, Path.trans_range, Path.trans_range, range_segPath, range_segPath]
  -- every point of the corridor is free and away from both ends
  have hBAr : ra < dist B A - rb := by linarith only [hrab]
  have KAV : ∀ y ∈ Set.range Ko, y ∉ Obs D2 u ∧ l1 * ra ≤ dist y A ∧ l2 * rb ≤ dist y B := by
    intro y hy
    rw [hKoR] at hy
    rcases hy with hy | hy | hy
    · -- the first straight piece, on the ray from `A` to `p`
      obtain ⟨s, hs, rfl⟩ := hy
      beta_reduce
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = l1 + s * (1 - l1) := ⟨_, rfl⟩
      have hy' : P0 + s • (p - P0) = A + t • (p - A) := by
        rw [hP0, ht]; ext <;> simp <;> ring
      rw [hy']
      have ht0 : l1 ≤ t := by
        rw [ht]; have := mul_nonneg hs.1 (by linarith only [hl11] : (0 : ℝ) ≤ 1 - l1)
        linarith only [this]
      have ht1 : t ≤ 1 := by
        rw [ht]
        have := mul_nonneg (by linarith only [hs.2] : (0 : ℝ) ≤ 1 - s)
          (by linarith only [hl11] : (0 : ℝ) ≤ 1 - l1)
        linarith only [this]
      have htpos : 0 < t := lt_of_lt_of_le hl1p ht0
      have hdA : dist (A + t • (p - A)) A = t * ra := by
        rw [dist_smul_add A _ htpos.le, ← dist_eq_norm, hτ1]
      have hmem : A + t • (p - A) ∈ seg A p := ⟨t, ⟨htpos.le, ht1⟩, rfl⟩
      have hdB : dist B A - ra ≤ dist (A + t • (p - A)) B := by
        have := dist_seg_far (B := B) hmem; rw [hτ1] at this; exact this
      refine ⟨?_, by rw [hdA]; exact mul_le_mul_of_nonneg_right ht0 hra.le,
        le_trans (mul_le_of_le_one_left hrb.le hl21) (by linarith only [hdB, hrab])⟩
      rcases eq_or_lt_of_le ht1 with e | e
      · rw [e, one_smul, add_sub_cancel]
        exact GM p hpR hpA (fun h => by rw [h, dist_self] at hpB; linarith only [hpB, hrb]) hτ1.ge
          hpB.le
      · intro hyo
        rcases NA _ hyo (by rw [hdA]; exact mul_lt_of_lt_one_left hra e) with h | ⟨⟨i, hi⟩, h⟩
        · rw [h, dist_self] at hdA; have := mul_pos htpos hra; linarith only [hdA, this]
        · have := seg_seg (hppa i hi) (hτ1.trans (hpa i hi).1.symm) hmem h
          rw [this, dist_self] at hdA; have := mul_pos htpos hra; linarith only [hdA, this]
    · -- the middle piece, part of the arc of `ab`
      rw [hmidR] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      have hdA := hγ2A s
      have hdB : rb ≤ dist (γ2 s) B := by
        rcases eq_or_lt_of_le hs.1 with e | e
        · rw [← e, hτ1']
        · exact (hτ2' s e).le
      refine ⟨GM _ (hγ2R s) (fun h => by rw [h, dist_self] at hdA; linarith only [hdA, hra])
        (fun h => by rw [h, dist_self] at hdB; linarith only [hdB, hrb]) hdA hdB,
        le_trans (mul_le_of_le_one_left hra.le hl11) hdA,
        le_trans (mul_le_of_le_one_left hrb.le hl21) hdB⟩
    · -- the last straight piece, on the ray from `B` to `q`
      obtain ⟨s, hs, rfl⟩ := hy
      beta_reduce
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 - s * (1 - l2) := ⟨_, rfl⟩
      have hy' : q + s • (P1 - q) = B + t • (q - B) := by
        rw [hP1, ht]; ext <;> simp <;> ring
      rw [hy']
      have ht0 : l2 ≤ t := by
        rw [ht]
        have := mul_nonneg (by linarith only [hs.2] : (0 : ℝ) ≤ 1 - s)
          (by linarith only [hl21] : (0 : ℝ) ≤ 1 - l2)
        linarith only [this]
      have ht1 : t ≤ 1 := by
        rw [ht]; have := mul_nonneg hs.1 (by linarith only [hl21] : (0 : ℝ) ≤ 1 - l2)
        linarith only [this]
      have htpos : 0 < t := lt_of_lt_of_le hl2p ht0
      have hdB : dist (B + t • (q - B)) B = t * rb := by
        rw [dist_smul_add B _ htpos.le, ← dist_eq_norm, hτ1']
      have hmem : B + t • (q - B) ∈ seg B q := ⟨t, ⟨htpos.le, ht1⟩, rfl⟩
      have hdA : dist A B - rb ≤ dist (B + t • (q - B)) A := by
        have := dist_seg_far (B := A) hmem; rw [hτ1'] at this; exact this
      rw [dist_comm A B] at hdA
      refine ⟨?_, le_trans (mul_le_of_le_one_left hra.le hl11) (by linarith only [hdA, hrab]),
        by rw [hdB]; exact mul_le_mul_of_nonneg_right ht0 hrb.le⟩
      rcases eq_or_lt_of_le ht1 with e | e
      · rw [e, one_smul, add_sub_cancel]
        exact GM q hqR hqA' hqB hqA hτ1'.ge
      · intro hyo
        rcases NB _ hyo (by rw [hdB]; exact mul_lt_of_lt_one_left hrb e) with h | ⟨⟨i, hi⟩, h⟩
        · rw [h, dist_self] at hdB; have := mul_pos htpos hrb; linarith only [hdB, this]
        · have := seg_seg (hqqb i hi) (hτ1'.trans (hqb i hi).1.symm) hmem h
          rw [this, dist_self] at hdB; have := mul_pos htpos hrb; linarith only [hdB, this]
  -- transport to the new coordinates
  have hX0 : Lc 1 (0, 0) (1, 0) (sX, 0) = Φ P0 := by
    rw [Lc_id, hΦ]; simp only
    rw [hP0, add_sub_cancel_left, mapM_smul, hmv, hl1]
    ext
    · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
    · simp
  have hW0 : Lc 1 kW dW (sX, 0) = Φ P1 := by
    rw [hΦ]; simp only
    have : P1 - A = (B - A) + l2 • (q - B) := by rw [hP1]; abel
    rw [this, mapM_add, mapM_smul, hme, hmw, hl2, smul_smul, div_mul_cancel₀ sX hs2.ne']
    ext <;> simp [Lc, kR]
  obtain ⟨K, hK⟩ : ∃ K : Path (Lc 1 (0, 0) (1, 0) (sX, 0)) (Lc 1 kW dW (sX, 0)),
      K = (Ko.map hΦc).cast hX0 hW0 := ⟨_, rfl⟩
  have hKv : ∀ t, K t = Φ (Ko t) := by intro t; rw [hK]; rfl
  have hKobs : ∀ t, K t ∉ Obs D3 u := by
    intro t hm
    rw [hObs3, hKv] at hm
    obtain ⟨y, hy, e⟩ := hm
    have := hΦi e
    exact (KAV (Ko t) (Set.mem_range_self t)).1 (this ▸ hy)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = c * min (l1 * ra) (l2 * rb) := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by rw [hρ']; positivity
  have hKfar : ∀ t, ρ' ≤ dist (K t) (kR (0, 0)) ∧ ρ' ≤ dist (K t) (kR kW) := by
    intro t
    obtain ⟨-, h1, h2⟩ := KAV (Ko t) (Set.mem_range_self t)
    rw [hKv, ← hΦA, ← hΦB, dist_eq_norm, dist_eq_norm, hΦsub, hΦsub]
    have g1 := hlow (Ko t - A)
    have g2 := hlow (Ko t - B)
    rw [← dist_eq_norm] at g1 g2
    have m1 := min_le_left (l1 * ra) (l2 * rb)
    have m2 := min_le_right (l1 * ra) (l2 * rb)
    constructor
    · rw [hρ']
      calc c * min (l1 * ra) (l2 * rb) ≤ c * dist (Ko t) A := mul_le_mul_of_nonneg_left (m1.trans h1) hc.le
        _ ≤ _ := g1
    · rw [hρ']
      calc c * min (l1 * ra) (l2 * rb) ≤ c * dist (Ko t) B := mul_le_mul_of_nonneg_left (m2.trans h2) hc.le
        _ ≤ _ := g2
  have hX : D3.P a = kR (0, 0) := by rw [hD3, ← hΦA]; show Φ (D2.P a) = Φ A; rw [hD2P]
  have hW : D3.P b = kR kW := by rw [hD3, ← hΦB]; show Φ (D2.P b) = Φ B; rw [hD2P]
  exact core H0 G' D3 a b u hab' hua hub hu0 hab0 hG'' kW dW hkW hdW hX hW ρ μ hρ hρ4 hμ
    coneX coneW sX sX hsX (by rw [hsXd]) hsX (by rw [hsXd]) K hKobs ρ' hρ'0 hKfar


end TTAE


open RobertsonSeymour1986.GM5 in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (a b u : Fin n) (hab : G.Adj a b) (hu : ∀ q, ¬ G.Adj u q)
    (G' : SimpleGraph (Fin n))
    (hG' : ∀ p q, G'.Adj p q ↔
      (G.Adj p q ∨ (p = u ∧ (q = a ∨ q = b)) ∨ (q = u ∧ (p = a ∨ p = b)))) :
    IsPlanar G' := by
  obtain ⟨D⟩ := hG
  exact TTAE.attach_main G D a b u hab hu G' hG'
