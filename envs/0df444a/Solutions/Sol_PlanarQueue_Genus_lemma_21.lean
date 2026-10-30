-- Prove2me | solution 1 for PlanarQueue.Genus.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T18:43:11.583316+00:00
-- url     : https://prove2.me/submissions/04e44727-7bbc-4212-9d60-7088a24f36f4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_PlanarQueue_Genus_Setting
import Definitions.Def_PlanarQueue_Genus_EulerGenus

set_option maxHeartbeats 1000000

set_option autoImplicit false

/-! C1a for lemma_21 (e1368385): a 2-page book embedding gives a plane drawing.
Vertices on the x-axis at `pos v`; the edge `vw` is the parabolic arc
`y = σ (x - pos v) (pos w - x)` with `σ = ±1` by page. -/

namespace PQL21

/-- x-coordinate along the arc from `a` to `b` -/
def bx (a b : ℝ) (t : unitInterval) : ℝ := a + (t : ℝ) * (b - a)

/-- the parabolic arc point -/
def bk (σ a b : ℝ) (t : unitInterval) : ℝ × ℝ :=
  (bx a b t, σ * ((bx a b t - a) * (b - bx a b t)))

noncomputable def bpath (σ a b : ℝ) : Path ((a, 0) : ℝ × ℝ) (b, 0) where
  toFun := bk σ a b
  continuous_toFun := by
    unfold bk bx
    fun_prop
  source' := by simp [bk, bx]
  target' := by simp [bk, bx]

theorem bpath_apply (σ a b : ℝ) (t : unitInterval) : bpath σ a b t = bk σ a b t := rfl

theorem bk_snd (σ a b : ℝ) (t : unitInterval) :
    (bk σ a b t).2 = σ * ((t : ℝ) * (1 - (t : ℝ)) * (b - a) ^ 2) := by
  simp only [bk, bx]; ring

/-- the page sign -/
def sg (p : Bool) : ℝ := if p then 1 else -1

theorem sg_ne (p : Bool) : sg p ≠ 0 := by cases p <;> simp [sg]

theorem sg_inj {p q : Bool} (h : sg p = sg q) : p = q := by
  cases p <;> cases q <;> simp [sg] at h ⊢ <;> norm_num at h

theorem unit_tri (t : unitInterval) : t = 0 ∨ t = 1 ∨ (0 < (t : ℝ) ∧ (t : ℝ) < 1) := by
  rcases eq_or_lt_of_le t.2.1 with h | h
  · left; exact Subtype.ext h.symm
  rcases eq_or_lt_of_le t.2.2 with h' | h'
  · right; left; exact Subtype.ext h'
  · right; right; exact ⟨h, h'⟩

/-- normalized nesting lemma: two parabolas over non-crossing intervals meeting at an interior
point have the same interval -/
theorem par_meet (lo1 hi1 lo2 hi2 X : ℝ) (h1 : lo1 < X) (h2 : X < hi1) (h3 : lo2 < X)
    (h4 : X < hi2) (hnc1 : ¬(lo1 < lo2 ∧ lo2 < hi1 ∧ hi1 < hi2))
    (hnc2 : ¬(lo2 < lo1 ∧ lo1 < hi2 ∧ hi2 < hi1))
    (heq : (X - lo1) * (hi1 - X) = (X - lo2) * (hi2 - X)) : lo1 = lo2 ∧ hi1 = hi2 := by
  rcases lt_trichotomy lo1 lo2 with ha | ha | ha <;>
    rcases lt_trichotomy hi1 hi2 with hb | hb | hb
  · exact absurd ⟨ha, by linarith, hb⟩ hnc1
  · subst hb; nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 h2)]
  · nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 h4), mul_pos (sub_pos.2 hb) (sub_pos.2 h3),
      mul_pos (sub_pos.2 h1) (sub_pos.2 h4)]
  · subst ha; nlinarith [mul_pos (sub_pos.2 hb) (sub_pos.2 h1)]
  · exact ⟨ha, hb⟩
  · subst ha; nlinarith [mul_pos (sub_pos.2 hb) (sub_pos.2 h1)]
  · nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 h2), mul_pos (sub_pos.2 hb) (sub_pos.2 h1),
      mul_pos (sub_pos.2 h3) (sub_pos.2 h2)]
  · subst hb; nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 h2)]
  · exact absurd ⟨ha, by linarith, hb⟩ hnc2

/-- interior parameter: the arc point is strictly between the ends -/
theorem bx_between (a b : ℝ) (t : unitInterval) (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
    (a < b → a < bx a b t ∧ bx a b t < b) ∧ (b < a → b < bx a b t ∧ bx a b t < a) := by
  unfold bx
  constructor
  · intro h; constructor <;> nlinarith [ht.1, ht.2]
  · intro h; constructor <;> nlinarith [ht.1, ht.2]

/-- the meeting lemma in arbitrary orientation -/
theorem par_meet' (a b c d X : ℝ) (hab : a ≠ b) (hcd : c ≠ d)
    (hX1 : (a < X ∧ X < b) ∨ (b < X ∧ X < a)) (hX2 : (c < X ∧ X < d) ∨ (d < X ∧ X < c))
    (hnc : ∀ p q u w : ℝ, ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) → ((u = c ∧ w = d) ∨ (u = d ∧ w = c)) →
      ¬(p < u ∧ u < q ∧ q < w))
    (hnc' : ∀ p q u w : ℝ, ((p = c ∧ q = d) ∨ (p = d ∧ q = c)) → ((u = a ∧ w = b) ∨ (u = b ∧ w = a)) →
      ¬(p < u ∧ u < q ∧ q < w))
    (heq : (X - a) * (b - X) = (X - c) * (d - X)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases hX1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hX2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · have := par_meet a b c d X h1 h2 h3 h4 (hnc a b c d (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩))
      (hnc' c d a b (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)) heq
    exact Or.inl this
  · have := par_meet a b d c X h1 h2 h3 h4 (hnc a b d c (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩))
      (hnc' d c a b (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)) (by linarith)
    exact Or.inr this
  · have := par_meet b a c d X h1 h2 h3 h4 (hnc b a c d (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩))
      (hnc' c d b a (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)) (by linarith)
    exact Or.inr ⟨this.2, this.1⟩
  · have := par_meet b a d c X h1 h2 h3 h4 (hnc b a d c (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩))
      (hnc' d c b a (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)) (by linarith)
    exact Or.inl ⟨this.2, this.1⟩

/-- C1a: a 2-page book embedding (vertices injectively on a line, each edge on a page, no two
edges of one page interleave) yields a plane drawing. -/
theorem planar_of_book2 {W : Type} (H : SimpleGraph W) (pos : W → ℝ)
    (hpos : Function.Injective pos) (page : W → W → Bool) (hpage : ∀ a b, page a b = page b a)
    (hnc : ∀ a b c d, H.Adj a b → H.Adj c d → page a b = page c d →
      ¬(pos a < pos c ∧ pos c < pos b ∧ pos b < pos d)) :
    RobertsonSeymour1986.GM5.IsPlanar H := by
  have hne : ∀ {v w : W}, H.Adj v w → pos v ≠ pos w := fun h e => H.ne_of_adj h (hpos e)
  refine ⟨{
    vertex := fun v => (pos v, 0)
    vertex_injective := fun v w e => hpos (congrArg Prod.fst e)
    arc := fun {v w} _ => bpath (sg (page v w)) (pos v) (pos w)
    arc_injective := ?_
    arc_reverse := ?_
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }⟩
  · intro v w h s t hst
    rw [bpath_apply, bpath_apply] at hst
    have h1 := congrArg Prod.fst hst
    simp only [bk, bx] at h1
    have h2 : ((s : ℝ) - t) * (pos w - pos v) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with e | e
    · exact Subtype.ext (by linarith)
    · exact absurd (by linarith) (hne h)
  · intro v w h
    ext t
    · simp [bpath_apply, bk, bx, unitInterval.coe_symm_eq]; ring
    · simp only [Path.symm_apply, Path.symm, Path.coe_mk_mk, ContinuousMap.coe_mk, Function.comp_apply, bpath_apply, bk, bx,
        unitInterval.coe_symm_eq]
      rw [hpage w v]; ring
  · intro v w h t x hx
    rw [bpath_apply] at hx
    have hy := congrArg Prod.snd hx
    rw [bk_snd] at hy
    simp only at hy
    have hab : (pos w - pos v) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (hne h).symm)
    have h0 : (t : ℝ) * (1 - (t : ℝ)) = 0 := by
      rcases mul_eq_zero.1 hy with e | e
      · exact absurd e (sg_ne _)
      · exact (mul_eq_zero.1 e).resolve_right hab
    have hxf := congrArg Prod.fst hx
    simp only [bk, bx] at hxf
    rcases mul_eq_zero.1 h0 with e | e
    · left; apply hpos; rw [e] at hxf; linarith
    · right; apply hpos; have : (t : ℝ) = 1 := by linarith
      rw [this] at hxf; linarith
  · intro v w x y h k s t hst
    rw [bpath_apply, bpath_apply] at hst
    have hy := congrArg Prod.snd hst
    rw [bk_snd, bk_snd] at hy
    have hsq1 : 0 < (pos w - pos v) ^ 2 := by
      have := sub_ne_zero.2 (hne h).symm; positivity
    have hsq2 : 0 < (pos y - pos x) ^ 2 := by
      have := sub_ne_zero.2 (hne k).symm; positivity
    have hP : ∀ (r : unitInterval), 0 < (r : ℝ) ∧ (r : ℝ) < 1 → ∀ c : ℝ, 0 < c →
        0 < (r : ℝ) * (1 - (r : ℝ)) * c := fun r hr c hc =>
      mul_pos (mul_pos hr.1 (by linarith [hr.2])) hc
    have hE : ∀ (r : unitInterval), (r = 0 ∨ r = 1) → (r : ℝ) * (1 - (r : ℝ)) = 0 := by
      intro r hr; rcases hr with rfl | rfl <;> simp
    rcases unit_tri s with hs | hs | hs <;> rcases unit_tri t with ht | ht | ht
    · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inl ht⟩)
    · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inr ht⟩)
    · exfalso; rw [hE s (Or.inl hs), zero_mul, mul_zero] at hy
      exact mul_ne_zero (sg_ne _) (hP t ht _ hsq2).ne' hy.symm
    · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inl ht⟩)
    · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inr ht⟩)
    · exfalso; rw [hE s (Or.inr hs), zero_mul, mul_zero] at hy
      exact mul_ne_zero (sg_ne _) (hP t ht _ hsq2).ne' hy.symm
    · exfalso; rw [hE t (Or.inl ht), zero_mul, mul_zero] at hy
      exact mul_ne_zero (sg_ne _) (hP s hs _ hsq1).ne' hy
    · exfalso; rw [hE t (Or.inr ht), zero_mul, mul_zero] at hy
      exact mul_ne_zero (sg_ne _) (hP s hs _ hsq1).ne' hy
    -- both interior
    have p1 := hP s hs _ hsq1
    have p2 := hP t ht _ hsq2
    have hpg : page v w = page x y := by
      apply sg_inj
      cases hp : page v w <;> cases hq : page x y <;> rw [hp, hq] at hy <;> simp only [sg] at hy ⊢ <;>
        first | rfl | (exfalso; norm_num at hy; linarith)
    have hx := congrArg Prod.fst hst
    have hy2 := congrArg Prod.snd hst
    simp only [bk] at hx hy2
    rw [hpg] at hy2
    have heq := mul_left_cancel₀ (sg_ne _) hy2
    rw [← hx] at heq
    have hN : ∀ p q u z : ℝ, ((p = pos v ∧ q = pos w) ∨ (p = pos w ∧ q = pos v)) →
        ((u = pos x ∧ z = pos y) ∨ (u = pos y ∧ z = pos x)) → ¬(p < u ∧ u < q ∧ q < z) := by
      intro p q u z h1 h2
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnc v w x y h k hpg
      · exact hnc v w y x h k.symm (by rw [hpage y x]; exact hpg)
      · exact hnc w v x y h.symm k (by rw [hpage w v]; exact hpg)
      · exact hnc w v y x h.symm k.symm (by rw [hpage w v, hpage y x]; exact hpg)
    have hN' : ∀ p q u z : ℝ, ((p = pos x ∧ q = pos y) ∨ (p = pos y ∧ q = pos x)) →
        ((u = pos v ∧ z = pos w) ∨ (u = pos w ∧ z = pos v)) → ¬(p < u ∧ u < q ∧ q < z) := by
      intro p q u z h1 h2
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnc x y v w k h hpg.symm
      · exact hnc x y w v k h.symm (by rw [hpage w v]; exact hpg.symm)
      · exact hnc y x v w k.symm h (by rw [hpage y x]; exact hpg.symm)
      · exact hnc y x w v k.symm h.symm (by rw [hpage w v, hpage y x]; exact hpg.symm)
    have hX1 : (pos v < bx (pos v) (pos w) s ∧ bx (pos v) (pos w) s < pos w) ∨
        (pos w < bx (pos v) (pos w) s ∧ bx (pos v) (pos w) s < pos v) := by
      rcases lt_or_gt_of_ne (hne h) with e | e
      · exact Or.inl ((bx_between _ _ s hs).1 e)
      · exact Or.inr ((bx_between _ _ s hs).2 e)
    have hX2 : (pos x < bx (pos v) (pos w) s ∧ bx (pos v) (pos w) s < pos y) ∨
        (pos y < bx (pos v) (pos w) s ∧ bx (pos v) (pos w) s < pos x) := by
      rw [hx]
      rcases lt_or_gt_of_ne (hne k) with e | e
      · exact Or.inl ((bx_between _ _ t ht).1 e)
      · exact Or.inr ((bx_between _ _ t ht).2 e)
    rcases par_meet' _ _ _ _ _ (hne h) (hne k) hX1 hX2 hN hN' heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hpos e1, hpos e2⟩
    · exact Or.inr (Or.inl ⟨hpos e1, hpos e2⟩)

end PQL21

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! C1c core for lemma_21 (e1368385): orbit counting of `π * swap a b`.
`norb π` = number of cycles (fixed points included). Multiplying by a transposition
merges two cycles (`a`, `b` in different cycles) or splits one (same cycle). -/

namespace PQL21

open Equiv Equiv.Perm

variable {α : Type} [DecidableEq α] [Fintype α]

/-- number of orbits (cycles, fixed points included) of a permutation -/
noncomputable def norb (π : Perm α) : ℕ := Nat.card (Quotient (SameCycle.setoid π))

theorem mulswap_of_ne (π : Perm α) {a b x : α} (ha : x ≠ a) (hb : x ≠ b) :
    (π * swap a b) x = π x := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha hb]

/-- while the `π`-walk avoids `a, b`, the `π * swap a b`-walk is the same -/
theorem walk (π : Perm α) (a b x : α) (n : ℕ)
    (h : ∀ i < n, (π ^ i) x ≠ a ∧ (π ^ i) x ≠ b) : ((π * swap a b) ^ n) x = (π ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : ((π * swap a b) ^ (n + 1)) x = (π * swap a b) (((π * swap a b) ^ n) x) := by
      rw [pow_succ', Perm.mul_apply]
    have e2 : (π ^ (n + 1)) x = π ((π ^ n) x) := by rw [pow_succ', Perm.mul_apply]
    rw [e1, e2, ih (fun i hi => h i (by omega))]
    exact mulswap_of_ne π (h n (by omega)).1 (h n (by omega)).2

theorem sc_of_nat {f : Perm α} {x y : α} (n : ℕ) (h : (f ^ n) x = y) : SameCycle f x y :=
  ⟨n, by rw [zpow_natCast]; exact h⟩

/-- a property invariant under `f` is constant on `f`-cycles -/
theorem pres (f : Perm α) (P : α → Prop) (hP : ∀ z, P (f z) ↔ P z) {x y : α}
    (h : SameCycle f x y) : (P y ↔ P x) := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, hP, ih]

/-- a forward-closed set contains the whole cycle of each of its points -/
theorem closed_mem (f : Perm α) (C : α → Prop) (hC : ∀ z, C z → C (f z)) {x y : α}
    (h : SameCycle f x y) (hx : C x) : C y := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Perm.mul_apply]; exact hC _ ih

theorem sc_apply (f : Perm α) (z : α) : SameCycle f z (f z) :=
  sameCycle_apply_right.mpr SameCycle.rfl

/-- if `a, b` share a `π`-cycle, the cycles of `π * swap a b` refine those of `π` -/
theorem refine_of_same (π : Perm α) {a b : α} (hab : SameCycle π a b) {x y : α}
    (h : SameCycle (π * swap a b) x y) : SameCycle π x y := by
  have key : ∀ z, SameCycle π x ((π * swap a b) z) ↔ SameCycle π x z := by
    intro z
    rw [Perm.mul_apply, sameCycle_apply_right]
    by_cases hza : z = a
    · subst hza; rw [swap_apply_left]
      exact ⟨fun h => h.trans hab.symm, fun h => h.trans hab⟩
    · by_cases hzb : z = b
      · subst hzb; rw [swap_apply_right]
        exact ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩
      · rw [swap_apply_of_ne_of_ne hza hzb]
  exact (pres _ (fun z => SameCycle π x z) key h).mpr SameCycle.rfl

/-- merge: if `a, b` lie in different `π`-cycles they share a `π * swap a b`-cycle -/
theorem merge_join (π : Perm α) {a b : α} (hab : ¬ SameCycle π a b) :
    SameCycle (π * swap a b) a b := by
  classical
  have hex : ∃ n : ℕ, (π ^ n) (π a) = a :=
    (sameCycle_apply_left.mpr (SameCycle.refl π a)).exists_nat_pow_eq
  have hn : (π ^ Nat.find hex) (π a) = a := Nat.find_spec hex
  have hlt : ∀ i < Nat.find hex, (π ^ i) (π a) ≠ a ∧ (π ^ i) (π a) ≠ b := by
    intro i hi
    refine ⟨Nat.find_min hex hi, fun hb => hab ?_⟩
    rw [← hb]
    exact sameCycle_pow_right.mpr (sc_apply π a)
  have hw := walk π a b (π a) _ hlt
  rw [hn] at hw
  have h1 : SameCycle (π * swap a b) (π a) a := sc_of_nat _ hw
  have h2 : (π * swap a b) b = π a := by rw [Perm.mul_apply, swap_apply_right]
  have h3 : SameCycle (π * swap a b) b (π a) := by rw [← h2]; exact sc_apply _ b
  exact (h3.trans h1).symm

/-- merge: the cycles of `π` are contained in cycles of `π * swap a b` -/
theorem merge_coarsen (π : Perm α) {a b : α} (hab : ¬ SameCycle π a b) {x y : α}
    (h : SameCycle π x y) : SameCycle (π * swap a b) x y := by
  have hj := merge_join π hab
  have step : ∀ z, SameCycle (π * swap a b) z (π z) := by
    intro z
    by_cases hza : z = a
    · have : (π * swap a b) b = π z := by rw [Perm.mul_apply, swap_apply_right, hza]
      rw [← this, hza]; exact hj.trans (sc_apply _ b)
    · by_cases hzb : z = b
      · have : (π * swap a b) a = π z := by rw [Perm.mul_apply, swap_apply_left, hzb]
        rw [← this, hzb]; exact hj.symm.trans (sc_apply _ a)
      · rw [← mulswap_of_ne π hza hzb]; exact sc_apply _ z
  have := pres π (fun z => SameCycle (π * swap a b) x z)
    (fun z => ⟨fun h' => h'.trans (step z).symm, fun h' => h'.trans (step z)⟩) h
  exact this.mpr SameCycle.rfl

/-- the cycles of `π * swap a b` relate only `π`-related points or points of the cycles of
`a` and `b` -/
theorem merge_classes (π : Perm α) {a b : α} {x y : α}
    (h : SameCycle (π * swap a b) x y) :
    SameCycle π x y ∨ ((SameCycle π x a ∨ SameCycle π x b) ∧
      (SameCycle π y a ∨ SameCycle π y b)) := by
  have key : ∀ z, (SameCycle π x ((π * swap a b) z) ∨ ((SameCycle π x a ∨ SameCycle π x b) ∧
      (SameCycle π ((π * swap a b) z) a ∨ SameCycle π ((π * swap a b) z) b))) ↔
      (SameCycle π x z ∨ ((SameCycle π x a ∨ SameCycle π x b) ∧
        (SameCycle π z a ∨ SameCycle π z b))) := by
    intro z
    rw [Perm.mul_apply, sameCycle_apply_right, sameCycle_apply_left, sameCycle_apply_left]
    by_cases hza : z = a
    · subst hza; rw [swap_apply_left]
      constructor
      · rintro (h1 | ⟨h1, _⟩)
        · exact Or.inr ⟨Or.inr h1, Or.inl SameCycle.rfl⟩
        · exact Or.inr ⟨h1, Or.inl SameCycle.rfl⟩
      · rintro (h1 | ⟨h1, _⟩)
        · exact Or.inr ⟨Or.inl h1, Or.inr SameCycle.rfl⟩
        · exact Or.inr ⟨h1, Or.inr SameCycle.rfl⟩
    · by_cases hzb : z = b
      · subst hzb; rw [swap_apply_right]
        constructor
        · rintro (h1 | ⟨h1, _⟩)
          · exact Or.inr ⟨Or.inl h1, Or.inr SameCycle.rfl⟩
          · exact Or.inr ⟨h1, Or.inr SameCycle.rfl⟩
        · rintro (h1 | ⟨h1, _⟩)
          · exact Or.inr ⟨Or.inr h1, Or.inl SameCycle.rfl⟩
          · exact Or.inr ⟨h1, Or.inl SameCycle.rfl⟩
      · rw [swap_apply_of_ne_of_ne hza hzb]
  exact (pres _ (fun z => SameCycle π x z ∨ ((SameCycle π x a ∨ SameCycle π x b) ∧
      (SameCycle π z a ∨ SameCycle π z b))) key h).mpr (Or.inl SameCycle.rfl)

/-- split: the explicit cycle of `b` in `π * swap a b` when `a ≠ b` share a `π`-cycle:
it is the `π`-arc from `π a` up to `b` -/
theorem split_class (π : Perm α) {a b : α} (hab : SameCycle π a b) (hne : a ≠ b) :
    ∃ n : ℕ, (π ^ n) (π a) = b ∧ (∀ i < n, (π ^ i) (π a) ≠ a ∧ (π ^ i) (π a) ≠ b) ∧
      ∀ y, SameCycle (π * swap a b) b y ↔ ∃ i ≤ n, (π ^ i) (π a) = y := by
  classical
  have hex : ∃ n : ℕ, (π ^ n) (π a) = a ∨ (π ^ n) (π a) = b :=
    let ⟨n, hn⟩ := (sameCycle_apply_left.mpr (SameCycle.refl π a)).exists_nat_pow_eq
    ⟨n, Or.inl hn⟩
  set n := Nat.find hex with hn_def
  have hmin : ∀ i < n, (π ^ i) (π a) ≠ a ∧ (π ^ i) (π a) ≠ b := by
    intro i hi
    have := Nat.find_min hex hi
    exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩
  have hhit : (π ^ n) (π a) = b := by
    rcases Nat.find_spec hex with h | h
    · exfalso
      have hcl : ∀ z, (∃ i ≤ n, (π ^ i) (π a) = z) → ∃ i ≤ n, (π ^ i) (π a) = π z := by
        rintro z ⟨i, hi, rfl⟩
        rcases Nat.lt_or_ge i n with hlt | hge
        · exact ⟨i + 1, by omega, by rw [pow_succ', Perm.mul_apply]⟩
        · have : i = n := le_antisymm hi hge
          subst this
          exact ⟨0, Nat.zero_le _, by rw [h]; simp⟩
      obtain ⟨i, hi, hb⟩ := closed_mem π _ hcl hab ⟨n, le_rfl, h⟩
      rcases Nat.lt_or_ge i n with hlt | hge
      · exact (hmin i hlt).2 hb
      · have : i = n := le_antisymm hi hge
        rw [this, h] at hb; exact hne hb
    · exact h
  refine ⟨n, hhit, hmin, fun y => ⟨fun hy => ?_, fun ⟨i, hi, hy⟩ => ?_⟩⟩
  · have hcl : ∀ z, (∃ i ≤ n, (π ^ i) (π a) = z) →
        ∃ i ≤ n, (π ^ i) (π a) = (π * swap a b) z := by
      rintro z ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i n with hlt | hge
      · refine ⟨i + 1, by omega, ?_⟩
        rw [mulswap_of_ne π (hmin i hlt).1 (hmin i hlt).2, pow_succ', Perm.mul_apply]
      · have : i = n := le_antisymm hi hge
        subst this
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [hhit, Perm.mul_apply, swap_apply_right]; simp
    exact closed_mem _ _ hcl hy ⟨n, le_rfl, hhit⟩
  · subst hy
    have hw := walk π a b (π a) i (fun j hj => hmin j (by omega))
    have h2 : (π * swap a b) b = π a := by rw [Perm.mul_apply, swap_apply_right]
    have h3 : SameCycle (π * swap a b) b (π a) := by rw [← h2]; exact sc_apply _ b
    exact h3.trans (sc_of_nat i hw)

/-- split: `a` and `b` end up in different cycles -/
theorem split_sep (π : Perm α) {a b : α} (hab : SameCycle π a b) (hne : a ≠ b) :
    ¬ SameCycle (π * swap a b) a b := by
  obtain ⟨n, hhit, hmin, hcls⟩ := split_class π hab hne
  intro h
  obtain ⟨i, hi, ha⟩ := (hcls a).mp h.symm
  rcases Nat.lt_or_ge i n with hlt | hge
  · exact (hmin i hlt).1 ha
  · have : i = n := le_antisymm hi hge
    subst this
    exact hne (ha.symm.trans hhit)

/-- counting: if the cycles of `ρ` refine those of `π` and only the `π`-cycle of `a ~ b`
splits, into the `ρ`-cycles of `a` and `b`, then `ρ` has one more cycle -/
theorem norb_split_aux (π ρ : Perm α) {a b : α}
    (hts : ∀ x y, SameCycle ρ x y → SameCycle π x y)
    (hsab : SameCycle π a b) (htab : ¬ SameCycle ρ a b)
    (hcl : ∀ x y, SameCycle π x y → SameCycle ρ x y ∨ (SameCycle ρ x a ∧ SameCycle ρ y b) ∨
      (SameCycle ρ x b ∧ SameCycle ρ y a)) :
    norb ρ = norb π + 1 := by
  classical
  let f : Quotient (SameCycle.setoid ρ) → Option (Quotient (SameCycle.setoid π)) :=
    Quotient.lift (fun x => if SameCycle ρ x b then none else some (Quotient.mk _ x)) (by
      intro x y hxy
      have hxy' : SameCycle ρ x y := hxy
      by_cases hx : SameCycle ρ x b
      · have hy : SameCycle ρ y b := hxy'.symm.trans hx
        simp only [hx, hy, if_true]
      · have hy : ¬ SameCycle ρ y b := fun hy => hx (hxy'.trans hy)
        simp only [hx, hy, if_false, Option.some.injEq]
        exact Quotient.sound (hts x y hxy'))
  have hf : ∀ x, f (Quotient.mk _ x) =
      if SameCycle ρ x b then none else some (Quotient.mk _ x) := fun x => rfl
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      obtain ⟨x, rfl⟩ := Quotient.exists_rep p
      obtain ⟨y, rfl⟩ := Quotient.exists_rep q
      rw [hf, hf] at hpq
      apply Quotient.sound
      show SameCycle ρ x y
      by_cases hx : SameCycle ρ x b <;> by_cases hy : SameCycle ρ y b
      · exact hx.trans hy.symm
      · rw [if_pos hx, if_neg hy] at hpq; cases hpq
      · rw [if_neg hx, if_pos hy] at hpq; cases hpq
      · rw [if_neg hx, if_neg hy, Option.some.injEq] at hpq
        have hs : SameCycle π x y := Quotient.exact hpq
        rcases hcl x y hs with h | ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hy
        · exact absurd h hx
    · intro o
      cases o with
      | none => exact ⟨Quotient.mk _ b, by rw [hf, if_pos SameCycle.rfl]⟩
      | some q =>
        obtain ⟨x, rfl⟩ := Quotient.exists_rep q
        by_cases hx : SameCycle ρ x b
        · refine ⟨Quotient.mk _ a, ?_⟩
          rw [hf, if_neg htab, Option.some.injEq]
          exact Quotient.sound (show SameCycle π a x from hsab.trans (hts x b hx).symm)
        · exact ⟨Quotient.mk _ x, by rw [hf, if_neg hx]⟩
  unfold norb
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Finite.card_option]

/-- a point of the `π`-cycle of `a` reaches `a` or `b` first, along the same walk in `ρ` -/
theorem split_side (π : Perm α) {a b z : α} (hz : SameCycle π z a) :
    SameCycle (π * swap a b) z a ∨ SameCycle (π * swap a b) z b := by
  classical
  have hex : ∃ m : ℕ, (π ^ m) z = a ∨ (π ^ m) z = b :=
    let ⟨m, hm⟩ := hz.exists_nat_pow_eq; ⟨m, Or.inl hm⟩
  have hw := walk π a b z (Nat.find hex) (fun i hi => by
    have := Nat.find_min hex hi
    exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩)
  rcases Nat.find_spec hex with h | h
  · rw [h] at hw; exact Or.inl (sc_of_nat _ hw)
  · rw [h] at hw; exact Or.inr (sc_of_nat _ hw)

/-- split count -/
theorem norb_split (π : Perm α) {a b : α} (hab : SameCycle π a b) (hne : a ≠ b) :
    norb (π * swap a b) = norb π + 1 := by
  apply norb_split_aux π (π * swap a b) (fun x y h => refine_of_same π hab h) hab
    (split_sep π hab hne)
  intro x y hxy
  by_cases hx : SameCycle π x a
  · have hy : SameCycle π y a := hxy.symm.trans hx
    rcases split_side π (b := b) hx with h1 | h1 <;> rcases split_side π (b := b) hy with h2 | h2
    · exact Or.inl (h1.trans h2.symm)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inl (h1.trans h2.symm)
  · left
    obtain ⟨m, rfl⟩ := hxy.exists_nat_pow_eq
    refine sc_of_nat m (walk π a b x m (fun i _ => ⟨fun h => hx ?_, fun h => hx ?_⟩))
    · rw [← h]; exact sameCycle_pow_right.mpr SameCycle.rfl
    · have : SameCycle π x b := by rw [← h]; exact sameCycle_pow_right.mpr SameCycle.rfl
      exact this.trans hab.symm

/-- merge count -/
theorem norb_merge (π : Perm α) {a b : α} (hab : ¬ SameCycle π a b) :
    norb (π * swap a b) + 1 = norb π := by
  symm
  apply norb_split_aux (π * swap a b) π (fun x y h => merge_coarsen π hab h)
    (merge_join π hab) hab
  intro x y hxy
  rcases merge_classes π hxy with h | ⟨h1 | h1, h2 | h2⟩
  · exact Or.inl h
  · exact Or.inl (h1.trans h2.symm)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inl (h1.trans h2.symm)

theorem mul_swap_self (π : Perm α) (a : α) : π * swap a a = π := by
  ext x; simp

theorem norb_swap_le (π : Perm α) (a b : α) : norb (π * swap a b) ≤ norb π + 1 := by
  by_cases hne : a = b
  · subst hne; rw [mul_swap_self]; omega
  · by_cases hab : SameCycle π a b
    · rw [norb_split π hab hne]
    · have := norb_merge π hab; omega

/-- product of the transpositions of a list of pairs -/
def sprod (L : List (α × α)) : Perm α := (L.map fun p => swap p.1 p.2).prod

theorem sprod_nil : sprod ([] : List (α × α)) = 1 := rfl

theorem sprod_cons (p : α × α) (L : List (α × α)) :
    sprod (p :: L) = swap p.1 p.2 * sprod L := by
  simp [sprod]

theorem norb_list_le (π : Perm α) (L : List (α × α)) :
    norb (π * sprod L) ≤ norb π + L.length := by
  induction L generalizing π with
  | nil => simp [sprod_nil]
  | cons p L ih =>
    rw [sprod_cons, ← mul_assoc]
    have h1 := ih (π * swap p.1 p.2)
    have h2 := norb_swap_le π p.1 p.2
    simp only [List.length_cons]
    omega

/-- if a list of transpositions raises the cycle count by its length, its first pair is a split
and the rest again raises by its length -/
theorem list_max_head (π : Perm α) (p : α × α) (L : List (α × α))
    (h : norb π + (L.length + 1) ≤ norb (π * sprod (p :: L))) :
    SameCycle π p.1 p.2 ∧ p.1 ≠ p.2 ∧
      norb (π * swap p.1 p.2) + L.length ≤ norb ((π * swap p.1 p.2) * sprod L) := by
  rw [sprod_cons, ← mul_assoc] at h
  have h1 := norb_list_le (π * swap p.1 p.2) L
  have hne : p.1 ≠ p.2 := by
    intro e
    rw [e, mul_swap_self] at h1 h
    omega
  have hs : SameCycle π p.1 p.2 := by
    by_contra hab
    have := norb_merge π hab
    omega
  refine ⟨hs, hne, ?_⟩
  rw [norb_split π hs hne] at h1 ⊢
  omega

/-- along a list of splits, the final cycles refine the initial ones -/
theorem list_max_refine (π : Perm α) (L : List (α × α))
    (h : norb π + L.length ≤ norb (π * sprod L)) {x y : α}
    (hxy : SameCycle (π * sprod L) x y) : SameCycle π x y := by
  induction L generalizing π with
  | nil => simpa [sprod_nil] using hxy
  | cons p L ih =>
    obtain ⟨hs, _, h'⟩ := list_max_head π p L h
    rw [sprod_cons, ← mul_assoc] at hxy
    exact refine_of_same π hs (ih _ h' hxy)

/-! ### positions along one cycle -/

theorem exists_ret (π : Perm α) (y0 : α) : ∃ i : ℕ, 0 < i ∧ (π ^ i) y0 = y0 :=
  ⟨orderOf π, orderOf_pos π, by rw [pow_orderOf_eq_one]; rfl⟩

/-- the length of the cycle through `y0` -/
noncomputable def per (π : Perm α) (y0 : α) : ℕ := by
  classical exact Nat.find (exists_ret π y0)

theorem per_spec (π : Perm α) (y0 : α) : 0 < per π y0 ∧ (π ^ per π y0) y0 = y0 := by
  classical
  unfold per
  convert Nat.find_spec (exists_ret π y0)

theorem per_min (π : Perm α) (y0 : α) {i : ℕ} (hi : i < per π y0) (h0 : 0 < i) :
    (π ^ i) y0 ≠ y0 := by
  classical
  intro h
  have hlt : i < Nat.find (exists_ret π y0) := by
    unfold per at hi; convert hi
  exact Nat.find_min (exists_ret π y0) hlt ⟨h0, h⟩

theorem pow_per_mul (π : Perm α) (y0 : α) (q : ℕ) : (π ^ (per π y0 * q)) y0 = y0 := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add, Perm.mul_apply, (per_spec π y0).2, ih]

theorem pow_mod_per (π : Perm α) (y0 : α) (i : ℕ) :
    (π ^ i) y0 = (π ^ (i % per π y0)) y0 := by
  conv_lhs => rw [← Nat.mod_add_div i (per π y0)]
  rw [pow_add, Perm.mul_apply, pow_per_mul]

theorem pow_inj_lt (π : Perm α) (y0 : α) {i j : ℕ} (hi : i < per π y0) (hj : j < per π y0)
    (h : (π ^ i) y0 = (π ^ j) y0) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have e : (π ^ j) y0 = (π ^ i) ((π ^ (j - i)) y0) := by
      rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e] at h
    exact per_min π y0 (by omega) (by omega) ((π ^ i).injective h).symm
  · have e : (π ^ i) y0 = (π ^ j) ((π ^ (i - j)) y0) := by
      rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e] at h
    exact per_min π y0 (by omega) (by omega) ((π ^ j).injective h)

theorem exists_pos (π : Perm α) {y0 y : α} (h : SameCycle π y0 y) :
    ∃ i < per π y0, (π ^ i) y0 = y := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact ⟨i % per π y0, Nat.mod_lt _ (per_spec π y0).1, (pow_mod_per π y0 i).symm⟩

theorem pow_shift (π : Perm α) (y0 : α) (i t : ℕ) :
    (π ^ t) (π ((π ^ i) y0)) = (π ^ (i + 1 + t)) y0 := by
  have e1 : π ((π ^ i) y0) = (π ^ (i + 1)) y0 := by rw [pow_succ', Perm.mul_apply]
  rw [e1, ← Perm.mul_apply, ← pow_add, Nat.add_comm t]

/-- splitting a cycle at positions `i < j`: the new cycle of the later point is the arc `(i, j]` -/
theorem split_interval (π : Perm α) (y0 : α) {i j : ℕ} (hij : i < j) (hj : j < per π y0)
    (y : α) :
    SameCycle (π * swap ((π ^ i) y0) ((π ^ j) y0)) ((π ^ j) y0) y ↔
      ∃ l, i < l ∧ l ≤ j ∧ (π ^ l) y0 = y := by
  have hab : SameCycle π ((π ^ i) y0) ((π ^ j) y0) :=
    (sameCycle_pow_left.mpr SameCycle.rfl).trans (sameCycle_pow_right.mpr SameCycle.rfl)
  have hne : (π ^ i) y0 ≠ (π ^ j) y0 := fun h =>
    absurd (pow_inj_lt π y0 (by omega) hj h) (by omega)
  obtain ⟨n, hhit, hmin, hcls⟩ := split_class π hab hne
  have hn : n = j - i - 1 := by
    rcases Nat.lt_trichotomy n (j - i - 1) with h | h | h
    · rw [pow_shift] at hhit
      have := pow_inj_lt π y0 (by omega) hj hhit
      omega
    · exact h
    · have := (hmin (j - i - 1) h).2
      rw [pow_shift] at this
      exact absurd (by congr 2; omega) this
  rw [hcls y]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨i + 1 + t, by omega, by omega, (pow_shift π y0 i t).symm⟩
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l - i - 1, by omega, by rw [pow_shift]; congr 2; omega⟩

/-! ### lists of disjoint pairs act as a partner involution -/

def flat (L : List (α × α)) : List α := L.flatMap fun p => [p.1, p.2]

theorem mem_flat {L : List (α × α)} {x : α} : x ∈ flat L ↔ ∃ p ∈ L, x = p.1 ∨ x = p.2 := by
  unfold flat
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

theorem flat_cons (p : α × α) (L : List (α × α)) : flat (p :: L) = p.1 :: p.2 :: flat L := by
  simp [flat]

theorem flat_append (L M : List (α × α)) : flat (L ++ M) = flat L ++ flat M := by
  simp [flat]

theorem sprod_append (L M : List (α × α)) : sprod (L ++ M) = sprod L * sprod M := by
  simp [sprod, List.prod_append]

theorem sprod_apply_f (f : α → α) (hf : Function.Involutive f) (L : List (α × α))
    (hpair : ∀ p ∈ L, p.2 = f p.1) (hnd : (flat L).Nodup) (x : α) :
    sprod L x = if x ∈ flat L then f x else x := by
  induction L with
  | nil => simp [sprod_nil, flat]
  | cons p L ih =>
    rw [flat_cons] at hnd ⊢
    have hp := hpair p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hpair q (List.mem_cons_of_mem _ hq)) hnd.of_cons.of_cons
    have h1 : p.1 ∉ p.2 :: flat L := (List.nodup_cons.mp hnd).1
    have h2 : p.2 ∉ flat L := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    have h1' : p.1 ∉ flat L := fun h => h1 (List.mem_cons_of_mem _ h)
    have hcl : ∀ y ∈ flat L, f y ∈ flat L := by
      intro y hy
      obtain ⟨q, hq, hy'⟩ := mem_flat.mp hy
      have := hpair q (List.mem_cons_of_mem _ hq)
      rcases hy' with rfl | rfl
      · exact mem_flat.mpr ⟨q, hq, Or.inr this.symm⟩
      · exact mem_flat.mpr ⟨q, hq, Or.inl (by rw [this, hf])⟩
    rw [sprod_cons, Perm.mul_apply, ih']
    by_cases hx : x ∈ flat L
    · have hfx := hcl x hx
      have n1 : f x ≠ p.1 := fun e => h1' (by rw [← e]; exact hfx)
      have n2 : f x ≠ p.2 := fun e => h2 (by rw [← e]; exact hfx)
      rw [if_pos hx, swap_apply_of_ne_of_ne n1 n2,
        if_pos (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))]
    · rw [if_neg hx]
      by_cases hx1 : x = p.1
      · subst hx1
        rw [swap_apply_left, if_pos (List.mem_cons_self ..)]
        exact hp
      · by_cases hx2 : x = p.2
        · subst hx2
          rw [swap_apply_right, if_pos (List.mem_cons_of_mem _ (List.mem_cons_self ..)), hp]
          exact (hf p.1).symm
        · rw [swap_apply_of_ne_of_ne hx1 hx2, if_neg]
          simp [hx, hx1, hx2]

/-- class functions -/
theorem pres_swap {β : Type} (π : Perm α) (κ : α → β) (h : ∀ x, κ (π x) = κ x) {a b : α}
    (hab : κ a = κ b) (x : α) : κ ((π * swap a b) x) = κ x := by
  rw [Perm.mul_apply, h]
  by_cases hxa : x = a
  · rw [hxa, swap_apply_left]; exact hab.symm
  · by_cases hxb : x = b
    · rw [hxb, swap_apply_right]; exact hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

theorem not_sc_of_kappa {β : Type} (π : Perm α) (κ : α → β) (h : ∀ x, κ (π x) = κ x) {a b : α}
    (hab : κ a ≠ κ b) : ¬ SameCycle π a b := by
  intro hs
  have := (pres π (fun z => κ z = κ a) (fun z => by simp only [h]) hs).mpr rfl
  exact hab this.symm

theorem pres_coarsen {β γ : Type} (π : Perm α) (κ : α → β) (κ' : α → γ)
    (h : ∀ x, κ (π x) = κ x) (hc : ∀ x y, κ x = κ y → κ' x = κ' y) (x : α) :
    κ' (π x) = κ' x := hc _ _ (h x)

/-! ### partner involutions on a set -/

/-- the involution swapping `x ↔ f x` on `C` -/
def pfFun (f : α → α) (C : Finset α) (x : α) : α := if x ∈ C ∧ f x ∈ C then f x else x

theorem pfFun_invol (f : α → α) (hf : Function.Involutive f) (C : Finset α) :
    Function.Involutive (pfFun f C) := by
  intro x
  unfold pfFun
  by_cases h : x ∈ C ∧ f x ∈ C
  · rw [if_pos h, hf x, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg h]

def PF (f : α → α) (hf : Function.Involutive f) (C : Finset α) : Perm α :=
  (pfFun_invol f hf C).toPerm _

theorem PF_apply (f : α → α) (hf : Function.Involutive f) (C : Finset α) (x : α) :
    PF f hf C x = pfFun f C x := rfl

theorem PF_empty (f : α → α) (hf : Function.Involutive f) : PF f hf ∅ = 1 := by
  ext x; simp [PF_apply, pfFun]

theorem PF_mul_self (f : α → α) (hf : Function.Involutive f) (C : Finset α) :
    PF f hf C * PF f hf C = 1 := by
  ext x; simp [Perm.mul_apply, PF_apply, pfFun_invol f hf C x]

theorem PF_decomp (f : α → α) (hf : Function.Involutive f) (C : Finset α) {x0 : α}
    (h0 : x0 ∈ C) (h1 : f x0 ∈ C) (hne : x0 ≠ f x0) :
    PF f hf C = swap x0 (f x0) * PF f hf ((C.erase x0).erase (f x0)) := by
  ext x
  rw [Perm.mul_apply, PF_apply, PF_apply]
  unfold pfFun
  by_cases hx0 : x = x0
  · subst hx0
    simp [h0, h1, hne]
  · by_cases hx1 : x = f x0
    · subst hx1
      have : f (f x0) = x0 := hf x0
      simp [h0, h1, hne, this]
    · have hfx0 : f x ≠ x0 := fun e => hx1 (by rw [← e, hf])
      have hfx1 : f x ≠ f x0 := fun e => hx0 (hf.injective e)
      by_cases hc : x ∈ C ∧ f x ∈ C
      · have hc' : x ∈ (C.erase x0).erase (f x0) ∧ f x ∈ (C.erase x0).erase (f x0) := by
          simp [hc.1, hc.2, hx0, hx1, hfx0, hfx1]
        rw [if_pos hc, if_pos hc', swap_apply_of_ne_of_ne hfx0 hfx1]
      · have hc' : ¬ (x ∈ (C.erase x0).erase (f x0) ∧ f x ∈ (C.erase x0).erase (f x0)) := by
          intro h; apply hc
          simp only [Finset.mem_erase] at h
          exact ⟨h.1.2.2, h.2.2.2⟩
        rw [if_neg hc, if_neg hc', swap_apply_of_ne_of_ne hx0 hx1]

/-- a closed, fixed-point-free partner set raises the cycle count by at most half its size -/
theorem PF_le (f : α → α) (hf : Function.Involutive f) :
    ∀ (n : ℕ) (C : Finset α), C.card = n → (∀ x ∈ C, f x ∈ C) → (∀ x ∈ C, f x ≠ x) →
      ∀ π : Perm α, 2 * norb (π * PF f hf C) ≤ 2 * norb π + C.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hC hcl hfp π
    rcases C.eq_empty_or_nonempty with he | ⟨x0, hx0⟩
    · subst he; simp [PF_empty]
    · have h1 := hcl x0 hx0
      have hne : x0 ≠ f x0 := fun e => hfp x0 hx0 e.symm
      set C' := (C.erase x0).erase (f x0) with hC'
      have hcard : C'.card + 2 = C.card := by
        rw [hC', Finset.card_erase_of_mem (by simp [h1, hne.symm]), Finset.card_erase_of_mem hx0]
        have : 2 ≤ C.card := by
          have : ({x0, f x0} : Finset α) ⊆ C := by
            intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
          have h2 := Finset.card_le_card this
          rwa [Finset.card_pair hne] at h2
        omega
      have hcl' : ∀ x ∈ C', f x ∈ C' := by
        intro x hx
        simp only [hC', Finset.mem_erase] at hx ⊢
        refine ⟨fun e => hx.2.1 (by rw [← hf x, e, hf x0]), fun e => hx.1 (by rw [← hf x, e]),
          hcl x hx.2.2⟩
      have hfp' : ∀ x ∈ C', f x ≠ x := fun x hx => hfp x (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hx))
      have := ih C'.card (by omega) C' rfl hcl' hfp' (π * swap x0 (f x0))
      rw [PF_decomp f hf C hx0 h1 hne, ← mul_assoc, ← hC']
      have h2 := norb_swap_le π x0 (f x0)
      omega

/-- if the bound is attained, every partner pair is a split, in any order -/
theorem PF_max_head (f : α → α) (hf : Function.Involutive f) (C : Finset α)
    (hcl : ∀ x ∈ C, f x ∈ C) (hfp : ∀ x ∈ C, f x ≠ x) (π : Perm α)
    (hmax : 2 * norb π + C.card ≤ 2 * norb (π * PF f hf C)) {x0 : α} (hx0 : x0 ∈ C) :
    SameCycle π x0 (f x0) ∧
      2 * norb (π * swap x0 (f x0)) + ((C.erase x0).erase (f x0)).card ≤
        2 * norb (π * swap x0 (f x0) * PF f hf ((C.erase x0).erase (f x0))) := by
  have h1 := hcl x0 hx0
  have hne : x0 ≠ f x0 := fun e => hfp x0 hx0 e.symm
  set C' := (C.erase x0).erase (f x0) with hC'
  have hcard : C'.card + 2 = C.card := by
    rw [hC', Finset.card_erase_of_mem (by simp [h1, hne.symm]), Finset.card_erase_of_mem hx0]
    have : 2 ≤ C.card := by
      have : ({x0, f x0} : Finset α) ⊆ C := by
        intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
      have h2 := Finset.card_le_card this
      rwa [Finset.card_pair hne] at h2
    omega
  have hcl' : ∀ x ∈ C', f x ∈ C' := by
    intro x hx
    simp only [hC', Finset.mem_erase] at hx ⊢
    refine ⟨fun e => hx.2.1 (by rw [← hf x, e, hf x0]), fun e => hx.1 (by rw [← hf x, e]),
      hcl x hx.2.2⟩
  have hfp' : ∀ x ∈ C', f x ≠ x := fun x hx => hfp x (Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hx))
  rw [PF_decomp f hf C hx0 h1 hne, ← mul_assoc, ← hC'] at hmax
  have hle := PF_le f hf _ C' rfl hcl' hfp' (π * swap x0 (f x0))
  have hs : SameCycle π x0 (f x0) := by
    by_contra hab
    have := norb_merge π hab
    omega
  refine ⟨hs, ?_⟩
  have := norb_split π hs hne
  omega

theorem PF_max_refine (f : α → α) (hf : Function.Involutive f) :
    ∀ (n : ℕ) (C : Finset α), C.card = n → (∀ x ∈ C, f x ∈ C) → (∀ x ∈ C, f x ≠ x) →
      ∀ π : Perm α, 2 * norb π + C.card ≤ 2 * norb (π * PF f hf C) →
      ∀ y z, SameCycle (π * PF f hf C) y z → SameCycle π y z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hC hcl hfp π hmax y z hyz
    rcases C.eq_empty_or_nonempty with he | ⟨x0, hx0⟩
    · subst he; simpa [PF_empty] using hyz
    · obtain ⟨hs, hmax'⟩ := PF_max_head f hf C hcl hfp π hmax hx0
      have h1 := hcl x0 hx0
      have hne : x0 ≠ f x0 := fun e => hfp x0 hx0 e.symm
      rw [PF_decomp f hf C hx0 h1 hne, ← mul_assoc] at hyz
      have hlt : ((C.erase x0).erase (f x0)).card < n := by
        rw [← hC]
        exact lt_of_le_of_lt (Finset.card_erase_le) (Finset.card_erase_lt_of_mem hx0)
      have hcl' : ∀ x ∈ (C.erase x0).erase (f x0), f x ∈ (C.erase x0).erase (f x0) := by
        intro x hx
        simp only [Finset.mem_erase] at hx ⊢
        refine ⟨fun e => hx.2.1 (by rw [← hf x, e, hf x0]), fun e => hx.1 (by rw [← hf x, e]),
          hcl x hx.2.2⟩
      have hfp' : ∀ x ∈ (C.erase x0).erase (f x0), f x ≠ x := fun x hx => hfp x
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      exact refine_of_same π hs (ih _ hlt _ rfl hcl' hfp' _ hmax' y z hyz)

theorem norb_ge_three (π : Perm α) {a b c : α} (hab : ¬ SameCycle π a b)
    (hac : ¬ SameCycle π a c) (hbc : ¬ SameCycle π b c) : 3 ≤ norb π := by
  classical
  unfold norb
  rw [Nat.card_eq_fintype_card]
  have : ({Quotient.mk (SameCycle.setoid π) a, Quotient.mk (SameCycle.setoid π) b,
      Quotient.mk (SameCycle.setoid π) c} : Finset (Quotient (SameCycle.setoid π))).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h; exact hbc (Quotient.exact h)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hab (Quotient.exact h)
      · exact hac (Quotient.exact h)
  rw [← this]
  exact Finset.card_le_univ _

theorem erase2_closed (f : α → α) (hf : Function.Involutive f) (C : Finset α)
    (hcl : ∀ x ∈ C, f x ∈ C) (x0 : α) :
    ∀ x ∈ (C.erase x0).erase (f x0), f x ∈ (C.erase x0).erase (f x0) := by
  intro x hx
  simp only [Finset.mem_erase] at hx ⊢
  exact ⟨fun e => hx.2.1 (by rw [← hf x, e, hf x0]), fun e => hx.1 (by rw [← hf x, e]),
    hcl x hx.2.2⟩

theorem erase2_fp (f : α → α) (C : Finset α) (hfp : ∀ x ∈ C, f x ≠ x) (x0 : α) :
    ∀ x ∈ (C.erase x0).erase (f x0), f x ≠ x := fun x hx =>
  hfp x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))

/-- maximal partner sets are non-crossing along a cycle -/
theorem no_cross (f : α → α) (hf : Function.Involutive f) (C : Finset α)
    (hcl : ∀ x ∈ C, f x ∈ C) (hfp : ∀ x ∈ C, f x ≠ x) (π : Perm α)
    (hmax : 2 * norb π + C.card ≤ 2 * norb (π * PF f hf C)) (y0 : α) {i j k l : ℕ}
    (hik : i < k) (hkj : k < j) (hjl : j < l) (hl : l < per π y0)
    (h0 : (π ^ i) y0 ∈ C) (hf0 : f ((π ^ i) y0) = (π ^ j) y0)
    (h1 : (π ^ k) y0 ∈ C) (hf1 : f ((π ^ k) y0) = (π ^ l) y0) : False := by
  obtain ⟨_, hmax'⟩ := PF_max_head f hf C hcl hfp π hmax h0
  have hk0 : (π ^ k) y0 ≠ (π ^ i) y0 := fun e =>
    absurd (pow_inj_lt π y0 (by omega) (by omega) e) (by omega)
  have hk1 : (π ^ k) y0 ≠ f ((π ^ i) y0) := by
    rw [hf0]; exact fun e => absurd (pow_inj_lt π y0 (by omega) (by omega) e) (by omega)
  have h1' : (π ^ k) y0 ∈ (C.erase ((π ^ i) y0)).erase (f ((π ^ i) y0)) := by
    simp only [Finset.mem_erase]; exact ⟨hk1, hk0, h1⟩
  obtain ⟨hs1, _⟩ := PF_max_head f hf _ (erase2_closed f hf C hcl _) (erase2_fp f C hfp _) _
    hmax' h1'
  rw [hf0, hf1] at hs1
  have hcls := split_interval π y0 (i := i) (j := j) (by omega) (by omega)
  have ha : SameCycle (π * swap ((π ^ i) y0) ((π ^ j) y0)) ((π ^ j) y0) ((π ^ k) y0) :=
    (hcls _).mpr ⟨k, hik, hkj.le, rfl⟩
  obtain ⟨l', hl1, hl2, hl3⟩ := (hcls _).mp (ha.trans hs1)
  have := pow_inj_lt π y0 (by omega) hl hl3
  omega

/-! ### the face permutation of an embedding scheme -/

section map

open PlanarQueue.Genus SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def sigFun (S : EmbeddingScheme G) (x : G.Dart × Bool) : G.Dart × Bool :=
  (if x.2 then S.rot⁻¹ x.1 else S.rot x.1, x.2)

def sigInv (S : EmbeddingScheme G) (x : G.Dart × Bool) : G.Dart × Bool :=
  (if x.2 then S.rot x.1 else S.rot⁻¹ x.1, x.2)

/-- the vertex rotations on both sheets -/
def SigP (S : EmbeddingScheme G) : Perm (G.Dart × Bool) where
  toFun := sigFun S
  invFun := sigInv S
  left_inv x := by rcases x with ⟨d, _ | _⟩ <;> simp [sigFun, sigInv]
  right_inv x := by rcases x with ⟨d, _ | _⟩ <;> simp [sigFun, sigInv]

theorem SigP_apply (S : EmbeddingScheme G) (x : G.Dart × Bool) :
    SigP S x = (if x.2 then S.rot⁻¹ x.1 else S.rot x.1, x.2) := rfl

def apFun (S : EmbeddingScheme G) (x : G.Dart × Bool) : G.Dart × Bool :=
  (x.1.symm, xor x.2 (S.sig x.1))

theorem apFun_invol (S : EmbeddingScheme G) : Function.Involutive (apFun S) := by
  rintro ⟨d, s⟩
  simp [apFun, S.sig_symm]

/-- the edge involution -/
def AP (S : EmbeddingScheme G) : Perm (G.Dart × Bool) := (apFun_invol S).toPerm _

theorem AP_apply (S : EmbeddingScheme G) (x : G.Dart × Bool) : AP S x = apFun S x := rfl

theorem faceStep_eq (S : EmbeddingScheme G) (x : G.Dart × Bool) :
    S.faceStep x = (SigP S * AP S) x := by
  rcases x with ⟨d, s⟩
  rw [Perm.mul_apply, AP_apply, SigP_apply]
  simp only [EmbeddingScheme.faceStep, apFun]
  rw [Perm.inv_def]
  by_cases h : (xor s (S.sig d)) = true <;> simp [h]

theorem card_faceOrbit (S : EmbeddingScheme G) :
    Nat.card S.FaceOrbit = norb (SigP S * AP S) := by
  have hit : ∀ n x, S.faceStep^[n] x = ((SigP S * AP S) ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, faceStep_eq, pow_succ']
      rfl
  unfold norb EmbeddingScheme.FaceOrbit
  apply Nat.card_congr
  apply Quot.congrRight
  intro x y
  constructor
  · rintro ⟨n, hn⟩
    rw [hit] at hn
    exact sc_of_nat n hn
  · intro h
    obtain ⟨n, hn⟩ := (h : SameCycle (SigP S * AP S) x y).exists_nat_pow_eq
    exact ⟨n, by rw [hit]; exact hn⟩

theorem rot_inv_fst (S : EmbeddingScheme G) (d : G.Dart) : (S.rot⁻¹ d).fst = d.fst := by
  have := S.rot_fst (S.rot⁻¹ d)
  have e : S.rot (S.rot⁻¹ d) = d := by simp
  rw [e] at this
  exact this.symm

theorem rot_symm_fst (S : EmbeddingScheme G) (d : G.Dart) : (S.rot.symm d).fst = d.fst :=
  rot_inv_fst S d

theorem SigP_pow (S : EmbeddingScheme G) (n : ℕ) (d : G.Dart) (b : Bool) :
    (SigP S ^ n) (d, b) = (if b then (S.rot ^ n)⁻¹ d else (S.rot ^ n) d, b) := by
  induction n with
  | zero => cases b <;> simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, SigP_apply]
    cases b
    · simp [pow_succ']
    · simp [pow_succ, mul_inv_rev]

/-- the cycles of `SigP` are the (vertex, sheet) classes -/
theorem sig_sc (S : EmbeddingScheme G) (x y : G.Dart × Bool) :
    SameCycle (SigP S) x y ↔ x.1.fst = y.1.fst ∧ x.2 = y.2 := by
  constructor
  · intro h
    have := pres (SigP S) (fun z => z.1.fst = x.1.fst ∧ z.2 = x.2) (fun z => by
      rcases z with ⟨d, b⟩
      rw [SigP_apply]
      cases b
      · simp [S.rot_fst]
      · simp [rot_symm_fst]) h
    obtain ⟨h1, h2⟩ := this.mpr ⟨rfl, rfl⟩
    exact ⟨h1.symm, h2.symm⟩
  · rcases x with ⟨d, b⟩
    rcases y with ⟨d', b'⟩
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h2
    cases b
    · obtain ⟨n, hn⟩ := S.rot_cyclic d d' h1
      exact sc_of_nat n (by rw [SigP_pow]; simp [hn])
    · obtain ⟨n, hn⟩ := S.rot_cyclic d' d h1.symm
      exact sc_of_nat n (by rw [SigP_pow]; simp [← hn])

/-- `SigP` has two cycles per vertex when every vertex has a dart -/
theorem norb_SigP (S : EmbeddingScheme G) (hdeg : ∀ v : V, ∃ d : G.Dart, d.fst = v) :
    norb (SigP S) = 2 * Fintype.card V := by
  classical
  let f : Quotient (SameCycle.setoid (SigP S)) → V × Bool :=
    Quotient.lift (fun x => (x.1.fst, x.2)) (by
      intro x y hxy
      obtain ⟨h1, h2⟩ := (sig_sc S x y).mp hxy
      simp [h1, h2])
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      obtain ⟨x, rfl⟩ := Quotient.exists_rep p
      obtain ⟨y, rfl⟩ := Quotient.exists_rep q
      apply Quotient.sound
      have hpq' : (x.1.fst, x.2) = (y.1.fst, y.2) := hpq
      simp only [Prod.mk.injEq] at hpq'
      exact (sig_sc S x y).mpr hpq'
    · rintro ⟨v, b⟩
      obtain ⟨d, hd⟩ := hdeg v
      exact ⟨Quotient.mk _ (d, b), by simp [f, hd]⟩
  unfold norb
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_bool]
  ring

/-- sheet and growth class -/
def kap (Sv : Finset V) (p : V → Bool) (x : G.Dart × Bool) : Bool × Option V :=
  (xor x.2 (p x.1.fst), if x.1.fst ∈ Sv then none else some x.1.fst)

def treePair (S : EmbeddingScheme G) (p : V → Bool) (d : G.Dart) (b : Bool) :
    (G.Dart × Bool) × (G.Dart × Bool) :=
  ((d, xor b (p d.fst)), apFun S (d, xor b (p d.fst)))

/-- invariant of the spanning-tree growth: `L` lists the tree pairs, every step merged -/
structure GInv (S : EmbeddingScheme G) (r : V) (Sv : Finset V) (TD : Finset G.Dart)
    (L : List ((G.Dart × Bool) × (G.Dart × Bool))) (p : V → Bool) : Prop where
  root : r ∈ Sv
  td_fst : ∀ d ∈ TD, d.fst ∈ Sv
  td_symm : ∀ d ∈ TD, d.symm ∈ TD
  par : ∀ d ∈ TD, p d.snd = xor (p d.fst) (S.sig d)
  pair : ∀ q ∈ L, q.2 = apFun S q.1
  nd : (flat L).Nodup
  cover : ∀ x, x ∈ flat L ↔ x.1 ∈ TD
  len : L.length + 2 = 2 * Sv.card
  kp : ∀ x, kap Sv p ((SigP S * sprod L) x) = kap Sv p x
  cnt : norb (SigP S * sprod L) + L.length = norb (SigP S)

theorem ginv_init (S : EmbeddingScheme G) (r : V) :
    GInv S r {r} ∅ [] (fun _ => false) where
  root := Finset.mem_singleton_self r
  td_fst := by simp
  td_symm := by simp
  par := by simp
  pair := by simp
  nd := by simp [flat]
  cover := by simp [flat]
  len := by simp
  kp := by
    intro x
    rcases x with ⟨d, b⟩
    simp only [sprod_nil, mul_one, SigP_apply, kap]
    cases b <;> simp [S.rot_fst, rot_symm_fst]
  cnt := by simp [sprod_nil]

theorem kap_eq_cases {Sv : Finset V} {p : V → Bool} {x y : G.Dart × Bool}
    (h : kap Sv p x = kap Sv p y) :
    (x.1.fst ∈ Sv ∧ y.1.fst ∈ Sv ∧ xor x.2 (p x.1.fst) = xor y.2 (p y.1.fst)) ∨
      (x.1.fst = y.1.fst ∧ x.2 = y.2) := by
  rcases x with ⟨xd, xb⟩
  rcases y with ⟨yd, yb⟩
  unfold kap at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  by_cases hx : xd.fst ∈ Sv <;> by_cases hy : yd.fst ∈ Sv
  · exact Or.inl ⟨hx, hy, h1⟩
  · rw [if_pos hx, if_neg hy] at h2; cases h2
  · rw [if_neg hx, if_pos hy] at h2; cases h2
  · rw [if_neg hx, if_neg hy] at h2
    have e := Option.some.inj h2
    right
    refine ⟨e, ?_⟩
    simp only at e h1 ⊢
    rw [e] at h1
    revert h1
    cases xb <;> cases yb <;> cases p yd.fst <;> simp

theorem dart_symm_fst (d : G.Dart) : d.symm.fst = d.snd := rfl
theorem dart_symm_snd (d : G.Dart) : d.symm.snd = d.fst := rfl

theorem ginv_step (S : EmbeddingScheme G) {r : V} {Sv : Finset V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool} (I : GInv S r Sv TD L p)
    (d : G.Dart) (hu : d.fst ∈ Sv) (hv : d.snd ∉ Sv) :
    GInv S r (insert d.snd Sv) (insert d (insert d.symm TD))
      (L ++ [treePair S p d false, treePair S p d true])
      (Function.update p d.snd (xor (p d.fst) (S.sig d))) := by
  have huv : d.fst ≠ d.snd := fun e => hv (by rw [← e]; exact hu)
  have hp'u : Function.update p d.snd (xor (p d.fst) (S.sig d)) d.fst = p d.fst :=
    Function.update_of_ne huv _ _
  have hp'v : Function.update p d.snd (xor (p d.fst) (S.sig d)) d.snd = xor (p d.fst) (S.sig d) :=
    Function.update_self _ _ _
  have hTDs : ∀ e ∈ TD, e.snd ∈ Sv := fun e he => by
    have := I.td_fst _ (I.td_symm _ he); rwa [dart_symm_fst] at this
  have hdTD : d ∉ TD := fun h => hv (hTDs d h)
  have hdsTD : d.symm ∉ TD := fun h => hv (by have := I.td_fst _ h; rwa [dart_symm_fst] at this)
  have hpo : ∀ w ∈ Sv, Function.update p d.snd (xor (p d.fst) (S.sig d)) w = p w :=
    fun w hw => Function.update_of_ne (fun e => hv (by rw [← e]; exact hw)) _ _
  have hds : d ≠ d.symm := (SimpleGraph.Dart.symm_ne d).symm
  -- the product
  set π := SigP S * sprod L with hπ
  set q0 := treePair S p d false with hq0
  set q1 := treePair S p d true with hq1
  have hprod : SigP S * sprod (L ++ [q0, q1]) = π * swap q0.1 q0.2 * swap q1.1 q1.2 := by
    rw [sprod_append, sprod_cons, sprod_cons, sprod_nil, hπ]
    simp only [mul_assoc, mul_one]
  set p' := Function.update p d.snd (xor (p d.fst) (S.sig d)) with hp'
  let κ1 : G.Dart × Bool → Bool × Option V := fun x =>
    (xor x.2 (p' x.1.fst), if x.1.fst ∈ Sv ∨ (x.1.fst = d.snd ∧ xor x.2 (p' x.1.fst) = false)
      then none else some x.1.fst)
  have hc01 : ∀ x y, kap Sv p x = kap Sv p y → κ1 x = κ1 y := by
    intro x y hxy
    rcases kap_eq_cases hxy with ⟨hx, hy, hs⟩ | ⟨h1, h2⟩
    · simp only [κ1, hpo _ hx, hpo _ hy, hs, hx, hy, true_or, if_true]
    · simp only [κ1, h1, h2]
  have hc1' : ∀ x y, κ1 x = κ1 y → kap (insert d.snd Sv) p' x = kap (insert d.snd Sv) p' y := by
    intro x y hxy
    simp only [κ1, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    unfold kap
    rw [h1]
    congr 1
    by_cases hx : x.1.fst ∈ Sv ∨ (x.1.fst = d.snd ∧ xor x.2 (p' x.1.fst) = false) <;>
      by_cases hy : y.1.fst ∈ Sv ∨ (y.1.fst = d.snd ∧ xor y.2 (p' y.1.fst) = false)
    · rw [if_pos hx, if_pos hy] at h2
      have hx' : x.1.fst ∈ insert d.snd Sv := by
        rcases hx with hx | ⟨hx, _⟩
        · exact Finset.mem_insert_of_mem hx
        · rw [hx]; exact Finset.mem_insert_self _ _
      have hy' : y.1.fst ∈ insert d.snd Sv := by
        rcases hy with hy | ⟨hy, _⟩
        · exact Finset.mem_insert_of_mem hy
        · rw [hy]; exact Finset.mem_insert_self _ _
      rw [if_pos hx', if_pos hy']
    · rw [if_pos hx, if_neg hy] at h2; cases h2
    · rw [if_neg hx, if_pos hy] at h2; cases h2
    · rw [if_neg hx, if_neg hy] at h2
      rw [Option.some.inj h2]
  have hk1 : ∀ x, κ1 (π x) = κ1 x := pres_coarsen π (kap Sv p) κ1 I.kp hc01
  have e00 : (kap Sv p q0.1).2 = none := by
    simp [kap, hq0, treePair, hu]
  have e02 : (kap Sv p q0.2).2 = some d.snd := by
    simp [kap, hq0, treePair, apFun, dart_symm_fst, hv]
  have hm0 : norb (π * swap q0.1 q0.2) + 1 = norb π :=
    norb_merge π (not_sc_of_kappa π _ I.kp (fun h => by rw [h, e02] at e00; simp at e00))
  have heq1 : κ1 q0.1 = κ1 q0.2 := by
    simp [κ1, hq0, treePair, apFun, dart_symm_fst, hp'u, hp'v, hu, hv]
  have hk1' := pres_swap π κ1 hk1 heq1
  have f11 : (κ1 q1.1).2 = none := by
    simp [κ1, hq1, treePair, hu]
  have f12 : (κ1 q1.2).2 = some d.snd := by
    simp [κ1, hq1, treePair, apFun, dart_symm_fst, hp'v, hv]
  have hm1 : norb (π * swap q0.1 q0.2 * swap q1.1 q1.2) + 1 = norb (π * swap q0.1 q0.2) :=
    norb_merge _ (not_sc_of_kappa _ κ1 hk1' (fun h => by rw [h, f12] at f11; simp at f11))
  have heq' : kap (insert d.snd Sv) p' q1.1 = kap (insert d.snd Sv) p' q1.2 := by
    simp [kap, hq1, treePair, apFun, dart_symm_fst, hp'u, hp'v, hu]
  have hk' := pres_swap _ _ (pres_coarsen _ κ1 _ hk1' hc1') heq'
  refine ⟨Finset.mem_insert_of_mem I.root, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_of_mem hu
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (I.td_fst e he)
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    rcases Finset.mem_insert.mp he with rfl | he
    · rw [SimpleGraph.Dart.symm_symm]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (I.td_symm e he))
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · rw [hp'v, hp'u]
    rcases Finset.mem_insert.mp he with rfl | he
    · rw [dart_symm_snd, dart_symm_fst, hp'u, hp'v, S.sig_symm]; simp
    · rw [hpo _ (hTDs e he), hpo _ (I.td_fst e he)]; exact I.par e he
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact I.pair q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
  · rw [flat_append, List.nodup_append]
    refine ⟨I.nd, ?_, ?_⟩
    · simp [flat, hq0, hq1, treePair, apFun, hds, hds.symm]
    · intro a ha b hb hab
      subst hab
      have : a.1 ∈ TD := (I.cover a).mp ha
      simp [flat, hq0, hq1, treePair, apFun] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact hdTD this
      · exact hdsTD this
      · exact hdTD this
      · exact hdsTD this
  · intro x
    rcases x with ⟨e, b⟩
    rw [flat_append, List.mem_append, I.cover]
    simp only [flat, hq0, hq1, treePair, apFun, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      Finset.mem_insert]
    by_cases h1 : e = d
    · subst h1; simp only [true_and, true_or, iff_true, hds]
      cases b <;> cases p e.fst <;> simp
    · by_cases h2 : e = d.symm
      · subst h2
        simp only [h1, false_and, false_or, true_and, or_true, iff_true]
        cases b <;> cases p d.fst <;> cases S.sig d <;> simp
      · simp [h1, h2]
  · simp only [List.length_append, List.length_cons, List.length_nil]
    rw [Finset.card_insert_of_notMem hv]
    have := I.len
    omega
  · intro x
    rw [hprod]
    exact hk' x
  · rw [hprod]
    have := I.cnt
    rw [← hπ] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
    omega

theorem exists_out_dart (hconn : G.Connected) {Sv : Finset V} {r v : V} (hr : r ∈ Sv)
    (hv : v ∉ Sv) : ∃ d : G.Dart, d.fst ∈ Sv ∧ d.snd ∉ Sv := by
  obtain ⟨w⟩ := hconn.preconnected r v
  obtain ⟨d, _, h1, h2⟩ := w.exists_boundary_dart (↑Sv) (by simpa using hr) (by simpa using hv)
  exact ⟨d, by simpa using h1, by simpa using h2⟩

theorem ginv_full (S : EmbeddingScheme G) (hconn : G.Connected) (r : V) :
    ∃ TD L p, GInv S r Finset.univ TD L p := by
  have key : ∀ k : ℕ, ∀ (Sv : Finset V) TD L p, GInv S r Sv TD L p →
      (Finset.univ \ Sv).card = k → ∃ TD' L' p', GInv S r Finset.univ TD' L' p' := by
    intro k
    induction k with
    | zero =>
      intro Sv TD L p I hk
      have : Sv = Finset.univ := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hk
        exact Finset.eq_univ_of_forall fun x => hk (Finset.mem_univ x)
      subst this
      exact ⟨TD, L, p, I⟩
    | succ k ih =>
      intro Sv TD L p I hk
      obtain ⟨v, hv⟩ : ∃ v, v ∉ Sv := by
        by_contra h
        simp only [not_exists, not_not] at h
        have : Finset.univ \ Sv = ∅ := by ext x; simp [h x]
        rw [this] at hk; simp at hk
      obtain ⟨d, h1, h2⟩ := exists_out_dart hconn I.root hv
      refine ih _ _ _ _ (ginv_step S I d h1 h2) ?_
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem (by simp [h2]), hk]
      simp
  exact key _ {r} ∅ [] (fun _ => false) (ginv_init S r) rfl

theorem exists_dart_at (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V) (v : V) :
    ∃ d : G.Dart, d.fst = v := by
  obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (h a).trans (h b).symm)
    omega
  obtain ⟨d, h1, _⟩ := exists_out_dart hconn (Sv := {v}) (Finset.mem_singleton_self v)
    (v := w) (by simpa using hw)
  exact ⟨d, by simpa using h1⟩

theorem length_flat {β : Type} (L : List (β × β)) : (flat L).length = 2 * L.length := by
  induction L with
  | nil => simp [flat]
  | cons p L ih => simp [flat] at ih ⊢; omega

theorem sprod_eq_PF {S : EmbeddingScheme G} {r : V} {Sv : Finset V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool} (I : GInv S r Sv TD L p) :
    sprod L = PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) := by
  refine Equiv.ext fun x => ?_
  rw [sprod_apply_f (apFun S) (apFun_invol S) L I.pair I.nd x, PF_apply]
  unfold pfFun
  have hx : x ∈ flat L ↔ x.1 ∈ TD := I.cover x
  by_cases h : x.1 ∈ TD
  · have h' : (apFun S x).1 ∈ TD := I.td_symm _ h
    rw [if_pos (hx.mpr h), if_pos ⟨Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩,
      Finset.mem_product.mpr ⟨h', Finset.mem_univ _⟩⟩]
  · rw [if_neg (fun h' => h (hx.mp h')), if_neg (fun h' => h (Finset.mem_product.mp h'.1).1)]

theorem AP_eq_PF (S : EmbeddingScheme G) (D : Finset G.Dart) (hD : ∀ d ∈ D, d.symm ∈ D) :
    AP S = PF (apFun S) (apFun_invol S) (D ×ˢ Finset.univ) *
      PF (apFun S) (apFun_invol S) (Dᶜ ×ˢ Finset.univ) := by
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, PF_apply, PF_apply, AP_apply]
  by_cases h : x.1 ∈ D
  · have h' : x.1.symm ∈ D := hD _ h
    have hin : pfFun (apFun S) (Dᶜ ×ˢ Finset.univ) x = x := by
      unfold pfFun; rw [if_neg]; simp [h]
    have hout : pfFun (apFun S) (D ×ˢ Finset.univ) x = apFun S x := by
      unfold pfFun; rw [if_pos]
      exact ⟨Finset.mem_product.mpr ⟨by simpa using h, Finset.mem_univ _⟩,
        Finset.mem_product.mpr ⟨by simpa [apFun] using h', Finset.mem_univ _⟩⟩
    rw [hin, hout]
  · have h' : x.1.symm ∉ D := fun h' => h (by simpa using hD _ h')
    have hin : pfFun (apFun S) (Dᶜ ×ˢ Finset.univ) x = apFun S x := by
      unfold pfFun; rw [if_pos]
      exact ⟨Finset.mem_product.mpr ⟨by simpa using h, Finset.mem_univ _⟩,
        Finset.mem_product.mpr ⟨by simpa [apFun] using h', Finset.mem_univ _⟩⟩
    have hout : pfFun (apFun S) (D ×ˢ Finset.univ) (apFun S x) = apFun S x := by
      unfold pfFun; rw [if_neg]; intro hc
      exact h' (Finset.mem_product.mp hc.1).1
    rw [hin, hout]

theorem card_TD_L {S : EmbeddingScheme G} {r : V} {Sv : Finset V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool} (I : GInv S r Sv TD L p) :
    L.length = TD.card := by
  have h1 := length_flat L
  have h2 : (flat L).toFinset = TD ×ˢ Finset.univ := by
    ext x; simp [I.cover x]
  have h3 := List.toFinset_card_of_nodup I.nd
  rw [h2, Finset.card_product, Finset.card_univ, Fintype.card_bool] at h3
  omega

/-- C1c part 1: on a connected graph with an Euler-genus-0 scheme, all tree pairs and all chord
pairs split (maximal cycle counts) -/
theorem genus0_max (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (hg : S.eulerGenus ≤ 0) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) :
    norb (SigP S * sprod L) = 2 ∧
    SigP S * sprod L * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) = SigP S ∧
    2 * norb (SigP S * sprod L) + (TD ×ˢ (Finset.univ : Finset Bool)).card ≤
      2 * norb (SigP S * sprod L * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ)) ∧
    2 * norb (SigP S * sprod L) + (TDᶜ ×ˢ (Finset.univ : Finset Bool)).card ≤
      2 * norb (SigP S * sprod L * PF (apFun S) (apFun_invol S) (TDᶜ ×ˢ Finset.univ)) := by
  have hdeg := exists_dart_at hconn h2
  have hsig := norb_SigP S hdeg
  have hcnt := I.cnt
  have hlen := I.len
  rw [Finset.card_univ] at hlen
  have hLT := card_TD_L I
  have hψ2 : norb (SigP S * sprod L) = 2 := by omega
  have hsp := sprod_eq_PF I
  have hback : SigP S * sprod L * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) = SigP S := by
    rw [hsp, mul_assoc, PF_mul_self, mul_one]
  have hCT : (TD ×ˢ (Finset.univ : Finset Bool)).card = 2 * TD.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  have hCC : (TDᶜ ×ˢ (Finset.univ : Finset Bool)).card = 2 * (Fintype.card G.Dart - TD.card) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, Finset.card_compl]; ring
  refine ⟨hψ2, hback, ?_, ?_⟩
  · rw [hback, hsig, hψ2, hCT]; omega
  · have hF : SigP S * sprod L * PF (apFun S) (apFun_invol S) (TDᶜ ×ˢ Finset.univ) =
        SigP S * AP S := by
      rw [AP_eq_PF S TD I.td_symm, hsp, mul_assoc]
    rw [hF, ← card_faceOrbit]
    have hc1 : Nat.card G.ConnectedComponent = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      obtain ⟨v⟩ := hconn.nonempty
      refine ⟨G.connectedComponentMk v, fun c => ?_⟩
      refine c.ind (fun w => ?_)
      exact SimpleGraph.ConnectedComponent.eq.mpr (hconn.preconnected w v)
    have hiso : (Finset.univ.filter (fun v => G.degree v = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _ hv0
      obtain ⟨d, hd⟩ := hdeg v
      have := (SimpleGraph.degree_pos_iff_exists_adj (G := G) (v := v)).mpr
        ⟨d.snd, by rw [← hd]; exact d.adj⟩
      omega
    have hm := G.dart_card_eq_twice_card_edges
    unfold EmbeddingScheme.eulerGenus EmbeddingScheme.faces at hg
    rw [hc1, hiso] at hg
    have hTDle : TD.card ≤ Fintype.card G.Dart := Finset.card_le_univ _
    rw [hCC, hψ2]
    push_cast at hg
    omega

/-- the sheet of a point -/
def sh (p : V → Bool) (x : G.Dart × Bool) : Bool := xor x.2 (p x.1.fst)

theorem sheet_pres {S : EmbeddingScheme G} {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (x : G.Dart × Bool) :
    sh p ((SigP S * sprod L) x) = sh p x := by
  have := congrArg Prod.fst (I.kp x)
  simpa [kap, sh] using this

theorem sheet_of_sc {S : EmbeddingScheme G} {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) {x y : G.Dart × Bool}
    (h : SameCycle (SigP S * sprod L) x y) : sh p y = sh p x :=
  (pres _ (fun z => sh p z = sh p x) (fun z => by simp only [sheet_pres I]) h).mpr rfl

/-- the sheet-`false` points form one cycle of `ψ` -/
theorem sheet_cycle (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (hg : S.eulerGenus ≤ 0) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (d0 : G.Dart) (x : G.Dart × Bool) (hx : sh p x = false) :
    SameCycle (SigP S * sprod L) (d0, p d0.fst) x := by
  by_contra hn
  have h0 : sh p (d0, p d0.fst) = false := by simp [sh]
  have hz : sh p (d0, !p d0.fst) = true := by simp [sh]
  have hsep : ∀ u v, sh p u ≠ sh p v → ¬ SameCycle (SigP S * sprod L) u v :=
    fun u v huv => not_sc_of_kappa _ (sh p) (sheet_pres I) huv
  have h3 := norb_ge_three (SigP S * sprod L) (c := (d0, !p d0.fst)) hn
    (hsep (d0, p d0.fst) (d0, !p d0.fst) (by rw [h0, hz]; decide))
    (hsep x (d0, !p d0.fst) (by rw [hx, hz]; decide))
  have h2' := (genus0_max S hconn h2 hg I).1
  omega

theorem CC_closed {TD : Finset G.Dart} (S : EmbeddingScheme G) (hTD : ∀ d ∈ TD, d.symm ∈ TD) :
    ∀ x ∈ TDᶜ ×ˢ (Finset.univ : Finset Bool), apFun S x ∈ TDᶜ ×ˢ (Finset.univ : Finset Bool) := by
  intro x hx
  simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_univ, and_true] at hx ⊢
  intro h
  apply hx
  have := hTD _ h
  simpa [apFun] using this

theorem CT_closed {TD : Finset G.Dart} (S : EmbeddingScheme G) (hTD : ∀ d ∈ TD, d.symm ∈ TD) :
    ∀ x ∈ TD ×ˢ (Finset.univ : Finset Bool), apFun S x ∈ TD ×ˢ (Finset.univ : Finset Bool) := by
  intro x hx
  simp only [Finset.mem_product, Finset.mem_univ, and_true] at hx ⊢
  exact hTD _ hx

theorem apFun_fp (S : EmbeddingScheme G) (C : Finset (G.Dart × Bool)) :
    ∀ x ∈ C, apFun S x ≠ x := by
  intro x _ h
  have := congrArg Prod.fst h
  exact (SimpleGraph.Dart.symm_ne x.1) this

/-- genus 0: every chord is untwisted relative to the tree parity -/
theorem chord_untwisted (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (hg : S.eulerGenus ≤ 0) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (d : G.Dart) (hd : d ∉ TD) :
    p d.snd = xor (p d.fst) (S.sig d) := by
  obtain ⟨_, _, _, hmax⟩ := genus0_max S hconn h2 hg I
  have hmem : ((d, p d.fst) : G.Dart × Bool) ∈ TDᶜ ×ˢ (Finset.univ : Finset Bool) := by
    simp [hd]
  obtain ⟨hs, _⟩ := PF_max_head (apFun S) (apFun_invol S) _ (CC_closed S I.td_symm)
    (apFun_fp S _) _ hmax hmem
  have heq := sheet_of_sc I hs
  simp only [sh, apFun, dart_symm_fst] at heq
  revert heq
  cases p d.fst <;> cases p d.snd <;> cases S.sig d <;> simp

end map

end PQL21

/-! C1 part 2/3 for lemma_21 (e1368385): the abstract dart certificate and the 2-page book
drawing of the dart-subdivided graph `H` on `V ⊕ G.Dart`. -/

namespace PQL21

open SimpleGraph

section cert

variable {V : Type} {G : SimpleGraph V}

/-- `x` lies in the arc `(pos e, pos e.symm]` -/
def inI (pos : G.Dart → ℕ) (e x : G.Dart) : Prop := pos e < pos x ∧ pos x ≤ pos e.symm

/-- dart certificate: contour positions, tree darts `TD`, chords `TDᶜ` -/
structure Cert (G : SimpleGraph V) where
  pos : G.Dart → ℕ
  inj : Function.Injective pos
  TD : Set G.Dart
  symm : ∀ d, d ∈ TD → d.symm ∈ TD
  F2 : ∀ d e, d ∈ TD → e ∈ TD →
    ¬ (pos d < pos e ∧ pos e < pos d.symm ∧ pos d.symm < pos e.symm)
  F3 : ∀ d e, d ∉ TD → e ∉ TD →
    ¬ (pos d < pos e ∧ pos e < pos d.symm ∧ pos d.symm < pos e.symm)
  F4 : ∀ d, d ∈ TD → pos d < pos d.symm → ∀ w : V,
    (∀ x : G.Dart, x.fst = w → inI pos d x) ∨ (∀ x : G.Dart, x.fst = w → ¬ inI pos d x)
  entry : ∀ b : G.Dart, 0 < pos b → (∀ x : G.Dart, x.fst = b.fst → pos b ≤ pos x) →
    ∃ e, e ∈ TD ∧ e.snd = b.fst ∧ pos e < pos b

theorem Cert.exists_min (C : Cert G) {u : V} (a : G.Dart) (ha : a.fst = u) :
    ∃ m : G.Dart, m.fst = u ∧ ∀ x : G.Dart, x.fst = u → C.pos m ≤ C.pos x := by
  classical
  have hex : ∃ n, ∃ x : G.Dart, x.fst = u ∧ C.pos x = n := ⟨_, a, ha, rfl⟩
  obtain ⟨m, hm, hmn⟩ := Nat.find_spec hex
  exact ⟨m, hm, fun x hx => hmn ▸ Nat.find_min' hex ⟨x, hx, rfl⟩⟩

theorem Cert.block (C : Cert G) {v : V} (m : G.Dart) (hm : m.fst = v)
    (hmin : ∀ x : G.Dart, x.fst = v → C.pos m ≤ C.pos x) (h0 : 0 < C.pos m) :
    ∃ e, e ∈ C.TD ∧ e.snd = v ∧ C.pos e < C.pos e.symm ∧
      (∀ x : G.Dart, x.fst = v → inI C.pos e x) ∧
      ∀ w : V, (∀ x : G.Dart, x.fst = w → inI C.pos e x) ∨
        (∀ x : G.Dart, x.fst = w → ¬ inI C.pos e x) := by
  obtain ⟨e, heT, hes, hep⟩ := C.entry m h0 (by rw [hm]; exact hmin)
  have hsymm : e.symm.fst = v := by rw [← hm, ← hes]; rfl
  have hle := hmin _ hsymm
  have hlt : C.pos e < C.pos e.symm := by omega
  refine ⟨e, heT, hes.trans hm, hlt, ?_, C.F4 e heT hlt⟩
  rcases C.F4 e heT hlt v with h | h
  · exact h
  · exact absurd ⟨by omega, hle⟩ (h m hm)

/-- F6: the dart blocks of two distinct vertices do not interleave -/
theorem Cert.F6 (C : Cert G) (a b c d : G.Dart) (hac : a.fst = c.fst) (hbd : b.fst = d.fst)
    (hab : a.fst ≠ b.fst) : ¬ (C.pos a < C.pos b ∧ C.pos b < C.pos c ∧ C.pos c < C.pos d) := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨mu, hmu, hmumin⟩ := C.exists_min a rfl
  obtain ⟨mw, hmw, hmwmin⟩ := C.exists_min b rfl
  have hU : 0 < C.pos mu → ∃ e, e ∈ C.TD ∧ e.snd = a.fst ∧
      (∀ x : G.Dart, x.fst = a.fst → inI C.pos e x) ∧
      (∀ x : G.Dart, x.fst = b.fst → inI C.pos e x) := by
    intro h0
    obtain ⟨e, heT, hes, _, hin, hlam⟩ := C.block mu hmu hmumin h0
    refine ⟨e, heT, hes, hin, ?_⟩
    rcases hlam b.fst with h | h
    · exact h
    · exfalso
      have ha' := hin a rfl
      have hc' := hin c hac.symm
      unfold inI at ha' hc'
      exact h b rfl ⟨by omega, by omega⟩
  have hW : 0 < C.pos mw → ∃ e, e ∈ C.TD ∧ e.snd = b.fst ∧
      (∀ x : G.Dart, x.fst = b.fst → inI C.pos e x) ∧
      (∀ x : G.Dart, x.fst = a.fst → inI C.pos e x) := by
    intro h0
    obtain ⟨e, heT, hes, _, hin, hlam⟩ := C.block mw hmw hmwmin h0
    refine ⟨e, heT, hes, hin, ?_⟩
    rcases hlam a.fst with h | h
    · exact h
    · exfalso
      have hb' := hin b rfl
      have hd' := hin d hbd.symm
      unfold inI at hb' hd'
      exact h c hac.symm ⟨by omega, by omega⟩
  rcases Nat.eq_zero_or_pos (C.pos mu) with hu0 | hu0 <;>
    rcases Nat.eq_zero_or_pos (C.pos mw) with hw0 | hw0
  · exact hab (by rw [← hmu, ← hmw, C.inj (hu0.trans hw0.symm)])
  · obtain ⟨e, -, -, -, hin⟩ := hW hw0
    have := hin mu hmu
    unfold inI at this
    omega
  · obtain ⟨e, -, -, -, hin⟩ := hU hu0
    have := hin mw hmw
    unfold inI at this
    omega
  · obtain ⟨e1, -, he1, -, hin1⟩ := hU hu0
    obtain ⟨e2, -, he2, -, hin2⟩ := hW hw0
    have x1 := hin2 e1.symm he1
    have x2 := hin1 e2.symm he2
    unfold inI at x1 x2
    have e12 : e1.symm = e2.symm := C.inj (le_antisymm x1.2 x2.2)
    apply hab
    rw [← he1, ← he2]
    exact congrArg (fun z : G.Dart => z.fst) e12

end cert

section draw

variable {V : Type} {G : SimpleGraph V}

/-- relation of the dart-subdivided graph: stars `v — d` (`d.fst = v`) and pairs `d — d.symm` -/
def subRel (G : SimpleGraph V) : V ⊕ G.Dart → V ⊕ G.Dart → Prop
  | Sum.inl v, Sum.inr d => d.fst = v
  | Sum.inr d, Sum.inr e => e = d.symm
  | _, _ => False

/-- the dart-subdivided graph -/
def subG (G : SimpleGraph V) : SimpleGraph (V ⊕ G.Dart) := SimpleGraph.fromRel (subRel G)

theorem subG_adj_cases {a b : V ⊕ G.Dart} (h : (subG G).Adj a b) :
    (∃ v x, a = Sum.inl v ∧ b = Sum.inr x ∧ x.fst = v) ∨
      (∃ v x, a = Sum.inr x ∧ b = Sum.inl v ∧ x.fst = v) ∨
      (∃ x : G.Dart, a = Sum.inr x ∧ b = Sum.inr x.symm) := by
  obtain ⟨_, h | h⟩ := h
  · rcases a with v | x <;> rcases b with w | y <;> simp only [subRel] at h
    · exact Or.inl ⟨v, y, rfl, rfl, h⟩
    · exact Or.inr (Or.inr ⟨x, rfl, by rw [h]⟩)
  · rcases a with v | x <;> rcases b with w | y <;> simp only [subRel] at h
    · exact Or.inr (Or.inl ⟨w, x, rfl, rfl, h⟩)
    · exact Or.inr (Or.inr ⟨x, rfl, by rw [h, Dart.symm_symm]⟩)

/-- a certificate gives a plane drawing of the dart-subdivided graph -/
theorem planar_subG (C : Cert G) (hdeg : ∀ v : V, ∃ d : G.Dart, d.fst = v) :
    RobertsonSeymour1986.GM5.IsPlanar (subG G) := by
  classical
  choose m hm hmin using fun v => C.exists_min (hdeg v).choose (hdeg v).choose_spec
  let pN : V ⊕ G.Dart → ℕ := fun w => match w with
    | Sum.inl v => 2 * C.pos (m v) + 1
    | Sum.inr d => 2 * C.pos d + 2
  have pN_inl : ∀ v, pN (Sum.inl v) = 2 * C.pos (m v) + 1 := fun _ => rfl
  have pN_inr : ∀ d, pN (Sum.inr d) = 2 * C.pos d + 2 := fun _ => rfl
  have pNinj : Function.Injective pN := by
    rintro (v | x) (w | y) h
    · rw [pN_inl, pN_inl] at h
      have e : m v = m w := C.inj (by omega)
      rw [← hm v, ← hm w, e]
    · rw [pN_inl, pN_inr] at h; omega
    · rw [pN_inr, pN_inl] at h; omega
    · rw [pN_inr, pN_inr] at h
      rw [C.inj (by omega : C.pos x = C.pos y)]
  let page : V ⊕ G.Dart → V ⊕ G.Dart → Bool := fun a b => match a, b with
    | Sum.inr x, Sum.inr y => decide (x ∈ C.TD ∧ y ∈ C.TD)
    | _, _ => true
  have hpage : ∀ a b, page a b = page b a := by
    rintro (v | x) (w | y) <;> simp only [page]
    by_cases h1 : x ∈ C.TD <;> by_cases h2 : y ∈ C.TD <;> simp [h1, h2]
  -- strict lower position of the block minimum
  have hmlt : ∀ (v : V) (x : G.Dart), x.fst = v → x ≠ m v → C.pos (m v) < C.pos x := by
    intro v x hx hne
    rcases Nat.lt_or_ge (C.pos (m v)) (C.pos x) with h | h
    · exact h
    · exact absurd (C.inj (le_antisymm (hmin v x hx) h)).symm hne
  have hsep : ∀ (v : V) (x : G.Dart), x.fst ≠ v → C.pos (m v) ≠ C.pos x := by
    intro v x hx e
    exact hx (by rw [← C.inj e, hm v])
  refine planar_of_book2 (subG G) (fun w => (pN w : ℝ)) (fun a b h => pNinj (Nat.cast_injective h))
    page hpage ?_
  intro a b c d hab hcd hpg hcr
  have hcr' : pN a < pN c ∧ pN c < pN b ∧ pN b < pN d := by
    obtain ⟨h1, h2, h3⟩ := hcr
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  clear hcr
  have hTDp : ∀ y : G.Dart, decide (y ∈ C.TD ∧ y.symm ∈ C.TD) = true ↔ y ∈ C.TD := by
    intro y
    simp only [decide_eq_true_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, C.symm y h⟩⟩
  rcases subG_adj_cases hab with ⟨v, x, rfl, rfl, hx⟩ | ⟨v, x, rfl, rfl, hx⟩ | ⟨x, rfl, rfl⟩ <;>
    rcases subG_adj_cases hcd with ⟨w, y, rfl, rfl, hy⟩ | ⟨w, y, rfl, rfl, hy⟩ | ⟨y, rfl, rfl⟩ <;>
    simp only [pN_inl, pN_inr] at hcr'
  · -- star / star
    have mx := hmin v x hx
    have my := hmin w y hy
    by_cases hvw : v = w
    · subst hvw; omega
    · have hs := hsep w x (by rw [hx]; exact hvw)
      exact C.F6 (m v) (m w) x y (by rw [hm, hx]) (by rw [hm, hy]) (by rw [hm, hm]; exact hvw)
        ⟨by omega, by omega, by omega⟩
  · have := hmin w y hy; omega
  · -- star / pair
    have mx := hmin v x hx
    have hyT : y ∈ C.TD := (hTDp y).1 (by simpa [page] using hpg.symm)
    rcases C.F4 y hyT (by omega) v with h | h
    · have := h (m v) (hm v); unfold inI at this; omega
    · exact h x hx ⟨by omega, by omega⟩
  · have := hmin v x hx; omega
  · have := hmin v x hx; omega
  · have := hmin v x hx; omega
  · -- pair / star
    have my := hmin w y hy
    have hxT : x ∈ C.TD := (hTDp x).1 (by simpa [page] using hpg)
    rcases C.F4 x hxT (by omega) w with h | h
    · have := h y hy; unfold inI at this; omega
    · exact h (m w) (hm w) ⟨by omega, by omega⟩
  · have := hmin w y hy; omega
  · -- pair / pair
    have hpg' : (x ∈ C.TD) ↔ (y ∈ C.TD) := by
      rw [← hTDp x, ← hTDp y]
      simp only [page] at hpg
      rw [hpg]
    by_cases hxT : x ∈ C.TD
    · exact C.F2 x y hxT (hpg'.1 hxT) ⟨by omega, by omega, by omega⟩
    · exact C.F3 x y hxT (fun h => hxT (hpg'.2 h)) ⟨by omega, by omega, by omega⟩

end draw

end PQL21

/-! C1 part 2 for lemma_21 (e1368385): the contour of a genus-0 scheme gives a `Cert`. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section exist

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SigP_fst (S : EmbeddingScheme G) (q : G.Dart × Bool) : (SigP S q).1.fst = q.1.fst := by
  rw [SigP_apply]
  split_ifs
  · exact rot_inv_fst S q.1
  · exact S.rot_fst q.1

theorem cert_exists (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (hg : S.eulerGenus ≤ 0) : Nonempty (Cert G) := by
  classical
  obtain ⟨r⟩ := hconn.nonempty
  obtain ⟨TD, L, p, I⟩ := ginv_full S hconn r
  obtain ⟨_, hT, hmT, hmC⟩ := genus0_max S hconn h2 hg I
  obtain ⟨d0, -⟩ := exists_dart_at hconn h2 r
  set ψ := SigP S * sprod L with hψ
  set y0 : G.Dart × Bool := (d0, p d0.fst) with hy0
  let y : G.Dart → G.Dart × Bool := fun d => (d, p d.fst)
  have hsc : ∀ d, SameCycle ψ y0 (y d) := fun d =>
    sheet_cycle S hconn h2 hg I d0 (y d) (by simp [sh, y])
  choose pos hposlt hpos using fun d => exists_pos ψ (hsc d)
  have hpartner : ∀ d, apFun S (y d) = y d.symm := by
    intro d
    have hp : p d.snd = xor (p d.fst) (S.sig d) := by
      by_cases hd : d ∈ TD
      · exact I.par d hd
      · exact chord_untwisted S hconn h2 hg I d hd
    simp only [apFun, y, dart_symm_fst, hp]
  have hinj : Function.Injective pos := by
    intro d e h
    have : y d = y e := by rw [← hpos d, ← hpos e, h]
    exact congrArg Prod.fst this
  have hnc : ∀ (C : Finset (G.Dart × Bool)), (∀ x ∈ C, apFun S x ∈ C) →
      2 * norb ψ + C.card ≤ 2 * norb (ψ * PF (apFun S) (apFun_invol S) C) →
      ∀ d e, y d ∈ C → y e ∈ C →
        ¬ (pos d < pos e ∧ pos e < pos d.symm ∧ pos d.symm < pos e.symm) := by
    intro C hcl hmax d e hd he ⟨h1, h2, h3⟩
    exact no_cross (apFun S) (apFun_invol S) C hcl (apFun_fp S C) ψ hmax y0 h1 h2 h3 (hposlt _)
      (by rw [hpos]; exact hd) (by rw [hpos, hpos, hpartner]) (by rw [hpos]; exact he)
      (by rw [hpos, hpos, hpartner])
  have hF4 : ∀ d, d ∈ TD → pos d < pos d.symm → ∀ w : V,
      (∀ x : G.Dart, x.fst = w → inI pos d x) ∨ (∀ x : G.Dart, x.fst = w → ¬ inI pos d x) := by
    intro d hd hlt w
    set C := TD ×ˢ (Finset.univ : Finset Bool) with hC
    have hyd : y d ∈ C := by simp [C, y, hd]
    obtain ⟨_, hmax'⟩ := PF_max_head (apFun S) (apFun_invol S) C (CT_closed S I.td_symm)
      (apFun_fp S C) ψ hmT hyd
    have href := PF_max_refine (apFun S) (apFun_invol S) _ _ rfl
      (erase2_closed (apFun S) (apFun_invol S) C (CT_closed S I.td_symm) (y d))
      (erase2_fp (apFun S) C (apFun_fp S C) (y d)) _ hmax'
    have hdec := PF_decomp (apFun S) (apFun_invol S) C hyd (CT_closed S I.td_symm _ hyd)
      (fun e => apFun_fp S C _ hyd e.symm)
    have hprod : ψ * swap (y d) (apFun S (y d)) *
        PF (apFun S) (apFun_invol S) ((C.erase (y d)).erase (apFun S (y d))) = SigP S := by
      rw [mul_assoc, ← hdec]; exact hT
    have hchar : ∀ x : G.Dart, inI pos d x ↔
        SameCycle (ψ * swap (y d) (apFun S (y d))) (apFun S (y d)) (y x) := by
      intro x
      have hs := split_interval ψ y0 hlt (hposlt d.symm) (y x)
      rw [hpos d, hpos d.symm, ← hpartner] at hs
      rw [hs]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨pos x, h1, h2, hpos x⟩
      · rintro ⟨l, hl1, hl2, hl3⟩
        have := pow_inj_lt ψ y0 (lt_of_le_of_lt hl2 (hposlt _)) (hposlt x)
          (hl3.trans (hpos x).symm)
        subst this
        exact ⟨hl1, hl2⟩
    have hsame : ∀ x x' : G.Dart, x.fst = w → x'.fst = w →
        SameCycle (ψ * swap (y d) (apFun S (y d))) (y x) (y x') := by
      intro x x' hx hx'
      apply href
      rw [hprod]
      exact (sig_sc S _ _).2 ⟨hx.trans hx'.symm, by simp [y, hx, hx']⟩
    by_cases h : ∃ x, x.fst = w ∧ inI pos d x
    · left
      intro x' hx'
      obtain ⟨x, hx, hin⟩ := h
      rw [hchar] at hin ⊢
      exact hin.trans (hsame x x' hx hx')
    · right
      intro x' hx' hin
      exact h ⟨x', hx', hin⟩
  have key : ∀ q : G.Dart × Bool, sh p q = false → y q.1 = q := by
    rintro ⟨e, s⟩ h
    simp only [sh] at h
    simp only [y, Prod.mk.injEq, true_and]
    revert h
    cases s <;> cases p e.fst <;> simp
  have hentry : ∀ b : G.Dart, 0 < pos b → (∀ x : G.Dart, x.fst = b.fst → pos b ≤ pos x) →
      ∃ e, e ∈ TD ∧ e.snd = b.fst ∧ pos e + 1 = pos b := by
    intro b hb hmin
    set z := (ψ ^ (pos b - 1)) y0 with hz
    have hzsh : sh p z = false := by
      have := sheet_of_sc I (sc_of_nat (pos b - 1) rfl : SameCycle ψ y0 z)
      rw [this]
      simp [sh, y0]
    have hz' := key z hzsh
    have hpe : pos z.1 = pos b - 1 :=
      pow_inj_lt ψ y0 (hposlt z.1) (by have := hposlt b; omega) ((hpos z.1).trans hz')
    have hstep : ψ (y z.1) = y b := by
      rw [hz', hz, ← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hb, hpos b]
    have hfst : (ψ (y z.1)).1.fst = b.fst := by rw [hstep]
    rw [hψ, Perm.mul_apply, SigP_fst, sprod_eq_PF I, PF_apply] at hfst
    unfold pfFun at hfst
    by_cases he : z.1 ∈ TD
    · refine ⟨z.1, he, ?_, by omega⟩
      rw [if_pos ⟨by simp [y, he], CT_closed S I.td_symm _ (by simp [y, he])⟩, hpartner] at hfst
      exact hfst
    · rw [if_neg (fun h => he (by simpa [y] using h.1))] at hfst
      have := hmin z.1 hfst
      omega
  exact ⟨{
    pos := pos
    inj := hinj
    TD := ↑TD
    symm := fun d hd => I.td_symm d hd
    F2 := fun d e hd he => hnc _ (CT_closed S I.td_symm) hmT d e (by simpa [y] using hd)
      (by simpa [y] using he)
    F3 := fun d e hd he => hnc _ (CC_closed S I.td_symm) hmC d e (by simpa [y] using hd)
      (by simpa [y] using he)
    F4 := hF4
    entry := fun b hb hmin => by
      obtain ⟨e, he1, he2, he3⟩ := hentry b hb hmin
      exact ⟨e, he1, he2, by omega⟩ }⟩

end exist

end PQL21

set_option autoImplicit false

/-! C1a' helpers for lemma_21 (e1368385): concatenating injective arcs. -/

namespace PQL21

/-- concatenation of injective paths that meet only at the junction is injective -/
theorem trans_inj {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y) (q : Path y z)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : ∀ s t, p s = q t → s = 1 ∧ t = 0) : Function.Injective (p.trans q) := by
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with h1 h2 h2
  · have e := hp hst
    have h' : (2 : ℝ) * s = 2 * t := congrArg Subtype.val e
    exact Subtype.ext (by linarith)
  · obtain ⟨_, e2⟩ := hpq _ _ hst
    have h' := congrArg Subtype.val e2
    norm_num at h'
    linarith
  · obtain ⟨_, e2⟩ := hpq _ _ hst.symm
    have h' := congrArg Subtype.val e2
    norm_num at h'
    linarith
  · have e := hq hst
    have h' : (2 : ℝ) * s - 1 = 2 * t - 1 := congrArg Subtype.val e
    exact Subtype.ext (by linarith)

/-- every point of a concatenation is a point of one of the pieces -/
theorem trans_mem {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y) (q : Path y z)
    (t : unitInterval) : (∃ s, (p.trans q) t = p s) ∨ (∃ s, (p.trans q) t = q s) := by
  rw [Path.trans_apply]
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

end PQL21

/-! C1a' for lemma_21 (e1368385): a plane drawing of the dart-subdivided graph `subG G` gives a
plane drawing of `G` (each edge `vw` is the 3-arc path `v, (v,w), (w,v), w`); then C1 assembly. -/

namespace PQL21

open SimpleGraph RobertsonSeymour1986.GM5

theorem arc_meet {W : Type} {H : SimpleGraph W} (D : PlaneDrawing H) {a b c e : W}
    (h : H.Adj a b) (k : H.Adj c e) (s t : unitInterval) (hst : D.arc h s = D.arc k t)
    (hne : ¬ ((a = c ∧ b = e) ∨ (a = e ∧ b = c))) :
    ∃ z, (z = a ∨ z = b) ∧ (z = c ∨ z = e) ∧ D.arc h s = D.vertex z := by
  rcases D.arcs_meet_only_at_endpoints h k s t hst with h1 | h1 | ⟨hs, ht⟩
  · exact absurd (Or.inl h1) hne
  · exact absurd (Or.inr h1) hne
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact ⟨a, Or.inl rfl, Or.inl (D.vertex_injective
        ((D.arc h).source.symm.trans (hst.trans (D.arc k).source))), (D.arc h).source⟩
    · exact ⟨a, Or.inl rfl, Or.inr (D.vertex_injective
        ((D.arc h).source.symm.trans (hst.trans (D.arc k).target))), (D.arc h).source⟩
    · exact ⟨b, Or.inr rfl, Or.inl (D.vertex_injective
        ((D.arc h).target.symm.trans (hst.trans (D.arc k).source))), (D.arc h).target⟩
    · exact ⟨b, Or.inr rfl, Or.inr (D.vertex_injective
        ((D.arc h).target.symm.trans (hst.trans (D.arc k).target))), (D.arc h).target⟩

section subdiv

variable {V : Type} {G : SimpleGraph V}

theorem sub_p1 (d : G.Dart) : (subG G).Adj (Sum.inl d.fst) (Sum.inr d) :=
  ⟨Sum.inl_ne_inr, Or.inl rfl⟩

theorem sub_p2 (d : G.Dart) : (subG G).Adj (Sum.inr d) (Sum.inr d.symm) :=
  ⟨fun h => d.symm_ne (Sum.inr_injective h).symm, Or.inl rfl⟩

theorem sub_p3 (d : G.Dart) : (subG G).Adj (Sum.inr d.symm) (Sum.inl d.snd) :=
  ⟨Sum.inr_ne_inl, Or.inr rfl⟩

theorem sub_not_ll (u u' : V) : ¬ (subG G).Adj (Sum.inl u) (Sum.inl u') := by
  rintro ⟨_, h | h⟩ <;> exact h

/-- the H-vertices on the path of the dart `d` -/
def Ed (d : G.Dart) (z : V ⊕ G.Dart) : Prop :=
  z = Sum.inl d.fst ∨ z = Sum.inr d ∨ z = Sum.inr d.symm ∨ z = Sum.inl d.snd

theorem Ed_symm (d : G.Dart) (z : V ⊕ G.Dart) : Ed d.symm z ↔ Ed d z := by
  unfold Ed
  rw [Dart.symm_symm]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

theorem Ed_ends {d d' : G.Dart} {z : V ⊕ G.Dart} (h1 : Ed d z) (h2 : Ed d' z) (hn1 : d' ≠ d)
    (hn2 : d' ≠ d.symm) : ∃ u, z = Sum.inl u ∧ (u = d.fst ∨ u = d.snd) ∧
      (u = d'.fst ∨ u = d'.snd) := by
  unfold Ed at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl
  · rcases h2 with h | h | h | h
    · exact ⟨_, rfl, Or.inl rfl, Or.inl (Sum.inl_injective h)⟩
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inl_ne_inr
    · exact ⟨_, rfl, Or.inl rfl, Or.inr (Sum.inl_injective h)⟩
  · exfalso
    rcases h2 with h | h | h | h
    · exact Sum.inr_ne_inl h
    · exact hn1 (Sum.inr_injective h).symm
    · exact hn2 (by rw [Sum.inr_injective h, Dart.symm_symm])
    · exact Sum.inr_ne_inl h
  · exfalso
    rcases h2 with h | h | h | h
    · exact Sum.inr_ne_inl h
    · exact hn2 (Sum.inr_injective h).symm
    · exact hn1 (by simpa using (congrArg Dart.symm (Sum.inr_injective h)).symm)
    · exact Sum.inr_ne_inl h
  · rcases h2 with h | h | h | h
    · exact ⟨_, rfl, Or.inr rfl, Or.inl (Sum.inl_injective h)⟩
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inl_ne_inr
    · exact ⟨_, rfl, Or.inr rfl, Or.inr (Sum.inl_injective h)⟩

variable (D : PlaneDrawing (subG G))

/-- the 3-arc path of the dart `d` -/
noncomputable def Qp (d : G.Dart) : Path (D.vertex (Sum.inl d.fst)) (D.vertex (Sum.inl d.snd)) :=
  (D.arc (sub_p1 d)).trans ((D.arc (sub_p2 d)).trans (D.arc (sub_p3 d)))

theorem Qp_pts (d : G.Dart) (t : unitInterval) :
    ∃ (a b : V ⊕ G.Dart) (hab : (subG G).Adj a b) (s : unitInterval),
      Ed d a ∧ Ed d b ∧ Qp D d t = D.arc hab s := by
  unfold Qp
  rcases trans_mem (D.arc (sub_p1 d)) ((D.arc (sub_p2 d)).trans (D.arc (sub_p3 d))) t with
    ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨_, _, sub_p1 d, s, Or.inl rfl, Or.inr (Or.inl rfl), hs⟩
  · rcases trans_mem (D.arc (sub_p2 d)) (D.arc (sub_p3 d)) s with ⟨s', hs'⟩ | ⟨s', hs'⟩
    · exact ⟨_, _, sub_p2 d, s', Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
        hs.trans hs'⟩
    · exact ⟨_, _, sub_p3 d, s', Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl)),
        hs.trans hs'⟩

theorem Qp_inj (d : G.Dart) : Function.Injective (Qp D d) := by
  have hne : d.fst ≠ d.snd := G.ne_of_adj d.adj
  have hsd : d.symm ≠ d := d.symm_ne
  have inner : Function.Injective ((D.arc (sub_p2 d)).trans (D.arc (sub_p3 d))) := by
    refine trans_inj _ _ (D.arc_injective _) (D.arc_injective _) ?_
    intro s t hst
    obtain ⟨z, hz1, hz2, hz⟩ := arc_meet D _ _ s t hst (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact d.symm_ne (Sum.inr_injective h1).symm
      · exact Sum.inr_ne_inl h1)
    have hzv : z = Sum.inr d.symm := by
      rcases hz1 with rfl | rfl <;> rcases hz2 with h | h
      · exact h
      · exact absurd h Sum.inr_ne_inl
      · exact h
      · exact absurd h Sum.inr_ne_inl
    subst hzv
    constructor
    · exact D.arc_injective _ (hz.trans (D.arc (sub_p2 d)).target.symm)
    · exact D.arc_injective _ ((hst.symm.trans hz).trans (D.arc (sub_p3 d)).source.symm)
  unfold Qp
  refine trans_inj _ _ (D.arc_injective _) inner ?_
  intro s t hst
  rcases trans_mem (D.arc (sub_p2 d)) (D.arc (sub_p3 d)) t with ⟨t', ht'⟩ | ⟨t', ht'⟩
  · rw [ht'] at hst
    obtain ⟨z, hz1, hz2, hz⟩ := arc_meet D _ _ s t' hst (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Sum.inl_ne_inr h1
      · exact Sum.inl_ne_inr h1)
    have hzv : z = Sum.inr d := by
      rcases hz1 with rfl | rfl <;> rcases hz2 with h | h
      · exact absurd h Sum.inl_ne_inr
      · exact absurd h Sum.inl_ne_inr
      · exact h
      · exact absurd (Sum.inr_injective h) hsd.symm
    subst hzv
    constructor
    · exact D.arc_injective _ (hz.trans (D.arc (sub_p1 d)).target.symm)
    · apply inner
      rw [Path.source]
      rw [ht', ← hst, hz]
  · rw [ht'] at hst
    exfalso
    obtain ⟨z, hz1, hz2, -⟩ := arc_meet D _ _ s t' hst (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Sum.inl_ne_inr h1
      · exact hne (Sum.inl_injective h1))
    rcases hz1 with rfl | rfl <;> rcases hz2 with h | h
    · exact Sum.inl_ne_inr h
    · exact hne (Sum.inl_injective h)
    · exact hsd.symm (Sum.inr_injective h)
    · exact Sum.inr_ne_inl h

end subdiv

end PQL21

namespace PQL21

open SimpleGraph RobertsonSeymour1986.GM5

section subdiv2

variable {V : Type} {G : SimpleGraph V}

/-- the reversed 3-arc path of `d.symm`, as a path from `d.fst` to `d.snd` -/
noncomputable def Qr (D : PlaneDrawing (subG G)) (d : G.Dart) :
    Path (D.vertex (Sum.inl d.fst)) (D.vertex (Sum.inl d.snd)) :=
  (Qp D d.symm).symm

theorem Qr_apply (D : PlaneDrawing (subG G)) (d : G.Dart) (t : unitInterval) :
    Qr D d t = Qp D d.symm (unitInterval.symm t) := rfl

theorem Qr_symm (D : PlaneDrawing (subG G)) (d : G.Dart) : (Qr D d).symm = Qp D d.symm :=
  Path.symm_symm _

/-- the oriented G-arc of a dart (orientation fixed by `ord` so that reversal is exact) -/
noncomputable def Ap (D : PlaneDrawing (subG G)) (ord : V → ℕ) (d : G.Dart) :
    Path (D.vertex (Sum.inl d.fst)) (D.vertex (Sum.inl d.snd)) :=
  if ord d.fst < ord d.snd then Qp D d else Qr D d

theorem Ap_pos (D : PlaneDrawing (subG G)) (ord : V → ℕ) (d : G.Dart)
    (h : ord d.fst < ord d.snd) : Ap D ord d = Qp D d := by
  unfold Ap; rw [if_pos h]

theorem Ap_neg (D : PlaneDrawing (subG G)) (ord : V → ℕ) (d : G.Dart)
    (h : ¬ ord d.fst < ord d.snd) : Ap D ord d = Qr D d := by
  unfold Ap; rw [if_neg h]

theorem Ap_pts (D : PlaneDrawing (subG G)) (ord : V → ℕ) (d : G.Dart) (t : unitInterval) :
    ∃ (a b : V ⊕ G.Dart) (hab : (subG G).Adj a b) (s : unitInterval),
      Ed d a ∧ Ed d b ∧ Ap D ord d t = D.arc hab s := by
  by_cases h : ord d.fst < ord d.snd
  · rw [Ap_pos D ord d h]
    exact Qp_pts D d t
  · rw [Ap_neg D ord d h, Qr_apply]
    obtain ⟨a, b, hab, s, h1, h2, h3⟩ := Qp_pts D d.symm (unitInterval.symm t)
    exact ⟨a, b, hab, s, (Ed_symm d a).1 h1, (Ed_symm d b).1 h2, h3⟩

theorem Ap_inj (D : PlaneDrawing (subG G)) (ord : V → ℕ) (d : G.Dart) :
    Function.Injective (Ap D ord d) := by
  by_cases h : ord d.fst < ord d.snd
  · rw [Ap_pos D ord d h]
    exact Qp_inj D d
  · rw [Ap_neg D ord d h]
    intro s t hst
    rw [Qr_apply, Qr_apply] at hst
    have := congrArg unitInterval.symm (Qp_inj D d.symm hst)
    simpa using this

theorem planar_of_subG (ord : V → ℕ) (hord : Function.Injective ord)
    (hH : IsPlanar (subG G)) : IsPlanar G := by
  obtain ⟨D⟩ := hH
  have hlt : ∀ {v w : V}, G.Adj v w → ord v < ord w ∨ ord w < ord v := by
    intro v w h
    rcases Nat.lt_trichotomy (ord v) (ord w) with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd (hord h1) (G.ne_of_adj h)
    · exact Or.inr h1
  refine ⟨{
    vertex := fun v => D.vertex (Sum.inl v)
    vertex_injective := fun v w h => Sum.inl_injective (D.vertex_injective h)
    arc := fun {v w} h => Ap D ord ⟨(v, w), h⟩
    arc_injective := fun {v w} h => Ap_inj D ord ⟨(v, w), h⟩
    arc_reverse := ?_
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }⟩
  · intro v w h
    show Ap D ord ⟨(w, v), h.symm⟩ = (Ap D ord ⟨(v, w), h⟩).symm
    rcases hlt h with h1 | h1
    · rw [Ap_neg D ord ⟨(w, v), h.symm⟩ (show ¬ (ord w < ord v) by omega),
        Ap_pos D ord ⟨(v, w), h⟩ h1]
      rfl
    · rw [Ap_pos D ord ⟨(w, v), h.symm⟩ h1,
        Ap_neg D ord ⟨(v, w), h⟩ (show ¬ (ord v < ord w) by omega)]
      rw [Qr_symm]
      rfl
  · intro v w h t x hx
    obtain ⟨a, b, hab, s, ha, hb, hs⟩ := Ap_pts D ord ⟨(v, w), h⟩ t
    have hx' : D.arc hab s = D.vertex (Sum.inl x) := hs.symm.trans hx
    have hE : Ed ⟨(v, w), h⟩ (Sum.inl x) := by
      rcases D.arc_avoids_vertices hab s _ hx' with e | e
      · rw [e]; exact ha
      · rw [e]; exact hb
    rcases hE with e | e | e | e
    · exact Or.inl (Sum.inl_injective e)
    · exact absurd e Sum.inl_ne_inr
    · exact absurd e Sum.inl_ne_inr
    · exact Or.inr (Sum.inl_injective e)
  · intro v w x y h k s t hst
    by_cases e1 : v = x ∧ w = y
    · exact Or.inl e1
    by_cases e2 : v = y ∧ w = x
    · exact Or.inr (Or.inl e2)
    right; right
    have hn1 : (⟨(x, y), k⟩ : G.Dart) ≠ ⟨(v, w), h⟩ := by
      intro e
      apply e1
      have := congrArg (fun z : G.Dart => z.toProd) e
      simp only [Prod.mk.injEq] at this
      exact ⟨this.1.symm, this.2.symm⟩
    have hn2 : (⟨(x, y), k⟩ : G.Dart) ≠ (⟨(v, w), h⟩ : G.Dart).symm := by
      intro e
      apply e2
      have := congrArg (fun z : G.Dart => z.toProd) e
      simp only [Dart.symm, Prod.swap_prod_mk, Prod.mk.injEq] at this
      exact ⟨this.2.symm, this.1.symm⟩
    obtain ⟨a, b, hab, s1, ha, hb, hs1⟩ := Ap_pts D ord ⟨(v, w), h⟩ s
    obtain ⟨c, e, hce, t1, hc, he, ht1⟩ := Ap_pts D ord ⟨(x, y), k⟩ t
    have hmeet : D.arc hab s1 = D.arc hce t1 := hs1.symm.trans (hst.trans ht1)
    obtain ⟨z, hz1, hz2, hz⟩ := arc_meet D hab hce s1 t1 hmeet (by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · obtain ⟨u, rfl, -⟩ := Ed_ends ha hc hn1 hn2
        obtain ⟨u', rfl, -⟩ := Ed_ends hb he hn1 hn2
        exact sub_not_ll u u' hab
      · obtain ⟨u, rfl, -⟩ := Ed_ends ha he hn1 hn2
        obtain ⟨u', rfl, -⟩ := Ed_ends hb hc hn1 hn2
        exact sub_not_ll u u' hab)
    have hEz : Ed ⟨(v, w), h⟩ z := by rcases hz1 with rfl | rfl; exacts [ha, hb]
    have hEz' : Ed ⟨(x, y), k⟩ z := by rcases hz2 with rfl | rfl; exacts [hc, he]
    obtain ⟨u, rfl, hu1, hu2⟩ := Ed_ends hEz hEz' hn1 hn2
    have hP : Ap D ord ⟨(v, w), h⟩ s = D.vertex (Sum.inl u) := hs1.trans hz
    have hQ : Ap D ord ⟨(x, y), k⟩ t = D.vertex (Sum.inl u) := ht1.trans (hmeet.symm.trans hz)
    constructor
    · rcases hu1 with e | e <;> rw [e] at hP
      · exact Or.inl (Ap_inj D ord _ (hP.trans (Ap D ord ⟨(v, w), h⟩).source.symm))
      · exact Or.inr (Ap_inj D ord _ (hP.trans (Ap D ord ⟨(v, w), h⟩).target.symm))
    · rcases hu2 with e | e <;> rw [e] at hQ
      · exact Or.inl (Ap_inj D ord _ (hQ.trans (Ap D ord ⟨(x, y), k⟩).source.symm))
      · exact Or.inr (Ap_inj D ord _ (hQ.trans (Ap D ord ⟨(x, y), k⟩).target.symm))

end subdiv2

/-- C1 (connected case): a connected graph with a genus-0 embedding scheme is planar -/
theorem genus0_planar_conn (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (h : PlanarQueue.Genus.EulerGenusLE G 0) :
    IsPlanar G := by
  by_cases h2 : 2 ≤ Fintype.card V
  · obtain ⟨S, hS⟩ := h
    obtain ⟨C⟩ := cert_exists S hconn h2 (by simpa using hS)
    exact planar_of_subG (fun v => ((Fintype.equivFin V v : Fin _) : ℕ))
      (fun a b hab => (Fintype.equivFin V).injective (Fin.ext hab))
      (planar_subG C (exists_dart_at hconn h2))
  · have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hno : ∀ {v w : V}, ¬ G.Adj v w := fun h => G.ne_of_adj h (Subsingleton.elim _ _)
    exact ⟨{
      vertex := fun _ => 0
      vertex_injective := fun a b _ => Subsingleton.elim a b
      arc := fun h => (hno h).elim
      arc_injective := fun h => (hno h).elim
      arc_reverse := fun h => (hno h).elim
      arc_avoids_vertices := fun h => (hno h).elim
      arcs_meet_only_at_endpoints := fun h => (hno h).elim }⟩

end PQL21

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! C2 perm-level lemmas for lemma_21 (e1368385): P1 mirror pairing, P2 even change count. -/

namespace PQL21

open Equiv Equiv.Perm

section c2perm

variable {α : Type} [DecidableEq α] [Fintype α]

theorem mirror_pow (Φ μ : Perm α) (hμ : ∀ x, μ (μ x) = x) (hconj : ∀ x, μ (Φ (μ x)) = Φ⁻¹ x)
    (x : α) : ∀ j : ℕ, μ ((Φ ^ j) x) = (Φ⁻¹ ^ j) (μ x) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hconj (μ ((Φ ^ j) x))
    rw [hμ] at h1
    rw [pow_succ', Perm.mul_apply, h1, ih, pow_succ', Perm.mul_apply]

/-- P1: under a fixed-point-free mirror `μ` (with `μ Φ` fixed-point-free) no `Φ`-cycle is
`μ`-invariant -/
theorem mirror_not_sc (Φ μ : Perm α) (hμ : ∀ x, μ (μ x) = x)
    (hconj : ∀ x, μ (Φ (μ x)) = Φ⁻¹ x) (hfp : ∀ x, μ x ≠ x) (hfp2 : ∀ x, μ (Φ x) ≠ x)
    (x : α) : ¬ SameCycle Φ x (μ x) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have key := mirror_pow Φ μ hμ hconj x
  have cancel : ∀ j y, (Φ⁻¹ ^ j) ((Φ ^ j) y) = y := by
    intro j y
    rw [inv_pow, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · apply hfp ((Φ ^ j) x)
    rw [key, ← hk, hj, pow_add Φ j j, Perm.mul_apply, cancel]
  · apply hfp2 ((Φ ^ j) x)
    have e : Φ ((Φ ^ j) x) = (Φ ^ (j + 1)) x := by rw [pow_succ', Perm.mul_apply]
    rw [e, key, ← hk, hj, show 2 * j + 1 = (j + 1) + j by ring, pow_add Φ (j + 1) j, Perm.mul_apply, cancel]

/-- P2: along an invariant set, a Boolean label changes an even number of times -/
theorem even_changes (σ : Perm α) (C : Finset α) (hC : ∀ z ∈ C, σ z ∈ C) (κ : α → Bool) :
    Even ((C.filter fun z => κ (σ z) ≠ κ z).card) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  let b : α → ZMod 2 := fun z => if κ z then 1 else 0
  have hb : ∀ z, ((if κ (σ z) ≠ κ z then 1 else 0 : ℕ) : ZMod 2) = b (σ z) + b z := by
    intro z
    simp only [b]
    cases κ (σ z) <;> cases κ z <;> decide
  have hmap : C.map σ.toEmbedding = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
      exact hC z hz
    · rw [Finset.card_map]
  have hsum : ∑ z ∈ C, b (σ z) = ∑ z ∈ C, b z := by
    conv_rhs => rw [← hmap]
    rw [Finset.sum_map]
    rfl
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [hb, Finset.sum_add_distrib, hsum]
  rw [← two_mul]
  exact mul_eq_zero_of_left (by decide) _

end c2perm

end PQL21

/-! C2 P3 for lemma_21 (e1368385): tree growth along a given spanning tree `T`. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section along

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem ginv_along (S : EmbeddingScheme G) (T : SimpleGraph V) (hTG : T ≤ G) (hTc : T.Connected)
    (r : V) : ∃ TD L p, GInv S r Finset.univ TD L p ∧ ∀ d ∈ TD, T.Adj d.fst d.snd := by
  have key : ∀ k : ℕ, ∀ (Sv : Finset V) TD L p, GInv S r Sv TD L p →
      (∀ d ∈ TD, T.Adj d.fst d.snd) → (Finset.univ \ Sv).card = k →
      ∃ TD' L' p', GInv S r Finset.univ TD' L' p' ∧ ∀ d ∈ TD', T.Adj d.fst d.snd := by
    intro k
    induction k with
    | zero =>
      intro Sv TD L p I hT hk
      have : Sv = Finset.univ := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hk
        exact Finset.eq_univ_of_forall fun x => hk (Finset.mem_univ x)
      subst this
      exact ⟨TD, L, p, I, hT⟩
    | succ k ih =>
      intro Sv TD L p I hT hk
      obtain ⟨v, hv⟩ : ∃ v, v ∉ Sv := by
        by_contra h
        simp only [not_exists, not_not] at h
        have : Finset.univ \ Sv = ∅ := by ext x; simp [h x]
        rw [this] at hk; simp at hk
      obtain ⟨w⟩ := hTc.preconnected r v
      obtain ⟨dT, _, h1, h2⟩ := w.exists_boundary_dart (↑Sv) (by simpa using I.root)
        (by simpa using hv)
      let d : G.Dart := ⟨dT.toProd, hTG dT.adj⟩
      have hd1 : d.fst ∈ Sv := by simpa using h1
      have hd2 : d.snd ∉ Sv := by simpa using h2
      refine ih _ _ _ _ (ginv_step S I d hd1 hd2) ?_ ?_
      · intro e he
        simp only [Finset.mem_insert] at he
        rcases he with rfl | rfl | he
        · exact dT.adj
        · exact dT.adj.symm
        · exact hT e he
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem (by simp [hd2]), hk]
        simp
  exact key _ {r} ∅ [] (fun _ => false) (ginv_init S r) (by simp) rfl

/-- the grown tree darts are exactly the darts of the spanning tree `T` -/
theorem td_eq_tree (S : EmbeddingScheme G) (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (hsub : ∀ d ∈ TD, T.Adj d.fst d.snd) (d : G.Dart) :
    d ∈ TD ↔ T.Adj d.fst d.snd := by
  classical
  refine ⟨hsub d, fun hd => ?_⟩
  set F := Finset.univ.filter (fun e : G.Dart => T.Adj e.fst e.snd) with hF
  have hsubF : TD ⊆ F := fun e he => by simp [F, hsub e he]
  have hcardTD : TD.card + 2 = 2 * Fintype.card V := by
    have := I.len
    rw [card_TD_L I, Finset.card_univ] at this
    exact this
  have hequiv : {e : G.Dart // T.Adj e.fst e.snd} ≃ T.Dart :=
    { toFun := fun e => ⟨e.1.toProd, e.2⟩
      invFun := fun e => ⟨⟨e.toProd, hTG e.adj⟩, e.adj⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcardF : F.card = Fintype.card T.Dart := by
    rw [hF, ← Fintype.card_subtype]
    exact Fintype.card_congr hequiv
  have h1 := T.dart_card_eq_twice_card_edges
  have h2 := hT.card_edgeFinset
  have hEq : TD = F := Finset.eq_of_subset_of_card_le hsubF (by omega)
  rw [hEq]
  simp [F, hd]

end along

end PQL21

/-! C2 P4 (+ P5 helpers) for lemma_21 (e1368385): the chord deletion process, genus-free sheet
cycle, and the even-subgraph-of-a-tree lemma. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section delperm

variable {α : Type} [DecidableEq α] [Fintype α]

theorem PF_decomp_r (f : α → α) (hf : Function.Involutive f) (C : Finset α) {x0 : α}
    (h0 : x0 ∈ C) (h1 : f x0 ∈ C) (hne : x0 ≠ f x0) :
    PF f hf C = PF f hf ((C.erase x0).erase (f x0)) * swap x0 (f x0) := by
  ext x
  rw [Perm.mul_apply, PF_apply, PF_apply]
  unfold pfFun
  by_cases hx0 : x = x0
  · subst hx0
    simp [h0, h1, hne, Ne.symm hne]
  · by_cases hx1 : x = f x0
    · subst hx1
      have : f (f x0) = x0 := hf x0
      simp [h0, h1, hne, Ne.symm hne, this]
    · rw [swap_apply_of_ne_of_ne hx0 hx1]
      have e1 : f x ≠ x0 := fun e => hx1 (by rw [← e, hf x])
      have e2 : f x ≠ f x0 := fun e => hx0 (hf.injective e)
      simp [hx0, hx1, e1, e2]

end delperm

section del

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- face permutation of the tree darts `TD` plus the chord darts `E` -/
def PhiE (S : EmbeddingScheme G) (TD E : Finset G.Dart) : Perm (G.Dart × Bool) :=
  SigP S * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) *
    PF (apFun S) (apFun_invol S) (E ×ˢ Finset.univ)

def del2 (E : Finset G.Dart) (q : G.Dart) : Finset G.Dart := (E.erase q).erase q.symm

theorem phiE_full (S : EmbeddingScheme G) (TD : Finset G.Dart) (hTD : ∀ d ∈ TD, d.symm ∈ TD) :
    PhiE S TD TDᶜ = SigP S * AP S := by
  rw [PhiE, AP_eq_PF S TD hTD, mul_assoc]

theorem del2_sub (E : Finset G.Dart) (q : G.Dart) : del2 E q ⊆ E :=
  fun _ hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)

theorem del2_card (E : Finset G.Dart) {q : G.Dart} (hq : q ∈ E) (hqs : q.symm ∈ E) :
    (del2 E q).card + 2 = E.card := by
  have hne : q.symm ≠ q := q.symm_ne
  unfold del2
  rw [Finset.card_erase_of_mem (by simp [hne, hqs]), Finset.card_erase_of_mem hq]
  have h2 : 2 ≤ E.card := by
    have hs : ({q, q.symm} : Finset G.Dart) ⊆ E := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hs
    rwa [Finset.card_pair hne.symm] at this
  omega

theorem del2_symm (E : Finset G.Dart) (hE : ∀ d ∈ E, d.symm ∈ E) (q : G.Dart) :
    ∀ d ∈ del2 E q, d.symm ∈ del2 E q := by
  intro d hd
  simp only [del2, Finset.mem_erase] at hd ⊢
  refine ⟨fun e => hd.2.1 (by simpa using congrArg SimpleGraph.Dart.symm e),
    fun e => hd.1 (by rw [← e, SimpleGraph.Dart.symm_symm]), hE d hd.2.2⟩

/-- P4: the deletion process stops at a chord set `E` (the future `Q`) whose deleted chords
split maximally and none of whose chords can be deleted with a merge -/
theorem deletion_exists (S : EmbeddingScheme G) (TD : Finset G.Dart)
    (hTD : ∀ d ∈ TD, d.symm ∈ TD) :
    ∃ E : Finset G.Dart, E ⊆ TDᶜ ∧ (∀ d ∈ E, d.symm ∈ E) ∧
      2 * norb (PhiE S TD E) + ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card ≤
        2 * norb (SigP S * AP S) ∧
      ∀ q ∈ E, norb (PhiE S TD E) < norb (PhiE S TD (del2 E q)) + 2 := by
  have key : ∀ n : ℕ, ∀ E : Finset G.Dart, E.card = n → E ⊆ TDᶜ → (∀ d ∈ E, d.symm ∈ E) →
      2 * norb (PhiE S TD E) + ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card ≤
        2 * norb (SigP S * AP S) →
      ∃ E : Finset G.Dart, E ⊆ TDᶜ ∧ (∀ d ∈ E, d.symm ∈ E) ∧
      2 * norb (PhiE S TD E) + ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card ≤
        2 * norb (SigP S * AP S) ∧
      ∀ q ∈ E, norb (PhiE S TD E) < norb (PhiE S TD (del2 E q)) + 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro E hn hsub hsymm hinv
      by_cases hstop : ∀ q ∈ E, norb (PhiE S TD E) < norb (PhiE S TD (del2 E q)) + 2
      · exact ⟨E, hsub, hsymm, hinv, hstop⟩
      · push Not at hstop
        obtain ⟨q, hq, hle⟩ := hstop
        have hqs := hsymm q hq
        have hc := del2_card E hq hqs
        refine ih _ (by omega) _ rfl ((del2_sub E q).trans hsub) (del2_symm E hsymm q) ?_
        have hsd : (TDᶜ \ del2 E q).card = (TDᶜ \ E).card + 2 := by
          rw [Finset.card_sdiff_of_subset ((del2_sub E q).trans hsub),
            Finset.card_sdiff_of_subset hsub]
          have := Finset.card_le_card hsub
          omega
        simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hinv ⊢
        rw [hsd]
        omega
  refine key _ TDᶜ rfl subset_rfl ?_ ?_
  · intro d hd
    simp only [Finset.mem_compl] at hd ⊢
    exact fun h => hd (by simpa using hTD _ h)
  · simp [phiE_full S TD hTD]

/-- `PF` over a symmetric dart set times both sheets -/
theorem PF_prod (S : EmbeddingScheme G) (D : Finset G.Dart) (hD : ∀ d ∈ D, d.symm ∈ D)
    (x : G.Dart × Bool) :
    PF (apFun S) (apFun_invol S) (D ×ˢ Finset.univ) x = if x.1 ∈ D then apFun S x else x := by
  rw [PF_apply]
  unfold pfFun
  by_cases h : x.1 ∈ D
  · have h' : (apFun S x).1 ∈ D := by simpa [apFun] using hD _ h
    rw [if_pos ⟨Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩,
      Finset.mem_product.mpr ⟨h', Finset.mem_univ _⟩⟩, if_pos h]
  · rw [if_neg (fun h' => h (Finset.mem_product.mp h'.1).1), if_neg h]

/-- the tree face permutation always has two orbits (no genus hypothesis) -/
theorem norb_psi (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) : norb (SigP S * sprod L) = 2 := by
  have h1 := I.cnt
  have h3 := I.len
  rw [norb_SigP S (exists_dart_at hconn h2)] at h1
  rw [Finset.card_univ] at h3
  omega

/-- genus-free version of `sheet_cycle` -/
theorem sheet_cycle' (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (d0 : G.Dart) (x : G.Dart × Bool) (hx : sh p x = false) :
    SameCycle (SigP S * sprod L) (d0, p d0.fst) x := by
  by_contra hn
  have h0 : sh p (d0, p d0.fst) = false := by simp [sh]
  have hz : sh p (d0, !p d0.fst) = true := by simp [sh]
  have hsep : ∀ u v, sh p u ≠ sh p v → ¬ SameCycle (SigP S * sprod L) u v :=
    fun u v huv => not_sc_of_kappa _ (sh p) (sheet_pres I) huv
  have h3 := norb_ge_three (SigP S * sprod L) (c := (d0, !p d0.fst)) hn
    (hsep (d0, p d0.fst) (d0, !p d0.fst) (by rw [h0, hz]; decide))
    (hsep x (d0, !p d0.fst) (by rw [hx, hz]; decide))
  have h2' := norb_psi S hconn h2 I
  omega

/-- in a tree, a vertex has at most one neighbour closer to the root -/
theorem tree_parent_unique (T : SimpleGraph V) (hT : T.IsTree) (r : V) {w x y : V}
    (hx : T.Adj x w) (hy : T.Adj y w) (hdx : T.dist r x + 1 = T.dist r w)
    (hdy : T.dist r y + 1 = T.dist r w) : x = y := by
  obtain ⟨px, hpx, hlx⟩ := hT.connected.exists_path_of_dist r x
  obtain ⟨py, hpy, hly⟩ := hT.connected.exists_path_of_dist r y
  have hwx : w ∉ px.support := by
    intro hw
    have h1 := px.length_takeUntil_le_length hw
    have h2 := T.dist_le (px.takeUntil w hw)
    omega
  have hwy : w ∉ py.support := by
    intro hw
    have h1 := py.length_takeUntil_le_length hw
    have h2 := T.dist_le (py.takeUntil w hw)
    omega
  have e := (hT.isAcyclic.subsingleton_path r w).elim ⟨px.concat hx, hpx.concat hwx hx⟩
    ⟨py.concat hy, hpy.concat hwy hy⟩
  have e' := congrArg Subtype.val e
  obtain ⟨hv, _⟩ := SimpleGraph.Walk.concat_inj e'
  exact hv

/-- a symmetric dart set inside a tree with even degree everywhere is empty -/
theorem even_tree_empty (T : SimpleGraph V) (hT : T.IsTree) (r : V) (B : Finset G.Dart)
    (hB : ∀ d ∈ B, T.Adj d.fst d.snd) (hs : ∀ d ∈ B, d.symm ∈ B)
    (hev : ∀ v, Even (B.filter (fun d => d.fst = v)).card) : B = ∅ := by
  by_contra hne
  obtain ⟨d, hd, hmax⟩ := B.exists_max_image (fun d => T.dist r d.snd)
    (Finset.nonempty_iff_ne_empty.mpr hne)
  have hor : T.dist r d.snd = T.dist r d.fst + 1 := by
    rcases hT.dist_eq_dist_add_one_of_adj r (hB d hd) with h | h
    · have : T.dist r d.fst ≤ T.dist r d.snd := hmax d.symm (hs d hd)
      omega
    · exact h
  have hmem : d.symm ∈ B.filter (fun e => e.fst = d.snd) := by
    rw [Finset.mem_filter]; exact ⟨hs d hd, rfl⟩
  have hcard : 1 < (B.filter (fun e => e.fst = d.snd)).card := by
    have h1 := Finset.card_pos.mpr ⟨_, hmem⟩
    obtain ⟨k, hk⟩ := hev d.snd
    omega
  obtain ⟨e, he, hne'⟩ := Finset.exists_mem_ne hcard d.symm
  rw [Finset.mem_filter] at he
  have hadj : T.Adj d.snd e.snd := he.2 ▸ hB e he.1
  rcases hT.dist_eq_dist_add_one_of_adj r hadj with h | h
  · have hpar := tree_parent_unique T hT r hadj.symm (hB d hd) (by omega) (by omega)
    exact hne' (SimpleGraph.Dart.ext _ _ (Prod.ext he.2 hpar))
  · have : T.dist r e.snd ≤ T.dist r d.snd := hmax e he.1
    omega

end del

end PQL21

/-! C2 P5 for lemma_21 (e1368385): the stopped chord set `E` leaves exactly one face pair. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section face

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- sheet flip -/
def nuF (x : G.Dart × Bool) : G.Dart × Bool := (x.1, !x.2)

theorem nuF_nuF (x : G.Dart × Bool) : nuF (nuF x) = x := by
  rcases x with ⟨d, b⟩; simp [nuF]

theorem SigP_nu (S : EmbeddingScheme G) (x : G.Dart × Bool) :
    SigP S (nuF (SigP S (nuF x))) = x := by
  rcases x with ⟨d, _ | _⟩ <;> simp [SigP_apply, nuF]

theorem apFun_nu (S : EmbeddingScheme G) (x : G.Dart × Bool) :
    apFun S (nuF x) = nuF (apFun S x) := by
  rcases x with ⟨d, b⟩
  cases b <;> cases h : S.sig d <;> simp [apFun, nuF, h]

/-- the combined edge involution of the tree darts and the chord darts `E` -/
def FF (S : EmbeddingScheme G) (TD E : Finset G.Dart) : Perm (G.Dart × Bool) :=
  PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) * PF (apFun S) (apFun_invol S) (E ×ˢ Finset.univ)

theorem phiE_eq (S : EmbeddingScheme G) (TD E : Finset G.Dart) :
    PhiE S TD E = SigP S * FF S TD E := by
  unfold PhiE FF; rw [mul_assoc]

theorem FF_apply (S : EmbeddingScheme G) (TD E : Finset G.Dart) (hTD : ∀ d ∈ TD, d.symm ∈ TD)
    (hEs : ∀ d ∈ E, d.symm ∈ E) (hE : E ⊆ TDᶜ) (x : G.Dart × Bool) :
    FF S TD E x = if x.1 ∈ TD ∨ x.1 ∈ E then apFun S x else x := by
  unfold FF
  rw [Perm.mul_apply, PF_prod S E hEs, PF_prod S TD hTD]
  by_cases h1 : x.1 ∈ E
  · have h2 : (apFun S x).1 ∉ TD := Finset.mem_compl.mp (hE (hEs _ h1))
    rw [if_pos h1, if_neg h2, if_pos (Or.inr h1)]
  · rw [if_neg h1]
    by_cases h3 : x.1 ∈ TD
    · rw [if_pos h3, if_pos (Or.inl h3)]
    · rw [if_neg h3, if_neg (by tauto)]

theorem FF_invol (S : EmbeddingScheme G) (TD E : Finset G.Dart) (hTD : ∀ d ∈ TD, d.symm ∈ TD)
    (hEs : ∀ d ∈ E, d.symm ∈ E) (hE : E ⊆ TDᶜ) (x : G.Dart × Bool) :
    FF S TD E (FF S TD E x) = x := by
  have key := FF_apply S TD E hTD hEs hE
  by_cases h : x.1 ∈ TD ∨ x.1 ∈ E
  · have h' : (apFun S x).1 ∈ TD ∨ (apFun S x).1 ∈ E := h.imp (hTD _) (hEs _)
    rw [key x, if_pos h, key, if_pos h', apFun_invol S x]
  · rw [key x, if_neg h, key, if_neg h]

theorem FF_nu (S : EmbeddingScheme G) (TD E : Finset G.Dart) (hTD : ∀ d ∈ TD, d.symm ∈ TD)
    (hEs : ∀ d ∈ E, d.symm ∈ E) (hE : E ⊆ TDᶜ) (x : G.Dart × Bool) :
    FF S TD E (nuF x) = nuF (FF S TD E x) := by
  have key := FF_apply S TD E hTD hEs hE
  rw [key, key]
  by_cases h : x.1 ∈ TD ∨ x.1 ∈ E
  · rw [if_pos (show (nuF x).1 ∈ TD ∨ (nuF x).1 ∈ E from h), if_pos h, apFun_nu]
  · rw [if_neg (show ¬((nuF x).1 ∈ TD ∨ (nuF x).1 ∈ E) from h), if_neg h]

/-- removing the four points of the chord `z.1` from `E × Bool` -/
theorem erase4 (S : EmbeddingScheme G) (E : Finset G.Dart) (z : G.Dart × Bool) :
    ((((E ×ˢ (Finset.univ : Finset Bool)).erase z).erase (apFun S z)).erase (nuF z)).erase
      (apFun S (nuF z)) = del2 E z.1 ×ˢ Finset.univ := by
  rcases z with ⟨q, b⟩
  ext ⟨d, c⟩
  simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_univ, and_true, del2, apFun, nuF,
    ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun hd => ?_, fun hd => ?_, h5⟩
    · subst hd
      cases c <;> cases b <;> cases hs : S.sig q <;> simp [hs] at h1 h3
    · subst hd
      cases c <;> cases b <;> simp at h2 h4
  · rintro ⟨h1, h2, h5⟩
    exact ⟨fun h => h1 h.1, fun h => h2 h.1, fun h => h1 h.1, fun h => h2 h.1, h5⟩

/-- P5: if no chord of `E` can be deleted with a merge, `E` and the tree leave one face pair -/
theorem one_face (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (T : SimpleGraph V) (hT : T.IsTree) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (htd : ∀ d, d ∈ TD ↔ T.Adj d.fst d.snd)
    (E : Finset G.Dart) (hE : E ⊆ TDᶜ) (hEs : ∀ d ∈ E, d.symm ∈ E)
    (hstop : ∀ q ∈ E, norb (PhiE S TD E) < norb (PhiE S TD (del2 E q)) + 2) :
    norb (PhiE S TD E) = 2 := by
  classical
  have hTD : ∀ d ∈ TD, d.symm ∈ TD := I.td_symm
  have hFa := FF_apply S TD E hTD hEs hE
  have hFF := FF_invol S TD E hTD hEs hE
  have hFnu := FF_nu S TD E hTD hEs hE
  set Φ := PhiE S TD E with hΦ
  set F := FF S TD E with hF
  have hΦa : ∀ x, Φ x = SigP S (F x) := fun x => by rw [hΦ, phiE_eq]; rfl
  have hμinv : Function.Involutive (fun x => F (nuF x)) := fun x => by
    simp only
    rw [← hFnu, hFF, nuF_nuF]
  let μ : Perm (G.Dart × Bool) := hμinv.toPerm
  have hμ : ∀ x, μ x = F (nuF x) := fun _ => rfl
  have hμμ : ∀ x, μ (μ x) = x := fun x => hμinv x
  have hconj : ∀ x, μ (Φ (μ x)) = Φ⁻¹ x := by
    intro x
    rw [eq_comm, Perm.inv_eq_iff_eq]
    simp only [hμ, hΦa, hFF]
    exact (SigP_nu S x).symm
  have hfp : ∀ x, μ x ≠ x := by
    intro x h
    rw [hμ, hFa] at h
    split_ifs at h
    · exact (SimpleGraph.Dart.symm_ne x.1) (congrArg Prod.fst h)
    · have := congrArg Prod.snd h
      simp [nuF] at this
  have hfp2 : ∀ x, μ (Φ x) ≠ x := by
    intro x h
    rw [hμ, hΦa] at h
    have h3 := congrArg F h
    rw [hFF] at h3
    have h4 := congrArg Prod.snd h3
    simp [nuF, SigP_apply] at h4
  have hnsc : ∀ x, ¬ SameCycle Φ x (μ x) := mirror_not_sc Φ μ hμμ hconj hfp hfp2
  have hmir : ∀ a b, SameCycle Φ a b → SameCycle Φ (μ a) (μ b) := by
    intro a b h
    obtain ⟨j, rfl⟩ := h.exists_nat_pow_eq
    rw [mirror_pow Φ μ hμμ hconj a j]
    exact sameCycle_inv.mp (sc_of_nat j rfl)
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨d0, -⟩ := exists_dart_at hconn h2 v0
  set x0 : G.Dart × Bool := (d0, p d0.fst) with hx0
  let κ : G.Dart × Bool → Prop := fun y => SameCycle Φ x0 y ∨ SameCycle Φ (μ x0) y
  have hκsc : ∀ a b, SameCycle Φ a b → (κ a ↔ κ b) := by
    intro a b h
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (h1.trans h)
      · exact Or.inr (h1.trans h)
    · rintro (h1 | h1)
      · exact Or.inl (h1.trans h.symm)
      · exact Or.inr (h1.trans h.symm)
  have hκΦ : ∀ y, κ (Φ y) ↔ κ y := fun y => (hκsc _ _ (sc_apply Φ y)).symm
  have hκμ : ∀ y, κ (μ y) ↔ κ y := by
    have one : ∀ y, κ y → κ (μ y) := by
      rintro y (h | h)
      · exact Or.inr (hmir _ _ h)
      · left
        have := hmir _ _ h
        rwa [hμμ] at this
    exact fun y => ⟨fun h => by have := one _ h; rwa [hμμ] at this, one y⟩
  have hκF_sig : ∀ z, κ (SigP S z) ↔ κ (F z) := by
    intro z
    have e : SigP S z = Φ (F z) := by rw [hΦa, hFF]
    rw [e]; exact hκΦ (F z)
  have hμF : ∀ y, μ (F y) = nuF y := by
    intro y; rw [hμ, hFnu, hFF]
  -- chords never separate classes
  have hchord : ∀ z : G.Dart × Bool, z.1 ∈ E → (κ (F z) ↔ κ z) := by
    intro z hz
    by_contra hbad
    have hq := hstop z.1 hz
    have hzs : z.1.symm ∈ E := hEs _ hz
    have hFz : F z = apFun S z := by rw [hFa, if_pos (Or.inr hz)]
    have hFnz : F (nuF z) = apFun S (nuF z) := by
      rw [hFa, if_pos (show (nuF z).1 ∈ TD ∨ (nuF z).1 ∈ E from Or.inr hz)]
    have hne1 : ¬ SameCycle Φ z (F z) := fun h => hbad (hκsc _ _ h).symm
    have hne2 : ¬ SameCycle (Φ * swap z (F z)) (nuF z) (F (nuF z)) := by
      intro h
      have hy : F (nuF z) = μ z := (hμ z).symm
      have hx : nuF z = μ (F z) := (hμF z).symm
      rcases merge_classes Φ h with h' | ⟨h1, _⟩
      · rw [hy, hx] at h'
        have := hmir _ _ h'
        rw [hμμ, hμμ] at this
        exact hne1 this.symm
      · rcases h1 with h1 | h1
        · rw [hx] at h1
          exact hbad ((hκμ _).symm.trans (hκsc _ _ h1))
        · rw [hx] at h1
          exact hnsc (F z) h1.symm
    -- decomposition of the chord involution
    rcases z with ⟨q, b⟩
    have hqE : (q, b) ∈ E ×ˢ (Finset.univ : Finset Bool) :=
      Finset.mem_product.mpr ⟨hz, Finset.mem_univ _⟩
    have hqE' : apFun S (q, b) ∈ E ×ˢ (Finset.univ : Finset Bool) :=
      Finset.mem_product.mpr ⟨hzs, Finset.mem_univ _⟩
    have hne : (q, b) ≠ apFun S (q, b) := (apFun_fp S {(q, b)} (q, b) (by simp)).symm
    have e1 := PF_decomp_r (apFun S) (apFun_invol S) _ hqE hqE' hne
    have hqs_ne : q ≠ q.symm := (SimpleGraph.Dart.symm_ne q).symm
    have h0' : nuF (q, b) ∈ ((E ×ˢ (Finset.univ : Finset Bool)).erase (q, b)).erase
        (apFun S (q, b)) := by
      simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_univ, and_true, nuF, apFun,
        ne_eq, Prod.mk.injEq]
      refine ⟨?_, ?_, hz⟩
      · rintro ⟨h, -⟩; exact hqs_ne h
      · rintro ⟨-, h⟩; cases b <;> simp at h
    have h1' : apFun S (nuF (q, b)) ∈ ((E ×ˢ (Finset.univ : Finset Bool)).erase (q, b)).erase
        (apFun S (q, b)) := by
      simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_univ, and_true, nuF, apFun,
        ne_eq, Prod.mk.injEq]
      refine ⟨?_, ?_, hzs⟩
      · rintro ⟨-, h⟩; cases b <;> cases S.sig q <;> simp at h
      · rintro ⟨h, -⟩; exact hqs_ne h.symm
    have hne' : nuF (q, b) ≠ apFun S (nuF (q, b)) := (apFun_fp S {nuF (q, b)} _ (by simp)).symm
    have e2 := PF_decomp_r (apFun S) (apFun_invol S) _ h0' h1' hne'
    rw [e2, erase4 S E (q, b)] at e1
    have hdel : PhiE S TD (del2 E q) =
        Φ * swap (q, b) (F (q, b)) * swap (nuF (q, b)) (F (nuF (q, b))) := by
      rw [hFz, hFnz, hΦ, PhiE, PhiE, e1]
      simp only [mul_assoc, Equiv.swap_mul_self_mul, Equiv.swap_mul_self, mul_one]
    have n1 := norb_merge Φ hne1
    have n2 := norb_merge (Φ * swap (q, b) (F (q, b))) hne2
    rw [← hdel] at n2
    have hq' : norb Φ < norb (PhiE S TD (del2 E q)) + 2 := hq
    omega
  -- the good relation
  let good : G.Dart × Bool → Prop := fun y => (κ (F y) ↔ κ y)
  have hgood_F : ∀ y, good (F y) ↔ good y := by
    intro y
    show (κ (F (F y)) ↔ κ (F y)) ↔ (κ (F y) ↔ κ y)
    rw [hFF]; exact iff_comm
  have hgood_nu : ∀ y, good (nuF y) ↔ good y := by
    intro y
    show (κ (F (nuF y)) ↔ κ (nuF y)) ↔ (κ (F y) ↔ κ y)
    have e1 : κ (F (nuF y)) ↔ κ y := by rw [← hμ]; exact hκμ y
    have e2 : κ (nuF y) ↔ κ (F y) := by rw [← hμF]; exact hκμ (F y)
    rw [e1, e2]; exact iff_comm
  -- bad tree darts
  set B := TD.filter (fun d => ¬ good (d, false)) with hBdef
  have hBsymm : ∀ d ∈ B, d.symm ∈ B := by
    intro d hd
    rw [hBdef, Finset.mem_filter] at hd ⊢
    refine ⟨hTD _ hd.1, fun hg => hd.2 ?_⟩
    have hFd : F (d, false) = apFun S (d, false) := by rw [hFa, if_pos (Or.inl hd.1)]
    rw [← hgood_F, hFd]
    cases hs : S.sig d
    · have e : apFun S (d, false) = (d.symm, false) := by simp [apFun, hs]
      rw [e]; exact hg
    · have e : apFun S (d, false) = nuF (d.symm, false) := by simp [apFun, nuF, hs]
      rw [e, hgood_nu]; exact hg
  have hchange : ∀ z : G.Dart × Bool, (decide (κ (SigP S z)) ≠ decide (κ z)) ↔
      (z.1 ∈ TD ∧ ¬ good z) := by
    intro z
    have e0 : (decide (κ (SigP S z)) ≠ decide (κ z)) ↔ ¬ good z := by
      show _ ↔ ¬ (κ (F z) ↔ κ z)
      rw [ne_eq, decide_eq_decide, hκF_sig]
    rw [e0]
    by_cases hz : z.1 ∈ TD
    · simp [hz]
    · simp only [hz, false_and, iff_false, not_not]
      by_cases hz' : z.1 ∈ E
      · exact hchord z hz'
      · show κ (F z) ↔ κ z
        rw [hFa, if_neg (by tauto)]
  have hev : ∀ v, Even (B.filter (fun d => d.fst = v)).card := by
    intro v
    set Cv := (Finset.univ : Finset (G.Dart × Bool)).filter (fun x => x.1.fst = v ∧ x.2 = false)
      with hCv
    have hC : ∀ z ∈ Cv, SigP S z ∈ Cv := by
      intro z hz
      rw [hCv, Finset.mem_filter] at hz ⊢
      obtain ⟨-, h1, h2⟩ := hz
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [SigP_apply, h2]; simp only [Bool.false_eq_true, if_false]; rw [S.rot_fst]; exact h1
      · rw [SigP_apply]; exact h2
    have hE2 := even_changes (SigP S) Cv hC (fun y => decide (κ y))
    have hset : Cv.filter (fun z => decide (κ (SigP S z)) ≠ decide (κ z)) =
        (B.filter (fun d => d.fst = v)).map ⟨fun d => (d, false), fun a b h => by simpa using h⟩ := by
      ext ⟨d, c⟩
      rw [Finset.mem_filter, hchange, hCv, Finset.mem_filter, Finset.mem_map]
      constructor
      · rintro ⟨⟨-, hv, hc⟩, hT1, hg⟩
        simp only at hv hc hT1 hg
        subst hc
        exact ⟨d, by rw [Finset.mem_filter, hBdef, Finset.mem_filter]; exact ⟨⟨hT1, hg⟩, hv⟩, rfl⟩
      · rintro ⟨d', hd', he⟩
        rw [Finset.mem_filter, hBdef, Finset.mem_filter] at hd'
        have he' : (d', false) = (d, c) := he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        exact ⟨⟨Finset.mem_univ _, hd'.2, rfl⟩, hd'.1.1, hd'.1.2⟩
    rw [hset, Finset.card_map] at hE2
    exact hE2
  have hB0 : B = ∅ := even_tree_empty T hT r B
    (fun d hd => (htd d).mp (Finset.mem_filter.mp hd).1) hBsymm hev
  have hgood_all : ∀ y, good y := by
    rintro ⟨d, c⟩
    by_cases hd : d ∈ TD
    · have hg : good (d, false) := by
        by_contra hng
        have : d ∈ B := by rw [hBdef, Finset.mem_filter]; exact ⟨hd, hng⟩
        rw [hB0] at this; simp at this
      cases c
      · exact hg
      · exact (hgood_nu (d, false)).mpr hg
    · by_cases hd' : d ∈ E
      · exact hchord (d, c) hd'
      · show κ (F (d, c)) ↔ κ (d, c)
        rw [hFa, if_neg (by tauto)]
  have hκSig : ∀ y, κ (SigP S y) ↔ κ y := fun y => (hκF_sig y).trans (hgood_all y)
  have hκψ : ∀ y, κ ((SigP S * sprod L) y) ↔ κ y := by
    intro y
    rw [sprod_eq_PF I, Perm.mul_apply, PF_prod S TD hTD]
    split_ifs with h
    · have e : apFun S y = F y := by rw [hFa, if_pos (Or.inl h)]
      rw [e]; exact (hκSig _).trans (hgood_all y)
    · exact hκSig y
  have hκnu : ∀ y, κ (nuF y) ↔ κ y := by
    intro y
    have e : κ (F (nuF y)) ↔ κ y := by rw [← hμ]; exact hκμ y
    exact (hgood_all (nuF y)).symm.trans e
  have base : ∀ y, sh p y = false → κ y := fun y hy =>
    (pres (SigP S * sprod L) κ hκψ (sheet_cycle' S hconn h2 I d0 y hy)).mpr
      (Or.inl (SameCycle.refl _ _))
  have hall : ∀ y, κ y := by
    rintro ⟨d, c⟩
    cases hy : sh p (d, c)
    · exact base _ hy
    · apply (hκnu (d, c)).mp
      apply base
      simp only [sh, nuF] at hy ⊢
      cases c <;> cases h : p d.fst <;> simp_all
  -- count the orbits
  unfold norb
  apply le_antisymm
  · have hsurj : Function.Surjective (fun b : Bool =>
        if b then Quotient.mk (SameCycle.setoid Φ) x0 else Quotient.mk (SameCycle.setoid Φ) (μ x0)) := by
      intro c
      obtain ⟨y, rfl⟩ := Quotient.exists_rep c
      rcases hall y with h | h
      · exact ⟨true, Quotient.sound h⟩
      · exact ⟨false, Quotient.sound h⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  · have hne : Quotient.mk (SameCycle.setoid Φ) x0 ≠ Quotient.mk (SameCycle.setoid Φ) (μ x0) :=
      fun h => hnsc x0 (Quotient.exact h)
    have : Nontrivial (Quotient (SameCycle.setoid Φ)) := ⟨⟨_, _, hne⟩⟩
    have := Finite.one_lt_card_iff_nontrivial.mpr this
    omega

end face

end PQL21

/-! C2 P6 for lemma_21 (e1368385): the kept chord set `E` has at most `eulerGenus` edges. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section count

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem sdiff_symm (D A : Finset G.Dart) (hD : ∀ d ∈ D, d.symm ∈ D) (hA : ∀ d ∈ A, d.symm ∈ A) :
    ∀ d ∈ D \ A, d.symm ∈ D \ A := by
  intro d hd
  rw [Finset.mem_sdiff] at hd ⊢
  exact ⟨hD _ hd.1, fun h => hd.2 (by simpa using hA _ h)⟩

theorem PF_split (S : EmbeddingScheme G) (D A : Finset G.Dart) (hD : ∀ d ∈ D, d.symm ∈ D)
    (hA : ∀ d ∈ A, d.symm ∈ A) (hAD : A ⊆ D) :
    PF (apFun S) (apFun_invol S) (A ×ˢ Finset.univ) *
      PF (apFun S) (apFun_invol S) ((D \ A) ×ˢ Finset.univ) =
    PF (apFun S) (apFun_invol S) (D ×ˢ Finset.univ) := by
  have hDA := sdiff_symm D A hD hA
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, PF_prod S _ hDA, PF_prod S _ hD]
  by_cases h1 : x.1 ∈ D \ A
  · have hn : (apFun S x).1 ∉ A := fun h =>
      (Finset.mem_sdiff.mp h1).2 (by simpa [apFun] using hA _ h)
    rw [if_pos h1, PF_prod S _ hA, if_neg hn, if_pos (Finset.mem_sdiff.mp h1).1]
  · rw [if_neg h1, PF_prod S _ hA]
    by_cases h2 : x.1 ∈ A
    · rw [if_pos h2, if_pos (hAD h2)]
    · rw [if_neg h2, if_neg]
      intro h
      exact h1 (Finset.mem_sdiff.mpr ⟨h, h2⟩)

/-- P6: one face pair forces `|E| ≤ 2 · eulerGenus` (`E` counted in darts) -/
theorem genus_bound (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (E : Finset G.Dart) (hE : E ⊆ TDᶜ)
    (hEs : ∀ d ∈ E, d.symm ∈ E) (h1 : norb (PhiE S TD E) = 2) :
    (E.card : ℤ) ≤ 2 * S.eulerGenus := by
  have hTD : ∀ d ∈ TD, d.symm ∈ TD := I.td_symm
  have hTc : ∀ d ∈ TDᶜ, d.symm ∈ TDᶜ := by
    intro d hd
    simp only [Finset.mem_compl] at hd ⊢
    exact fun h => hd (by simpa using hTD _ h)
  have hsplit := PF_split S TDᶜ E hTc hEs hE
  have hfull : PhiE S TD E * PF (apFun S) (apFun_invol S) ((TDᶜ \ E) ×ˢ Finset.univ) =
      SigP S * AP S := by
    rw [← phiE_full S TD hTD]
    simp only [PhiE, mul_assoc, hsplit]
  have hCs := sdiff_symm TDᶜ E hTc hEs
  have hcl : ∀ x ∈ (TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool),
      apFun S x ∈ (TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool) := by
    intro x hx
    rw [Finset.mem_product] at hx ⊢
    exact ⟨hCs _ hx.1, Finset.mem_univ _⟩
  have hle := PF_le (apFun S) (apFun_invol S) _ _ rfl hcl (apFun_fp S _) (PhiE S TD E)
  rw [hfull, h1] at hle
  have hc2 : ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card = 2 * (TDᶜ \ E).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  have hsd : (TDᶜ \ E).card + E.card = TDᶜ.card := Finset.card_sdiff_add_card_eq_card hE
  have hcomp : TDᶜ.card + TD.card = Fintype.card G.Dart := by
    rw [Finset.card_compl]; have := Finset.card_le_univ TD; omega
  have hlen := I.len
  rw [Finset.card_univ] at hlen
  have hLT := card_TD_L I
  have hm := G.dart_card_eq_twice_card_edges
  have hdeg := exists_dart_at hconn h2
  have hc1 : Nat.card G.ConnectedComponent = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    obtain ⟨v⟩ := hconn.nonempty
    refine ⟨G.connectedComponentMk v, fun c => ?_⟩
    refine c.ind (fun w => ?_)
    exact SimpleGraph.ConnectedComponent.eq.mpr (hconn.preconnected w v)
  have hiso : (Finset.univ.filter (fun v => G.degree v = 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _ hv0
    obtain ⟨d, hd⟩ := hdeg v
    have := (SimpleGraph.degree_pos_iff_exists_adj (G := G) (v := v)).mpr
      ⟨d.snd, by rw [← hd]; exact d.adj⟩
    omega
  have hfo := card_faceOrbit S
  unfold EmbeddingScheme.eulerGenus EmbeddingScheme.faces
  rw [hc1, hiso, hfo]
  rw [hc2] at hle
  push_cast
  omega

end count

end PQL21

/-! C2 P9a for lemma_21 (e1368385): geodesics in a tree, ancestor closure, layer bound. -/

namespace PQL21

open SimpleGraph

section graph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the vertex of a tree path `r → e` at depth `dist r v` is `v`, for `v` on the geodesic -/
theorem geodesic_vert (T : SimpleGraph V) (hT : T.IsTree) {r e v : V}
    (hv : T.dist r v + T.dist v e = T.dist r e) (p : T.Walk r e) (hp : p.IsPath) :
    p.getVert (T.dist r v) = v := by
  obtain ⟨p1, -, h1⟩ := hT.connected.exists_path_of_dist r v
  obtain ⟨p2, -, h2⟩ := hT.connected.exists_path_of_dist v e
  have hl : (p1.append p2).length = T.dist r e := by rw [Walk.length_append]; omega
  have hpath := (p1.append p2).isPath_of_length_eq_dist hl
  have heq : p = p1.append p2 :=
    congrArg Subtype.val ((hT.isAcyclic.subsingleton_path r e).elim ⟨p, hp⟩ ⟨_, hpath⟩)
  rw [heq, Walk.getVert_append, if_neg (by omega), h1, Nat.sub_self, Walk.getVert_zero]

/-- two vertices on the same geodesic at the same depth coincide -/
theorem geodesic_unique (T : SimpleGraph V) (hT : T.IsTree) {r e v v' : V}
    (hv : T.dist r v + T.dist v e = T.dist r e) (hv' : T.dist r v' + T.dist v' e = T.dist r e)
    (hd : T.dist r v = T.dist r v') : v = v' := by
  obtain ⟨p, hp, -⟩ := hT.connected.exists_path_of_dist r e
  have a := geodesic_vert T hT hv p hp
  have b := geodesic_vert T hT hv' p hp
  rw [hd] at a
  exact a.symm.trans b

/-- ancestors of ancestors are ancestors -/
theorem anc_trans (T : SimpleGraph V) (hT : T.IsTree) {r u v e : V}
    (huv : T.dist r u + T.dist u v = T.dist r v) (hve : T.dist r v + T.dist v e = T.dist r e) :
    T.dist r u + T.dist u e = T.dist r e := by
  have t1 := hT.connected.dist_triangle (u := r) (v := u) (w := e)
  have t2 := hT.connected.dist_triangle (u := u) (v := v) (w := e)
  omega

/-- P9a: each BFS layer of an ancestor-closed set generated by `Ends` has at most `|Ends|`
vertices -/
theorem layer_bound (T : SimpleGraph V) (hT : T.IsTree) (r : V) (Ends Zv : Finset V)
    (hZ : ∀ v ∈ Zv, ∃ e ∈ Ends, T.dist r v + T.dist v e = T.dist r e) (i : ℕ) :
    (Zv.filter (fun v => T.dist r v = i)).card ≤ Ends.card := by
  classical
  choose! f hf using hZ
  apply Finset.card_le_card_of_injOn f
  · intro v hv
    exact (hf v (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1).1
  · intro v hv v' hv' he
    have m1 := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
    have m2 := Finset.mem_filter.mp (Finset.mem_coe.mp hv')
    have h1 := (hf v m1.1).2
    have h2 := (hf v' m2.1).2
    rw [he] at h1
    exact geodesic_unique T hT h1 h2 (by rw [m1.2, m2.2])

end graph

end PQL21

set_option autoImplicit false

/-! P9b (s5): the graph part of lemma_21. A rooted tree from a parent map (`ParT`), the cut graph
`G⁺` on `CW` (root + private paths to the tops + the vertices outside `Zs`), BFS tree, distances,
vertical paths. -/

namespace PQL21

open SimpleGraph

section partree

/-- a rooted tree given by a parent map lowering a depth function by one -/
structure ParT (W : Type) where
  root : W
  par : W → W
  dep : W → ℕ
  dep_root : ∀ w, dep w = 0 ↔ w = root
  dep_par : ∀ w, w ≠ root → dep (par w) + 1 = dep w

variable {W : Type}

theorem ParT.par_ne (P : ParT W) (w : W) (hw : w ≠ P.root) : P.par w ≠ w := by
  intro h
  have := P.dep_par w hw
  rw [h] at this
  omega

def ParT.gr (P : ParT W) : SimpleGraph W where
  Adj a b := (a ≠ P.root ∧ P.par a = b) ∨ (b ≠ P.root ∧ P.par b = a)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact P.par_ne a h1 h2⟩

theorem ParT.gr_adj (P : ParT W) {a b : W} :
    P.gr.Adj a b ↔ (a ≠ P.root ∧ P.par a = b) ∨ (b ≠ P.root ∧ P.par b = a) := Iff.rfl

theorem ParT.adj_dep (P : ParT W) {a b : W} (h : P.gr.Adj a b) :
    P.dep a = P.dep b + 1 ∨ P.dep b = P.dep a + 1 := by
  rcases P.gr_adj.1 h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact Or.inl (P.dep_par a h1).symm
  · exact Or.inr (P.dep_par b h1).symm

theorem ParT.adj_up (P : ParT W) {a b : W} (h : P.gr.Adj a b) (hd : P.dep b = P.dep a + 1) :
    b ≠ P.root ∧ P.par b = a := by
  rcases P.gr_adj.1 h with ⟨h1, h2⟩ | h
  · subst h2
    have := P.dep_par a h1
    omega
  · exact h

theorem ParT.walk_root (P : ParT W) : ∀ (n : ℕ) (w : W), P.dep w = n →
    ∃ p : P.gr.Walk P.root w, p.length = n := by
  intro n
  induction n with
  | zero =>
    intro w hw
    rw [(P.dep_root w).1 hw]
    exact ⟨Walk.nil, rfl⟩
  | succ n ih =>
    intro w hw
    have hne : w ≠ P.root := by
      intro h
      have := (P.dep_root w).2 h
      omega
    obtain ⟨p, hp⟩ := ih (P.par w) (by have := P.dep_par w hne; omega)
    exact ⟨p.concat (P.gr_adj.2 (Or.inr ⟨hne, rfl⟩)), by rw [Walk.length_concat, hp]⟩

theorem dep_le_walk {H : SimpleGraph W} (δ : W → ℕ) (hδ : ∀ a b, H.Adj a b → δ b ≤ δ a + 1) :
    ∀ {a b : W} (p : H.Walk a b), δ b ≤ δ a + p.length := by
  intro a b p
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [Walk.length_cons]
    have := hδ _ _ h
    omega

theorem ParT.reach (P : ParT W) (w : W) : P.gr.Reachable P.root w :=
  ⟨(P.walk_root _ w rfl).choose⟩

theorem ParT.connected (P : ParT W) : P.gr.Connected := by
  have : Nonempty W := ⟨P.root⟩
  exact ⟨fun a b => (P.reach a).symm.trans (P.reach b)⟩

theorem ParT.dist_eq (P : ParT W) (w : W) : P.gr.dist P.root w = P.dep w := by
  obtain ⟨p, hp⟩ := P.walk_root _ w rfl
  have h1 := dist_le p
  obtain ⟨q, hq⟩ := (P.reach w).exists_walk_length_eq_dist
  have h2 := dep_le_walk P.dep (fun a b h => by rcases P.adj_dep h with h | h <;> omega) q
  have h0 := (P.dep_root P.root).2 rfl
  omega

/-- a supergraph whose edges change the depth by at most one has the same root distances -/
theorem ParT.dist_sup (P : ParT W) (H : SimpleGraph W) (hle : P.gr ≤ H)
    (hH : ∀ a b, H.Adj a b → P.dep b ≤ P.dep a + 1) (w : W) : H.dist P.root w = P.dep w := by
  obtain ⟨p, hp⟩ := P.walk_root _ w rfl
  have h1 := dist_le (p.mapLe hle)
  rw [Walk.length_mapLe] at h1
  obtain ⟨q, hq⟩ := ((P.reach w).mono hle).exists_walk_length_eq_dist
  have h2 := dep_le_walk P.dep hH q
  have h0 := (P.dep_root P.root).2 rfl
  omega

theorem ParT.isTree [Finite W] (P : ParT W) : P.gr.IsTree := by
  classical
  haveI := Fintype.ofFinite W
  rw [isTree_iff_connected_and_card]
  refine ⟨P.connected, ?_⟩
  let f : {a : W // a ≠ P.root} → P.gr.edgeSet := fun a =>
    ⟨s(a.1, P.par a.1), (mem_edgeSet _).2 (P.gr_adj.2 (Or.inl ⟨a.2, rfl⟩))⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' : s(a, P.par a) = s(b, P.par b) := congrArg Subtype.val h
      rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h1
      · exfalso
        have e1 := P.dep_par a ha
        have e2 := P.dep_par b hb
        rw [h2] at e1
        rw [← h1] at e2
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h x y =>
        rcases P.gr_adj.1 ((mem_edgeSet _).1 he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨⟨x, h1⟩, by simp [f, h2]⟩
        · exact ⟨⟨y, h1⟩, by simp [f, h2, Sym2.eq_swap]⟩
  rw [← Nat.card_eq_of_bijective f hf]
  have hc : Nat.card {a : W // a ≠ P.root} = Fintype.card W - 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Set.card_ne_eq P.root
  have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨P.root⟩
  rw [hc, Nat.card_eq_fintype_card]
  omega

end partree

section cut

variable {V : Type} [Fintype V] [DecidableEq V]

theorem dist_lt_card (H : SimpleGraph V) (u v : V) : H.dist u v < Fintype.card V := by
  by_cases hr : H.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have h1 := dist_le p.bypass
    have h2 := p.length_bypass_le_length
    have h3 := p.bypass_isPath.length_lt
    omega
  · rw [dist_eq_zero_of_not_reachable hr]
    exact Fintype.card_pos_iff.2 ⟨u⟩

theorem exists_tpar (T : SimpleGraph V) (hT : T.IsTree) (r v : V) (hv : v ≠ r) :
    ∃ w, T.Adj v w ∧ T.dist r w + 1 = T.dist r v := by
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact absurd rfl hv
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    have h1 := dist_le q
    rw [Walk.length_cons] at hp
    have h2 := hT.connected.dist_triangle (u := r) (v := w) (w := v)
    have h3 : T.dist w v = 1 := dist_eq_one_iff_adj.mpr h.symm
    have e1 : T.dist v r = T.dist r v := dist_comm
    have e2 : T.dist w r = T.dist r w := dist_comm
    omega

variable (T : SimpleGraph V) (r : V) (Zs : Set V)

open Classical in
/-- the T-parent (closer to `r`), `v` itself if there is none -/
noncomputable def tpar (v : V) : V :=
  if h : ∃ w, T.Adj v w ∧ T.dist r w + 1 = T.dist r v then h.choose else v

theorem tpar_spec (hT : T.IsTree) {v : V} (hv : v ≠ r) :
    T.Adj v (tpar T r v) ∧ T.dist r (tpar T r v) + 1 = T.dist r v := by
  have h := exists_tpar T hT r v hv
  unfold tpar
  rw [dif_pos h]
  exact h.choose_spec

/-- vertices of `G⁺`: `none` = new root, `inl v` for `v ∉ Zs`, `inr (x, j)` = private node `j` of
the top `x` (`x ∉ Zs`, T-parent in `Zs`, `1 ≤ j < dist r x`) -/
def cvalid : Option (V ⊕ V × Fin (Fintype.card V)) → Prop
  | none => True
  | some (Sum.inl v) => v ∉ Zs
  | some (Sum.inr (x, j)) => x ∉ Zs ∧ tpar T r x ∈ Zs ∧ 1 ≤ (j : ℕ) ∧ (j : ℕ) < T.dist r x

def CW : Type := {w : Option (V ⊕ V × Fin (Fintype.card V)) // cvalid T r Zs w}

noncomputable scoped instance : Fintype (CW T r Zs) := by
  classical
  unfold CW
  infer_instance

scoped instance : Finite (CW T r Zs) := by
  classical
  infer_instance

def croot : CW T r Zs := ⟨none, trivial⟩

open Classical in
noncomputable def cpar : CW T r Zs → CW T r Zs
  | ⟨none, _⟩ => croot T r Zs
  | ⟨some (Sum.inl v), h⟩ =>
    if hp : tpar T r v ∈ Zs then
      (if hj : 1 < T.dist r v then
        ⟨some (Sum.inr (v, ⟨T.dist r v - 1, by have := dist_lt_card T r v; omega⟩)),
          ⟨h, hp, by simp only; omega, by simp only; omega⟩⟩
      else croot T r Zs)
    else ⟨some (Sum.inl (tpar T r v)), hp⟩
  | ⟨some (Sum.inr (x, j)), h⟩ =>
    if hj : (j : ℕ) = 1 then croot T r Zs
    else ⟨some (Sum.inr (x, ⟨(j : ℕ) - 1, by omega⟩)),
      ⟨h.1, h.2.1, by have := h.2.2.1; simp only; omega, by have := h.2.2.2; simp only; omega⟩⟩

noncomputable def cdep : CW T r Zs → ℕ
  | ⟨none, _⟩ => 0
  | ⟨some (Sum.inl v), _⟩ => T.dist r v
  | ⟨some (Sum.inr (_, j)), _⟩ => (j : ℕ)

theorem dist_pos_of_ne (hT : T.IsTree) {v : V} (hv : v ≠ r) : 1 ≤ T.dist r v := by
  have := (tpar_spec T r hT hv).2
  omega

noncomputable def cP (hT : T.IsTree) (hr : r ∈ Zs) : ParT (CW T r Zs) where
  root := croot T r Zs
  par := cpar T r Zs
  dep := cdep T r Zs
  dep_root := by
    rintro ⟨w, hw⟩
    rcases w with _ | v | ⟨x, j⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · constructor
      · intro h
        have h' : T.dist r v = 0 := h
        have : r = v := (hT.connected.dist_eq_zero_iff).1 h'
        exact absurd (this ▸ hr) hw
      · intro h
        exact absurd (congrArg Subtype.val h) (by simp [croot])
    · constructor
      · intro h
        have h' : (j : ℕ) = 0 := h
        have := hw.2.2.1
        omega
      · intro h
        exact absurd (congrArg Subtype.val h) (by simp [croot])
  dep_par := by
    rintro ⟨w, hw⟩ hne
    rcases w with _ | v | ⟨x, j⟩
    · exact absurd rfl hne
    · have hvr : v ≠ r := fun e => hw (e ▸ hr)
      have hs := (tpar_spec T r hT hvr).2
      have h1 := dist_pos_of_ne T r hT hvr
      by_cases hp : tpar T r v ∈ Zs
      · by_cases hj : 1 < T.dist r v
        · simp only [cpar, hp, hj, ↓reduceDIte, cdep]
          omega
        · simp only [cpar, hp, hj, ↓reduceDIte, cdep, croot]
          omega
      · simp only [cpar, hp, ↓reduceDIte, cdep]
        exact hs
    · have h1 := hw.2.2.1
      by_cases hj : (j : ℕ) = 1
      · simp only [cpar, hj, ↓reduceDIte, cdep, croot]
      · simp only [cpar, hj, ↓reduceDIte, cdep]
        omega

/-- the embedding of `V ∖ Zs` -/
def cι : ↥Zsᶜ ↪ CW T r Zs where
  toFun a := ⟨some (Sum.inl a.1), a.2⟩
  inj' := by
    intro a b h
    have := congrArg Subtype.val h
    simp only [Option.some.injEq, Sum.inl.injEq] at this
    exact Subtype.ext this

/-- `G⁺` -/
noncomputable def cG (G : SimpleGraph V) (hT : T.IsTree) (hr : r ∈ Zs) : SimpleGraph (CW T r Zs) :=
  (cP T r Zs hT hr).gr ⊔ (G.induce Zsᶜ).map (cι T r Zs)

end cut

end PQL21

namespace PQL21

open SimpleGraph PlanarQueue.Genus

section cutpack

variable {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) (r : V) (Zs : Set V)

def getV : CW T r Zs → Option V
  | ⟨some (Sum.inl v), _⟩ => some v
  | _ => none

theorem getV_some {w : CW T r Zs} {v : V} (h : getV T r Zs w = some v) :
    ∃ hv : v ∈ Zsᶜ, w = cι T r Zs ⟨v, hv⟩ := by
  rcases w with ⟨_ | u | ⟨x, j⟩, hw⟩
  · simp [getV] at h
  · simp only [getV, Option.some.injEq] at h
    subst h
    exact ⟨hw, rfl⟩
  · simp [getV] at h

theorem par_to_inl (hT : T.IsTree) (hr : r ∈ Zs) {b : CW T r Zs} {v : V} (hv : v ∈ Zsᶜ)
    (h : cpar T r Zs b = cι T r Zs ⟨v, hv⟩) :
    ∃ w, ∃ hw : w ∈ Zsᶜ, b = cι T r Zs ⟨w, hw⟩ ∧ T.Adj v w ∧ T.dist r w = T.dist r v + 1 := by
  have hv' : ((cι T r Zs ⟨v, hv⟩ : CW T r Zs)).1 = some (Sum.inl v) := rfl
  rcases b with ⟨_ | w | ⟨x, j⟩, hb⟩
  · have := congrArg Subtype.val h
    rw [hv'] at this
    simp [cpar, croot] at this
  · by_cases hp : tpar T r w ∈ Zs
    · by_cases hj : 1 < T.dist r w
      · have := congrArg Subtype.val h
        rw [hv'] at this
        simp only [cpar, hp, hj, ↓reduceDIte] at this
        simp at this
      · have := congrArg Subtype.val h
        rw [hv'] at this
        simp only [cpar, hp, hj, ↓reduceDIte, croot] at this
        simp at this
    · have := congrArg Subtype.val h
      rw [hv'] at this
      simp only [cpar, hp, ↓reduceDIte, Option.some.injEq, Sum.inl.injEq] at this
      have hwr : w ≠ r := fun e => hb (e ▸ hr)
      have hs := tpar_spec T r hT hwr
      rw [this] at hs
      exact ⟨w, hb, rfl, hs.1.symm, by omega⟩
  · by_cases hj : (j : ℕ) = 1
    · have := congrArg Subtype.val h
      rw [hv'] at this
      simp only [cpar, hj, ↓reduceDIte, croot] at this
      simp at this
    · have := congrArg Subtype.val h
      rw [hv'] at this
      simp only [cpar, hj, ↓reduceDIte] at this
      simp at this

theorem chainV (hT : T.IsTree) (hr : r ∈ Zs) : ∀ (l : List (CW T r Zs)) (a : CW T r Zs),
    (a :: l).IsChain (fun a b => b ≠ croot T r Zs ∧ cpar T r Zs b = a) →
    ((a :: l).filterMap (getV T r Zs)).IsChain
      (fun v w => T.Adj v w ∧ T.dist r w = T.dist r v + 1) := by
  intro l
  induction l with
  | nil =>
    intro a _
    rcases ha : getV T r Zs a with _ | v
    · rw [List.filterMap_cons_none ha]
      exact List.IsChain.nil
    · rw [List.filterMap_cons_some ha]
      exact List.IsChain.singleton _
  | cons b l ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    have hb := ih b h.2
    rcases ha : getV T r Zs a with _ | v
    · rw [List.filterMap_cons_none ha]
      exact hb
    · obtain ⟨hv, rfl⟩ := getV_some T r Zs ha
      obtain ⟨w, hw, rfl, h1, h2⟩ := par_to_inl T r Zs hT hr hv h.1.2
      rw [List.filterMap_cons_some ha]
      have hw' : getV T r Zs (cι T r Zs ⟨w, hw⟩) = some w := rfl
      rw [List.filterMap_cons_some hw'] at hb ⊢
      exact List.isChain_cons_cons.2 ⟨⟨h1, h2⟩, hb⟩

theorem chain_depth {α : Type} (f : α → ℕ) (L : List α)
    (hc : L.IsChain (fun v w => f w = f v + 1)) :
    ∀ i (h : i < L.length), f L[i] = f (L[0]'(by omega)) + i := by
  intro i
  induction i with
  | zero => intro h; simp
  | succ i ih =>
    intro h
    have e1 := hc.getElem i h
    have e2 := ih (by omega)
    omega

theorem cut_vertical (hT : T.IsTree) (hr : r ∈ Zs) (l : List (CW T r Zs))
    (hl : IsVertical (cP T r Zs hT hr).gr (croot T r Zs) l) :
    {v : V | ∃ h : v ∈ Zsᶜ, cι T r Zs ⟨v, h⟩ ∈ l} = ∅ ∨
      IsVerticalSet T r {v : V | ∃ h : v ∈ Zsᶜ, cι T r Zs ⟨v, h⟩ ∈ l} := by
  obtain ⟨hne, hch, d, hd⟩ := hl
  have hdep : ∀ w, (cP T r Zs hT hr).gr.dist w (croot T r Zs) = cdep T r Zs w := fun w => by
    rw [dist_comm]
    exact (cP T r Zs hT hr).dist_eq w
  have hR : l.IsChain (fun a b => b ≠ croot T r Zs ∧ cpar T r Zs b = a) := by
    rw [List.isChain_iff_getElem] at hch ⊢
    intro i hi
    have e1 := hd i (by omega)
    have e2 := hd (i + 1) hi
    simp only [List.get_eq_getElem] at e1 e2
    rw [hdep] at e1 e2
    exact (cP T r Zs hT hr).adj_up (hch i hi) (by show cdep T r Zs _ = cdep T r Zs _ + 1; omega)
  cases l with
  | nil => exact absurd rfl hne
  | cons a l' =>
    have hc := chainV T r Zs hT hr l' a hR
    have hset : {v : V | ∃ h : v ∈ Zsᶜ, cι T r Zs ⟨v, h⟩ ∈ a :: l'} =
        {v : V | v ∈ (a :: l').filterMap (getV T r Zs)} := by
      ext v
      simp only [Set.mem_setOf_eq, List.mem_filterMap]
      constructor
      · rintro ⟨h, hm⟩
        exact ⟨_, hm, rfl⟩
      · rintro ⟨w, hw, he⟩
        obtain ⟨h, rfl⟩ := getV_some T r Zs he
        exact ⟨h, hw⟩
    rw [hset]
    generalize hL : (a :: l').filterMap (getV T r Zs) = L at hc
    cases L with
    | nil =>
      left
      ext v
      simp
    | cons v0 L' =>
      right
      refine ⟨v0 :: L', ⟨by simp, hc.imp (fun _ _ h => h.1), T.dist v0 r, ?_⟩, rfl⟩
      intro i hi
      have := chain_depth (fun v => T.dist r v) (v0 :: L') (hc.imp (fun _ _ h => h.2)) i hi
      simp only [List.get_eq_getElem]
      rw [dist_comm, dist_comm (u := v0)]
      simpa using this

theorem cG_dep (G : SimpleGraph V) (hconn : G.Connected) (hB : IsBFSTree G T r) (hr : r ∈ Zs) :
    ∀ a b, (cG T r Zs G hB.2.1 hr).Adj a b → cdep T r Zs b ≤ cdep T r Zs a + 1 := by
  intro a b h
  rcases (sup_adj _ _ _ _).1 h with h | h
  · rcases (cP T r Zs hB.2.1 hr).adj_dep h with e | e
    · change cdep T r Zs a = cdep T r Zs b + 1 at e
      omega
    · change cdep T r Zs b = cdep T r Zs a + 1 at e
      omega
  · obtain ⟨u, v, huv, rfl, rfl⟩ := (map_adj _ _ _ _).1 h
    change T.dist r v.1 ≤ T.dist r u.1 + 1
    rw [hB.2.2, hB.2.2]
    have h1 := hconn.dist_triangle (u := r) (v := u.1) (w := v.1)
    have h2 : G.dist u.1 v.1 = 1 := dist_eq_one_iff_adj.mpr huv
    omega

theorem cut_pack (G : SimpleGraph V) (hconn : G.Connected) (hB : IsBFSTree G T r) (hr : r ∈ Zs) :
    (cG T r Zs G hB.2.1 hr).Connected ∧
    (∀ a b : ↥Zsᶜ, G.Adj a b → (cG T r Zs G hB.2.1 hr).Adj (cι T r Zs a) (cι T r Zs b)) ∧
    IsBFSTree (cG T r Zs G hB.2.1 hr) (cP T r Zs hB.2.1 hr).gr (croot T r Zs) ∧
    (∀ a : ↥Zsᶜ, (cG T r Zs G hB.2.1 hr).dist (croot T r Zs) (cι T r Zs a) = G.dist r a) ∧
    ∀ l : List (CW T r Zs), IsVertical (cP T r Zs hB.2.1 hr).gr (croot T r Zs) l →
      {v : V | ∃ h : v ∈ Zsᶜ, cι T r Zs ⟨v, h⟩ ∈ l} = ∅ ∨
        IsVerticalSet T r {v : V | ∃ h : v ∈ Zsᶜ, cι T r Zs ⟨v, h⟩ ∈ l} := by
  set P := cP T r Zs hB.2.1 hr with hP
  have hle : P.gr ≤ cG T r Zs G hB.2.1 hr := le_sup_left
  have hd := P.dist_sup (cG T r Zs G hB.2.1 hr) hle (cG_dep T r Zs G hconn hB hr)
  refine ⟨P.connected.mono hle, ?_, ⟨hle, P.isTree, ?_⟩, ?_, cut_vertical T r Zs hB.2.1 hr⟩
  · intro a b h
    exact (sup_adj _ _ _ _).2 (Or.inr ((map_adj _ _ _ _).2 ⟨a, b, h, rfl, rfl⟩))
  · intro v
    exact (P.dist_eq v).trans (hd v).symm
  · intro a
    exact (hd (cι T r Zs a)).trans (hB.2.2 a.1)

/-- the vertices of `Z`: ancestors of the end vertices `Ends` -/
def ancS (Ends : Set V) : Set V := {v | ∃ e ∈ Ends, T.dist r v + T.dist v e = T.dist r e}

theorem root_mem_ancS {Ends : Set V} {e : V} (he : e ∈ Ends) : r ∈ ancS T r Ends :=
  ⟨e, he, by simp⟩

theorem ancS_closed (hT : T.IsTree) (Ends : Set V) {v : V} (hv : v ∈ ancS T r Ends) (hvr : v ≠ r) :
    tpar T r v ∈ ancS T r Ends := by
  obtain ⟨e, he, hve⟩ := hv
  refine ⟨e, he, ?_⟩
  have hs := tpar_spec T r hT hvr
  have h1 : T.dist (tpar T r v) v = 1 := dist_eq_one_iff_adj.mpr hs.1.symm
  have t1 := hT.connected.dist_triangle (u := r) (v := tpar T r v) (w := e)
  have t2 := hT.connected.dist_triangle (u := tpar T r v) (v := v) (w := e)
  omega

/-- the subgraph `Z`: tree edges inside `Zs` -/
def zsub (G : SimpleGraph V) (hTG : T ≤ G) : G.Subgraph where
  verts := Zs
  Adj a b := a ∈ Zs ∧ b ∈ Zs ∧ T.Adj a b
  adj_sub h := hTG h.2.2
  edge_vert h := h.1
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩

theorem zsub_connected (G : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (hanc : ∀ v ∈ Zs, v ≠ r → tpar T r v ∈ Zs) : (zsub T Zs G hTG).Connected := by
  rw [Subgraph.connected_iff']
  have key : ∀ (n : ℕ) (v : V) (hv : v ∈ Zs), T.dist r v = n →
      (zsub T Zs G hTG).coe.Reachable ⟨v, hv⟩ ⟨r, hr⟩ := by
    intro n
    induction n with
    | zero =>
      intro v hv h0
      have := (hT.connected.dist_eq_zero_iff).1 h0
      subst this
      rfl
    | succ n ih =>
      intro v hv hn
      have hvr : v ≠ r := by
        intro e
        subst e
        simp at hn
      have hs := tpar_spec T r hT hvr
      have hp := hanc v hv hvr
      have hadj : (zsub T Zs G hTG).coe.Adj ⟨v, hv⟩ ⟨tpar T r v, hp⟩ := ⟨hv, hp, hs.1⟩
      exact hadj.reachable.trans (ih _ hp (by omega))
  have : Nonempty ↥(zsub T Zs G hTG).verts := ⟨⟨r, hr⟩⟩
  exact ⟨fun a b => (key _ a.1 a.2 rfl).trans (key _ b.1 b.2 rfl).symm⟩

end cutpack

end PQL21

/-! P7 core (s5): runs of the tree contour. For a tree pair `d` whose removal cuts off the side `D`
(containing `d.snd`), the sheet-`q` points at `D` form exactly the class of `yq d.symm` after
splitting `ψ` at the pair, i.e. a contiguous `ψ`-segment. Genus-free. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section run

variable {α : Type} [DecidableEq α] [Fintype α]

theorem norb_ge_four (π : Perm α) {a b c e : α} (hab : ¬ SameCycle π a b)
    (hac : ¬ SameCycle π a c) (hae : ¬ SameCycle π a e) (hbc : ¬ SameCycle π b c)
    (hbe : ¬ SameCycle π b e) (hce : ¬ SameCycle π c e) : 4 ≤ norb π := by
  classical
  unfold norb
  rw [Nat.card_eq_fintype_card]
  have : ({Quotient.mk (SameCycle.setoid π) a, Quotient.mk (SameCycle.setoid π) b,
      Quotient.mk (SameCycle.setoid π) c, Quotient.mk (SameCycle.setoid π) e} :
        Finset (Quotient (SameCycle.setoid π))).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h; exact hce (Quotient.exact h)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hbc (Quotient.exact h)
      · exact hbe (Quotient.exact h)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact hab (Quotient.exact h)
      · exact hac (Quotient.exact h)
      · exact hae (Quotient.exact h)
  rw [← this]
  exact Finset.card_le_univ _

end run

section run2

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- genus-free: the tree pairs split maximally on `ψ` -/
theorem psi_max (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) :
    SigP S * sprod L * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) = SigP S ∧
    2 * norb (SigP S * sprod L) + (TD ×ˢ (Finset.univ : Finset Bool)).card ≤
      2 * norb (SigP S * sprod L * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ)) := by
  have hdeg := exists_dart_at hconn h2
  have hsig := norb_SigP S hdeg
  have hcnt := I.cnt
  have hlen := I.len
  rw [Finset.card_univ] at hlen
  have hLT := card_TD_L I
  have hψ2 : norb (SigP S * sprod L) = 2 := by omega
  have hsp := sprod_eq_PF I
  have hback : SigP S * sprod L * PF (apFun S) (apFun_invol S) (TD ×ˢ Finset.univ) = SigP S := by
    rw [hsp, mul_assoc, PF_mul_self, mul_one]
  have hCT : (TD ×ˢ (Finset.univ : Finset Bool)).card = 2 * TD.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  refine ⟨hback, ?_⟩
  rw [hback, hsig, hψ2, hCT]
  omega

/-- the point of dart `d` on sheet `q` -/
def yq (p : V → Bool) (q : Bool) (d : G.Dart) : G.Dart × Bool := (d, xor (p d.fst) q)

theorem sh_yq (p : V → Bool) (q : Bool) (d : G.Dart) : sh p (yq p q d) = q := by
  simp only [sh, yq]
  cases p d.fst <;> cases q <;> rfl

theorem yq_of_sh {p : V → Bool} {q : Bool} {x : G.Dart × Bool} (h : sh p x = q) :
    yq p q x.1 = x := by
  rcases x with ⟨e, s⟩
  simp only [sh] at h
  subst h
  simp only [yq, Prod.mk.injEq, true_and]
  cases s <;> cases p e.fst <;> rfl

theorem sh_SigP (S : EmbeddingScheme G) (p : V → Bool) (y : G.Dart × Bool) :
    sh p (SigP S y) = sh p y := by
  simp only [sh, SigP_fst]
  rfl

theorem sheet_cycle_q (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (q : Bool) (d0 : G.Dart) (x : G.Dart × Bool)
    (hx : sh p x = q) : SameCycle (SigP S * sprod L) (yq p q d0) x := by
  by_contra hn
  have hsep : ∀ u v, sh p u ≠ sh p v → ¬ SameCycle (SigP S * sprod L) u v :=
    fun u v huv => not_sc_of_kappa _ (sh p) (sheet_pres I) huv
  have h3 := norb_ge_three (SigP S * sprod L) (c := yq p (!q) d0) hn
    (hsep _ _ (by rw [sh_yq, sh_yq]; cases q <;> decide))
    (hsep _ _ (by rw [hx, sh_yq]; cases q <;> decide))
  have h2' := norb_psi S hconn h2 I
  omega

theorem partner_q (S : EmbeddingScheme G)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (q : Bool) {d : G.Dart} (hd : d ∈ TD) :
    apFun S (yq p q d) = yq p q d.symm := by
  have hp := I.par d hd
  simp only [apFun, yq, dart_symm_fst, hp, Prod.mk.injEq, true_and]
  cases p d.fst <;> cases q <;> cases S.sig d <;> rfl

theorem sprod_apply_TD
    {S : EmbeddingScheme G} {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (y : G.Dart × Bool) :
    sprod L y = if y.1 ∈ TD then apFun S y else y := by
  rw [sprod_eq_PF I, PF_apply]
  unfold pfFun
  by_cases hy : y.1 ∈ TD
  · rw [if_pos ⟨by simp [hy], CT_closed S I.td_symm _ (by simp [hy])⟩, if_pos hy]
  · rw [if_neg (fun h => hy (by simpa using h.1)), if_neg hy]

/-- P7 core: after splitting `ψ` at the sheet-`q` points of the tree pair `d`, the class of
`yq d.symm` is exactly the set of sheet-`q` points on the side `D` of `d.snd`. -/
theorem run_side (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (q : Bool) (d : G.Dart) (hd : d ∈ TD) (D : Set V)
    (hx : d.snd ∈ D) (hz : d.fst ∉ D)
    (hD : ∀ e ∈ TD, e ≠ d → e ≠ d.symm → (e.fst ∈ D ↔ e.snd ∈ D)) (y : G.Dart × Bool) :
    SameCycle (SigP S * sprod L * swap (yq p q d) (yq p q d.symm)) (yq p q d.symm) y ↔
      (sh p y = q ∧ y.1.fst ∈ D) := by
  classical
  set ψ := SigP S * sprod L with hψ
  set a := yq p q d with ha
  set b := yq p q d.symm with hb
  have hab : apFun S a = b := partner_q S I q hd
  have hba : apFun S b = a := by rw [← hab, apFun_invol]
  have hdb : d.symm ∈ TD := I.td_symm d hd
  let κ : G.Dart × Bool → Option Bool := fun y =>
    if sh p y = q then some (decide (y.1.fst ∈ D)) else none
  have hsig : ∀ y, κ (SigP S y) = κ y := by
    intro y
    simp only [κ, sh_SigP, SigP_fst]
  have hψa : ψ a = SigP S b := by
    rw [hψ, Perm.mul_apply, sprod_apply_TD I, if_pos (show a.1 ∈ TD from hd), hab]
  have hψb : ψ b = SigP S a := by
    rw [hψ, Perm.mul_apply, sprod_apply_TD I, if_pos (show b.1 ∈ TD from hdb), hba]
  have hfa : κ a = some false := by
    have h1 : sh p a = q := sh_yq p q d
    have h2 : a.1.fst ∉ D := hz
    simp [κ, h1, h2]
  have hfb : κ b = some true := by
    have h1 : sh p b = q := sh_yq p q d.symm
    have h2 : b.1.fst ∈ D := hx
    simp [κ, h1, h2]
  have hinv : ∀ y, κ ((ψ * swap a b) y) = κ y := by
    intro y
    rw [Perm.mul_apply]
    by_cases hya : y = a
    · rw [hya, swap_apply_left, hψb, hsig]
    by_cases hyb : y = b
    · rw [hyb, swap_apply_right, hψa, hsig]
    rw [swap_apply_of_ne_of_ne hya hyb, hψ, Perm.mul_apply, hsig, sprod_apply_TD I]
    by_cases hy : y.1 ∈ TD
    · rw [if_pos hy]
      have hsh : sh p (apFun S y) = sh p y := by
        have hp := I.par y.1 hy
        simp only [sh, apFun, dart_symm_fst, hp]
        cases y.2 <;> cases p y.1.fst <;> cases S.sig y.1 <;> rfl
      simp only [κ, hsh]
      by_cases hq : sh p y = q
      · rw [if_pos hq, if_pos hq]
        have h1 : y.1 ≠ d := by
          intro e
          apply hya
          rw [← yq_of_sh hq, e]
        have h2 : y.1 ≠ d.symm := by
          intro e
          apply hyb
          rw [← yq_of_sh hq, e]
        have := hD y.1 hy h1 h2
        simp only [apFun, dart_symm_fst, Option.some.injEq]
        exact decide_eq_decide.mpr this.symm
      · rw [if_neg hq, if_neg hq]
    · rw [if_neg hy]
  have hsc : SameCycle ψ a b :=
    (sheet_cycle_q S hconn h2 I q d a (sh_yq p q d)).symm.trans
      (sheet_cycle_q S hconn h2 I q d b (sh_yq p q d.symm))
  have hne : a ≠ b := by
    intro e
    exact SimpleGraph.Dart.symm_ne d (congrArg Prod.fst e).symm
  have h3 : norb (ψ * swap a b) = 3 := by
    rw [norb_split ψ hsc hne, norb_psi S hconn h2 I]
  constructor
  · intro h
    have := (pres _ (fun z => κ z = κ b) (fun z => by simp only [hinv]) h).mpr rfl
    rw [hfb] at this
    simp only [κ] at this
    by_cases hq : sh p y = q
    · rw [if_pos hq] at this
      simp only [Option.some.injEq, decide_eq_true_eq] at this
      exact ⟨hq, this⟩
    · rw [if_neg hq] at this
      exact absurd this (by simp)
  · rintro ⟨hq, hyD⟩
    by_contra hn
    have hfy : κ y = some true := by simp [κ, hq, hyD]
    set w := yq p (!q) d with hw
    have hfw : κ w = none := by
      simp only [κ, hw, sh_yq]
      cases q <;> simp
    have sep : ∀ u v, κ u ≠ κ v → ¬ SameCycle (ψ * swap a b) u v :=
      fun u v h => not_sc_of_kappa _ κ hinv h
    have h4 := norb_ge_four (ψ * swap a b) (a := b) (b := y) (c := a) (e := w) hn
      (sep _ _ (by rw [hfb, hfa]; simp)) (sep _ _ (by rw [hfb, hfw]; simp))
      (sep _ _ (by rw [hfy, hfa]; simp)) (sep _ _ (by rw [hfy, hfw]; simp))
      (sep _ _ (by rw [hfa, hfw]; simp))
    omega

end run2

end PQL21

namespace PQL21

open SimpleGraph

section side

variable {V : Type} [Fintype V] [DecidableEq V]

theorem tpar_root (T : SimpleGraph V) (r : V) : tpar T r r = r := by
  unfold tpar
  rw [dif_neg]
  rintro ⟨w, -, h⟩
  simp at h

theorem dist_tpar_le (T : SimpleGraph V) (hT : T.IsTree) (r v : V) :
    T.dist r (tpar T r v) ≤ T.dist r v := by
  by_cases hv : v = r
  · subst hv; rw [tpar_root]
  · have := (tpar_spec T r hT hv).2; omega

theorem dist_iter_le (T : SimpleGraph V) (hT : T.IsTree) (r v : V) (n : ℕ) :
    T.dist r ((tpar T r)^[n] v) ≤ T.dist r v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (dist_tpar_le T hT r v)

/-- tree edges join a vertex and its parent -/
theorem adj_tpar (T : SimpleGraph V) (hT : T.IsTree) (r : V) {u w : V} (h : T.Adj u w) :
    w = tpar T r u ∨ u = tpar T r w := by
  rcases hT.dist_eq_dist_add_one_of_adj r h with e | e
  · -- dist r u = dist r w + 1
    left
    have hu : u ≠ r := by intro h0; subst h0; simp at e
    have hs := tpar_spec T r hT hu
    exact tree_parent_unique T hT r h.symm hs.1.symm (by omega) (by omega)
  · right
    have hw : w ≠ r := by intro h0; subst h0; simp at e
    have hs := tpar_spec T r hT hw
    exact tree_parent_unique T hT r h hs.1.symm (by omega) (by omega)

/-- descendants of `x` (including `x`) -/
def desc (T : SimpleGraph V) (r x : V) : Set V := {v | ∃ n, (tpar T r)^[n] v = x}

theorem mem_desc_self (T : SimpleGraph V) (r x : V) : x ∈ desc T r x := ⟨0, rfl⟩

theorem tpar_not_desc (T : SimpleGraph V) (hT : T.IsTree) (r x : V) (hx : x ≠ r) :
    tpar T r x ∉ desc T r x := by
  rintro ⟨n, hn⟩
  have h1 := dist_iter_le T hT r (tpar T r x) n
  rw [hn] at h1
  have := (tpar_spec T r hT hx).2
  omega

/-- crossing a tree edge other than `x — tpar x` keeps the side -/
theorem desc_edge (T : SimpleGraph V) (hT : T.IsTree) (r x : V) {u w : V} (h : T.Adj u w)
    (h1 : ¬ (u = x ∧ w = tpar T r x)) (h2 : ¬ (w = x ∧ u = tpar T r x)) :
    u ∈ desc T r x ↔ w ∈ desc T r x := by
  have key : ∀ {u w : V}, w = tpar T r u → ¬ (u = x ∧ w = tpar T r x) →
      (u ∈ desc T r x ↔ w ∈ desc T r x) := by
    intro u w hw hne
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero =>
        simp only [Function.iterate_zero, id_eq] at hn
        exact absurd ⟨hn, hn ▸ hw⟩ hne
      | succ n =>
        rw [Function.iterate_succ_apply] at hn
        exact ⟨n, hw ▸ hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← hw]
      exact hn
  rcases adj_tpar T hT r h with e | e
  · exact key e h1
  · exact (key e h2).symm

end side

end PQL21

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section runpos

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- P7b (ψ-level): from the base `yq d`, the sheet-`q` points on the side `D` are exactly the
positions `1..j` where `j` is the position of `yq d.symm` -/
theorem run_pos (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    {r : V} {TD : Finset G.Dart} {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (q : Bool) (d : G.Dart) (hd : d ∈ TD) (D : Set V)
    (hx : d.snd ∈ D) (hz : d.fst ∉ D)
    (hD : ∀ e ∈ TD, e ≠ d → e ≠ d.symm → (e.fst ∈ D ↔ e.snd ∈ D)) :
    ∃ j, 0 < j ∧ j < per (SigP S * sprod L) (yq p q d) ∧
      ((SigP S * sprod L) ^ j) (yq p q d) = yq p q d.symm ∧
      ∀ y, sh p y = q → (y.1.fst ∈ D ↔
        ∃ l, 0 < l ∧ l ≤ j ∧ ((SigP S * sprod L) ^ l) (yq p q d) = y) := by
  set ψ := SigP S * sprod L with hψ
  have hsc : SameCycle ψ (yq p q d) (yq p q d.symm) :=
    (sheet_cycle_q S hconn h2 I q d _ (sh_yq p q d)).symm.trans
      (sheet_cycle_q S hconn h2 I q d _ (sh_yq p q d.symm))
  obtain ⟨j, hjlt, hj⟩ := exists_pos ψ hsc
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      subst h
      simp only [pow_zero, Perm.one_apply] at hj
      exact SimpleGraph.Dart.symm_ne d (congrArg Prod.fst hj).symm
    · exact h
  refine ⟨j, hj0, hjlt, hj, ?_⟩
  intro y hy
  have hs := split_interval ψ (yq p q d) hj0 hjlt y
  simp only [pow_zero, Perm.one_apply, hj] at hs
  rw [← hs, run_side S hconn h2 I q d hd D hx hz hD y]
  exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩

end runpos

end PQL21

/-! P7b (s6): the run structure on the face cycle `Y` of `Φ = PhiE S TD E`. Off `E`, `Φ = ψ`;
each top `x` (outside `Zs`, parent in `Zs`) has, on each sheet, a `Φ`-run consisting exactly of
the points at the descendants of `x`; the two sheets' runs lie in different `Φ`-cycles. -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section ylev

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem phi_apply_off (S : EmbeddingScheme G) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (E : Finset G.Dart) (x : G.Dart × Bool) (hx : x.1 ∉ E) :
    PhiE S TD E x = (SigP S * sprod L) x := by
  have hE : PF (apFun S) (apFun_invol S) (E ×ˢ Finset.univ) x = x := by
    rw [PF_apply]
    unfold pfFun
    rw [if_neg (fun h => hx (by simpa using h.1))]
  rw [PhiE, Perm.mul_apply, hE, sprod_eq_PF I]

theorem phi_pow_eq (S : EmbeddingScheme G) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (E : Finset G.Dart) (a : G.Dart × Bool) (n : ℕ)
    (h : ∀ i < n, (((SigP S * sprod L) ^ i) a).1 ∉ E) :
    ∀ i ≤ n, (PhiE S TD E ^ i) a = ((SigP S * sprod L) ^ i) a := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [pow_succ', Perm.mul_apply, ih (by omega), phi_apply_off S I E _ (h i (by omega)),
      pow_succ']
    rfl

/-- the mirror `x ↦ F (ν x)` never maps a point into its own `Φ`-cycle -/
theorem phi_mirror (S : EmbeddingScheme G) (TD E : Finset G.Dart) (hTD : ∀ d ∈ TD, d.symm ∈ TD)
    (hEs : ∀ d ∈ E, d.symm ∈ E) (hE : E ⊆ TDᶜ) (x : G.Dart × Bool) :
    ¬ SameCycle (PhiE S TD E) x (FF S TD E (nuF x)) := by
  have hFa := FF_apply S TD E hTD hEs hE
  have hFF := FF_invol S TD E hTD hEs hE
  have hFnu := FF_nu S TD E hTD hEs hE
  set Φ := PhiE S TD E with hΦ
  set F := FF S TD E with hF
  have hΦa : ∀ x, Φ x = SigP S (F x) := fun x => by rw [hΦ, phiE_eq]; rfl
  have hμinv : Function.Involutive (fun x => F (nuF x)) := fun x => by
    simp only
    rw [← hFnu, hFF, nuF_nuF]
  let μ : Perm (G.Dart × Bool) := hμinv.toPerm
  have hμ : ∀ x, μ x = F (nuF x) := fun _ => rfl
  have hμμ : ∀ x, μ (μ x) = x := fun x => hμinv x
  have hconj : ∀ x, μ (Φ (μ x)) = Φ⁻¹ x := by
    intro x
    rw [eq_comm, Perm.inv_eq_iff_eq]
    simp only [hμ, hΦa, hFF]
    exact (SigP_nu S x).symm
  have hfp : ∀ x, μ x ≠ x := by
    intro x h
    rw [hμ, hFa] at h
    split_ifs at h
    · exact (SimpleGraph.Dart.symm_ne x.1) (congrArg Prod.fst h)
    · have := congrArg Prod.snd h
      simp [nuF] at this
  have hfp2 : ∀ x, μ (Φ x) ≠ x := by
    intro x h
    rw [hμ, hΦa] at h
    have h3 := congrArg F h
    rw [hFF] at h3
    have h4 := congrArg Prod.snd h3
    simp [nuF, SigP_apply] at h4
  have := mirror_not_sc Φ μ hμμ hconj hfp hfp2 x
  exact this

/-- the deleted chords `C* = TDᶜ \ E` still split maximally on `Φ` -/
theorem cstar_max (S : EmbeddingScheme G) (TD E : Finset G.Dart) (hTD : ∀ d ∈ TD, d.symm ∈ TD)
    (hE : E ⊆ TDᶜ) (hEs : ∀ d ∈ E, d.symm ∈ E)
    (hinv : 2 * norb (PhiE S TD E) + ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card ≤
        2 * norb (SigP S * AP S)) :
    2 * norb (PhiE S TD E) + ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card ≤
      2 * norb (PhiE S TD E * PF (apFun S) (apFun_invol S) ((TDᶜ \ E) ×ˢ Finset.univ)) := by
  have hTc : ∀ d ∈ TDᶜ, d.symm ∈ TDᶜ := by
    intro d hd
    simp only [Finset.mem_compl] at hd ⊢
    exact fun h => hd (by simpa using hTD _ h)
  have hsplit := PF_split S TDᶜ E hTc hEs hE
  have hfull : PhiE S TD E * PF (apFun S) (apFun_invol S) ((TDᶜ \ E) ×ˢ Finset.univ) =
      SigP S * AP S := by
    rw [← phiE_full S TD hTD]
    simp only [PhiE, mul_assoc, hsplit]
  rw [hfull]
  exact hinv

theorem yq_nu (p : V → Bool) (q : Bool) (d : G.Dart) : nuF (yq p q d) = yq p (!q) d := by
  simp only [nuF, yq, Prod.mk.injEq, true_and]
  cases p d.fst <;> cases q <;> rfl

end ylev

section tops

variable {V : Type} [Fintype V] [DecidableEq V]

theorem iter_mem (T : SimpleGraph V) (r : V) (Zs : Set V) (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) :
    ∀ (n : ℕ) (v : V), v ∈ Zs → (tpar T r)^[n] v ∈ Zs := by
  intro n
  induction n with
  | zero => intro v hv; exact hv
  | succ n ih =>
    intro v hv
    rw [Function.iterate_succ_apply]
    exact ih _ (hanc v hv)

theorem desc_not_mem (T : SimpleGraph V) (r : V) (Zs : Set V) (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs)
    {x : V} (hx : x ∉ Zs) {v : V} (hv : v ∈ desc T r x) : v ∉ Zs := by
  intro h
  obtain ⟨n, hn⟩ := hv
  exact hx (hn ▸ iter_mem T r Zs hanc n v h)

theorem top_exists (T : SimpleGraph V) (hT : T.IsTree) (r : V) (Zs : Set V) (hr : r ∈ Zs) :
    ∀ (n : ℕ) (v : V), T.dist r v = n → v ∉ Zs →
      ∃ x, x ∉ Zs ∧ tpar T r x ∈ Zs ∧ v ∈ desc T r x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv
    by_cases hp : tpar T r v ∈ Zs
    · exact ⟨v, hv, hp, mem_desc_self T r v⟩
    · have hvr : v ≠ r := fun h => hv (h ▸ hr)
      have hs := (tpar_spec T r hT hvr).2
      obtain ⟨x, hx1, hx2, m, hm⟩ := ih _ (by omega) (tpar T r v) rfl hp
      exact ⟨x, hx1, hx2, m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

theorem top_unique (T : SimpleGraph V) (r : V) (Zs : Set V) (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs)
    {x x' : V} (hx : x ∉ Zs) (hxp : tpar T r x ∈ Zs) (hx' : x' ∉ Zs) (hxp' : tpar T r x' ∈ Zs)
    {v : V} (h1 : v ∈ desc T r x) (h2 : v ∈ desc T r x') : x = x' := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have key : ∀ {a b : V} {n m : ℕ}, a ∉ Zs → tpar T r a ∈ Zs → b ∉ Zs →
      (tpar T r)^[n] v = a → (tpar T r)^[m] v = b → n ≤ m → a = b := by
    intro a b n m ha hap hb hna hmb hle
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, hna] at hmb
    cases k with
    | zero => exact hmb
    | succ k =>
      exfalso
      rw [Function.iterate_succ_apply] at hmb
      exact hb (hmb ▸ iter_mem T r Zs hanc k _ hap)
  rcases le_total n m with h | h
  · exact key hx hxp hx' hn hm h
  · exact (key hx' hxp' hx hm hn h).symm

end tops

section yrun

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- the `Φ`-run of a top `x` on sheet `q`, starting at the point of the entry dart `d` -/
theorem run_phi (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (T : SimpleGraph V) (hT : T.IsTree) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (htd : ∀ d, d ∈ TD ↔ T.Adj d.fst d.snd)
    (E : Finset G.Dart) (hE : E ⊆ TDᶜ) (Zs : Set V) (hEZ : ∀ e ∈ E, e.fst ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) (hr : r ∈ Zs)
    {x : V} (hx : x ∉ Zs) (d : G.Dart) (hd1 : d.fst = tpar T r x) (hd2 : d.snd = x)
    (q : Bool) :
    d ∈ TD ∧ ∃ j, 0 < j ∧
      (PhiE S TD E ^ j) (yq p q d) = yq p q d.symm ∧
      (∀ i ≤ j, (PhiE S TD E ^ i) (yq p q d) = ((SigP S * sprod L) ^ i) (yq p q d)) ∧
      (∀ l, 0 < l → l ≤ j → sh p ((PhiE S TD E ^ l) (yq p q d)) = q ∧
        ((PhiE S TD E ^ l) (yq p q d)).1.fst ∈ desc T r x) ∧
      ∀ y, sh p y = q → (y.1.fst ∈ desc T r x ↔
        ∃ l, 0 < l ∧ l ≤ j ∧ (PhiE S TD E ^ l) (yq p q d) = y) := by
  have hxr : x ≠ r := fun h => hx (h ▸ hr)
  have hd : d ∈ TD := by
    rw [htd, hd1, hd2]
    exact (tpar_spec T r hT hxr).1.symm
  refine ⟨hd, ?_⟩
  set D := desc T r x with hDdef
  have hxD : d.snd ∈ D := by rw [hd2]; exact mem_desc_self T r x
  have hzD : d.fst ∉ D := by rw [hd1]; exact tpar_not_desc T hT r x hxr
  have hD : ∀ e ∈ TD, e ≠ d → e ≠ d.symm → (e.fst ∈ D ↔ e.snd ∈ D) := by
    intro e he hne1 hne2
    refine desc_edge T hT r x ((htd e).1 he) ?_ ?_
    · rintro ⟨h1, h2⟩
      apply hne2
      apply SimpleGraph.Dart.ext
      exact Prod.ext (h1.trans hd2.symm) (h2.trans hd1.symm)
    · rintro ⟨h1, h2⟩
      apply hne1
      apply SimpleGraph.Dart.ext
      exact Prod.ext (h2.trans hd1.symm) (h1.trans hd2.symm)
  obtain ⟨j, hj0, -, hjψ, hchar⟩ := run_pos S hconn h2 I q d hd D hxD hzD hD
  set ψ := SigP S * sprod L with hψ
  have hsh : ∀ i, sh p ((ψ ^ i) (yq p q d)) = q := by
    intro i
    rw [sheet_of_sc I (sc_of_nat i rfl : SameCycle ψ (yq p q d) _), sh_yq]
  have hin : ∀ l, 0 < l → l ≤ j → ((ψ ^ l) (yq p q d)).1.fst ∈ D := fun l h1 h2 =>
    (hchar _ (hsh l)).2 ⟨l, h1, h2, rfl⟩
  have hnE : ∀ i < j, ((ψ ^ i) (yq p q d)).1 ∉ E := by
    intro i hi hmem
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      simp only [pow_zero, Perm.one_apply, yq] at hmem
      exact Finset.mem_compl.mp (hE hmem) hd
    · exact desc_not_mem T r Zs hanc hx (hin i h0 hi.le) (hEZ _ hmem)
  have heq := phi_pow_eq S I E (yq p q d) j hnE
  refine ⟨j, hj0, by rw [heq j le_rfl, hjψ], heq, ?_, ?_⟩
  · intro l h1 h2
    rw [heq l h2]
    exact ⟨hsh l, hin l h1 h2⟩
  · intro y hy
    rw [hchar y hy]
    constructor
    · rintro ⟨l, h1, h2, h3⟩
      exact ⟨l, h1, h2, by rw [heq l h2, h3]⟩
    · rintro ⟨l, h1, h2, h3⟩
      exact ⟨l, h1, h2, by rw [← heq l h2, h3]⟩

/-- the two sheets of a top's entry dart lie in different `Φ`-cycles -/
theorem run_sheets (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (T : SimpleGraph V) (hT : T.IsTree) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (htd : ∀ d, d ∈ TD ↔ T.Adj d.fst d.snd)
    (E : Finset G.Dart) (hE : E ⊆ TDᶜ) (hEs : ∀ d ∈ E, d.symm ∈ E) (Zs : Set V)
    (hEZ : ∀ e ∈ E, e.fst ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) (hr : r ∈ Zs)
    {x : V} (hx : x ∉ Zs) (d : G.Dart) (hd1 : d.fst = tpar T r x) (hd2 : d.snd = x)
    (q : Bool) : ¬ SameCycle (PhiE S TD E) (yq p q d) (yq p (!q) d) := by
  obtain ⟨hd, j, -, hj, -⟩ := run_phi S hconn h2 T hT I htd E hE Zs hEZ hanc hr hx d hd1 hd2 (!q)
  intro h
  apply phi_mirror S TD E I.td_symm hEs hE (yq p q d)
  rw [yq_nu, FF_apply S TD E I.td_symm hEs hE, if_pos (show (yq p (!q) d).1 ∈ TD ∨ _ from Or.inl hd), partner_q S I _ hd, ← hj]
  exact h.trans (sc_of_nat j rfl)

/-- a run in the `Φ`-cycle of a base point `z0` at `Zs`: positions `s .. s + j`, no wrap -/
theorem run_Y (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (T : SimpleGraph V) (hT : T.IsTree) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (htd : ∀ d, d ∈ TD ↔ T.Adj d.fst d.snd)
    (E : Finset G.Dart) (hE : E ⊆ TDᶜ) (Zs : Set V) (hEZ : ∀ e ∈ E, e.fst ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) (hr : r ∈ Zs)
    (z0 : G.Dart × Bool) (hz0 : z0.1.fst ∈ Zs)
    {x : V} (hx : x ∉ Zs) (d : G.Dart) (hd1 : d.fst = tpar T r x) (hd2 : d.snd = x)
    (q : Bool) (hq : SameCycle (PhiE S TD E) z0 (yq p q d)) :
    ∃ s j, 0 < j ∧ s + j < per (PhiE S TD E) z0 ∧
      (PhiE S TD E ^ s) z0 = yq p q d ∧ (PhiE S TD E ^ (s + j)) z0 = yq p q d.symm ∧
      (∀ l, 0 < l → l ≤ j → sh p ((PhiE S TD E ^ (s + l)) z0) = q ∧
        ((PhiE S TD E ^ (s + l)) z0).1.fst ∈ desc T r x) ∧
      ∀ y, sh p y = q → (y.1.fst ∈ desc T r x ↔
        ∃ l, 0 < l ∧ l ≤ j ∧ (PhiE S TD E ^ (s + l)) z0 = y) := by
  obtain ⟨-, j, hj0, hj, -, hin, hchar⟩ :=
    run_phi S hconn h2 T hT I htd E hE Zs hEZ hanc hr hx d hd1 hd2 q
  set Φ := PhiE S TD E with hΦ
  obtain ⟨s, hs, hsa⟩ := exists_pos Φ hq
  have hadd : ∀ l, (Φ ^ (s + l)) z0 = (Φ ^ l) (yq p q d) := by
    intro l
    rw [Nat.add_comm, pow_add, Perm.mul_apply, hsa]
  have hwrap : s + j < per Φ z0 := by
    by_contra hc
    push_neg at hc
    have hl0 : 0 < per Φ z0 - s := by omega
    have hl1 : per Φ z0 - s ≤ j := by omega
    have h3 := (hin _ hl0 hl1).2
    rw [← hadd, Nat.add_sub_cancel' hs.le, (per_spec Φ z0).2] at h3
    exact desc_not_mem T r Zs hanc hx h3 hz0
  refine ⟨s, j, hj0, hwrap, hsa, by rw [hadd, hj], fun l h1 h2 => by rw [hadd]; exact hin l h1 h2,
    fun y hy => ?_⟩
  rw [hchar y hy]
  simp only [hadd]

end yrun

end PQL21

/-! P8 (s6) general step: a `Cert` from a parent-map spanning tree and positions on vertex pairs
whose subtree intervals are exact (L1), plus a root dart at 0 and non-crossing chords. -/

namespace PQL21

open SimpleGraph

section certpar

variable {W : Type} {H : SimpleGraph W}

theorem cert_of_par (P : ParT W) (hle : P.gr ≤ H) (pos2 : W → W → ℕ)
    (hinj : ∀ d e : H.Dart, pos2 d.fst d.snd = pos2 e.fst e.snd → d = e)
    (sub : W → W → Prop) (hS1 : ∀ v, sub v v)
    (hS2 : ∀ v u, u ≠ P.root → sub v (P.par u) → u ≠ v → sub v u)
    (hL1 : ∀ v, v ≠ P.root → ∀ d : H.Dart, (sub v d.fst ↔
      (pos2 (P.par v) v < pos2 d.fst d.snd ∧ pos2 d.fst d.snd ≤ pos2 v (P.par v))))
    (hL2 : ∃ d : H.Dart, d.fst = P.root ∧ pos2 d.fst d.snd = 0)
    (hL3 : ∀ d e : H.Dart, ¬ P.gr.Adj d.fst d.snd → ¬ P.gr.Adj e.fst e.snd →
      ¬ (pos2 d.fst d.snd < pos2 e.fst e.snd ∧ pos2 e.fst e.snd < pos2 d.snd d.fst ∧
        pos2 d.snd d.fst < pos2 e.snd e.fst)) :
    Nonempty (Cert H) := by
  have hdn : ∀ v, v ≠ P.root → H.Adj (P.par v) v := fun v hv =>
    hle ((P.gr_adj).2 (Or.inr ⟨hv, rfl⟩))
  have hup : ∀ v, v ≠ P.root → H.Adj v (P.par v) := fun v hv => (hdn v hv).symm
  have hAB : ∀ v, v ≠ P.root → pos2 (P.par v) v < pos2 v (P.par v) := by
    intro v hv
    have := (hL1 v hv ⟨(v, P.par v), hup v hv⟩).1 (hS1 v)
    exact this.1
  -- a tree dart with increasing positions points down to its child
  have hdown : ∀ d : H.Dart, P.gr.Adj d.fst d.snd → pos2 d.fst d.snd < pos2 d.snd d.fst →
      d.snd ≠ P.root ∧ P.par d.snd = d.fst := by
    intro d hd hlt
    rcases (P.gr_adj).1 hd with ⟨h1, h2⟩ | h
    · exfalso
      have := hAB _ h1
      rw [h2] at this
      omega
    · exact h
  refine ⟨{
    pos := fun d => pos2 d.fst d.snd
    inj := fun d e h => hinj d e h
    TD := {d | P.gr.Adj d.fst d.snd}
    symm := fun d hd => (show P.gr.Adj d.fst d.snd from hd).symm
    F2 := ?_
    F3 := fun d e hd he => hL3 d e hd he
    F4 := ?_
    entry := ?_ }⟩
  · rintro d e hd he ⟨h1, h2, h3⟩
    change pos2 d.fst d.snd < pos2 e.fst e.snd at h1
    change pos2 e.fst e.snd < pos2 d.snd d.fst at h2
    change pos2 d.snd d.fst < pos2 e.snd e.fst at h3
    have hd' := hdown d hd (by omega)
    have he' := hdown e he (by omega)
    have hsd : d.fst = P.par d.snd := hd'.2.symm
    have hse : e.fst = P.par e.snd := he'.2.symm
    have hin : sub d.snd e.fst := by
      rw [hL1 _ hd'.1 e, ← hsd]
      exact ⟨h1, h2.le⟩
    have hout : ¬ sub d.snd e.snd := by
      intro hs
      have h4 := ((hL1 _ hd'.1 e.symm).1 hs).2
      change pos2 e.snd e.fst ≤ pos2 d.snd (P.par d.snd) at h4
      rw [← hsd] at h4
      omega
    apply hout
    refine hS2 _ _ he'.1 (by rw [← hse]; exact hin) ?_
    intro hed
    have : e = d := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext (by rw [hse, hsd, hed]) hed
    subst this
    omega
  · intro d hd hlt w
    change pos2 d.fst d.snd < pos2 d.snd d.fst at hlt
    have hd' := hdown d hd hlt
    have hsd : d.fst = P.par d.snd := hd'.2.symm
    by_cases hw : sub d.snd w
    · left
      intro x hx
      have := (hL1 _ hd'.1 x).1 (by rw [hx]; exact hw)
      rw [← hsd] at this
      exact this
    · right
      intro x hx hin
      apply hw
      rw [← hx, hL1 _ hd'.1 x, ← hsd]
      exact hin
  · intro b hb hmin
    change 0 < pos2 b.fst b.snd at hb
    by_cases hr : b.fst = P.root
    · exfalso
      obtain ⟨d0, hd0, hd00⟩ := hL2
      have := hmin d0 (hd0.trans hr.symm)
      change pos2 b.fst b.snd ≤ pos2 d0.fst d0.snd at this
      omega
    · refine ⟨⟨(P.par b.fst, b.fst), hdn _ hr⟩, ?_, rfl, ?_⟩
      · exact (P.gr_adj).2 (Or.inr ⟨hr, rfl⟩)
      · exact ((hL1 _ hr b).1 (hS1 _)).1

end certpar

end PQL21

/-! P8b (s6) part 1: the parent structure of `G⁺` (children of each vertex) and the position
function `p2v` / subtree predicate `subv` on the underlying values. -/

namespace PQL21

open SimpleGraph

section inst

variable {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) (r : V) (Zs : Set V)

abbrev CV (V : Type) [Fintype V] := Option (V ⊕ V × Fin (Fintype.card V))

noncomputable def dv : CV V → ℕ
  | none => 0
  | some (Sum.inl v) => T.dist r v
  | some (Sum.inr (_, j)) => (j : ℕ)

theorem cdep_eq (a : CW T r Zs) : cdep T r Zs a = dv T r a.1 := by
  rcases a with ⟨_ | v | ⟨x, j⟩, ha⟩ <;> rfl

theorem child_inl {b : CW T r Zs} {u : V} (hu : u ∉ Zs)
    (h : cpar T r Zs b = ⟨some (Sum.inl u), hu⟩) :
    ∃ v, b.1 = some (Sum.inl v) ∧ tpar T r v = u ∧ v ∉ Zs := by
  rcases b with ⟨_ | v | ⟨x, j⟩, hb⟩
  · change croot T r Zs = _ at h
    have h' := congrArg Subtype.val h
    simp [croot] at h'
  · by_cases hp : tpar T r v ∈ Zs
    · by_cases hj : 1 < T.dist r v
      · simp only [cpar, hp, hj, ↓reduceDIte] at h
        have h' := congrArg Subtype.val h
        simp at h'
      · simp only [cpar, hp, hj, ↓reduceDIte] at h
        have h' := congrArg Subtype.val h
        simp [croot] at h'
    · simp only [cpar, hp, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp only [Option.some.injEq, Sum.inl.injEq] at h'
      exact ⟨v, rfl, h', hb⟩
  · by_cases hj : (j : ℕ) = 1
    · simp only [cpar, hj, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp [croot] at h'
    · simp only [cpar, hj, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp at h'

theorem child_inr {b : CW T r Zs} {x : V} {j : Fin (Fintype.card V)}
    (hx : cvalid T r Zs (some (Sum.inr (x, j))))
    (h : cpar T r Zs b = ⟨some (Sum.inr (x, j)), hx⟩) :
    (b.1 = some (Sum.inl x) ∧ (j : ℕ) + 1 = T.dist r x) ∨
      ∃ j' : Fin (Fintype.card V), b.1 = some (Sum.inr (x, j')) ∧ (j' : ℕ) = j + 1 := by
  rcases b with ⟨_ | v | ⟨y, k⟩, hb⟩
  · change croot T r Zs = _ at h
    have h' := congrArg Subtype.val h
    simp [croot] at h'
  · by_cases hp : tpar T r v ∈ Zs
    · by_cases hj : 1 < T.dist r v
      · simp only [cpar, hp, hj, ↓reduceDIte] at h
        have h' := congrArg Subtype.val h
        simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff] at h'
        obtain ⟨rfl, h2⟩ := h'
        left
        refine ⟨rfl, ?_⟩
        omega
      · simp only [cpar, hp, hj, ↓reduceDIte] at h
        have h' := congrArg Subtype.val h
        simp [croot] at h'
    · simp only [cpar, hp, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp at h'
  · by_cases hj : (k : ℕ) = 1
    · simp only [cpar, hj, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp [croot] at h'
    · simp only [cpar, hj, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff] at h'
      obtain ⟨rfl, h2⟩ := h'
      right
      refine ⟨k, rfl, ?_⟩
      have := hb.2.2.1
      omega

theorem child_root {b : CW T r Zs} (h : cpar T r Zs b = croot T r Zs)
    (hb : b ≠ croot T r Zs) :
    ∃ x, x ∉ Zs ∧ tpar T r x ∈ Zs ∧
      ((b.1 = some (Sum.inl x) ∧ T.dist r x ≤ 1) ∨
        ∃ j' : Fin (Fintype.card V), b.1 = some (Sum.inr (x, j')) ∧ (j' : ℕ) = 1) := by
  rcases b with ⟨_ | v | ⟨y, k⟩, hb'⟩
  · exact absurd rfl hb
  · by_cases hp : tpar T r v ∈ Zs
    · by_cases hj : 1 < T.dist r v
      · simp only [cpar, hp, hj, ↓reduceDIte] at h
        have h' := congrArg Subtype.val h
        simp [croot] at h'
      · exact ⟨v, hb', hp, Or.inl ⟨rfl, by omega⟩⟩
    · simp only [cpar, hp, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp [croot] at h'
  · by_cases hj : (k : ℕ) = 1
    · exact ⟨y, hb'.1, hb'.2.1, Or.inr ⟨k, rfl, hj⟩⟩
    · simp only [cpar, hj, ↓reduceDIte] at h
      have h' := congrArg Subtype.val h
      simp [croot] at h'

theorem par_inl_nz {u : V} (hu : u ∉ Zs) (hp : tpar T r u ∉ Zs) :
    (cpar T r Zs ⟨some (Sum.inl u), hu⟩).1 = some (Sum.inl (tpar T r u)) := by
  simp only [cpar, hp, ↓reduceDIte]

theorem par_inl_top (hT : T.IsTree) (hr : r ∈ Zs) {u : V} (hu : u ∉ Zs) (hp : tpar T r u ∈ Zs) :
    (∀ v, (cpar T r Zs ⟨some (Sum.inl u), hu⟩).1 ≠ some (Sum.inl v)) ∧
      dv T r (cpar T r Zs ⟨some (Sum.inl u), hu⟩).1 + 1 = T.dist r u := by
  have hur : u ≠ r := fun e => hu (e ▸ hr)
  have h1 := dist_pos_of_ne T r hT hur
  by_cases hj : 1 < T.dist r u
  · simp only [cpar, hp, hj, ↓reduceDIte]
    refine ⟨fun v => by simp, ?_⟩
    simp only [dv]
    omega
  · simp only [cpar, hp, hj, ↓reduceDIte, croot]
    refine ⟨fun v => by simp, ?_⟩
    simp only [dv]
    omega

theorem par_inr_val {x : V} {j : Fin (Fintype.card V)} (hx : cvalid T r Zs (some (Sum.inr (x, j)))) :
    dv T r (cpar T r Zs ⟨some (Sum.inr (x, j)), hx⟩).1 + 1 = j := by
  have := hx.2.2.1
  by_cases hj : (j : ℕ) = 1
  · simp only [cpar, hj, ↓reduceDIte, croot, dv]
  · simp only [cpar, hj, ↓reduceDIte, dv]
    omega

variable (kk : V → V → ℕ)

/-- positions on vertex pairs of `G⁺` (`M = |V|`): `M * (Y-index) + offset` -/
noncomputable def p2v : CV V → CV V → ℕ
  | some (Sum.inl u), some (Sum.inl w) => Fintype.card V * kk u w
  | some (Sum.inl u), _ => Fintype.card V * kk u (tpar T r u)
  | some (Sum.inr (x, j)), b => if dv T r b = (j : ℕ) + 1 then
      Fintype.card V * kk (tpar T r x) x + j
    else Fintype.card V * kk x (tpar T r x) + (T.dist r x - j)
  | none, some (Sum.inl v) => Fintype.card V * kk (tpar T r v) v
  | none, some (Sum.inr (x, _)) => Fintype.card V * kk (tpar T r x) x
  | none, none => 0

/-- `subv v u`: `u` lies in the subtree of `v` -/
def subv : CV V → CV V → Prop
  | some (Sum.inl w), some (Sum.inl u) => u ∈ desc T r w
  | some (Sum.inl _), _ => False
  | some (Sum.inr (x, _)), some (Sum.inl u) => u ∈ desc T r x
  | some (Sum.inr (x, i)), some (Sum.inr (x', j)) => x' = x ∧ (i : ℕ) ≤ j
  | some (Sum.inr _), none => False
  | none, _ => True

theorem p2v_inl_up (u : V) (b' : CV V) (hb : ∀ v, b' ≠ some (Sum.inl v)) :
    p2v T r kk (some (Sum.inl u)) b' = Fintype.card V * kk u (tpar T r u) := by
  rcases b' with _ | v | ⟨y, k⟩
  · rfl
  · exact absurd rfl (hb v)
  · rfl

/-- the three kinds of darts of `G⁺` with their positions -/
theorem forms (G : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (a b : CW T r Zs) (hab : (cG T r Zs G hT hr).Adj a b) :
    (∃ u t, a.1 = some (Sum.inl u) ∧ u ∉ Zs ∧ G.Adj u t ∧
      p2v T r kk a.1 b.1 = Fintype.card V * kk u t ∧
      (b.1 = some (Sum.inl t) ∨ (t = tpar T r u ∧ t ∈ Zs ∧ b = cpar T r Zs a))) ∨
    (∃ x, ∃ j : Fin (Fintype.card V), a.1 = some (Sum.inr (x, j)) ∧ x ∉ Zs ∧ tpar T r x ∈ Zs ∧
      1 ≤ (j : ℕ) ∧ (j : ℕ) < T.dist r x ∧
      ((p2v T r kk a.1 b.1 = Fintype.card V * kk (tpar T r x) x + j ∧ cpar T r Zs b = a ∧
          b ≠ croot T r Zs) ∨
        (p2v T r kk a.1 b.1 = Fintype.card V * kk x (tpar T r x) + (T.dist r x - j) ∧
          b = cpar T r Zs a))) ∨
    (a = croot T r Zs ∧ ∃ x, x ∉ Zs ∧ tpar T r x ∈ Zs ∧
      p2v T r kk a.1 b.1 = Fintype.card V * kk (tpar T r x) x ∧
      cpar T r Zs b = croot T r Zs ∧ b ≠ croot T r Zs ∧
      (b.1 = some (Sum.inl x) ∨ ∃ j, b.1 = some (Sum.inr (x, j)))) := by
  rcases (sup_adj _ _ _ _).1 hab with h | h
  · rcases a with ⟨_ | u | ⟨x, j⟩, ha⟩
    · right; right
      rcases (cP T r Zs hT hr).gr_adj.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact absurd rfl h1
      · obtain ⟨x, hx1, hx2, hb⟩ := child_root T r Zs h2 h1
        refine ⟨rfl, x, hx1, hx2, ?_, h2, h1, ?_⟩
        · rcases hb with ⟨hb, -⟩ | ⟨j', hb, -⟩ <;> simp only [hb, p2v]
        · rcases hb with ⟨hb, -⟩ | ⟨j', hb, -⟩
          · exact Or.inl hb
          · exact Or.inr ⟨j', hb⟩
    · left
      have hur : u ≠ r := fun e => ha (e ▸ hr)
      rcases (cP T r Zs hT hr).gr_adj.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : cpar T r Zs ⟨some (Sum.inl u), ha⟩ = b := h2
        have hTa : T.Adj u (tpar T r u) := (tpar_spec T r hT hur).1
        refine ⟨u, tpar T r u, rfl, ha, hTG hTa, ?_⟩
        by_cases hp : tpar T r u ∈ Zs
        · have hn := (par_inl_top T r Zs hT hr ha hp).1
          rw [h2'] at hn
          exact ⟨p2v_inl_up T r kk u _ hn, Or.inr ⟨rfl, hp, h2'.symm⟩⟩
        · have hb1 := par_inl_nz T r Zs ha hp
          rw [h2'] at hb1
          refine ⟨by simp only [hb1, p2v], Or.inl hb1⟩
      · have h2' : cpar T r Zs b = ⟨some (Sum.inl u), ha⟩ := h2
        obtain ⟨v, hb1, hv1, hv2⟩ := child_inl T r Zs ha h2'
        have hvr : v ≠ r := fun e => hv2 (e ▸ hr)
        have hTa : T.Adj v (tpar T r v) := (tpar_spec T r hT hvr).1
        rw [hv1] at hTa
        exact ⟨u, v, rfl, ha, hTG hTa.symm, by simp only [hb1, p2v], Or.inl hb1⟩
    · right; left
      refine ⟨x, j, rfl, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, ?_⟩
      rcases (cP T r Zs hT hr).gr_adj.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : cpar T r Zs ⟨some (Sum.inr (x, j)), ha⟩ = b := h2
        right
        refine ⟨?_, h2'.symm⟩
        have hd := par_inr_val T r Zs ha
        rw [h2'] at hd
        simp only [p2v]
        rw [if_neg (by omega)]
      · have h2' : cpar T r Zs b = ⟨some (Sum.inr (x, j)), ha⟩ := h2
        left
        refine ⟨?_, h2', h1⟩
        have hdv : dv T r b.1 = (j : ℕ) + 1 := by
          rcases child_inr T r Zs ha h2' with ⟨hb, hj⟩ | ⟨j', hb, hj⟩
          · rw [hb]; exact hj.symm
          · rw [hb]; exact hj
        simp only [p2v]
        rw [if_pos hdv]
  · obtain ⟨u, w, huw, rfl, rfl⟩ := (map_adj _ _ _ _).1 h
    left
    exact ⟨u.1, w.1, rfl, u.2, huw, rfl, Or.inl rfl⟩

end inst

end PQL21

/-! P8b (s6) part 2: the abstract index interface `KKH` (what the face cycle `Y` provides) and
its interval consequences. -/

namespace PQL21

open SimpleGraph

section lex

theorem lex_lt {M c b o o' : ℕ} (ho : o < M) (ho' : o' < M) :
    M * c + o < M * b + o' ↔ c < b ∨ (c = b ∧ o < o') := by
  constructor
  · intro h
    rcases lt_trichotomy c b with hcb | rfl | hcb
    · exact Or.inl hcb
    · exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hcb)
      rw [Nat.mul_succ] at this
      omega
  · rintro (hcb | ⟨rfl, h⟩)
    · have := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hcb)
      rw [Nat.mul_succ] at this
      omega
    · omega

theorem lex_le {M c b o o' : ℕ} (ho : o < M) (ho' : o' < M) :
    M * c + o ≤ M * b + o' ↔ c < b ∨ (c = b ∧ o ≤ o') := by
  rw [← not_lt, lex_lt ho' ho]
  constructor
  · intro h
    rcases lt_trichotomy c b with hcb | rfl | hcb
    · exact Or.inl hcb
    · exact Or.inr ⟨rfl, by omega⟩
    · exact absurd (Or.inl hcb) h
  · rintro (hcb | ⟨rfl, h⟩) (h' | ⟨h1, h2⟩) <;> omega

theorem lex_eq {M c b o o' : ℕ} (ho : o < M) (ho' : o' < M) (h : M * c + o = M * b + o') :
    c = b ∧ o = o' := by
  have h1 := (lex_le ho ho').1 h.le
  have h2 := (lex_le ho' ho).1 h.ge
  omega

end lex

section kkh

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : SimpleGraph V) (r : V)
  (Zs : Set V) (kk : V → V → ℕ)

/-- the index facts the face cycle provides (P8a proves them) -/
structure KKH : Prop where
  inj : ∀ u t u' t', G.Adj u t → G.Adj u' t' → (u ∉ Zs ∨ (t ∉ Zs ∧ u = tpar T r t)) →
    (u' ∉ Zs ∨ (t' ∉ Zs ∧ u' = tpar T r t')) → kk u t = kk u' t' → u = u' ∧ t = t'
  run : ∀ w, w ∉ Zs → kk (tpar T r w) w < kk w (tpar T r w) ∧
    ∀ u t, G.Adj u t → u ∉ Zs →
      (u ∈ desc T r w ↔ kk (tpar T r w) w < kk u t ∧ kk u t ≤ kk w (tpar T r w))
  chord : ∀ u t u' t', G.Adj u t → ¬ T.Adj u t → u ∉ Zs → t ∉ Zs →
    G.Adj u' t' → ¬ T.Adj u' t' → u' ∉ Zs → t' ∉ Zs →
    ¬ (kk u t < kk u' t' ∧ kk u' t' < kk t u ∧ kk t u < kk t' u')
  zero : ∃ x, x ∉ Zs ∧ tpar T r x ∈ Zs ∧ kk (tpar T r x) x = 0

theorem desc_succ {u w : V} (h : tpar T r u ∈ desc T r w) : u ∈ desc T r w := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem desc_trans {u v w : V} (h1 : u ∈ desc T r v) (h2 : v ∈ desc T r w) : u ∈ desc T r w := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  exact ⟨m + n, by rw [Function.iterate_add_apply, hn, hm]⟩

theorem desc_step {w x : V} (h : w ∈ desc T r x) (hne : w ≠ x) : tpar T r w ∈ desc T r x := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn hne
  | succ n =>
    rw [Function.iterate_succ_apply] at hn
    exact ⟨n, hn⟩

theorem desc_antisymm (hT : T.IsTree) {u w : V} (h1 : u ∈ desc T r w) (h2 : w ∈ desc T r u)
    (hu : u ≠ r) : u = w := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have hk : (tpar T r)^[m + n] u = u := by rw [Function.iterate_add_apply, hn, hm]
  cases n with
  | zero => exact hn
  | succ n =>
    exfalso
    rw [Nat.add_succ, Function.iterate_succ_apply] at hk
    have h3 := dist_iter_le T hT r (tpar T r u) (m + n)
    have h4 := (tpar_spec T r hT hu).2
    rw [hk] at h3
    omega

variable {G T r Zs kk}

theorem adj_up (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs) {w : V} (hw : w ∉ Zs) :
    G.Adj w (tpar T r w) :=
  hTG (tpar_spec T r hT (fun e => hw (by rw [e]; exact hr))).1

theorem top_of (hT : T.IsTree) (hr : r ∈ Zs) {w : V} (hw : w ∉ Zs) :
    ∃ x, x ∉ Zs ∧ tpar T r x ∈ Zs ∧ w ∈ desc T r x :=
  top_exists T hT r Zs hr _ w rfl hw

theorem K_e (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) {w x : V} (hw : w ∉ Zs) (hx : x ∉ Zs)
    (hxp : tpar T r x ∈ Zs) (h1 : kk (tpar T r w) w < kk x (tpar T r x))
    (h2 : kk x (tpar T r x) < kk w (tpar T r w)) : False := by
  have hxw : x ∈ desc T r w :=
    ((K.run w hw).2 x _ (adj_up hTG hT hr hx) hx).2 ⟨h1, h2.le⟩
  obtain ⟨x'', h1'', h2'', hw''⟩ := top_of hT hr hw
  have hxx := top_unique T r Zs hanc hx hxp h1'' h2'' (mem_desc_self T r x)
    (desc_trans T r hxw hw'')
  subst hxx
  have := desc_antisymm T r hT hw'' hxw (fun e => hw (by rw [e]; exact hr))
  subst this
  omega

theorem K_s (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) {w x : V} (hw : w ∉ Zs) (hx : x ∉ Zs)
    (hxp : tpar T r x ∈ Zs) (h1 : kk (tpar T r w) w < kk (tpar T r x) x)
    (h2 : kk (tpar T r x) x < kk w (tpar T r w)) : False := by
  have hrx := (K.run x hx).1
  rcases lt_trichotomy (kk x (tpar T r x)) (kk w (tpar T r w)) with h3 | h3 | h3
  · exact K_e K hTG hT hr hanc hw hx hxp (by omega) h3
  · obtain ⟨rfl, -⟩ := K.inj _ _ _ _ (adj_up hTG hT hr hx) (adj_up hTG hT hr hw) (Or.inl hx)
      (Or.inl hw) h3
    omega
  · have hwx : w ∈ desc T r x :=
      ((K.run x hx).2 w _ (adj_up hTG hT hr hw) hw).2 ⟨by omega, h3.le⟩
    by_cases hp : tpar T r w ∈ Zs
    · have := top_unique T r Zs hanc hw hp hx hxp (mem_desc_self T r w) hwx
      subst this
      omega
    · have hn : tpar T r w ∉ desc T r x := by
        intro hin
        have := ((K.run x hx).2 _ w (adj_up hTG hT hr hw).symm hp).1 hin
        omega
      by_cases hwx' : w = x
      · subst hwx'
        omega
      · exact hn (desc_step T r hwx hwx')

/-- distinct tops have disjoint index intervals -/
theorem K_disj (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) {x x' : V} (hx : x ∉ Zs) (hxp : tpar T r x ∈ Zs)
    (hx' : x' ∉ Zs) (hxp' : tpar T r x' ∈ Zs) (hne : x ≠ x') :
    (kk (tpar T r x') x' < kk (tpar T r x) x ∨ kk x (tpar T r x) < kk (tpar T r x') x') ∧
    (kk x' (tpar T r x') < kk (tpar T r x) x ∨ kk x (tpar T r x) < kk x' (tpar T r x')) := by
  have hrx := (K.run x hx).1
  have hrx' := (K.run x' hx').1
  have hA : ∀ y, y ∉ Zs → G.Adj (tpar T r y) y := fun y hy => (adj_up hTG hT hr hy).symm
  have he : kk x' (tpar T r x') < kk (tpar T r x) x ∨ kk x (tpar T r x) < kk x' (tpar T r x') := by
    by_contra hc
    push_neg at hc
    rcases hc.1.lt_or_eq with h | h
    · have := ((K.run x hx).2 x' _ (adj_up hTG hT hr hx') hx').2 ⟨h, hc.2⟩
      exact hne (top_unique T r Zs hanc hx hxp hx' hxp' this (mem_desc_self T r x'))
    · obtain ⟨h1, -⟩ := K.inj _ _ _ _ (hA x hx) (adj_up hTG hT hr hx') (Or.inr ⟨hx, rfl⟩)
        (Or.inl hx') h
      exact hx' (h1 ▸ hxp)
  refine ⟨?_, he⟩
  by_contra hc
  push_neg at hc
  rcases hc.1.lt_or_eq with h | h
  · rcases hc.2.lt_or_eq with h' | h'
    · exact K_s K hTG hT hr hanc hx hx' hxp' h h'
    · obtain ⟨h1, -⟩ := K.inj _ _ _ _ (adj_up hTG hT hr hx) (hA x' hx') (Or.inl hx)
        (Or.inr ⟨hx', rfl⟩) h'.symm
      exact hx (h1 ▸ hxp')
  · obtain ⟨-, h2⟩ := K.inj _ _ _ _ (hA x hx) (hA x' hx') (Or.inr ⟨hx, rfl⟩)
      (Or.inr ⟨hx', rfl⟩) h
    exact hne h2

end kkh

end PQL21

/-! P8b (s6) part 3: the pieces of `cert_of_par` for `G⁺`: subtree-interval endpoints (A/B),
S2, the root dart at 0 (L2), chords are inner non-tree G-edges (L3 shape). -/

namespace PQL21

open SimpleGraph

section cg

variable {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) (r : V) (Zs : Set V)
  (kk : V → V → ℕ)

open Classical in
theorem A_inl {w : V} (hw : w ∉ Zs) :
    p2v T r kk (cpar T r Zs ⟨some (Sum.inl w), hw⟩).1 (some (Sum.inl w)) =
      Fintype.card V * kk (tpar T r w) w + (if tpar T r w ∈ Zs then T.dist r w - 1 else 0) := by
  by_cases hp : tpar T r w ∈ Zs
  · rw [if_pos hp]
    by_cases hj : 1 < T.dist r w
    · simp only [cpar, hp, hj, ↓reduceDIte, p2v]
      rw [if_pos (by simp only [dv, Fin.val_mk]; omega)]
    · simp only [cpar, hp, hj, ↓reduceDIte, croot, p2v]
      omega
  · rw [if_neg hp]
    simp only [cpar, hp, ↓reduceDIte, p2v]
    omega

theorem B_inl (hT : T.IsTree) (hr : r ∈ Zs) {w : V} (hw : w ∉ Zs) :
    p2v T r kk (some (Sum.inl w)) (cpar T r Zs ⟨some (Sum.inl w), hw⟩).1 =
      Fintype.card V * kk w (tpar T r w) := by
  by_cases hp : tpar T r w ∈ Zs
  · exact p2v_inl_up T r kk w _ (par_inl_top T r Zs hT hr hw hp).1
  · rw [par_inl_nz T r Zs hw hp]
    rfl

theorem A_inr {x : V} {i : Fin (Fintype.card V)} (hx : cvalid T r Zs (some (Sum.inr (x, i)))) :
    p2v T r kk (cpar T r Zs ⟨some (Sum.inr (x, i)), hx⟩).1 (some (Sum.inr (x, i))) =
      Fintype.card V * kk (tpar T r x) x + ((i : ℕ) - 1) := by
  have h1 := hx.2.2.1
  by_cases hi : (i : ℕ) = 1
  · simp only [cpar, hi, ↓reduceDIte, croot, p2v]
    omega
  · simp only [cpar, hi, ↓reduceDIte, p2v]
    rw [if_pos (by simp only [dv, Fin.val_mk]; omega)]

theorem B_inr {x : V} {i : Fin (Fintype.card V)} (hx : cvalid T r Zs (some (Sum.inr (x, i)))) :
    p2v T r kk (some (Sum.inr (x, i))) (cpar T r Zs ⟨some (Sum.inr (x, i)), hx⟩).1 =
      Fintype.card V * kk x (tpar T r x) + (T.dist r x - i) := by
  have hd := par_inr_val T r Zs hx
  simp only [p2v]
  rw [if_neg (by omega)]

theorem S2_cg (u v : CW T r Zs) (hu : u ≠ croot T r Zs)
    (h : subv T r v.1 (cpar T r Zs u).1) : subv T r v.1 u.1 := by
  rcases u with ⟨_ | u' | ⟨x', j⟩, hu'⟩
  · exact absurd rfl hu
  · by_cases hp : tpar T r u' ∈ Zs
    · by_cases hj : 1 < T.dist r u'
      · simp only [cpar, hp, hj, ↓reduceDIte] at h
        rcases v with ⟨_ | w | ⟨x, i⟩, hv⟩
        · trivial
        · exact h.elim
        · obtain ⟨rfl, -⟩ := h
          exact mem_desc_self T r _
      · simp only [cpar, hp, hj, ↓reduceDIte, croot] at h
        rcases v with ⟨_ | w | ⟨x, i⟩, hv⟩
        · trivial
        · exact h.elim
        · exact h.elim
    · simp only [cpar, hp, ↓reduceDIte] at h
      rcases v with ⟨_ | w | ⟨x, i⟩, hv⟩
      · trivial
      · exact desc_succ T r h
      · exact desc_succ T r h
  · by_cases hj : (j : ℕ) = 1
    · simp only [cpar, hj, ↓reduceDIte, croot] at h
      rcases v with ⟨_ | w | ⟨x, i⟩, hv⟩
      · trivial
      · exact h.elim
      · exact h.elim
    · simp only [cpar, hj, ↓reduceDIte] at h
      rcases v with ⟨_ | w | ⟨x, i⟩, hv⟩
      · trivial
      · exact h.elim
      · obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by simp only at h2; omega⟩

theorem S1_cg (v : CW T r Zs) : subv T r v.1 v.1 := by
  rcases v with ⟨_ | w | ⟨x, i⟩, hv⟩
  · trivial
  · exact mem_desc_self T r w
  · exact ⟨rfl, le_rfl⟩

/-- the first node below the root on the private path of a top `x` -/
theorem root_child {x : V} (hx : x ∉ Zs) (hxp : tpar T r x ∈ Zs) :
    ∃ b : CW T r Zs, b ≠ croot T r Zs ∧ cpar T r Zs b = croot T r Zs ∧
      (b.1 = some (Sum.inl x) ∨ ∃ j, b.1 = some (Sum.inr (x, j))) := by
  by_cases hj : 1 < T.dist r x
  · have hc := dist_lt_card T r x
    refine ⟨⟨some (Sum.inr (x, ⟨1, by omega⟩)), ⟨hx, hxp, le_rfl, hj⟩⟩, ?_, ?_,
      Or.inr ⟨_, rfl⟩⟩
    · intro h
      have := congrArg Subtype.val h
      simp [croot] at this
    · simp only [cpar, ↓reduceDIte]
  · refine ⟨⟨some (Sum.inl x), hx⟩, ?_, ?_, Or.inl rfl⟩
    · intro h
      have := congrArg Subtype.val h
      simp [croot] at this
    · simp only [cpar, hxp, hj, ↓reduceDIte]

theorem p2v_root (b : CW T r Zs) {x : V}
    (hb : b.1 = some (Sum.inl x) ∨ ∃ j, b.1 = some (Sum.inr (x, j))) :
    p2v T r kk none b.1 = Fintype.card V * kk (tpar T r x) x := by
  rcases hb with hb | ⟨j, hb⟩ <;> rw [hb] <;> rfl

/-- non-tree darts of `G⁺` are G-edges between vertices outside `Zs` that are not `T`-edges -/
theorem chord_form (G : SimpleGraph V) (hT : T.IsTree) (hr : r ∈ Zs) (a b : CW T r Zs)
    (hab : (cG T r Zs G hT hr).Adj a b) (hn : ¬ (cP T r Zs hT hr).gr.Adj a b) :
    ∃ u t, a.1 = some (Sum.inl u) ∧ b.1 = some (Sum.inl t) ∧ u ∉ Zs ∧ t ∉ Zs ∧ G.Adj u t ∧
      ¬ T.Adj u t := by
  rcases (sup_adj _ _ _ _).1 hab with h | h
  · exact absurd h hn
  · obtain ⟨u, w, huw, rfl, rfl⟩ := (map_adj _ _ _ _).1 h
    refine ⟨u.1, w.1, rfl, rfl, u.2, w.2, huw, fun hT' => hn ?_⟩
    rw [(cP T r Zs hT hr).gr_adj]
    rcases adj_tpar T hT r hT' with e | e
    · left
      refine ⟨fun h => ?_, ?_⟩
      · have := congrArg Subtype.val h
        simp [croot, cι, cP] at this
      · apply Subtype.ext
        have hp : tpar T r u.1 ∉ Zs := e ▸ w.2
        change (cpar T r Zs ⟨some (Sum.inl u.1), u.2⟩).1 = some (Sum.inl w.1)
        rw [par_inl_nz T r Zs u.2 hp, ← e]
    · right
      refine ⟨fun h => ?_, ?_⟩
      · have := congrArg Subtype.val h
        simp [croot, cι, cP] at this
      · apply Subtype.ext
        have hp : tpar T r w.1 ∉ Zs := e ▸ u.2
        change (cpar T r Zs ⟨some (Sum.inl w.1), w.2⟩).1 = some (Sum.inl u.1)
        rw [par_inl_nz T r Zs w.2 hp, ← e]

end cg

end PQL21

/-! P8b (s7): `cert_cG` — a `Cert` for `G⁺` from the index facts `KKH`, via `cert_of_par`. -/

namespace PQL21

open SimpleGraph

section fin

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : SimpleGraph V) (r : V)
  (Zs : Set V) (kk : V → V → ℕ)

theorem dart_eq' {W : Type} {H : SimpleGraph W} {d e : H.Dart} (h1 : d.fst = e.fst)
    (h2 : d.snd = e.snd) : d = e :=
  SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)

theorem kk_ss (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs) {a b : V}
    (ha : a ∉ Zs) (hb : b ∉ Zs) (h : kk (tpar T r a) a = kk (tpar T r b) b) : a = b :=
  (K.inj _ _ _ _ (adj_up hTG hT hr ha).symm (adj_up hTG hT hr hb).symm
    (Or.inr ⟨ha, rfl⟩) (Or.inr ⟨hb, rfl⟩) h).2

theorem kk_ee (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs) {a b : V}
    (ha : a ∉ Zs) (hb : b ∉ Zs) (h : kk a (tpar T r a) = kk b (tpar T r b)) : a = b :=
  (K.inj _ _ _ _ (adj_up hTG hT hr ha) (adj_up hTG hT hr hb)
    (Or.inl ha) (Or.inl hb) h).1

theorem kk_se (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs) {a b : V}
    (ha : a ∉ Zs) (hb : b ∉ Zs) (h : kk (tpar T r a) a = kk b (tpar T r b)) : False := by
  obtain ⟨h1, h2⟩ := K.inj _ _ _ _ (adj_up hTG hT hr ha).symm
    (adj_up hTG hT hr hb) (Or.inr ⟨ha, rfl⟩) (Or.inl hb) h
  have har : a ≠ r := fun e => ha (e ▸ hr)
  have hbr : b ≠ r := fun e => hb (e ▸ hr)
  have s1 := (tpar_spec T r hT har).2
  have s2 := (tpar_spec T r hT hbr).2
  rw [h1] at s1
  rw [← h2] at s2
  omega

theorem child_inr_uniq {a b b' : CW T r Zs} {x : V} {j : Fin (Fintype.card V)}
    (ha : a.1 = some (Sum.inr (x, j))) (hb : cpar T r Zs b = a) (hb' : cpar T r Zs b' = a) :
    b = b' := by
  obtain ⟨a1, a2⟩ := a
  change a1 = some (Sum.inr (x, j)) at ha
  subst ha
  have h1 := child_inr T r Zs a2 hb
  have h2 := child_inr T r Zs a2 hb'
  apply Subtype.ext
  rcases h1 with ⟨e1, f1⟩ | ⟨k1, e1, f1⟩ <;> rcases h2 with ⟨e2, f2⟩ | ⟨k2, e2, f2⟩
  · rw [e1, e2]
  · exfalso
    have hv := b'.2
    rw [e2] at hv
    have := hv.2.2.2
    omega
  · exfalso
    have hv := b.2
    rw [e1] at hv
    have := hv.2.2.2
    omega
  · rw [e1, e2, Fin.ext (f1.trans f2.symm)]

theorem root_child_x {b : CW T r Zs} {x : V} (hb : cpar T r Zs b = croot T r Zs)
    (hb0 : b ≠ croot T r Zs)
    (hf : b.1 = some (Sum.inl x) ∨ ∃ j, b.1 = some (Sum.inr (x, j))) :
    (b.1 = some (Sum.inl x) ∧ T.dist r x ≤ 1) ∨
      ∃ j' : Fin (Fintype.card V), b.1 = some (Sum.inr (x, j')) ∧ (j' : ℕ) = 1 := by
  obtain ⟨y, -, -, h1⟩ := child_root T r Zs hb hb0
  rcases h1 with ⟨e1, f1⟩ | ⟨k, e1, f1⟩
  · rcases hf with e | ⟨j, e⟩
    · rw [e1] at e
      simp only [Option.some.injEq, Sum.inl.injEq] at e
      subst e
      exact Or.inl ⟨e1, f1⟩
    · rw [e1] at e
      simp at e
  · rcases hf with e | ⟨j, e⟩
    · rw [e1] at e
      simp at e
    · rw [e1] at e
      simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      exact Or.inr ⟨k, e1, f1⟩

theorem root_child_uniq {b b' : CW T r Zs} {x : V} (hb : cpar T r Zs b = croot T r Zs)
    (hb0 : b ≠ croot T r Zs)
    (hf : b.1 = some (Sum.inl x) ∨ ∃ j, b.1 = some (Sum.inr (x, j)))
    (hb' : cpar T r Zs b' = croot T r Zs) (hb0' : b' ≠ croot T r Zs)
    (hf' : b'.1 = some (Sum.inl x) ∨ ∃ j, b'.1 = some (Sum.inr (x, j))) : b = b' := by
  apply Subtype.ext
  rcases root_child_x T r Zs hb hb0 hf with ⟨e1, f1⟩ | ⟨k1, e1, f1⟩ <;>
    rcases root_child_x T r Zs hb' hb0' hf' with ⟨e2, f2⟩ | ⟨k2, e2, f2⟩
  · rw [e1, e2]
  · exfalso
    have hv := b'.2
    rw [e2] at hv
    have := hv.2.2.2
    omega
  · exfalso
    have hv := b.2
    rw [e1] at hv
    have := hv.2.2.2
    omega
  · rw [e1, e2, Fin.ext (f1.trans f2.symm)]

theorem inj_cg (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (d e : (cG T r Zs G hT hr).Dart)
    (h : p2v T r kk d.fst.1 d.snd.1 = p2v T r kk e.fst.1 e.snd.1) : d = e := by
  have hM : ∀ x : V, T.dist r x < Fintype.card V := fun x => dist_lt_card T r x
  have hM0 : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  rcases forms T r Zs kk G hTG hT hr d.fst d.snd d.adj with
    ⟨u, t, ha, hu, hut, hp, hb⟩ | ⟨x, j, ha, hx, hxp, hj1, hj2, ⟨hp, hcb, hbr⟩ | ⟨hp, hb⟩⟩ |
    ⟨ha, x, hx, hxp, hp, hcb, hbr, hf⟩ <;>
  rcases forms T r Zs kk G hTG hT hr e.fst e.snd e.adj with
    ⟨u', t', ha', hu', hut', hp', hb'⟩ | ⟨x', j', ha', hx', hxp', hj1', hj2', ⟨hp', hcb', hbr'⟩ |
      ⟨hp', hb'⟩⟩ | ⟨ha', x', hx', hxp', hp', hcb', hbr', hf'⟩ <;>
  rw [hp, hp'] at h
  -- 1 (i,i)
  · have hc := Nat.eq_of_mul_eq_mul_left hM0 h
    obtain ⟨rfl, rfl⟩ := K.inj u t u' t' hut hut' (Or.inl hu) (Or.inl hu') hc
    have hfst : d.fst = e.fst := Subtype.ext (ha.trans ha'.symm)
    refine dart_eq' hfst ?_
    rcases hb with hb | ⟨-, htz, hb⟩ <;> rcases hb' with hb' | ⟨-, htz', hb'⟩
    · exact Subtype.ext (hb.trans hb'.symm)
    · exfalso
      have hv := d.snd.2
      rw [hb] at hv
      exact hv htz'
    · exfalso
      have hv := e.snd.2
      rw [hb'] at hv
      exact hv htz
    · rw [hb, hb', hfst]
  -- 2 (i,ii down)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk u t) (b := kk (tpar T r x') x') (o := 0) hM0 j'.isLt
      (by omega)
    omega
  -- 3 (i,ii up)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk u t) (b := kk x' (tpar T r x')) (o := 0) hM0
      (show T.dist r x' - j' < _ by have := hM x'; omega) (by omega)
    omega
  -- 4 (i,iii)
  · have hc := Nat.eq_of_mul_eq_mul_left hM0 h
    obtain ⟨h1, -⟩ := K.inj _ _ _ _ hut (adj_up hTG hT hr hx').symm (Or.inl hu)
      (Or.inr ⟨hx', rfl⟩) hc
    rw [h1] at hu
    exact absurd hxp' hu
  -- 5 (ii down,i)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk (tpar T r x) x) (b := kk u' t') (o' := 0) j.isLt hM0
      (by omega)
    omega
  -- 6 (ii down, ii down)
  · obtain ⟨hc, ho⟩ := lex_eq j.isLt j'.isLt h
    have hxx := kk_ss G T r Zs kk K hTG hT hr hx hx' hc
    subst hxx
    have hjj : j = j' := Fin.ext ho
    subst hjj
    have hfst : d.fst = e.fst := Subtype.ext (ha.trans ha'.symm)
    exact dart_eq' hfst (child_inr_uniq T r Zs ha hcb (hcb'.trans hfst.symm))
  -- 7 (ii down, ii up)
  · obtain ⟨hc, -⟩ := lex_eq (c := kk (tpar T r x) x) (b := kk x' (tpar T r x')) j.isLt
      (show T.dist r x' - j' < _ by have := hM x'; omega) h
    exact (kk_se G T r Zs kk K hTG hT hr hx hx' hc).elim
  -- 8 (ii down, iii)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk (tpar T r x) x) (b := kk (tpar T r x') x') (o' := 0)
      j.isLt hM0 (by omega)
    omega
  -- 9 (ii up, i)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk x (tpar T r x)) (b := kk u' t') (o' := 0)
      (show T.dist r x - j < _ by have := hM x; omega) hM0 (by omega)
    omega
  -- 10 (ii up, ii down)
  · obtain ⟨hc, -⟩ := lex_eq (c := kk x (tpar T r x)) (b := kk (tpar T r x') x')
      (show T.dist r x - j < _ by have := hM x; omega) j'.isLt h
    exact (kk_se G T r Zs kk K hTG hT hr hx' hx hc.symm).elim
  -- 11 (ii up, ii up)
  · obtain ⟨hc, ho⟩ := lex_eq (show T.dist r x - j < _ by have := hM x; omega)
      (show T.dist r x' - j' < _ by have := hM x'; omega) h
    have hxx := kk_ee G T r Zs kk K hTG hT hr hx hx' hc
    subst hxx
    have hjj : j = j' := Fin.ext (by omega)
    subst hjj
    have hfst : d.fst = e.fst := Subtype.ext (ha.trans ha'.symm)
    exact dart_eq' hfst (by rw [hb, hb', hfst])
  -- 12 (ii up, iii)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk x (tpar T r x)) (b := kk (tpar T r x') x') (o' := 0)
      (show T.dist r x - j < _ by have := hM x; omega) hM0 (by omega)
    omega
  -- 13 (iii, i)
  · have hc := Nat.eq_of_mul_eq_mul_left hM0 h
    obtain ⟨h1, -⟩ := K.inj _ _ _ _ (adj_up hTG hT hr hx).symm hut' (Or.inr ⟨hx, rfl⟩)
      (Or.inl hu') hc
    rw [← h1] at hu'
    exact absurd hxp hu'
  -- 14 (iii, ii down)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk (tpar T r x) x) (b := kk (tpar T r x') x') (o := 0)
      hM0 j'.isLt (by omega)
    omega
  -- 15 (iii, ii up)
  · obtain ⟨-, h0⟩ := lex_eq (c := kk (tpar T r x) x) (b := kk x' (tpar T r x')) (o := 0)
      hM0 (show T.dist r x' - j' < _ by have := hM x'; omega) (by omega)
    omega
  -- 16 (iii, iii)
  · have hc := Nat.eq_of_mul_eq_mul_left hM0 h
    have hxx := kk_ss G T r Zs kk K hTG hT hr hx hx' hc
    subst hxx
    have hfst : d.fst = e.fst := ha.trans ha'.symm
    exact dart_eq' hfst (root_child_uniq T r Zs hcb hbr hf hcb' hbr' hf')

theorem L1_cg (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) (v : CW T r Zs) (hv : v ≠ croot T r Zs)
    (d : (cG T r Zs G hT hr).Dart) :
    subv T r v.1 d.fst.1 ↔ (p2v T r kk (cpar T r Zs v).1 v.1 < p2v T r kk d.fst.1 d.snd.1 ∧
      p2v T r kk d.fst.1 d.snd.1 ≤ p2v T r kk v.1 (cpar T r Zs v).1) := by
  have hM : ∀ x : V, T.dist r x < Fintype.card V := fun x => dist_lt_card T r x
  have hM0 : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  have lx : ∀ {c b o o' : ℕ}, o < Fintype.card V → o' < Fintype.card V →
      (Fintype.card V * c + o < Fintype.card V * b + o' ↔ c < b ∨ (c = b ∧ o < o')) ∧
      (Fintype.card V * c + o ≤ Fintype.card V * b + o' ↔ c < b ∨ (c = b ∧ o ≤ o')) :=
    fun ho ho' => ⟨lex_lt ho ho', lex_le ho ho'⟩
  rcases v with ⟨_ | w | ⟨x, i⟩, hvv⟩
  · exact absurd (Subtype.ext rfl) hv
  · -- v = inl w
    have hw : w ∉ Zs := hvv
    have hA : ∃ o, p2v T r kk (cpar T r Zs ⟨some (Sum.inl w), hw⟩).1 (some (Sum.inl w)) =
        Fintype.card V * kk (tpar T r w) w + o ∧ o < Fintype.card V ∧
        (tpar T r w ∈ Zs → o = T.dist r w - 1) := by
      rw [A_inl T r Zs kk hw]
      by_cases hpw : tpar T r w ∈ Zs
      · rw [if_pos hpw]
        exact ⟨_, rfl, by have := hM w; omega, fun _ => rfl⟩
      · rw [if_neg hpw]
        exact ⟨_, rfl, hM0, fun h => absurd h hpw⟩
    obtain ⟨oA, hA, hoAlt, hoAtop⟩ := hA
    have hrw := (K.run w hw).1
    dsimp only
    rw [hA, B_inl T r Zs kk hT hr hw]
    rcases forms T r Zs kk G hTG hT hr d.fst d.snd d.adj with
      ⟨u, t, ha, hu, hut, hp, -⟩ | ⟨x', j, ha, hx', hxp', hj1, hj2, ⟨hp, -, -⟩ | ⟨hp, -⟩⟩ |
      ⟨ha, x', hx', hxp', hp, -, -, -⟩
    · rw [hp, ha]
      show u ∈ desc T r w ↔ _
      rw [(K.run w hw).2 u t hut hu]
      have h1 := lx (c := kk (tpar T r w) w) (b := kk u t) hoAlt hM0
      have h2 := lx (c := kk u t) (b := kk w (tpar T r w)) hM0 hM0
      constructor <;> intro h <;> omega
    · rw [hp, ha]
      show False ↔ _
      have h1 := lx (c := kk (tpar T r w) w) (b := kk (tpar T r x') x') hoAlt j.isLt
      have h2 := lx (c := kk (tpar T r x') x') (b := kk w (tpar T r w)) j.isLt hM0
      have hKs : ¬ (kk (tpar T r w) w < kk (tpar T r x') x' ∧
          kk (tpar T r x') x' < kk w (tpar T r w)) :=
        fun h => K_s K hTG hT hr hanc hw hx' hxp' h.1 h.2
      refine ⟨False.elim, fun h => ?_⟩
      by_cases hwx : w = x'
      · subst hwx
        have := hoAtop hxp'
        omega
      · have hss : kk (tpar T r w) w ≠ kk (tpar T r x') x' :=
          fun e => hwx (kk_ss G T r Zs kk K hTG hT hr hw hx' e)
        omega
    · rw [hp, ha]
      show False ↔ _
      have ho : T.dist r x' - j < Fintype.card V := by have := hM x'; omega
      have h1 := lx (c := kk (tpar T r w) w) (b := kk x' (tpar T r x')) hoAlt ho
      have h2 := lx (c := kk x' (tpar T r x')) (b := kk w (tpar T r w)) ho hM0
      have hKe : ¬ (kk (tpar T r w) w < kk x' (tpar T r x') ∧
          kk x' (tpar T r x') < kk w (tpar T r w)) :=
        fun h => K_e K hTG hT hr hanc hw hx' hxp' h.1 h.2
      have hse : kk (tpar T r w) w ≠ kk x' (tpar T r x') :=
        fun e => kk_se G T r Zs kk K hTG hT hr hw hx' e
      refine ⟨False.elim, fun h => ?_⟩
      omega
    · rw [hp, ha]
      show False ↔ _
      have h1 := lx (c := kk (tpar T r w) w) (b := kk (tpar T r x') x') hoAlt hM0
      have h2 := lx (c := kk (tpar T r x') x') (b := kk w (tpar T r w)) hM0 hM0
      have hKs : ¬ (kk (tpar T r w) w < kk (tpar T r x') x' ∧
          kk (tpar T r x') x' < kk w (tpar T r w)) :=
        fun h => K_s K hTG hT hr hanc hw hx' hxp' h.1 h.2
      have hes : kk (tpar T r x') x' ≠ kk w (tpar T r w) :=
        fun e => kk_se G T r Zs kk K hTG hT hr hx' hw e
      refine ⟨False.elim, fun h => ?_⟩
      omega
  · -- v = inr (x, i)
    have hx : x ∉ Zs := hvv.1
    have hxp : tpar T r x ∈ Zs := hvv.2.1
    have hi1 : 1 ≤ (i : ℕ) := hvv.2.2.1
    have hi2 : (i : ℕ) < T.dist r x := hvv.2.2.2
    have hrx := (K.run x hx).1
    have hoA : (i : ℕ) - 1 < Fintype.card V := by have := hM x; omega
    have hoB : T.dist r x - i < Fintype.card V := by have := hM x; omega
    dsimp only
    rw [A_inr T r Zs kk hvv, B_inr T r Zs kk hvv]
    rcases forms T r Zs kk G hTG hT hr d.fst d.snd d.adj with
      ⟨u, t, ha, hu, hut, hp, -⟩ | ⟨x', j, ha, hx', hxp', hj1, hj2, ⟨hp, -, -⟩ | ⟨hp, -⟩⟩ |
      ⟨ha, x', hx', hxp', hp, -, -, -⟩
    · rw [hp, ha]
      show u ∈ desc T r x ↔ _
      rw [(K.run x hx).2 u t hut hu]
      have h1 := lx (c := kk (tpar T r x) x) (b := kk u t) hoA hM0
      have h2 := lx (c := kk u t) (b := kk x (tpar T r x)) hM0 hoB
      constructor <;> intro h <;> omega
    · rw [hp, ha]
      show (x' = x ∧ (i : ℕ) ≤ j) ↔ _
      by_cases hxx : x' = x
      · subst hxx
        have h2 := lx (c := kk (tpar T r x') x') (b := kk x' (tpar T r x')) j.isLt hoB
        constructor
        · rintro ⟨-, h⟩
          constructor <;> omega
        · intro h
          exact ⟨rfl, by omega⟩
      · have hne : x ≠ x' := fun e => hxx e.symm
        have hD := K_disj K hTG hT hr hanc hx hxp hx' hxp' hne
        have h1 := lx (c := kk (tpar T r x) x) (b := kk (tpar T r x') x') hoA j.isLt
        have h2 := lx (c := kk (tpar T r x') x') (b := kk x (tpar T r x)) j.isLt hoB
        have hss : kk (tpar T r x) x ≠ kk (tpar T r x') x' :=
          fun e => hne (kk_ss G T r Zs kk K hTG hT hr hx hx' e)
        refine ⟨fun h => absurd h.1 hxx, fun h => ?_⟩
        exfalso
        omega
    · rw [hp, ha]
      show (x' = x ∧ (i : ℕ) ≤ j) ↔ _
      have ho : T.dist r x' - j < Fintype.card V := by have := hM x'; omega
      by_cases hxx : x' = x
      · subst hxx
        have h1 := lx (c := kk (tpar T r x') x') (b := kk x' (tpar T r x')) hoA ho
        constructor
        · rintro ⟨-, h⟩
          constructor <;> omega
        · intro h
          exact ⟨rfl, by omega⟩
      · have hne : x ≠ x' := fun e => hxx e.symm
        have hD := K_disj K hTG hT hr hanc hx hxp hx' hxp' hne
        have h1 := lx (c := kk (tpar T r x) x) (b := kk x' (tpar T r x')) hoA ho
        have h2 := lx (c := kk x' (tpar T r x')) (b := kk x (tpar T r x)) ho hoB
        have hee : kk x' (tpar T r x') ≠ kk x (tpar T r x) :=
          fun e => hxx (kk_ee G T r Zs kk K hTG hT hr hx' hx e)
        have hrx' := (K.run x' hx').1
        refine ⟨fun h => absurd h.1 hxx, fun h => ?_⟩
        exfalso
        omega
    · rw [hp, ha]
      show False ↔ _
      refine ⟨False.elim, fun h => ?_⟩
      by_cases hxx : x' = x
      · subst hxx
        omega
      · have hne : x ≠ x' := fun e => hxx e.symm
        have hD := K_disj K hTG hT hr hanc hx hxp hx' hxp' hne
        have h1 := lx (c := kk (tpar T r x) x) (b := kk (tpar T r x') x') hoA hM0
        have h2 := lx (c := kk (tpar T r x') x') (b := kk x (tpar T r x)) hM0 hoB
        have hss : kk (tpar T r x) x ≠ kk (tpar T r x') x' :=
          fun e => hne (kk_ss G T r Zs kk K hTG hT hr hx hx' e)
        omega

theorem L3_cg (K : KKH G T r Zs kk) (hT : T.IsTree) (hr : r ∈ Zs)
    (d e : (cG T r Zs G hT hr).Dart) (hd : ¬ (cP T r Zs hT hr).gr.Adj d.fst d.snd)
    (he : ¬ (cP T r Zs hT hr).gr.Adj e.fst e.snd) :
    ¬ (p2v T r kk d.fst.1 d.snd.1 < p2v T r kk e.fst.1 e.snd.1 ∧
      p2v T r kk e.fst.1 e.snd.1 < p2v T r kk d.snd.1 d.fst.1 ∧
      p2v T r kk d.snd.1 d.fst.1 < p2v T r kk e.snd.1 e.fst.1) := by
  have hM0 : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  obtain ⟨u, t, ha, hb, hu, ht, hut, hnT⟩ := chord_form T r Zs G hT hr d.fst d.snd d.adj hd
  obtain ⟨u', t', ha', hb', hu', ht', hut', hnT'⟩ :=
    chord_form T r Zs G hT hr e.fst e.snd e.adj he
  rw [ha, hb, ha', hb']
  show ¬ (Fintype.card V * kk u t < Fintype.card V * kk u' t' ∧
    Fintype.card V * kk u' t' < Fintype.card V * kk t u ∧
    Fintype.card V * kk t u < Fintype.card V * kk t' u')
  have h1 := lex_lt (c := kk u t) (b := kk u' t') hM0 hM0
  have h2 := lex_lt (c := kk u' t') (b := kk t u) hM0 hM0
  have h3 := lex_lt (c := kk t u) (b := kk t' u') hM0 hM0
  intro h
  exact K.chord u t u' t' hut hnT hu ht hut' hnT' hu' ht' ⟨by omega, by omega, by omega⟩

theorem L2_cg (K : KKH G T r Zs kk) (hT : T.IsTree) (hr : r ∈ Zs) :
    ∃ d : (cG T r Zs G hT hr).Dart, d.fst = (cP T r Zs hT hr).root ∧
      p2v T r kk d.fst.1 d.snd.1 = 0 := by
  obtain ⟨x0, hx0, hxp0, hz⟩ := K.zero
  obtain ⟨b0, hb0, hpb0, hf⟩ := root_child T r Zs hx0 hxp0
  refine ⟨⟨(croot T r Zs, b0), ?_⟩, rfl, ?_⟩
  · exact (sup_adj _ _ _ _).2 (Or.inl ((cP T r Zs hT hr).gr_adj.2 (Or.inr ⟨hb0, hpb0⟩)))
  · show p2v T r kk none b0.1 = 0
    rw [p2v_root T r Zs kk b0 hf, hz, Nat.mul_zero]

theorem cert_cG (K : KKH G T r Zs kk) (hTG : T ≤ G) (hT : T.IsTree) (hr : r ∈ Zs)
    (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) : Nonempty (Cert (cG T r Zs G hT hr)) :=
  cert_of_par (cP T r Zs hT hr)
    (le_sup_left : (cP T r Zs hT hr).gr ≤ (cP T r Zs hT hr).gr ⊔ (G.induce Zsᶜ).map (cι T r Zs))
    (fun a b => p2v T r kk a.1 b.1)
    (fun d e h => inj_cg G T r Zs kk K hTG hT hr d e h)
    (fun v u => subv T r v.1 u.1) (S1_cg T r Zs) (fun v u hu h _ => S2_cg T r Zs u v hu h)
    (fun v hv d => L1_cg G T r Zs kk K hTG hT hr hanc v hv d) (L2_cg G T r Zs kk K hT hr)
    (fun d e hd he => L3_cg G T r Zs kk K hT hr d e hd he)

end fin

end PQL21

/-! P8a (s7): the index facts `KKH` from the face cycle `Y` (the `Φ`-cycle of an entry point). -/

namespace PQL21

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus

section kkhex

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem kkh_exists (S : EmbeddingScheme G) (hconn : G.Connected) (h2 : 2 ≤ Fintype.card V)
    (T : SimpleGraph V) (hT : T.IsTree) (hTG : T ≤ G) {r : V} {TD : Finset G.Dart}
    {L : List ((G.Dart × Bool) × (G.Dart × Bool))} {p : V → Bool}
    (I : GInv S r Finset.univ TD L p) (htd : ∀ d, d ∈ TD ↔ T.Adj d.fst d.snd)
    (E : Finset G.Dart) (hE : E ⊆ TDᶜ) (hEs : ∀ d ∈ E, d.symm ∈ E) (Zs : Set V)
    (hEZ : ∀ e ∈ E, e.fst ∈ Zs) (hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs) (hr : r ∈ Zs)
    (hnorb : norb (PhiE S TD E) = 2)
    (hinv : 2 * norb (PhiE S TD E) + ((TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool)).card ≤
        2 * norb (SigP S * AP S))
    {x0 : V} (hx0 : x0 ∉ Zs) (hxp0 : tpar T r x0 ∈ Zs) :
    ∃ kk : V → V → ℕ, KKH G T r Zs kk := by
  classical
  have hadj : ∀ {w : V}, w ∉ Zs → G.Adj (tpar T r w) w := fun hw => (adj_up hTG hT hr hw).symm
  have hTD : ∀ d ∈ TD, d.symm ∈ TD := fun d hd => (htd _).2 ((htd d).1 hd).symm
  obtain ⟨e0, he01, he02⟩ : ∃ d : G.Dart, d.fst = tpar T r x0 ∧ d.snd = x0 :=
    ⟨⟨(tpar T r x0, x0), hadj hx0⟩, rfl, rfl⟩
  obtain ⟨z0, hz0def⟩ : ∃ z, z = yq p false e0 := ⟨_, rfl⟩
  have hz0 : z0.1.fst ∈ Zs := by rw [hz0def]; show e0.fst ∈ Zs; rw [he01]; exact hxp0
  -- the two sheets at a good dart lie in different cycles
  have hsep : ∀ d : G.Dart, (d.fst ∉ Zs ∨ (d.snd ∉ Zs ∧ d.fst = tpar T r d.snd)) →
      ¬ SameCycle (PhiE S TD E) (yq p false d) (yq p true d) := by
    intro d hd
    rcases hd with hd | ⟨hs, hf⟩
    · obtain ⟨x, hx, -, hvx⟩ := top_exists T hT r Zs hr _ d.fst rfl hd
      obtain ⟨ex, hex1, hex2⟩ : ∃ e : G.Dart, e.fst = tpar T r x ∧ e.snd = x :=
        ⟨⟨(tpar T r x, x), hadj hx⟩, rfl, rfl⟩
      have hs2 := run_sheets S hconn h2 T hT I htd E hE hEs Zs hEZ hanc hr hx ex hex1 hex2 false
      have hrun : ∀ q, SameCycle (PhiE S TD E) (yq p q ex) (yq p q d) := by
        intro q
        obtain ⟨-, j, -, -, -, -, hmem⟩ :=
          run_phi S hconn h2 T hT I htd E hE Zs hEZ hanc hr hx ex hex1 hex2 q
        obtain ⟨l, -, -, hl⟩ := (hmem (yq p q d) (sh_yq p q d)).1 hvx
        exact sc_of_nat l hl
      intro hsc
      exact hs2 (((hrun false).trans hsc).trans (hrun true).symm)
    · exact run_sheets S hconn h2 T hT I htd E hE hEs Zs hEZ hanc hr hs d hf rfl false
  have hin : ∀ d : G.Dart, (d.fst ∉ Zs ∨ (d.snd ∉ Zs ∧ d.fst = tpar T r d.snd)) →
      SameCycle (PhiE S TD E) z0 (yq p false d) ∨ SameCycle (PhiE S TD E) z0 (yq p true d) := by
    intro d hd
    by_contra hno
    push_neg at hno
    have := norb_ge_three (PhiE S TD E) (hsep d hd) (fun h => hno.1 h.symm)
      (fun h => hno.2 h.symm)
    omega
  obtain ⟨yY, hyY⟩ : ∃ f : G.Dart → G.Dart × Bool, ∀ d, f d =
      if SameCycle (PhiE S TD E) z0 (yq p false d) then yq p false d else yq p true d :=
    ⟨_, fun _ => rfl⟩
  have hyY_fst : ∀ d, (yY d).1 = d := by
    intro d
    rw [hyY]
    split_ifs <;> rfl
  have hyY_sc : ∀ d : G.Dart, (d.fst ∉ Zs ∨ (d.snd ∉ Zs ∧ d.fst = tpar T r d.snd)) →
      SameCycle (PhiE S TD E) z0 (yY d) := by
    intro d hd
    rw [hyY]
    by_cases h : SameCycle (PhiE S TD E) z0 (yq p false d)
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact (hin d hd).resolve_left h
  have hyY_uniq : ∀ d : G.Dart, (d.fst ∉ Zs ∨ (d.snd ∉ Zs ∧ d.fst = tpar T r d.snd)) →
      ∀ y : G.Dart × Bool, y.1 = d → SameCycle (PhiE S TD E) z0 y → y = yY d := by
    intro d hd y hy hsc
    have hy' : yq p (sh p y) d = y := by
      rw [← hy]
      exact yq_of_sh rfl
    rw [← hy', hyY]
    by_cases h : SameCycle (PhiE S TD E) z0 (yq p false d)
    · rw [if_pos h]
      cases hb : sh p y
      · rfl
      · exfalso
        rw [hb] at hy'
        rw [← hy'] at hsc
        exact hsep d hd (h.symm.trans hsc)
    · rw [if_neg h]
      cases hb : sh p y
      · exfalso
        rw [hb] at hy'
        rw [← hy'] at hsc
        exact h hsc
      · rfl
  obtain ⟨idx, hidx⟩ : ∃ f : G.Dart × Bool → ℕ, ∀ y, SameCycle (PhiE S TD E) z0 y →
      f y < per (PhiE S TD E) z0 ∧ (PhiE S TD E ^ f y) z0 = y := by
    refine ⟨fun y => if h : SameCycle (PhiE S TD E) z0 y then
      Classical.choose (exists_pos _ h) else 0, ?_⟩
    intro y h
    simp only [dif_pos h]
    exact Classical.choose_spec (exists_pos _ h)
  have hidx_eq : ∀ y i, i < per (PhiE S TD E) z0 → (PhiE S TD E ^ i) z0 = y → idx y = i := by
    intro y i hi hy
    have hsc : SameCycle (PhiE S TD E) z0 y := sc_of_nat i hy
    exact pow_inj_lt _ _ (hidx y hsc).1 hi ((hidx y hsc).2.trans hy.symm)
  obtain ⟨kk, hkk⟩ : ∃ f : V → V → ℕ, ∀ u t (h : G.Adj u t), f u t = idx (yY ⟨(u, t), h⟩) :=
    ⟨fun u t => if h : G.Adj u t then idx (yY ⟨(u, t), h⟩) else 0,
      fun u t h => by simp only [dif_pos h]⟩
  have hkk' : ∀ d : G.Dart, kk d.fst d.snd = idx (yY d) := fun d => hkk d.fst d.snd d.adj
  refine ⟨kk, ?_, ?_, ?_, ?_⟩
  · -- inj
    intro u t u' t' h h' hc hc' heq
    rw [hkk u t h, hkk u' t' h'] at heq
    have s1 := hidx _ (hyY_sc ⟨(u, t), h⟩ hc)
    have s2 := hidx _ (hyY_sc ⟨(u', t'), h'⟩ hc')
    rw [heq] at s1
    have hyy := congrArg Prod.fst (s1.2.symm.trans s2.2)
    rw [hyY_fst, hyY_fst] at hyy
    have hp := congrArg SimpleGraph.Dart.toProd hyy
    simp only [Prod.mk.injEq] at hp
    exact hp
  · -- run
    intro w hw
    obtain ⟨dw, hdw1, hdw2⟩ : ∃ d : G.Dart, d.fst = tpar T r w ∧ d.snd = w :=
      ⟨⟨(tpar T r w, w), hadj hw⟩, rfl, rfl⟩
    have hgw : dw.fst ∉ Zs ∨ (dw.snd ∉ Zs ∧ dw.fst = tpar T r dw.snd) :=
      Or.inr ⟨by rw [hdw2]; exact hw, by rw [hdw1, hdw2]⟩
    obtain ⟨q, hq⟩ : ∃ q, sh p (yY dw) = q := ⟨_, rfl⟩
    have hyq : yq p q dw = yY dw := by
      have := yq_of_sh hq
      rwa [hyY_fst] at this
    obtain ⟨s, j, hj, hsj, hs, hsj', hl, hmem⟩ :=
      run_Y S hconn h2 T hT I htd E hE Zs hEZ hanc hr z0 hz0 hw dw hdw1 hdw2 q
        (by rw [hyq]; exact hyY_sc dw hgw)
    have hks : kk (tpar T r w) w = s := by
      have := hkk' dw
      rw [hdw1, hdw2] at this
      rw [this]
      exact hidx_eq _ s (by omega) (hs.trans hyq)
    have hke : kk w (tpar T r w) = s + j := by
      have := hkk' dw.symm
      rw [show dw.symm.fst = w from hdw2, show dw.symm.snd = tpar T r w from hdw1] at this
      rw [this]
      have hu := hyY_uniq dw.symm (Or.inl (show dw.symm.fst ∉ Zs by rw [show dw.symm.fst = w from hdw2]; exact hw))
        (yq p q dw.symm) rfl (sc_of_nat (s + j) hsj')
      exact hidx_eq _ (s + j) hsj (hsj'.trans hu)
    refine ⟨by omega, ?_⟩
    intro u t hut hu
    rw [hks, hke, hkk u t hut]
    constructor
    · intro hud
      obtain ⟨l, hl0, hlj, hleq⟩ := (hmem (yq p q ⟨(u, t), hut⟩) (sh_yq p q _)).1 hud
      have hu' := hyY_uniq ⟨(u, t), hut⟩ (Or.inl hu) (yq p q ⟨(u, t), hut⟩) rfl
        (sc_of_nat _ hleq)
      have := hidx_eq _ (s + l) (by omega) (hleq.trans hu')
      omega
    · rintro ⟨h1, h2⟩
      have hi := hidx _ (hyY_sc ⟨(u, t), hut⟩ (Or.inl hu))
      have he : (PhiE S TD E ^ (s + (idx (yY ⟨(u, t), hut⟩) - s))) z0 = yY ⟨(u, t), hut⟩ := by
        rw [Nat.add_sub_cancel' h1.le]
        exact hi.2
      have hv := (hl (idx (yY ⟨(u, t), hut⟩) - s) (by omega) (by omega)).2
      rw [he, hyY_fst] at hv
      exact hv
  · -- chord
    intro u t u' t' hut hnT hu ht hut' hnT' hu' ht' ⟨h1, h2, h3⟩
    rw [hkk u t hut, hkk u' t' hut'] at h1
    rw [hkk u' t' hut', hkk t u hut.symm] at h2
    rw [hkk t u hut.symm, hkk t' u' hut'.symm] at h3
    have hcl : ∀ x ∈ (TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool),
        apFun S x ∈ (TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool) := by
      rintro ⟨d, b⟩ hx
      simp only [apFun, Finset.mem_product, Finset.mem_sdiff, Finset.mem_compl,
        Finset.mem_univ, and_true] at hx ⊢
      refine ⟨fun h => hx.1 ?_, fun h => hx.2 ?_⟩
      · have := hTD _ h
        rwa [SimpleGraph.Dart.symm_symm] at this
      · have := hEs _ h
        rwa [SimpleGraph.Dart.symm_symm] at this
    have hfp : ∀ x ∈ (TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool), apFun S x ≠ x :=
      fun x _ h => (SimpleGraph.Dart.symm_ne x.1) (congrArg Prod.fst h)
    have hmax := cstar_max S TD E hTD hE hEs hinv
    have hmemC : ∀ d : G.Dart, ¬ T.Adj d.fst d.snd → d.fst ∉ Zs →
        yY d ∈ (TDᶜ \ E) ×ˢ (Finset.univ : Finset Bool) := by
      intro d hnT0 hu0
      rw [Finset.mem_product, Finset.mem_sdiff, Finset.mem_compl, hyY_fst]
      exact ⟨⟨fun h => hnT0 ((htd d).1 h), fun h => hu0 (hEZ d h)⟩, Finset.mem_univ _⟩
    have hpart : ∀ (a b : V) (hab : G.Adj a b), ¬ T.Adj a b → a ∉ Zs → b ∉ Zs →
        apFun S (yY ⟨(a, b), hab⟩) = yY ⟨(b, a), hab.symm⟩ := by
      intro a b hab hnT0 ha hb
      have hsc := (PF_max_head (apFun S) (apFun_invol S) _ hcl hfp (PhiE S TD E) hmax
        (hmemC ⟨(a, b), hab⟩ hnT0 ha)).1
      exact hyY_uniq ⟨(b, a), hab.symm⟩ (Or.inl hb) _
        (by show (yY ⟨(a, b), hab⟩).1.symm = _; rw [hyY_fst]; rfl)
        ((hyY_sc ⟨(a, b), hab⟩ (Or.inl ha)).trans hsc)
    have i1 := hidx _ (hyY_sc ⟨(u, t), hut⟩ (Or.inl hu))
    have i2 := hidx _ (hyY_sc ⟨(u', t'), hut'⟩ (Or.inl hu'))
    have i4 := hidx _ (hyY_sc ⟨(t', u'), hut'.symm⟩ (Or.inl ht'))
    have i3 := hidx _ (hyY_sc ⟨(t, u), hut.symm⟩ (Or.inl ht))
    refine no_cross (apFun S) (apFun_invol S) _ hcl hfp (PhiE S TD E) hmax z0 h1 h2 h3 i4.1
      ?_ ?_ ?_ ?_
    · rw [i1.2]
      exact hmemC _ hnT hu
    · rw [i1.2, i3.2]
      exact hpart u t hut hnT hu ht
    · rw [i2.2]
      exact hmemC _ hnT' hu'
    · rw [i2.2, i4.2]
      exact hpart u' t' hut' hnT' hu' ht'
  · -- zero
    refine ⟨x0, hx0, hxp0, ?_⟩
    have := hkk' e0
    rw [he01, he02] at this
    rw [this]
    have hsc0 : SameCycle (PhiE S TD E) z0 (yq p false e0) := by
      subst hz0def
      exact SameCycle.refl _ _
    have hy0 : yY e0 = z0 := by
      rw [hyY, if_pos hsc0, hz0def]
    rw [hy0]
    exact hidx_eq _ 0 (per_spec _ _).1 (by simp)

end kkhex

end PQL21

/-! s7: assembly of lemma_21 (C2 cut construction + C1 for g = 0). -/

namespace PQL21

open PlanarQueue.Genus

/-- planarity pulls back along injective adjacency-preserving maps -/
theorem planar_comap {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ a b, G.Adj a b → H.Adj (f a) (f b))
    (hH : RobertsonSeymour1986.GM5.IsPlanar H) : RobertsonSeymour1986.GM5.IsPlanar G := by
  obtain ⟨D⟩ := hH
  refine ⟨{
    vertex := D.vertex ∘ f
    vertex_injective := D.vertex_injective.comp hf
    arc := fun {a b} h => D.arc (hadj a b h)
    arc_injective := fun {a b} h => D.arc_injective (hadj a b h)
    arc_reverse := fun {a b} h => D.arc_reverse (hadj a b h)
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }⟩
  · intro a b h t x hx
    rcases D.arc_avoids_vertices (hadj a b h) t (f x) hx with e | e
    · exact Or.inl (hf e)
    · exact Or.inr (hf e)
  · intro a b c d h k s t hst
    rcases D.arcs_meet_only_at_endpoints (hadj a b h) (hadj c d k) s t hst with
      ⟨e1, e2⟩ | ⟨e1, e2⟩ | e
    · exact Or.inl ⟨hf e1, hf e2⟩
    · exact Or.inr (Or.inl ⟨hf e1, hf e2⟩)
    · exact Or.inr (Or.inr e)

/-- a graph on at most one vertex is planar -/
theorem planar_of_allEq {W : Type} (H : SimpleGraph W) (hs : ∀ a b : W, a = b) :
    RobertsonSeymour1986.GM5.IsPlanar H := by
  have hno : ∀ {v w : W}, ¬ H.Adj v w := fun h => H.ne_of_adj h (hs _ _)
  exact ⟨{
    vertex := fun _ => 0
    vertex_injective := fun a b _ => hs a b
    arc := fun h => (hno h).elim
    arc_injective := fun h => (hno h).elim
    arc_reverse := fun h => (hno h).elim
    arc_avoids_vertices := fun h => (hno h).elim
    arcs_meet_only_at_endpoints := fun h => (hno h).elim }⟩

theorem lemma21_main (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hconn : G.Connected) (g : ℕ) (hg : EulerGenusLE G g)
    (T : SimpleGraph V) (r : V) (hT : IsBFSTree G T r) :
    ∃ Z : G.Subgraph,
      (Z.verts = ∅ ∨ Z.Connected) ∧
      (∀ i : ℕ, Nat.card {v : V // v ∈ Z.verts ∧ G.dist r v = i} ≤ 2 * g) ∧
      RobertsonSeymour1986.GM5.IsPlanar (G.induce Z.vertsᶜ) ∧
      ∃ (W : Type) (_ : Finite W) (Gp Tp : SimpleGraph W) (rp : W) (ι : ↥(Z.vertsᶜ) ↪ W),
        Gp.Connected ∧ RobertsonSeymour1986.GM5.IsPlanar Gp ∧
        (∀ a b : ↥(Z.vertsᶜ), G.Adj a b → Gp.Adj (ι a) (ι b)) ∧
        IsBFSTree Gp Tp rp ∧
        (∀ a : ↥(Z.vertsᶜ), Gp.dist rp (ι a) = G.dist r a) ∧
        ∀ l : List W, IsVertical Tp rp l →
          {v : V | ∃ h : v ∈ Z.vertsᶜ, ι ⟨v, h⟩ ∈ l} = ∅ ∨
            IsVerticalSet T r {v : V | ∃ h : v ∈ Z.vertsᶜ, ι ⟨v, h⟩ ∈ l} := by
  classical
  by_cases hsmall : g = 0 ∨ Fintype.card V < 2
  · -- Z = ∅, G⁺ = G
    have hpl : RobertsonSeymour1986.GM5.IsPlanar G := by
      rcases hsmall with h0 | h1
      · subst h0
        exact genus0_planar_conn V G hconn hg
      · exact planar_of_allEq G (fun a b => Fintype.card_le_one_iff.1 (by omega) a b)
    refine ⟨⊥, Or.inl rfl, fun i => ?_, ?_, V, inferInstance, G, T, r,
      Function.Embedding.subtype _, hconn, hpl, fun a b h => h, hT, fun a => rfl,
      fun l hl => Or.inr ⟨l, hl, ?_⟩⟩
    · haveI : IsEmpty {v : V // v ∈ (⊥ : G.Subgraph).verts ∧ G.dist r v = i} :=
        ⟨fun x => by simpa using x.2.1⟩
      rw [Nat.card_of_isEmpty]
      omega
    · exact planar_comap _ G Subtype.val Subtype.val_injective (fun a b h => h) hpl
    · ext v
      constructor
      · intro hv
        exact ⟨by simp, hv⟩
      · rintro ⟨_, hv⟩
        exact hv
  push Not at hsmall
  obtain ⟨hg0, h2⟩ := hsmall
  obtain ⟨S, hS⟩ := hg
  have hTG : T ≤ G := hT.1
  have hTt : T.IsTree := hT.2.1
  obtain ⟨TD, L, p, I, hsub⟩ := ginv_along S T hTG hTt.connected r
  have htd := td_eq_tree S T hTG hTt I hsub
  have hTD : ∀ d ∈ TD, d.symm ∈ TD := fun d hd => (htd _).2 ((htd d).1 hd).symm
  obtain ⟨E, hE, hEs, hinv, hstop⟩ := deletion_exists S TD hTD
  have hnorb := one_face S hconn h2 T hTt I htd E hE hEs hstop
  have hgb := genus_bound S hconn h2 I E hE hEs hnorb
  have hEc : E.card ≤ 2 * g := by omega
  obtain ⟨Ends, hEnds1, hEnds2, hEnds3⟩ : ∃ Ends : Finset V, Ends.card ≤ 2 * g ∧
      (∃ e, e ∈ Ends) ∧ ∀ e ∈ E, e.fst ∈ Ends := by
    by_cases hE0 : E = ∅
    · refine ⟨{r}, by rw [Finset.card_singleton]; omega, ⟨r, Finset.mem_singleton_self r⟩, ?_⟩
      intro e he
      rw [hE0] at he
      simp at he
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hE0
      exact ⟨E.image (fun d => d.fst), Finset.card_image_le.trans hEc,
        ⟨e.fst, Finset.mem_image_of_mem _ he⟩, fun e he => Finset.mem_image_of_mem _ he⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Set V, Zs = ancS T r (↑Ends : Set V) := ⟨_, rfl⟩
  have hr : r ∈ Zs := by
    obtain ⟨e, he⟩ := hEnds2
    rw [hZs]
    exact root_mem_ancS T r (Finset.mem_coe.2 he)
  have hanc : ∀ v ∈ Zs, tpar T r v ∈ Zs := by
    intro v hv
    by_cases hvr : v = r
    · subst hvr
      rw [tpar_root]
      exact hv
    · rw [hZs] at hv ⊢
      exact ancS_closed T r hTt _ hv hvr
  have hEZ : ∀ e ∈ E, e.fst ∈ Zs := by
    intro e he
    rw [hZs]
    exact ⟨e.fst, Finset.mem_coe.2 (hEnds3 e he), by simp⟩
  have hlayer : ∀ i : ℕ,
      Nat.card {v : V // v ∈ (zsub T Zs G hTG).verts ∧ G.dist r v = i} ≤ 2 * g := by
    intro i
    have hlb := layer_bound T hTt r Ends (Finset.univ.filter (fun v => v ∈ Zs))
      (fun v hv => by
        have := (Finset.mem_filter.1 hv).2
        rw [hZs] at this
        exact this) i
    rw [Finset.filter_filter] at hlb
    have hc : Nat.card {v : V // v ∈ (zsub T Zs G hTG).verts ∧ G.dist r v = i} =
        (Finset.univ.filter (fun v => v ∈ Zs ∧ T.dist r v = i)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hT.2.2 v]
      rfl
    omega
  obtain ⟨hc, hadj, hbfs, hdist, hvert⟩ := cut_pack T r Zs G hconn hT hr
  have hplan : RobertsonSeymour1986.GM5.IsPlanar (cG T r Zs G hT.2.1 hr) := by
    by_cases htop : ∃ x, x ∉ Zs ∧ tpar T r x ∈ Zs
    · obtain ⟨x0, hx0, hxp0⟩ := htop
      obtain ⟨kk, K⟩ := kkh_exists S hconn h2 T hTt hTG I htd E hE hEs Zs hEZ hanc hr hnorb
        hinv hx0 hxp0
      obtain ⟨C⟩ := cert_cG G T r Zs kk K hTG hT.2.1 hr hanc
      have h2W : 2 ≤ Fintype.card (CW T r Zs) := by
        refine Fintype.one_lt_card_iff.2 ⟨croot T r Zs, ⟨some (Sum.inl x0), hx0⟩, fun h => ?_⟩
        have := congrArg Subtype.val h
        simp [croot] at this
      exact planar_of_subG (fun v => ((Fintype.equivFin _ v : Fin _) : ℕ))
        (fun a b hab => (Fintype.equivFin _).injective (Fin.ext hab))
        (planar_subG C (exists_dart_at hc h2W))
    · have hall : ∀ v, v ∈ Zs := by
        intro v
        by_contra hv
        obtain ⟨x, hx, hxp, -⟩ := top_exists T hTt r Zs hr _ v rfl hv
        exact htop ⟨x, hx, hxp⟩
      have hroot : ∀ a : CW T r Zs, a = croot T r Zs := by
        rintro ⟨_ | v | ⟨x, j⟩, ha⟩
        · rfl
        · exact absurd (hall v) ha
        · exact absurd (hall x) ha.1
      exact planar_of_allEq _ (fun a b => (hroot a).trans (hroot b).symm)
  refine ⟨zsub T Zs G hTG, Or.inr (zsub_connected T r Zs G hTG hTt hr (fun v hv _ => hanc v hv)),
    hlayer, ?_, CW T r Zs, inferInstance, cG T r Zs G hT.2.1 hr, (cP T r Zs hT.2.1 hr).gr,
    croot T r Zs, cι T r Zs, hc, hplan, hadj, hbfs, hdist, hvert⟩
  exact planar_comap _ _ (cι T r Zs) (cι T r Zs).injective (fun a b h => hadj a b h) hplan

end PQL21

open PlanarQueue.Genus in
theorem solution (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (g : ℕ) (hg : EulerGenusLE G g)
    (T : SimpleGraph V) (r : V) (hT : IsBFSTree G T r) :
    ∃ Z : G.Subgraph,
      (Z.verts = ∅ ∨ Z.Connected) ∧
      (∀ i : ℕ, Nat.card {v : V // v ∈ Z.verts ∧ G.dist r v = i} ≤ 2 * g) ∧
      RobertsonSeymour1986.GM5.IsPlanar (G.induce Z.vertsᶜ) ∧
      ∃ (W : Type) (_ : Finite W) (Gp Tp : SimpleGraph W) (rp : W) (ι : ↥(Z.vertsᶜ) ↪ W),
        Gp.Connected ∧ RobertsonSeymour1986.GM5.IsPlanar Gp ∧
        (∀ a b : ↥(Z.vertsᶜ), G.Adj a b → Gp.Adj (ι a) (ι b)) ∧
        IsBFSTree Gp Tp rp ∧
        (∀ a : ↥(Z.vertsᶜ), Gp.dist rp (ι a) = G.dist r a) ∧
        ∀ l : List W, IsVertical Tp rp l →
          {v : V | ∃ h : v ∈ Z.vertsᶜ, ι ⟨v, h⟩ ∈ l} = ∅ ∨
            IsVerticalSet T r {v : V | ∃ h : v ∈ Z.vertsᶜ, ι ⟨v, h⟩ ∈ l} := by
  exact PQL21.lemma21_main V G hconn g hg T r hT
