-- Prove2me | solution 1 for PlanarQueue.Planar.theorem_15_core_grid_model
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T16:05:13.67525+00:00
-- url     : https://prove2.me/submissions/ea454d6c-cefe-412d-878c-1732cb318e9e

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

set_option autoImplicit false
set_option linter.all false
set_option linter.deprecated false

/-! L3: an even edge function of the Z^2 grid supported in a box is a sum of unit squares. -/

namespace PF12

open Finset

/-- horizontal grid edge from `p` -/
def gH (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1 + 1, p.2))
/-- vertical grid edge from `p` -/
def gV (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1, p.2 + 1))

lemma gH_inj {p q : ℤ × ℤ} : gH p = gH q ↔ p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [gH, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro (h | h) <;> omega
  · rintro ⟨rfl, rfl⟩; left; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

lemma gV_inj {p q : ℤ × ℤ} : gV p = gV q ↔ p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [gV, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro (h | h) <;> omega
  · rintro ⟨rfl, rfl⟩; left; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

lemma gH_ne_gV (p q : ℤ × ℤ) : gH p ≠ gV q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [gH, gV, ne_eq, Sym2.eq_iff, Prod.mk.injEq]
  omega

/-- mod-2 degree of a grid edge function at a point -/
def gdeg (z : Sym2 (ℤ × ℤ) → ZMod 2) (p : ℤ × ℤ) : ZMod 2 :=
  z (gH p) + z (gH (p.1 - 1, p.2)) + z (gV p) + z (gV (p.1, p.2 - 1))

/-- the boundary of the unit square with lower-left corner `q` -/
def sq (q : ℤ × ℤ) : Sym2 (ℤ × ℤ) → ZMod 2 := fun e =>
  if e = gH q ∨ e = gV q ∨ e = gH (q.1, q.2 + 1) ∨ e = gV (q.1 + 1, q.2) then 1 else 0

/-- the box `[-M, M]^2` -/
def InBox (M : ℤ) (p : ℤ × ℤ) : Prop := -M ≤ p.1 ∧ p.1 ≤ M ∧ -M ≤ p.2 ∧ p.2 ≤ M

/-- grid edge functions supported on edges of the box -/
def BoxSupp (M : ℤ) (z : Sym2 (ℤ × ℤ) → ZMod 2) : Prop :=
  ∀ e, z e ≠ 0 → ∃ p : ℤ × ℤ, (e = gH p ∧ InBox M p ∧ InBox M (p.1 + 1, p.2)) ∨
    (e = gV p ∧ InBox M p ∧ InBox M (p.1, p.2 + 1))

lemma zH_zero {M : ℤ} {z : Sym2 (ℤ × ℤ) → ZMod 2} (hz : BoxSupp M z) (p : ℤ × ℤ)
    (h : ¬ (InBox M p ∧ InBox M (p.1 + 1, p.2))) : z (gH p) = 0 := by
  by_contra hne
  obtain ⟨q, hq | hq⟩ := hz _ hne
  · rw [gH_inj] at hq; obtain ⟨rfl, h1, h2⟩ := hq; exact h ⟨h1, h2⟩
  · exact gH_ne_gV _ _ hq.1

lemma zV_zero {M : ℤ} {z : Sym2 (ℤ × ℤ) → ZMod 2} (hz : BoxSupp M z) (p : ℤ × ℤ)
    (h : ¬ (InBox M p ∧ InBox M (p.1, p.2 + 1))) : z (gV p) = 0 := by
  by_contra hne
  obtain ⟨q, hq | hq⟩ := hz _ hne
  · exact gH_ne_gV _ _ hq.1.symm
  · rw [gV_inj] at hq; obtain ⟨rfl, h1, h2⟩ := hq; exact h ⟨h1, h2⟩

section L3
variable (M : ℤ) (z : Sym2 (ℤ × ℤ) → ZMod 2)

/-- square coefficients: prefix sums of vertical edges along the row -/
noncomputable def coef (q : ℤ × ℤ) : ZMod 2 :=
  ∑ i ∈ Icc (-M) M, if i ≤ q.1 then z (gV (i, q.2)) else 0

variable {M z}

lemma coef_step (hz : BoxSupp M z) (i j : ℤ) :
    coef M z (i, j) = coef M z (i - 1, j) + z (gV (i, j)) := by
  have h : ∀ i' : ℤ, (if i' ≤ i then z (gV (i', j)) else 0) =
      (if i' ≤ i - 1 then z (gV (i', j)) else 0) + (if i' = i then z (gV (i', j)) else 0) := by
    intro i'
    by_cases h1 : i' ≤ i - 1
    · have h2 : i' ≤ i := by omega
      have h3 : i' ≠ i := by omega
      simp [h1, h2, h3]
    · by_cases h3 : i' = i
      · subst h3; simp [h1]
      · have h2 : ¬ i' ≤ i := by omega
        simp [h1, h2, h3]
  simp only [coef]
  rw [Finset.sum_congr rfl (fun i' _ => h i'), Finset.sum_add_distrib, Finset.sum_ite_eq']
  by_cases hi : i ∈ Icc (-M) M
  · rw [if_pos hi]
  · rw [if_neg hi]
    rw [zV_zero hz (i, j) (fun h => hi (Finset.mem_Icc.mpr ⟨h.1.1, h.1.2.1⟩))]

lemma coef_low (i j : ℤ) (hi : i < -M) : coef M z (i, j) = 0 := by
  simp only [coef]
  refine Finset.sum_eq_zero fun i' hi' => ?_
  rw [Finset.mem_Icc] at hi'
  have : ¬ i' ≤ i := by omega
  simp [this]

lemma coef_row (hz : BoxSupp M z) (i j : ℤ) (hj : j < -M ∨ M - 1 < j) : coef M z (i, j) = 0 := by
  simp only [coef]
  refine Finset.sum_eq_zero fun i' _ => ?_
  rw [zV_zero hz (i', j) (by intro h; simp only [InBox] at h; omega)]
  simp

lemma coef_horiz (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) (i j : ℤ) :
    coef M z (i, j) + coef M z (i, j - 1) = z (gH (i, j)) := by
  have base : ∀ i : ℤ, i < -M → coef M z (i, j) + coef M z (i, j - 1) = z (gH (i, j)) := by
    intro i hi
    rw [coef_low i j hi, coef_low i (j - 1) hi, zH_zero hz (i, j) (by
      intro h; simp only [InBox] at h; omega)]
    simp
  have step : ∀ k : ℕ, coef M z (-M - 1 + k, j) + coef M z (-M - 1 + k, j - 1) =
      z (gH (-M - 1 + k, j)) := by
    intro k
    induction k with
    | zero => simpa using base (-M - 1) (by omega)
    | succ k ih =>
      have e1 := coef_step hz (-M - 1 + (k + 1 : ℕ)) j
      have e2 := coef_step hz (-M - 1 + (k + 1 : ℕ)) (j - 1)
      have hd := he (-M - 1 + (k + 1 : ℕ), j)
      simp only [gdeg] at hd
      have r1 : (-M - 1 + ((k + 1 : ℕ) : ℤ) - 1) = -M - 1 + (k : ℤ) := by push_cast; ring
      rw [r1] at e1 e2 hd
      rw [e1, e2]
      have hd' : z (gV (-M - 1 + ((k + 1 : ℕ) : ℤ), j - 1)) =
          z (gV ((-M - 1 + ((k + 1 : ℕ) : ℤ), j).1, (-M - 1 + ((k + 1 : ℕ) : ℤ), j).2 - 1)) := rfl
      rw [hd']
      have key : ∀ a b c d e f : ZMod 2, a + b = c → f + c + d + e = 0 →
          a + d + (b + e) = f := by decide
      exact key _ _ _ _ _ _ ih hd
  by_cases hi : i < -M
  · exact base i hi
  · have := step (i + M + 1).toNat
    have h' : (-M - 1 + ((i + M + 1).toNat : ℤ)) = i := by omega
    rw [h'] at this
    exact this

lemma coef_high (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) (i j : ℤ) (hi : M ≤ i) :
    coef M z (i, j) = 0 := by
  have hM : coef M z (i, j) = coef M z (M, j) := by
    simp only [coef]
    refine Finset.sum_congr rfl fun i' hi' => ?_
    rw [Finset.mem_Icc] at hi'
    have h1 : i' ≤ i := by omega
    have h2 : i' ≤ M := hi'.2
    simp [h1, h2]
  rw [hM]
  -- induction on j
  have hstep : ∀ j : ℤ, coef M z (M, j) = coef M z (M, j - 1) := by
    intro j
    have h := coef_horiz hz he M j
    rw [zH_zero hz (M, j) (by intro h; simp only [InBox] at h; omega)] at h
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact key _ _ h
  have hk : ∀ k : ℕ, coef M z (M, -M - 1 + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using coef_row hz M (-M - 1) (Or.inl (by omega))
    | succ k ih =>
      rw [hstep]
      have : (-M - 1 + ((k + 1 : ℕ) : ℤ) - 1) = -M - 1 + (k : ℤ) := by push_cast; ring
      rw [this]; exact ih
  by_cases hj : j < -M
  · exact coef_row hz M j (Or.inl hj)
  · have := hk (j + M + 1).toNat
    have h' : (-M - 1 + ((j + M + 1).toNat : ℤ)) = j := by omega
    rw [h'] at this
    exact this

/-- the box of squares -/
noncomputable def sqBox (M : ℤ) : Finset (ℤ × ℤ) := Icc (-M) (M - 1) ×ˢ Icc (-M) (M - 1)

lemma coef_out (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) (q : ℤ × ℤ) (hq : q ∉ sqBox M) :
    coef M z q = 0 := by
  obtain ⟨i, j⟩ := q
  simp only [sqBox, Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hq
  rcases hq with (h | h) | (h | h)
  · exact coef_low i j h
  · exact coef_high hz he i j (by omega)
  · exact coef_row hz i j (Or.inl h)
  · exact coef_row hz i j (Or.inr h)

theorem even_mem_span_squares (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) :
    z = ∑ q ∈ sqBox M, coef M z q • sq q := by
  funext e
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hV : ∃ p, e = gV p
  · obtain ⟨⟨i, j⟩, rfl⟩ := hV
    rw [Finset.sum_eq_add (i, j) (i - 1, j)]
    · have h1 : sq (i, j) (gV (i, j)) = 1 := by simp [sq]
      have h2 : sq (i - 1, j) (gV (i, j)) = 1 := by
        simp only [sq]; rw [if_pos]; right; right; right; congr 1; ext <;> simp
      rw [h1, h2, mul_one, mul_one, coef_step hz i j]
      have key : ∀ a b : ZMod 2, b = a + b + a := by decide
      exact key _ _
    · intro h; simp only [Prod.mk.injEq] at h; omega
    · intro c _ hc
      obtain ⟨c1, c2⟩ := c
      have : sq (c1, c2) (gV (i, j)) = 0 := by
        simp only [sq]
        rw [if_neg]
        simp only [not_or]
        refine ⟨(gH_ne_gV _ _).symm, ?_, (gH_ne_gV _ _).symm, ?_⟩
        · rw [gV_inj]; exact fun h => hc.1 h.symm
        · rw [gV_inj]; intro h; apply hc.2; simp only [Prod.mk.injEq] at h ⊢; omega
      rw [this, mul_zero]
    · intro h; rw [coef_out hz he _ h, zero_mul]
    · intro h; rw [coef_out hz he _ h, zero_mul]
  by_cases hH : ∃ p, e = gH p
  · obtain ⟨⟨i, j⟩, rfl⟩ := hH
    rw [Finset.sum_eq_add (i, j) (i, j - 1)]
    · have h1 : sq (i, j) (gH (i, j)) = 1 := by simp [sq]
      have h2 : sq (i, j - 1) (gH (i, j)) = 1 := by
        simp only [sq]; rw [if_pos]; right; right; left; congr 1; ext <;> simp
      rw [h1, h2, mul_one, mul_one, coef_horiz hz he i j]
    · intro h; simp only [Prod.mk.injEq] at h; omega
    · intro c _ hc
      obtain ⟨c1, c2⟩ := c
      have : sq (c1, c2) (gH (i, j)) = 0 := by
        simp only [sq]
        rw [if_neg]
        simp only [not_or]
        refine ⟨?_, gH_ne_gV _ _, ?_, gH_ne_gV _ _⟩
        · rw [gH_inj]; exact fun h => hc.1 h.symm
        · rw [gH_inj]; intro h; apply hc.2; simp only [Prod.mk.injEq] at h ⊢; omega
      rw [this, mul_zero]
    · intro h; rw [coef_out hz he _ h, zero_mul]
    · intro h; rw [coef_out hz he _ h, zero_mul]
  · push Not at hV hH
    have hz0 : z e = 0 := by
      by_contra hne
      obtain ⟨p, hp | hp⟩ := hz e hne
      · exact hH p hp.1
      · exact hV p hp.1
    rw [hz0]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    have : sq q e = 0 := by
      simp only [sq]
      rw [if_neg]
      simp only [not_or]
      exact ⟨hH _, hV _, hH _, hV _⟩
    rw [this, mul_zero]

end L3

end PF12

namespace PF12

/-- grid adjacency -/
def gAdj (a b : ℤ × ℤ) : Prop :=
  b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1)

lemma gV_ne_gH (p q : ℤ × ℤ) : gV p ≠ gH q := fun h => gH_ne_gV q p h.symm

/-- one step inside a blob -/
def BlobRel (B : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) : Prop := a ∈ B ∧ b ∈ B ∧ gAdj a b

lemma blobRel_symm (B : Finset (ℤ × ℤ)) {a b : ℤ × ℤ} (h : BlobRel B a b) : BlobRel B b a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, h1, ?_⟩
  unfold gAdj at h3 ⊢
  tauto

lemma reach_symm {B : Finset (ℤ × ℤ)} {p q : ℤ × ℤ}
    (h : Relation.ReflTransGen (BlobRel B) p q) : Relation.ReflTransGen (BlobRel B) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (blobRel_symm B hbc) ih

end PF12

namespace PQL5

/-- a PF12 grid minor model of `G` -/
def HasGridModel {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
    (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (PF12.BlobRel (B v)) p q) ∧
    (∀ v, (B v).Nonempty) ∧ (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, PF12.gAdj p q)

end PQL5

/-! 8100c3d9 D2: the triangulated grid Δ, a mod-2 Jordan lemma (all left triangles of a simple
closed Δ-walk lie on one side of any boundary chain), and connectivity of the triangle graph. -/

namespace PQT

abbrev Cell := ℤ × ℤ

/-- the six Δ-directions in counter-clockwise order -/
def dir : Fin 6 → ℤ × ℤ
  | 0 => (1, 0) | 1 => (0, 1) | 2 => (-1, 1) | 3 => (-1, 0) | 4 => (0, -1) | 5 => (1, -1)

/-- triangles: `(i, j, false)` = `{(i,j),(i+1,j),(i,j+1)}`, `(i, j, true)` = `{(i+1,j),(i+1,j+1),(i,j+1)}` -/
abbrev Tri := ℤ × ℤ × Bool

/-- the triangle `{c, c + dir k, c + dir (k+1)}` -/
def triAt (c : Cell) : Fin 6 → Tri
  | 0 => (c.1, c.2, false)
  | 1 => (c.1 - 1, c.2, true)
  | 2 => (c.1 - 1, c.2, false)
  | 3 => (c.1 - 1, c.2 - 1, true)
  | 4 => (c.1, c.2 - 1, false)
  | 5 => (c.1, c.2 - 1, true)

lemma dir_inj {k l : Fin 6} (h : dir k = dir l) : k = l := by
  fin_cases k <;> fin_cases l <;> simp_all [dir]

lemma dir_add3 (k : Fin 6) : dir (k + 3) = -dir k := by
  fin_cases k <;> simp [dir]

/-- seen from the other end, the left triangle of `a → a + dir k` -/
lemma triAt_add2 (a : Cell) (k : Fin 6) : triAt (a + dir k) (k + 2) = triAt a k := by
  obtain ⟨i, j⟩ := a
  fin_cases k <;> simp [triAt, dir] <;> (try constructor) <;> (try ring_nf) <;> (try rfl)

/-- seen from the other end, the right triangle of `a → a + dir k` -/
lemma triAt_add3 (a : Cell) (k : Fin 6) : triAt (a + dir k) (k + 3) = triAt a (k - 1) := by
  obtain ⟨i, j⟩ := a
  fin_cases k <;> simp [triAt, dir] <;> (try constructor) <;> (try ring_nf) <;> (try rfl)

lemma hex_all : ∀ f : Fin 6 → Bool, ∀ ka kb : Fin 6, ka ≠ kb →
    (∀ k, (f k ≠ f (k - 1)) ↔ (k = ka ∨ k = kb)) → f kb = f (ka - 1) := by
  decide

lemma triAt_eq {a a' : Cell} {k k' : Fin 6} (h : triAt a k = triAt a' k') :
    (a' = a ∧ k' = k) ∨ (a' = a + dir k ∧ k' = k + 2) ∨ (a' = a + dir (k + 1) ∧ k' = k + 4) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨i', j'⟩ := a'
  fin_cases k <;> fin_cases k' <;> simp [triAt, dir, Prod.ext_iff] at h ⊢ <;> omega

lemma triAt_third (a : Cell) (k : Fin 6) : triAt (a + dir (k + 1)) (k + 4) = triAt a k := by
  have := triAt_add3 a (k + 1)
  rw [show k + 1 + 3 = k + 4 by rw [add_assoc]; rfl, add_sub_cancel_right] at this
  exact this

lemma dir_succ_sub (k : Fin 6) : dir (k + 1) - dir k = dir (k + 2) := by
  fin_cases k <;> simp [dir] <;> rfl

/-- a simple closed Δ-walk of length `n ≥ 3` -/
structure SWalk (n : ℕ) [NeZero n] where
  c : Fin n → Cell
  inj : Function.Injective c
  three : 3 ≤ n
  step : ∀ i, ∃ k, c (i + 1) = c i + dir k

section Walk

variable {n : ℕ} [NeZero n] (W : SWalk n)

/-- the direction of the `i`-th step -/
noncomputable def SWalk.kOut (i : Fin n) : Fin 6 := Classical.choose (W.step i)

lemma SWalk.kOut_spec (i : Fin n) : W.c (i + 1) = W.c i + dir (W.kOut i) :=
  Classical.choose_spec (W.step i)

/-- the triangle left of the `i`-th step -/
noncomputable def SWalk.left (i : Fin n) : Tri := triAt (W.c i) (W.kOut i)

/-- `{a, b}` is a step of the walk -/
def SWalk.WE (a b : Cell) : Prop := ∃ i, (W.c i = a ∧ W.c (i + 1) = b) ∨ (W.c i = b ∧ W.c (i + 1) = a)

/-- `S` is a (mod 2) 2-chain with boundary the walk -/
def IsBd (S : Tri → Bool) (E : Cell → Cell → Prop) : Prop :=
  ∀ a k, (S (triAt a k) ≠ S (triAt a (k - 1))) ↔ E a (a + dir k)

lemma fin_two_ne {m : ℕ} [NeZero m] (h3 : 3 ≤ m) (i : Fin m) : i + 1 + 1 ≠ i := by
  intro h
  have h2 : (1 : Fin m) + 1 = 0 := by
    have := congrArg (· - i) h
    rw [add_assoc, add_sub_cancel_left, sub_self] at this
    exact this
  have := congrArg Fin.val h2
  rw [Fin.val_add, Fin.val_one', Fin.val_zero] at this
  rw [Nat.one_mod_eq_one.mpr (by omega)] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

lemma SWalk.back (i : Fin n) : W.c (i + 1) + dir (W.kOut i + 3) = W.c i := by
  rw [dir_add3, W.kOut_spec]; abel

lemma SWalk.we_at (i : Fin n) (k : Fin 6) :
    W.WE (W.c (i + 1)) (W.c (i + 1) + dir k) ↔ (k = W.kOut i + 3 ∨ k = W.kOut (i + 1)) := by
  constructor
  · rintro ⟨j, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · have hj := W.inj h1
      subst hj
      right
      rw [W.kOut_spec] at h2
      exact (dir_inj (add_left_cancel h2)).symm
    · have hj : j = i := add_right_cancel (W.inj h2)
      subst hj
      left
      rw [← W.back j] at h1
      exact (dir_inj (add_left_cancel h1)).symm
  · rintro (h | h)
    · exact ⟨i, Or.inr ⟨by rw [h, W.back], rfl⟩⟩
    · exact ⟨i + 1, Or.inl ⟨rfl, by rw [h, W.kOut_spec]⟩⟩

lemma SWalk.ka_ne (i : Fin n) : W.kOut i + 3 ≠ W.kOut (i + 1) := by
  intro h
  have h1 := W.kOut_spec (i + 1)
  rw [← h, W.back] at h1
  exact fin_two_ne W.three i (W.inj h1)

/-- consecutive left triangles lie on the same side -/
lemma SWalk.left_succ {S : Tri → Bool} (hS : IsBd S W.WE) (i : Fin n) :
    S (W.left (i + 1)) = S (W.left i) := by
  have key := hex_all (fun k => S (triAt (W.c (i + 1)) k)) (W.kOut i + 3) (W.kOut (i + 1))
    (W.ka_ne i) (fun k => by rw [hS, W.we_at])
  have e : W.kOut i + 3 - 1 = W.kOut i + 2 := by rw [add_sub_assoc]; rfl
  have h2 : triAt (W.c (i + 1)) (W.kOut i + 2) = triAt (W.c i) (W.kOut i) := by
    rw [W.kOut_spec]; exact triAt_add2 _ _
  rw [e, h2] at key
  exact key

/-- the mod-2 Jordan lemma: all left triangles lie on one side -/
theorem SWalk.left_const {S : Tri → Bool} (hS : IsBd S W.WE) (i : Fin n) :
    S (W.left i) = S (W.left 0) := by
  have : ∀ m : ℕ, ∀ j : Fin n, j.val = m → S (W.left j) = S (W.left 0) := by
    intro m
    induction m with
    | zero => intro j hj; rw [show j = 0 from Fin.ext (by simpa using hj)]
    | succ m ih =>
      intro j hj
      have hm : m < n := by omega
      have hj' : j = (⟨m, hm⟩ : Fin n) + 1 := by
        ext
        rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.mpr (by omega)]
        simp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hj', W.left_succ hS, ih _ rfl]
  exact this _ i rfl

/-- left normalisation: flipping the chain keeps its boundary -/
lemma isBd_flip {S : Tri → Bool} {E : Cell → Cell → Prop} (hS : IsBd S E) (b : Bool) :
    IsBd (fun τ => (S τ == b)) E := by
  intro a k
  show ((S (triAt a k) == b) ≠ (S (triAt a (k - 1)) == b)) ↔ _
  rw [← hS a k]
  generalize S (triAt a k) = x
  generalize S (triAt a (k - 1)) = y
  cases x <;> cases y <;> cases b <;> simp

theorem SWalk.normalize {S : Tri → Bool} (hS : IsBd S W.WE) :
    ∃ S' : Tri → Bool, IsBd S' W.WE ∧ ∀ i, S' (W.left i) = true := by
  refine ⟨fun τ => (S τ == S (W.left 0)), isBd_flip hS _, fun i => ?_⟩
  simp [W.left_const hS i]

/-- `a → b` is a forward step of the walk -/
def SWalk.Fwd (a b : Cell) : Prop := ∃ i, W.c i = a ∧ W.c (i + 1) = b

lemma SWalk.kOut_eq {i : Fin n} {k : Fin 6} (h : W.c (i + 1) = W.c i + dir k) : W.kOut i = k := by
  rw [W.kOut_spec] at h; exact dir_inj (add_left_cancel h)

lemma SWalk.not_fwd_both {a b : Cell} (h1 : W.Fwd a b) (h2 : W.Fwd b a) : False := by
  obtain ⟨i, hi1, hi2⟩ := h1
  obtain ⟨j, hj1, hj2⟩ := h2
  have hj : j = i + 1 := W.inj (hj1.trans hi2.symm)
  subst hj
  exact fin_two_ne W.three i (W.inj (hj2.trans hi1.symm))

/-- the left normalised chain jumps by the walk flow -/
theorem SWalk.jump {S : Tri → Bool} (hS : IsBd S W.WE) (hL : ∀ i, S (W.left i) = true)
    (a : Cell) (k : Fin 6) :
    S (triAt a k) = true ∧ S (triAt a (k - 1)) = false ∧ W.Fwd a (a + dir k) ∨
    S (triAt a k) = false ∧ S (triAt a (k - 1)) = true ∧ W.Fwd (a + dir k) a ∨
    S (triAt a k) = S (triAt a (k - 1)) ∧ ¬ W.Fwd a (a + dir k) ∧ ¬ W.Fwd (a + dir k) a := by
  by_cases hf : W.Fwd a (a + dir k)
  · obtain ⟨i, hi1, hi2⟩ := hf
    have hk : W.kOut i = k := W.kOut_eq (by rw [hi2, hi1])
    have h1 : S (triAt a k) = true := by rw [← hi1, ← hk]; exact hL i
    have hx := (hS a k).mpr ⟨i, Or.inl ⟨hi1, hi2⟩⟩
    left
    refine ⟨h1, ?_, ⟨i, hi1, hi2⟩⟩
    rw [h1] at hx; cases h : S (triAt a (k - 1)) <;> simp_all
  · by_cases hb : W.Fwd (a + dir k) a
    · obtain ⟨j, hj1, hj2⟩ := hb
      have hcj : W.c (j + 1) = W.c j + dir (W.kOut j) := W.kOut_spec j
      have hk : k = W.kOut j + 3 := by
        apply dir_inj
        rw [dir_add3]
        have : a + dir k + dir (W.kOut j) = a := by rw [← hj1, ← hcj, hj2]
        have h2 : dir k + dir (W.kOut j) = 0 := by
          have h3 := congrArg (· - a) this
          simp only [sub_self] at h3
          rw [← h3]; abel
        exact eq_neg_of_add_eq_zero_left h2
      have e : k - 1 = W.kOut j + 2 := by rw [hk, add_sub_assoc]; rfl
      have h1 : S (triAt a (k - 1)) = true := by
        rw [e, ← hj2, hcj, triAt_add2]; exact hL j
      have hx := (hS a k).mpr ⟨j, Or.inr ⟨hj1, hj2⟩⟩
      right; left
      refine ⟨?_, h1, ⟨j, hj1, hj2⟩⟩
      rw [h1] at hx; cases h : S (triAt a k) <;> simp_all
    · right; right
      refine ⟨?_, hf, hb⟩
      by_contra hne
      obtain ⟨i, hi⟩ := (hS a k).mp hne
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hf ⟨i, h1, h2⟩
      · exact hb ⟨i, h1, h2⟩

/-- integer Sperner lemma: a left-normalised region whose boundary carries three contiguous colour
arcs `1, 2, 3` contains a counter-clockwise trichromatic triangle. -/
theorem SWalk.sperner {S : Tri → Bool} (hS : IsBd S W.WE) (hL : ∀ i, S (W.left i) = true)
    (κ : Cell → ℕ) (C0 : Finset Cell) (hC0 : ∀ a k, κ a = 1 → κ (a + dir k) = 2 → a ∈ C0)
    (hcol : ∀ a k, S (triAt a k) = true → κ a = 1 ∨ κ a = 2 ∨ κ a = 3)
    (s1 s2 : ℕ) (h01 : 0 < s1) (h12 : s1 < s2) (h2n : s2 < n)
    (harc : ∀ i : Fin n, κ (W.c i) = if i.val < s1 then 1 else if i.val < s2 then 2 else 3) :
    ∃ a k, S (triAt a k) = true ∧ κ a = 1 ∧ κ (a + dir k) = 2 ∧ κ (a + dir (k + 1)) = 3 := by
  classical
  by_contra hno
  push_neg at hno
  set P12 : Finset (Cell × Fin 6) :=
    (C0 ×ˢ Finset.univ).filter (fun p => κ p.1 = 1 ∧ κ (p.1 + dir p.2) = 2) with hP
  have memP : ∀ a k, κ a = 1 → κ (a + dir k) = 2 → (a, k) ∈ P12 := by
    intro a k h1 h2; simp [hP, hC0 a k h1 h2, h1, h2]
  set A := P12.filter (fun p => S (triAt p.1 p.2) = true)
  set B := P12.filter (fun p => S (triAt p.1 (p.2 - 1)) = true)
  -- the partner map
  let φ : Cell × Fin 6 → Cell × Fin 6 := fun p =>
    if κ (p.1 + dir (p.2 + 1)) = 1 then (p.1 + dir (p.2 + 1), p.2 + 5) else (p.1, p.2 + 1)
  have hφ : ∀ p ∈ A, φ p ∈ B ∧ triAt (φ p).1 ((φ p).2 - 1) = triAt p.1 p.2 := by
    rintro ⟨a, k⟩ hp
    simp only [A, hP, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
    obtain ⟨⟨_, h1, h2⟩, hin⟩ := hp
    have h3 := hcol _ _ (by rw [triAt_third]; exact hin)
    have hn3 : κ (a + dir (k + 1)) ≠ 3 := hno a k hin h1 h2
    by_cases hc : κ (a + dir (k + 1)) = 1
    · have ht : triAt (a + dir (k + 1)) (k + 5 - 1) = triAt a k := by
        rw [show k + 5 - 1 = k + 4 by rw [add_sub_assoc]; rfl, triAt_third]
      have hb : a + dir (k + 1) + dir (k + 5) = a + dir k := by
        have e : dir (k + 5) = -dir (k + 2) := by
          rw [show k + 5 = k + 2 + 3 by rw [add_assoc]; rfl, dir_add3]
        rw [e, ← dir_succ_sub]; abel
      simp only [φ, hc, if_true]
      refine ⟨?_, ht⟩
      simp only [B, Finset.mem_filter]
      exact ⟨memP _ _ hc (by rw [hb]; exact h2), by rw [ht]; exact hin⟩
    · have hc2 : κ (a + dir (k + 1)) = 2 := by omega
      have ht : triAt a (k + 1 - 1) = triAt a k := by rw [add_sub_cancel_right]
      simp only [φ, hc, if_false]
      refine ⟨?_, ht⟩
      simp only [B, Finset.mem_filter]
      exact ⟨memP _ _ h1 hc2, by rw [ht]; exact hin⟩
  have hinj : Set.InjOn φ A := by
    rintro ⟨a, k⟩ hp ⟨a', k'⟩ hp' he
    have e1 := (hφ _ hp).2
    have e2 := (hφ _ hp').2
    rw [he, e2] at e1
    simp only at e1
    simp only [A, hP, Finset.coe_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      and_true, Set.mem_setOf_eq] at hp hp'
    obtain ⟨⟨_, h1, h2⟩, _⟩ := hp
    obtain ⟨⟨_, h1', h2'⟩, _⟩ := hp'
    rcases triAt_eq e1 with ⟨ea, ek⟩ | ⟨ea, ek⟩ | ⟨ea, ek⟩
    · rw [ea, ek]
    · exfalso; rw [ea] at h1; omega
    · exfalso
      rw [ea, ek] at h2
      have : a' + dir (k' + 1) + dir (k' + 4) = a' := by
        rw [show k' + 4 = k' + 1 + 3 by rw [add_assoc]; rfl, dir_add3]; abel
      rw [this] at h2; omega
  have hAB : A.card ≤ B.card := Finset.card_le_card_of_injOn φ (fun p hp => (hφ p hp).1) hinj
  -- the walk: no backward 1 → 2 step, and one forward step
  have hB : B ⊆ A := by
    rintro ⟨a, k⟩ hp
    simp only [B, A, Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rcases W.jump hS hL a k with ⟨h, _⟩ | ⟨_, _, ⟨i, hi1, hi2⟩⟩ | ⟨h, _⟩
    · exact h
    · exfalso
      simp only [hP, Finset.mem_filter] at hp
      obtain ⟨⟨_, h1, h2⟩, _⟩ := hp
      rw [← hi1, harc] at h2
      rw [← hi2, harc] at h1
      have hv : (i + 1).val = i.val + 1 := by
        rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.mpr (by have := W.three; omega)]
        apply Nat.mod_eq_of_lt
        split_ifs at h2 <;> omega
      rw [hv] at h1
      split_ifs at h1 h2 <;> omega
    · rw [h]; exact hp.2
  have hs1 : s1 - 1 < n := by omega
  set i0 : Fin n := ⟨s1 - 1, hs1⟩
  have hv0 : (i0 + 1).val = s1 := by
    rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.mpr (by have := W.three; omega)]
    simp only [i0]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have c1 : κ (W.c i0) = 1 := by rw [harc]; simp only [i0]; rw [if_pos (by omega)]
  have c2 : κ (W.c i0 + dir (W.kOut i0)) = 2 := by
    rw [← W.kOut_spec, harc, hv0, if_neg (by omega), if_pos h12]
  have p0A : (W.c i0, W.kOut i0) ∈ A := by
    simp only [A, Finset.mem_filter]; exact ⟨memP _ _ c1 c2, hL i0⟩
  have p0B : (W.c i0, W.kOut i0) ∉ B := by
    simp only [B, Finset.mem_filter, not_and]
    intro _
    rcases W.jump hS hL (W.c i0) (W.kOut i0) with ⟨_, h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩
    · simp [h]
    · have := hL i0; simp only [SWalk.left] at this; rw [this] at h; exact absurd h (by simp)
    · exact absurd ⟨i0, rfl, W.kOut_spec i0⟩ h
  have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hB, fun h => p0B (h ▸ p0A)⟩)
  omega

end Walk

/-- a jump-free integer function on triangles is constant -/
theorem const_of_jumpfree (f : Tri → ℤ) (h : ∀ a k, f (triAt a k) = f (triAt a (k - 1))) :
    ∀ τ, f τ = f (0, 0, false) := by
  have hU : ∀ i j : ℤ, f (i, j, true) = f (i + 1, j, false) := by
    intro i j
    have := h (i + 1, j) 1
    simpa [triAt] using this
  have hL0 : ∀ i j : ℤ, f (i, j, false) = f (i, j - 1, true) := by
    intro i j
    have := h (i, j) 0
    rw [show (0 : Fin 6) - 1 = 5 from rfl] at this
    simpa [triAt] using this
  have hL2 : ∀ i j : ℤ, f (i - 1, j, false) = f (i - 1, j, true) := by
    intro i j
    have := h (i, j) 2
    simpa [triAt] using this
  have hx : ∀ i j : ℤ, f (i + 1, j, false) = f (i, j, false) := by
    intro i j
    have := hL2 (i + 1) j
    simp at this
    rw [← hU, this]
  have hy : ∀ i j : ℤ, f (i, j + 1, false) = f (i, j, false) := by
    intro i j
    have := hL0 i (j + 1)
    simp at this
    rw [this, hU, hx]
  have hrow : ∀ i j : ℤ, f (i, j, false) = f (0, j, false) := by
    intro i j
    induction i using Int.induction_on with
    | zero => rfl
    | succ m ih => rw [hx, ih]
    | pred m ih => rw [← ih, ← hx (-(m : ℤ) - 1) j]; ring_nf
  have hcol : ∀ j : ℤ, f (0, j, false) = f (0, 0, false) := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ m ih => rw [hy, ih]
    | pred m ih => rw [← ih, ← hy 0 (-(m : ℤ) - 1)]; ring_nf
  rintro ⟨i, j, b⟩
  cases b
  · rw [hrow, hcol]
  · rw [hU, hrow, hcol]

end PQT


/-! 8100c3d9 D1: every simple closed Δ-walk bounds a mod-2 chain (via PF12 even_mem_span_squares'
square coefficients). -/

namespace PQT

open PF12 Finset

section D1

variable {n : ℕ} [NeZero n] (W : SWalk n)

lemma SWalk.WE_symm {a b : Cell} (h : W.WE a b) : W.WE b a := by
  obtain ⟨i, h | h⟩ := h
  · exact ⟨i, Or.inr h⟩
  · exact ⟨i, Or.inl h⟩

/-- indicator of a walk edge -/
noncomputable def SWalk.ind (a b : Cell) : ZMod 2 := by
  classical exact if W.WE a b then 1 else 0

lemma SWalk.ind_symm (a b : Cell) : W.ind a b = W.ind b a := by
  classical
  unfold SWalk.ind
  by_cases h : W.WE a b
  · rw [if_pos h, if_pos (W.WE_symm h)]
  · rw [if_neg h, if_neg (fun h' => h (W.WE_symm h'))]

lemma SWalk.ind_eq_one {a b : Cell} : W.ind a b = 1 ↔ W.WE a b := by
  classical
  unfold SWalk.ind
  split_ifs with h <;> simp [h]

lemma SWalk.on_walk {a b : Cell} (h : W.WE a b) : ∃ i, W.c i = a := by
  obtain ⟨i, ⟨h1, _⟩ | ⟨_, h2⟩⟩ := h
  · exact ⟨i, h1⟩
  · exact ⟨i + 1, h2⟩

lemma SWalk.ind_zero {a b : Cell} (h : ∀ i, W.c i ≠ a) : W.ind a b = 0 := by
  classical
  unfold SWalk.ind
  rw [if_neg]
  intro hw
  obtain ⟨i, hi⟩ := W.on_walk hw
  exact h i hi

/-- the walk has even degree at every cell -/
lemma SWalk.deg_even (p : Cell) : ∑ k : Fin 6, W.ind p (p + dir k) = 0 := by
  classical
  by_cases hp : ∃ j, W.c j = p
  · obtain ⟨j, rfl⟩ := hp
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by abel⟩
    have key : ∀ k, W.ind (W.c (i + 1)) (W.c (i + 1) + dir k) =
        if (k = W.kOut i + 3 ∨ k = W.kOut (i + 1)) then 1 else 0 := by
      intro k
      have := W.we_at i k
      unfold SWalk.ind
      by_cases h : (k = W.kOut i + 3 ∨ k = W.kOut (i + 1))
      · rw [if_pos (this.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
    simp only [key]
    have hne := W.ka_ne i
    generalize W.kOut i + 3 = ka at hne ⊢
    generalize W.kOut (i + 1) = kb at hne ⊢
    rw [Fin.sum_univ_six]
    fin_cases ka <;> fin_cases kb <;> simp_all <;> decide
  · push_neg at hp
    exact Finset.sum_eq_zero (fun k _ => W.ind_zero hp)

/-- horizontal / vertical / diagonal walk-edge indicators at a lower-left corner -/
noncomputable def SWalk.zH (p : Cell) : ZMod 2 := W.ind p (p.1 + 1, p.2)
noncomputable def SWalk.zV (p : Cell) : ZMod 2 := W.ind p (p.1, p.2 + 1)
noncomputable def SWalk.zD (p : Cell) : ZMod 2 := W.ind (p.1 + 1, p.2) (p.1, p.2 + 1)

/-- a box radius containing the walk -/
noncomputable def SWalk.rad : ℤ := ∑ i, (|(W.c i).1| + |(W.c i).2|) + 2

lemma SWalk.in_rad (i : Fin n) : |(W.c i).1| ≤ W.rad - 2 ∧ |(W.c i).2| ≤ W.rad - 2 := by
  have h := Finset.single_le_sum (f := fun i => |(W.c i).1| + |(W.c i).2|)
    (fun i _ => by positivity) (Finset.mem_univ i)
  simp only [SWalk.rad]
  constructor <;> nlinarith [abs_nonneg (W.c i).1, abs_nonneg (W.c i).2]

noncomputable def SWalk.boxC : Finset Cell := Icc (-W.rad) W.rad ×ˢ Icc (-W.rad) W.rad

/-- the 4-grid edge function: diagonals replaced by the two other edges of their triangle -/
noncomputable def SWalk.z4 : Sym2 (ℤ × ℤ) → ZMod 2 := fun e => by
  classical exact ∑ p ∈ W.boxC, ((if e = gH p then W.zH p + W.zD p else 0) +
    (if e = gV p then W.zV p + W.zD p else 0))

lemma SWalk.near {a : Cell} (h : ∃ i, W.c i = a) : |a.1| ≤ W.rad - 2 ∧ |a.2| ≤ W.rad - 2 := by
  obtain ⟨i, rfl⟩ := h; exact W.in_rad i

lemma SWalk.zH_zD_out (a : Cell) (ha : a ∉ W.boxC) : W.zH a + W.zD a = 0 ∧ W.zV a + W.zD a = 0 := by
  have hz : ∀ b c : Cell, (|b.1 - a.1| ≤ 1) → (|b.2 - a.2| ≤ 1) → W.ind b c = 0 := by
    intro b c h1 h2
    apply W.ind_zero
    intro i hi
    have := W.in_rad i
    rw [hi] at this
    apply ha
    simp only [SWalk.boxC, mem_product, mem_Icc]
    rw [abs_le] at h1 h2
    obtain ⟨h3, h4⟩ := this
    rw [abs_le] at h3 h4
    omega
  have e1 := hz a (a.1 + 1, a.2) (by simp) (by simp)
  have e2 := hz a (a.1, a.2 + 1) (by simp) (by simp)
  have e3 := hz (a.1 + 1, a.2) (a.1, a.2 + 1) (by simp) (by simp)
  simp only [SWalk.zH, SWalk.zV, SWalk.zD]
  rw [e1, e2, e3]; simp

lemma SWalk.z4_gH (a : Cell) : W.z4 (gH a) = W.zH a + W.zD a := by
  classical
  unfold SWalk.z4
  by_cases ha : a ∈ W.boxC
  · rw [Finset.sum_eq_single a]
    · simp [gH_ne_gV]
    · intro p _ hp
      simp [gH_inj, gH_ne_gV, Ne.symm hp]
    · intro h; exact absurd ha h
  · rw [Finset.sum_eq_zero, (W.zH_zD_out a ha).1]
    intro p hp
    have hp' : p ≠ a := fun h => ha (h ▸ hp)
    simp [gH_inj, gH_ne_gV, Ne.symm hp']

lemma SWalk.z4_gV (a : Cell) : W.z4 (gV a) = W.zV a + W.zD a := by
  classical
  unfold SWalk.z4
  by_cases ha : a ∈ W.boxC
  · rw [Finset.sum_eq_single a]
    · simp [gV_ne_gH]
    · intro p _ hp
      simp [gV_inj, gV_ne_gH, Ne.symm hp]
    · intro h; exact absurd ha h
  · rw [Finset.sum_eq_zero, (W.zH_zD_out a ha).2]
    intro p hp
    have hp' : p ≠ a := fun h => ha (h ▸ hp)
    simp [gV_inj, gV_ne_gH, Ne.symm hp']

lemma SWalk.z4_box : BoxSupp W.rad W.z4 := by
  classical
  intro e he
  unfold SWalk.z4 at he
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  simp only [SWalk.boxC, mem_product, mem_Icc] at hp
  by_cases h1 : e = gH p
  · refine ⟨p, Or.inl ⟨h1, ?_, ?_⟩⟩
    · simp only [InBox]; omega
    · simp only [InBox]
      have hv : W.zH p + W.zD p ≠ 0 := by
        rw [h1] at hne; simpa [gH_ne_gV] using hne
      by_contra hb
      apply hv
      have hz1 : W.zH p = 0 := W.ind_zero (fun i hi => by
        have := W.in_rad i; rw [hi] at this; rw [abs_le, abs_le] at this; omega)
      have hz2 : W.zD p = 0 := W.ind_zero (fun i hi => by
        have := W.in_rad i; rw [hi] at this; rw [abs_le, abs_le] at this; simp at this; omega)
      rw [hz1, hz2]; simp
  · by_cases h2 : e = gV p
    · refine ⟨p, Or.inr ⟨h2, ?_, ?_⟩⟩
      · simp only [InBox]; omega
      · simp only [InBox]
        have hv : W.zV p + W.zD p ≠ 0 := by
          rw [h2] at hne; simpa [gV_ne_gH] using hne
        by_contra hb
        apply hv
        have hz1 : W.zV p = 0 := W.ind_zero (fun i hi => by
          have := W.in_rad i; rw [hi] at this; rw [abs_le, abs_le] at this; omega)
        have hz2 : W.zD p = 0 := W.ind_zero (fun i hi => by
          have := W.in_rad i; rw [hi] at this; rw [abs_le, abs_le] at this; simp at this; omega)
        rw [hz1, hz2]; simp
    · simp [h1, h2] at hne

lemma SWalk.z4_even (p : Cell) : gdeg W.z4 p = 0 := by
  obtain ⟨i, j⟩ := p
  have hd := W.deg_even (i, j)
  rw [Fin.sum_univ_six] at hd
  simp only [dir, Prod.mk_add_mk] at hd
  simp only [gdeg, SWalk.z4_gH, SWalk.z4_gV, SWalk.zH, SWalk.zV, SWalk.zD]
  have s1 := W.ind_symm (i, j) (i + -1, j + 0)
  have s2 := W.ind_symm (i, j) (i + 0, j + -1)
  have s3 := W.ind_symm (i, j) (i + 1, j + -1)
  simp only [add_zero] at hd s1 s2 s3
  have e1 : (i + -1, j) = (i - 1, j) := by simp [sub_eq_add_neg]
  have e2 : (i, j + -1) = (i, j - 1) := by simp [sub_eq_add_neg]
  have e3 : (i + -1, j + 1) = (i - 1, j + 1) := by simp [sub_eq_add_neg]
  have e4 : (i + 1, j + -1) = (i + 1, j - 1) := by simp [sub_eq_add_neg]
  rw [e1, e2, e3, e4] at hd
  rw [e1] at s1; rw [e2] at s2; rw [e4] at s3
  simp only [sub_add_cancel]
  rw [s1, s2] at hd
  rw [W.ind_symm (i, j) (i + 1, j - 1)] at hd
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination hd + W.ind (i + 1, j) (i, j + 1) * h2

/-- D1: every simple closed Δ-walk bounds a mod-2 chain -/
theorem SWalk.exists_bd : ∃ S : Tri → Bool, IsBd S W.WE := by
  classical
  set M := W.rad
  set z := W.z4
  have hz : BoxSupp M z := W.z4_box
  have he : ∀ p, gdeg z p = 0 := W.z4_even
  let S : Tri → Bool := fun τ =>
    if τ.2.2 then decide (coef M z (τ.1, τ.2.1) = 1)
    else decide (coef M z (τ.1, τ.2.1) + W.zD (τ.1, τ.2.1) = 1)
  refine ⟨S, ?_⟩
  have xr : ∀ x y : ZMod 2, (decide (x = 1) ≠ decide (y = 1)) ↔ x + y = 1 := by decide
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hH : ∀ i j, coef M z (i, j) + coef M z (i, j - 1) = W.zH (i, j) + W.zD (i, j) := by
    intro i j; rw [coef_horiz hz he]; exact W.z4_gH (i, j)
  have hV : ∀ i j, coef M z (i, j) + coef M z (i - 1, j) = W.zV (i, j) + W.zD (i, j) := by
    intro i j
    rw [coef_step hz i j]
    have := W.z4_gV (i, j)
    linear_combination this + coef M z (i - 1, j) * h2
  intro a k
  obtain ⟨i, j⟩ := a
  rw [← W.ind_eq_one]
  fin_cases k
  · have hs : S (triAt (i, j) 0) = decide (coef M z (i, j) + W.zD (i, j) = 1) := rfl
    have hs' : S (triAt (i, j) (0 - 1)) = decide (coef M z (i, j - 1) = 1) := rfl
    have hd : (i, j) + dir 0 = (i + 1, j) := by simp [dir]
    have e : coef M z (i, j) + W.zD (i, j) + coef M z (i, j - 1) = W.zH (i, j) := by
      linear_combination hH i j + W.zD (i, j) * h2
    simp only [Fin.zero_eta, Fin.isValue] at hs hs' ⊢
    rw [hs, hs', xr, hd, e]; rfl
  · have hs : S (triAt (i, j) 1) = decide (coef M z (i - 1, j) = 1) := rfl
    have hs' : S (triAt (i, j) (1 - 1)) = decide (coef M z (i, j) + W.zD (i, j) = 1) := rfl
    have hd : (i, j) + dir 1 = (i, j + 1) := by simp [dir]
    have e : coef M z (i - 1, j) + (coef M z (i, j) + W.zD (i, j)) = W.zV (i, j) := by
      linear_combination hV i j + W.zD (i, j) * h2
    simp only [Fin.mk_one, Fin.isValue] at hs hs' ⊢
    rw [hs, hs', xr, hd, e]; rfl
  · have hs : S (triAt (i, j) 2) = decide (coef M z (i - 1, j) + W.zD (i - 1, j) = 1) := rfl
    have hs' : S (triAt (i, j) (2 - 1)) = decide (coef M z (i - 1, j) = 1) := rfl
    have hd : (i, j) + dir 2 = (i - 1, j + 1) := by simp [dir, sub_eq_add_neg]
    have e : coef M z (i - 1, j) + W.zD (i - 1, j) + coef M z (i - 1, j) = W.zD (i - 1, j) := by
      linear_combination coef M z (i - 1, j) * h2
    simp only [Fin.reduceFinMk, Fin.isValue] at hs hs' ⊢
    rw [hs, hs', xr, hd, e]
    simp only [SWalk.zD, sub_add_cancel]
  · have hs : S (triAt (i, j) 3) = decide (coef M z (i - 1, j - 1) = 1) := rfl
    have hs' : S (triAt (i, j) (3 - 1)) = decide (coef M z (i - 1, j) + W.zD (i - 1, j) = 1) := rfl
    have hd : (i, j) + dir 3 = (i - 1, j) := by simp [dir, sub_eq_add_neg]
    have e : coef M z (i - 1, j - 1) + (coef M z (i - 1, j) + W.zD (i - 1, j)) = W.zH (i - 1, j) := by
      linear_combination hH (i - 1) j + W.zD (i - 1, j) * h2
    simp only [Fin.reduceFinMk, Fin.isValue] at hs hs' ⊢
    rw [hs, hs', xr, hd, e]
    simp only [SWalk.zH, sub_add_cancel]
    rw [W.ind_symm]
  · have hs : S (triAt (i, j) 4) = decide (coef M z (i, j - 1) + W.zD (i, j - 1) = 1) := rfl
    have hs' : S (triAt (i, j) (4 - 1)) = decide (coef M z (i - 1, j - 1) = 1) := rfl
    have hd : (i, j) + dir 4 = (i, j - 1) := by simp [dir, sub_eq_add_neg]
    have e : coef M z (i, j - 1) + W.zD (i, j - 1) + coef M z (i - 1, j - 1) = W.zV (i, j - 1) := by
      linear_combination hV i (j - 1) + W.zD (i, j - 1) * h2
    simp only [Fin.reduceFinMk, Fin.isValue] at hs hs' ⊢
    rw [hs, hs', xr, hd, e]
    simp only [SWalk.zV, sub_add_cancel]
    rw [W.ind_symm]
  · have hs : S (triAt (i, j) 5) = decide (coef M z (i, j - 1) = 1) := rfl
    have hs' : S (triAt (i, j) (5 - 1)) = decide (coef M z (i, j - 1) + W.zD (i, j - 1) = 1) := rfl
    have hd : (i, j) + dir 5 = (i + 1, j - 1) := by simp [dir, sub_eq_add_neg]
    have e : coef M z (i, j - 1) + (coef M z (i, j - 1) + W.zD (i, j - 1)) = W.zD (i, j - 1) := by
      linear_combination coef M z (i, j - 1) * h2
    simp only [Fin.reduceFinMk, Fin.isValue] at hs hs' ⊢
    rw [hs, hs', xr, hd, e]
    simp only [SWalk.zD, sub_add_cancel]
    rw [W.ind_symm]

end D1

end PQT

/-! 8100c3d9 D4a: a Δ-model gives a 4-grid model (brick refinement). -/

namespace PQT

open PF12

/-- Δ-adjacency of cells -/
def dAdj (a b : Cell) : Prop := ∃ k, b = a + dir k

/-- one Δ-step inside a cell set -/
def DRel (B : Finset Cell) (a b : Cell) : Prop := a ∈ B ∧ b ∈ B ∧ dAdj a b

/-- the 2 × 2 brick of a Δ-cell in the 4-grid -/
def brick (c : Cell) : Finset (ℤ × ℤ) :=
  {(2 * c.1 + c.2, 2 * c.2), (2 * c.1 + c.2 + 1, 2 * c.2), (2 * c.1 + c.2, 2 * c.2 + 1),
    (2 * c.1 + c.2 + 1, 2 * c.2 + 1)}

lemma brick_eq {c d : Cell} {p : ℤ × ℤ} (hc : p ∈ brick c) (hd : p ∈ brick d) : c = d := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  obtain ⟨p1, p2⟩ := p
  simp only [brick, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hc hd
  ext <;> simp only <;> omega

lemma brick_reach (c : Cell) {B : Finset (ℤ × ℤ)} (hB : brick c ⊆ B) {p : ℤ × ℤ}
    (hp : p ∈ brick c) : Relation.ReflTransGen (BlobRel B) p (2 * c.1 + c.2, 2 * c.2) := by
  have m : ∀ x ∈ brick c, x ∈ B := fun x hx => hB hx
  have b0 : (2 * c.1 + c.2, 2 * c.2) ∈ brick c := by simp [brick]
  have b1 : (2 * c.1 + c.2 + 1, 2 * c.2) ∈ brick c := by simp [brick]
  have b2 : (2 * c.1 + c.2, 2 * c.2 + 1) ∈ brick c := by simp [brick]
  have b3 : (2 * c.1 + c.2 + 1, 2 * c.2 + 1) ∈ brick c := by simp [brick]
  have s1 : BlobRel B (2 * c.1 + c.2 + 1, 2 * c.2) (2 * c.1 + c.2, 2 * c.2) :=
    ⟨m _ b1, m _ b0, Or.inr (Or.inl rfl)⟩
  have s2 : BlobRel B (2 * c.1 + c.2, 2 * c.2 + 1) (2 * c.1 + c.2, 2 * c.2) :=
    ⟨m _ b2, m _ b0, Or.inr (Or.inr (Or.inr rfl))⟩
  have s3 : BlobRel B (2 * c.1 + c.2 + 1, 2 * c.2 + 1) (2 * c.1 + c.2 + 1, 2 * c.2) :=
    ⟨m _ b3, m _ b1, Or.inr (Or.inr (Or.inr rfl))⟩
  simp only [brick, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single s1
  · exact Relation.ReflTransGen.single s2
  · exact Relation.ReflTransGen.head s3 (Relation.ReflTransGen.single s1)

lemma brick_conn (c : Cell) {B : Finset (ℤ × ℤ)} (hB : brick c ⊆ B) {p q : ℤ × ℤ}
    (hp : p ∈ brick c) (hq : q ∈ brick c) : Relation.ReflTransGen (BlobRel B) p q :=
  (brick_reach c hB hp).trans (reach_symm (brick_reach c hB hq))

lemma brick_adj {c d : Cell} (h : dAdj c d) : ∃ p ∈ brick c, ∃ q ∈ brick d, gAdj p q := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨c1, c2⟩ := c
  fin_cases k <;> simp only [dir, Prod.mk_add_mk, Fin.isValue]
  · exact ⟨(2 * c1 + c2 + 1, 2 * c2), by simp [brick], (2 * (c1 + 1) + (c2 + 0), 2 * (c2 + 0)),
      by simp [brick], Or.inl (by ext <;> simp <;> ring)⟩
  · exact ⟨(2 * c1 + c2 + 1, 2 * c2 + 1), by simp [brick], (2 * (c1 + 0) + (c2 + 1), 2 * (c2 + 1)),
      by simp [brick], Or.inr (Or.inr (Or.inl (by ext <;> simp <;> ring)))⟩
  · exact ⟨(2 * c1 + c2, 2 * c2 + 1), by simp [brick],
      (2 * (c1 + -1) + (c2 + 1) + 1, 2 * (c2 + 1)), by simp [brick],
      Or.inr (Or.inr (Or.inl (by ext <;> simp <;> ring)))⟩
  · exact ⟨(2 * c1 + c2, 2 * c2), by simp [brick],
      (2 * (c1 + -1) + (c2 + 0) + 1, 2 * (c2 + 0)), by simp [brick],
      Or.inr (Or.inl (by ext <;> simp <;> ring))⟩
  · exact ⟨(2 * c1 + c2, 2 * c2), by simp [brick],
      (2 * (c1 + 0) + (c2 + -1) + 1, 2 * (c2 + -1) + 1), by simp [brick],
      Or.inr (Or.inr (Or.inr (by ext <;> simp <;> ring)))⟩
  · exact ⟨(2 * c1 + c2 + 1, 2 * c2), by simp [brick],
      (2 * (c1 + 1) + (c2 + -1), 2 * (c2 + -1) + 1), by simp [brick],
      Or.inr (Or.inr (Or.inr (by ext <;> simp <;> ring)))⟩

/-- D4a: a Δ-model gives a 4-grid model -/
theorem gridModel_of_dModel {W : Type} (H : SimpleGraph W) (B : W → Finset Cell)
    (hdisj : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hconn : ∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (DRel (B v)) p q)
    (hne : ∀ v, (B v).Nonempty)
    (hadj : ∀ v w, H.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, dAdj p q) :
    PQL5.HasGridModel H := by
  classical
  refine ⟨fun v => (B v).biUnion brick, ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_biUnion] at hp hq
    obtain ⟨c, hc, hpc⟩ := hp
    obtain ⟨d, hd, hpd⟩ := hq
    have := brick_eq hpc hpd
    subst this
    exact Finset.disjoint_left.mp (hdisj v w hvw) hc hd
  · intro v p hp q hq
    simp only [Finset.mem_biUnion] at hp hq
    obtain ⟨c, hc, hpc⟩ := hp
    obtain ⟨d, hd, hqd⟩ := hq
    have sub : ∀ e ∈ B v, brick e ⊆ (B v).biUnion brick := fun e he =>
      Finset.subset_biUnion_of_mem brick he
    have key : ∀ e, Relation.ReflTransGen (DRel (B v)) c e → e ∈ B v →
        ∀ q ∈ brick e, Relation.ReflTransGen (BlobRel ((B v).biUnion brick)) p q := by
      intro e he
      induction he with
      | refl => intro _ q hq; exact brick_conn c (sub c hc) hpc hq
      | tail _ hst ih =>
        intro he' q hq
        obtain ⟨hs, ht, hadj'⟩ := hst
        obtain ⟨p1, hp1, q1, hq1, hg⟩ := brick_adj hadj'
        exact ((ih hs p1 hp1).tail ⟨sub _ hs hp1, sub _ ht hq1, hg⟩).trans
          (brick_conn _ (sub _ ht) hq1 hq)
    exact key d (hconn v c hc d hd) hd q hqd
  · intro v
    obtain ⟨c, hc⟩ := hne v
    exact ⟨(2 * c.1 + c.2, 2 * c.2), Finset.mem_biUnion.mpr ⟨c, hc, by simp [brick]⟩⟩
  · intro v w hvw
    obtain ⟨p, hp, q, hq, hpq⟩ := hadj v w hvw
    obtain ⟨p1, hp1, q1, hq1, hg⟩ := brick_adj hpq
    exact ⟨p1, Finset.mem_biUnion.mpr ⟨p, hp, hp1⟩, q1, Finset.mem_biUnion.mpr ⟨q, hq, hq1⟩, hg⟩

end PQT

/-! 8100c3d9 D4b: Voronoi filling of a grid model; the Δ-contraction graph has a grid model. -/

namespace PQT

open PF12

section D4b

lemma dAdj_iff (a b : Cell) : dAdj a b ↔
    (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2 + 1) ∨
    (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) ∨ (b.1 = a.1 + 1 ∧ b.2 = a.2 - 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [dir] <;> omega
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, by ext <;> simp [dir] <;> omega⟩
    · exact ⟨1, by ext <;> simp [dir] <;> omega⟩
    · exact ⟨2, by ext <;> simp [dir] <;> omega⟩
    · exact ⟨3, by ext <;> simp [dir] <;> omega⟩
    · exact ⟨4, by ext <;> simp [dir] <;> omega⟩
    · exact ⟨5, by ext <;> simp [dir] <;> omega⟩

lemma dAdj_symm {a b : Cell} (h : dAdj a b) : dAdj b a := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 3, by rw [dir_add3]; abel⟩

/-- a Δ-step inside a cell predicate -/
def PRel (Q : Cell → Prop) (a b : Cell) : Prop := Q a ∧ Q b ∧ dAdj a b

lemma rtg_symm {Q : Cell → Prop} {a b : Cell} (h : Relation.ReflTransGen (PRel Q) a b) :
    Relation.ReflTransGen (PRel Q) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head ⟨hst.2.1, hst.1, dAdj_symm hst.2.2⟩ ih

lemma rtg_mono {Q Q' : Cell → Prop} (hQ : ∀ x, Q x → Q' x) {a b : Cell}
    (h : Relation.ReflTransGen (PRel Q) a b) : Relation.ReflTransGen (PRel Q') a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact ih.tail ⟨hQ _ hst.1, hQ _ hst.2.1, hst.2.2⟩

lemma rtg_map {Q : Cell → Prop} {r : Cell → Cell → Prop} (f : Cell → Cell)
    (hf : ∀ a b, PRel Q a b → Relation.ReflTransGen r (f a) (f b)) {a b : Cell}
    (h : Relation.ReflTransGen (PRel Q) a b) : Relation.ReflTransGen r (f a) (f b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact ih.trans (hf _ _ hst)

/-- descent: every `Q`-cell reaches a `T`-cell inside `Q` if non-`T` cells can strictly descend -/
lemma descent (Q T : Cell → Prop) (f : Cell → ℕ)
    (h : ∀ c, Q c → ¬ T c → ∃ c', Q c' ∧ dAdj c c' ∧ f c' < f c) :
    ∀ n c, f c = n → Q c → ∃ t, T t ∧ Relation.ReflTransGen (PRel Q) c t := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro c hn hc
  by_cases hT : T c
  · exact ⟨c, hT, Relation.ReflTransGen.refl⟩
  · obtain ⟨c', hc', hadj, hlt⟩ := h c hc hT
    obtain ⟨t, ht, hr⟩ := ih (f c') (by rw [← hn]; exact hlt) c' rfl hc'
    exact ⟨t, ht, Relation.ReflTransGen.head ⟨hc, hc', hadj⟩ hr⟩

/-- 4-grid (L1) distance -/
def l1 (a b : Cell) : ℕ :=
  (a.1 - b.1).toNat + (b.1 - a.1).toNat + (a.2 - b.2).toNat + (b.2 - a.2).toNat

lemma l1_self (c : Cell) : l1 c c = 0 := by simp [l1]

lemma l1_pos {c p : Cell} (h : c ≠ p) : 1 ≤ l1 c p := by
  by_contra hh
  apply h
  simp only [l1] at hh
  ext <;> omega

/-- the closed box `[-R, R]²` -/
def inBox (R : ℤ) (c : Cell) : Prop := -R ≤ c.1 ∧ c.1 ≤ R ∧ -R ≤ c.2 ∧ c.2 ≤ R

lemma adjR (c : Cell) : dAdj c (c.1 + 1, c.2) := ⟨0, by ext <;> simp [dir]⟩
lemma adjU (c : Cell) : dAdj c (c.1, c.2 + 1) := ⟨1, by ext <;> simp [dir]⟩
lemma adjL (c : Cell) : dAdj c (c.1 - 1, c.2) := ⟨3, by ext <;> simp [dir] <;> ring⟩
lemma adjD (c : Cell) : dAdj c (c.1, c.2 - 1) := ⟨4, by ext <;> simp [dir] <;> ring⟩

lemma step_toward (c p : Cell) (h : c ≠ p) : ∃ c', dAdj c c' ∧ l1 c' p + 1 = l1 c p ∧
    (∀ x, l1 c x ≤ l1 c' x + 1) ∧ (∀ R : ℤ, inBox R c → inBox R p → inBox R c') := by
  have hne : c.1 ≠ p.1 ∨ c.2 ≠ p.2 := by
    by_contra hh; push_neg at hh; exact h (Prod.ext hh.1 hh.2)
  rcases lt_trichotomy c.1 p.1 with h1 | h1 | h1
  · refine ⟨(c.1 + 1, c.2), adjR c, by simp only [l1]; omega, fun x => by simp only [l1]; omega,
      fun R hc hp => by simp only [inBox] at hc hp ⊢; omega⟩
  · rcases lt_trichotomy c.2 p.2 with h2 | h2 | h2
    · refine ⟨(c.1, c.2 + 1), adjU c, by simp only [l1]; omega, fun x => by simp only [l1]; omega,
        fun R hc hp => by simp only [inBox] at hc hp ⊢; omega⟩
    · omega
    · refine ⟨(c.1, c.2 - 1), adjD c, by simp only [l1]; omega, fun x => by simp only [l1]; omega,
        fun R hc hp => by simp only [inBox] at hc hp ⊢; omega⟩
  · refine ⟨(c.1 - 1, c.2), adjL c, by simp only [l1]; omega, fun x => by simp only [l1]; omega,
      fun R hc hp => by simp only [inBox] at hc hp ⊢; omega⟩

lemma out_step (R : ℤ) (hR : 0 ≤ R) (c : Cell) (hc : ¬ inBox R c) (hT : c ≠ (R + 1, R + 1)) :
    ∃ c', ¬ inBox R c' ∧ dAdj c c' ∧ l1 c' (R + 1, R + 1) < l1 c (R + 1, R + 1) := by
  simp only [inBox] at hc
  have hne : c.1 ≠ R + 1 ∨ c.2 ≠ R + 1 := by
    by_contra hh; push_neg at hh; exact hT (Prod.ext hh.1 hh.2)
  by_cases h1 : R + 1 < c.1
  · exact ⟨(c.1 - 1, c.2), by simp only [inBox]; omega, adjL c, by simp only [l1]; omega⟩
  by_cases h1' : c.1 = R + 1
  · by_cases h2 : R + 1 < c.2
    · exact ⟨(c.1, c.2 - 1), by simp only [inBox]; omega, adjD c, by simp only [l1]; omega⟩
    · exact ⟨(c.1, c.2 + 1), by simp only [inBox]; omega, adjU c, by simp only [l1]; omega⟩
  by_cases h2 : R + 1 < c.2
  · exact ⟨(c.1, c.2 - 1), by simp only [inBox]; omega, adjD c, by simp only [l1]; omega⟩
  by_cases h2' : c.2 = R + 1
  · exact ⟨(c.1 + 1, c.2), by simp only [inBox]; omega, adjR c, by simp only [l1]; omega⟩
  by_cases h3 : c.2 < -R
  · exact ⟨(c.1 + 1, c.2), by simp only [inBox]; omega, adjR c, by simp only [l1]; omega⟩
  · exact ⟨(c.1, c.2 + 1), by simp only [inBox]; omega, adjU c, by simp only [l1]; omega⟩

/-- coordinatewise clamping into `[-R, R]` -/
def clampZ (R x : ℤ) : ℤ := if x < -R then -R else if R < x then R else x

lemma clampZ_spec (R x : ℤ) : (x < -R ∧ clampZ R x = -R) ∨ (-R ≤ x ∧ x ≤ R ∧ clampZ R x = x) ∨
    (-R ≤ x ∧ R < x ∧ clampZ R x = R) := by
  unfold clampZ; split_ifs <;> omega

lemma clampZ_step {R : ℤ} (hR : 0 ≤ R) (x y : ℤ) (h : y - x = 1 ∨ y - x = 0 ∨ y - x = -1) :
    clampZ R y = clampZ R x ∨ clampZ R y - clampZ R x = y - x := by
  rcases clampZ_spec R x with hx | hx | hx <;> rcases clampZ_spec R y with hy | hy | hy <;> omega

def clamp (R : ℤ) (c : Cell) : Cell := (clampZ R c.1, clampZ R c.2)

lemma clamp_adj {R : ℤ} (hR : 0 ≤ R) {a b : Cell} (h : dAdj a b) :
    clamp R a = clamp R b ∨ dAdj (clamp R a) (clamp R b) := by
  rw [dAdj_iff] at h ⊢
  simp only [clamp, Prod.ext_iff]
  have e1 := clampZ_step hR a.1 b.1 (by omega)
  have e2 := clampZ_step hR a.2 b.2 (by omega)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
  first
  | exact Or.inl ⟨by omega, by omega⟩
  | exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))

lemma clamp_inBox (R : ℤ) (hR : 0 ≤ R) (c : Cell) : inBox R (clamp R c) := by
  simp only [inBox, clamp]
  have := clampZ_spec R c.1; have := clampZ_spec R c.2; omega

lemma clamp_id {R : ℤ} {c : Cell} (h : inBox R c) : clamp R c = c := by
  simp only [inBox] at h
  have := clampZ_spec R c.1; have := clampZ_spec R c.2
  ext <;> simp only [clamp] <;> omega

lemma clamp_out {R : ℤ} (hR : 0 ≤ R) {c : Cell} (h : ¬ inBox (R + 1) c) : ¬ inBox R (clamp (R + 1) c) := by
  have := clampZ_spec (R + 1) c.1; have := clampZ_spec (R + 1) c.2
  simp only [inBox, clamp] at h ⊢; omega

/-- the contraction graph of a cell colouring -/
def Gphi {V : Type} (phi : Cell → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ c c', phi c = u ∧ phi c' = v ∧ dAdj c c'

/-- the box as a finset -/
noncomputable def boxF (R : ℤ) : Finset Cell := Finset.Icc (-R) R ×ˢ Finset.Icc (-R) R

lemma mem_boxF {R : ℤ} {c : Cell} : c ∈ boxF R ↔ inBox R c := by
  simp only [boxF, Finset.mem_product, Finset.mem_Icc, inBox]; tauto

/-- D4b-1: a cell colouring with one unbounded colour and Δ-connected fibres gives a Δ-model
of its contraction graph -/
theorem dModel_of_phi {V : Type} [DecidableEq V] (phi : Cell → V) (R : ℤ) (hR : 0 ≤ R) (q : V)
    (hout : ∀ c, ¬ inBox R c → phi c = q) (hsurj : ∀ v, ∃ c, phi c = v)
    (hconn : ∀ v c c', phi c = v → phi c' = v →
      Relation.ReflTransGen (PRel (fun x => phi x = v)) c c') :
    ∃ B : V → Finset Cell, (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (DRel (B v)) p q) ∧
      (∀ v, (B v).Nonempty) ∧ (∀ v w, (Gphi phi).Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, dAdj p q) := by
  classical
  have hR1 : 0 ≤ R + 1 := by omega
  have hpc : ∀ c, phi (clamp (R + 1) c) = phi c := by
    intro c
    by_cases h : inBox (R + 1) c
    · rw [clamp_id h]
    · rw [hout _ (clamp_out hR h), hout c (fun h' => h (by simp only [inBox] at h' ⊢; omega))]
  have memB : ∀ v x, x ∈ (boxF (R + 1)).filter (fun x => phi x = v) ↔ inBox (R + 1) x ∧ phi x = v := by
    intro v x; rw [Finset.mem_filter, mem_boxF]
  refine ⟨fun v => (boxF (R + 1)).filter (fun x => phi x = v), ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [memB] at hx hx'
    exact hvw (hx.2.symm.trans hx'.2)
  · intro v p hp p' hp'
    rw [memB] at hp hp'
    have h := hconn v p p' hp.2 hp'.2
    have key := rtg_map (r := DRel ((boxF (R + 1)).filter (fun x => phi x = v)))
      (clamp (R + 1)) (fun a b hab => by
        rcases clamp_adj hR1 hab.2.2 with he | hd
        · exact he ▸ Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single
            ⟨(memB v _).2 ⟨clamp_inBox _ hR1 a, (hpc a).trans hab.1⟩,
             (memB v _).2 ⟨clamp_inBox _ hR1 b, (hpc b).trans hab.2.1⟩, hd⟩) h
    rwa [clamp_id hp.1, clamp_id hp'.1] at key
  · intro v
    obtain ⟨c, hc⟩ := hsurj v
    exact ⟨clamp (R + 1) c, (memB v _).2 ⟨clamp_inBox _ hR1 c, (hpc c).trans hc⟩⟩
  · intro v w hvw
    rw [Gphi, SimpleGraph.fromRel_adj] at hvw
    obtain ⟨hne, hr⟩ := hvw
    have main : ∀ c c', phi c = v → phi c' = w → dAdj c c' →
        ∃ p ∈ (boxF (R + 1)).filter (fun x => phi x = v),
          ∃ q ∈ (boxF (R + 1)).filter (fun x => phi x = w), dAdj p q := by
      intro c c' hc hc' hcc
      rcases clamp_adj hR1 hcc with he | hd
      · exact absurd (show v = w by rw [← hc, ← hc', ← hpc c, ← hpc c', he]) hne
      · exact ⟨_, (memB v _).2 ⟨clamp_inBox _ hR1 c, (hpc c).trans hc⟩,
          _, (memB w _).2 ⟨clamp_inBox _ hR1 c', (hpc c').trans hc'⟩, hd⟩
    rcases hr with ⟨c, c', hc, hc', hcc⟩ | ⟨c, c', hc, hc', hcc⟩
    · exact main c c' hc hc' hcc
    · exact main c' c hc' hc (dAdj_symm hcc)

section Fill

variable {V : Type} [Fintype V] [DecidableEq V] (B : V → Finset Cell) (hne : ∀ v, (B v).Nonempty)

/-- L1 distance to a blob -/
noncomputable def dv (v : V) (c : Cell) : ℕ := (B v).inf' (hne v) (l1 c)

/-- Voronoi score: distance first, then a fixed index -/
noncomputable def sc (v : V) (c : Cell) : ℕ :=
  (Fintype.equivFin V v).val + dv B hne v c * Fintype.card V

lemma sc_inj (c : Cell) {v w : V} (h : sc B hne v c = sc B hne w c) : v = w := by
  have h1 := congrArg (· % Fintype.card V) h
  simp only [sc, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.isLt _)] at h1
  exact (Fintype.equivFin V).injective (Fin.ext h1)

variable [Nonempty V]

/-- the Voronoi owner of a cell -/
noncomputable def vor (c : Cell) : V :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun v => sc B hne v c) Finset.univ_nonempty)

lemma vor_spec (c : Cell) (w : V) : sc B hne (vor B hne c) c ≤ sc B hne w c :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ (fun v => sc B hne v c)
    Finset.univ_nonempty)).2 w (Finset.mem_univ w)

lemma vor_eq {c : Cell} {v : V} (h : ∀ w, sc B hne v c ≤ sc B hne w c) : vor B hne c = v :=
  sc_inj B hne c (le_antisymm (vor_spec B hne c v) (h _))

open Classical in
/-- the filling: Voronoi inside the box, the owner of the corner outside -/
noncomputable def phiF (R : ℤ) (c : Cell) : V :=
  if inBox R c then vor B hne c else vor B hne (R, R)

end Fill

/-- D4b: Voronoi filling of a grid model -/
theorem filling {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (hG : PQL5.HasGridModel G) :
    ∃ (phi : Cell → V) (R : ℤ) (q : V), 0 ≤ R ∧ (∀ c, ¬ inBox R c → phi c = q) ∧
      (∀ v, ∃ c, phi c = v) ∧
      (∀ v c c', phi c = v → phi c' = v → Relation.ReflTransGen (PRel (fun x => phi x = v)) c c') ∧
      G ≤ Gphi phi := by
  classical
  obtain ⟨B, hdisj, hconn, hne, hadj⟩ := hG
  obtain ⟨R, hR0, hRB⟩ : ∃ R : ℤ, 0 ≤ R ∧ ∀ v, ∀ p ∈ B v, inBox R p := by
    refine ⟨∑ v, ∑ p ∈ B v, (|p.1| + |p.2|),
      Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun p _ => by positivity)), fun v p hp => ?_⟩
    have h1 : |p.1| + |p.2| ≤ ∑ p ∈ B v, (|p.1| + |p.2|) :=
      Finset.single_le_sum (f := fun p : Cell => |p.1| + |p.2|) (fun p _ => by positivity) hp
    have h2 : ∑ p ∈ B v, (|p.1| + |p.2|) ≤ ∑ v, ∑ p ∈ B v, (|p.1| + |p.2|) :=
      Finset.single_le_sum (f := fun v => ∑ p ∈ B v, (|p.1| + |p.2|))
        (fun v _ => Finset.sum_nonneg (fun p _ => by positivity)) (Finset.mem_univ v)
    have a1 := abs_nonneg p.1
    have a2 := abs_nonneg p.2
    have b1 := le_abs_self p.1
    have b2 := neg_abs_le p.1
    have b3 := le_abs_self p.2
    have b4 := neg_abs_le p.2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdv_le : ∀ v c, ∀ p ∈ B v, dv B hne v c ≤ l1 c p := fun v c p hp => Finset.inf'_le _ hp
  have hdv_ex : ∀ v c, ∃ p ∈ B v, dv B hne v c = l1 c p := fun v c =>
    Finset.exists_mem_eq_inf' (hne v) (l1 c)
  -- blob cells are owned by their vertex
  have hvor_blob : ∀ v c, c ∈ B v → vor B hne c = v := by
    intro v c hc
    apply vor_eq
    intro w
    by_cases hw : w = v
    · rw [hw]
    · have h0 : dv B hne v c = 0 := Nat.le_zero.mp ((hdv_le v c c hc).trans (l1_self c).le)
      obtain ⟨p, hp, hpe⟩ := hdv_ex w c
      have hcp : c ≠ p := fun h => Finset.disjoint_left.mp (hdisj v w (Ne.symm hw)) hc (h ▸ hp)
      have h1 : 1 ≤ dv B hne w c := by rw [hpe]; exact l1_pos hcp
      have hN1 : Fintype.card V ≤ dv B hne w c * Fintype.card V := Nat.le_mul_of_pos_left _ h1
      have hv := (Fintype.equivFin V v).isLt
      simp only [sc, h0, zero_mul, add_zero]
      omega
  -- Voronoi descent step inside the box
  have hstep : ∀ v c, inBox R c → vor B hne c = v → c ∉ B v →
      ∃ c', inBox R c' ∧ vor B hne c' = v ∧ dAdj c c' ∧ dv B hne v c' < dv B hne v c := by
    intro v c hc hvc hcB
    obtain ⟨p, hp, hpe⟩ := hdv_ex v c
    have hcp : c ≠ p := fun h => hcB (h ▸ hp)
    obtain ⟨c', hadj', hl, hlip, hbox⟩ := step_toward c p hcp
    have hd1 : dv B hne v c' + 1 ≤ dv B hne v c := by
      have := hdv_le v c' p hp; omega
    refine ⟨c', hbox R hc (hRB v p hp), ?_, hadj', by omega⟩
    apply vor_eq
    intro w
    obtain ⟨p', hp', hpe'⟩ := hdv_ex w c'
    have hd2 : dv B hne w c ≤ dv B hne w c' + 1 := by
      have := hdv_le w c p' hp'; have := hlip p'; omega
    have hs := vor_spec B hne c w
    rw [hvc] at hs
    have m1 : (dv B hne v c' + 1) * Fintype.card V ≤ dv B hne v c * Fintype.card V := Nat.mul_le_mul_right _ hd1
    have m2 : dv B hne w c * Fintype.card V ≤ (dv B hne w c' + 1) * Fintype.card V := Nat.mul_le_mul_right _ hd2
    simp only [sc] at hs ⊢
    rw [add_mul, one_mul] at m1 m2
    omega
  set phi := phiF B hne R with hphi
  have phi_in : ∀ c, inBox R c → phi c = vor B hne c := fun c h => by
    rw [hphi, phiF, if_pos h]
  have phi_out : ∀ c, ¬ inBox R c → phi c = vor B hne (R, R) := fun c h => by
    rw [hphi, phiF, if_neg h]
  have hRR : inBox R (R, R) := by simp only [inBox]; omega
  have phi_blob : ∀ v c, c ∈ B v → phi c = v := fun v c hc =>
    (phi_in c (hRB v c hc)).trans (hvor_blob v c hc)
  -- blob connectivity
  have blob_rtg : ∀ v, ∀ p ∈ B v, ∀ p' ∈ B v,
      Relation.ReflTransGen (PRel (fun x => phi x = v)) p p' := by
    intro v p hp p' hp'
    have hc0 := hconn v p hp p' hp'
    induction hc0 with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
    obtain ⟨ha, hb, hg⟩ := hst
    refine (ih ha).tail ⟨phi_blob v _ ha, phi_blob v _ hb, ?_⟩
    rw [dAdj_iff]
    unfold gAdj at hg
    rcases hg with h | h | h | h <;> subst h <;> dsimp only <;> omega
  -- inside cells reach their blob
  have in_blob : ∀ v c, inBox R c → vor B hne c = v →
      ∃ t ∈ B v, Relation.ReflTransGen (PRel (fun x => phi x = v)) c t := by
    intro v c hc hvc
    obtain ⟨t, ht, hr⟩ := descent (fun x => inBox R x ∧ vor B hne x = v) (· ∈ B v) (dv B hne v)
      (fun x hx hT => by
        obtain ⟨c', h1, h2, h3, h4⟩ := hstep v x hx.1 hx.2 hT
        exact ⟨c', ⟨h1, h2⟩, h3, h4⟩) _ c rfl ⟨hc, hvc⟩
    exact ⟨t, ht, rtg_mono (fun x hx => (phi_in x hx.1).trans hx.2) hr⟩
  have to_blob : ∀ v c, phi c = v → ∃ t ∈ B v, Relation.ReflTransGen (PRel (fun x => phi x = v)) c t := by
    intro v c hc
    by_cases hb : inBox R c
    · exact in_blob v c hb ((phi_in c hb).symm.trans hc)
    · have hq : vor B hne (R, R) = v := (phi_out c hb).symm.trans hc
      obtain ⟨t, ht, hr⟩ := descent (fun x => ¬ inBox R x) (· = (R + 1, R + 1)) (fun x => l1 x (R + 1, R + 1))
        (fun x hx hT => out_step R hR0 x hx hT) _ c rfl hb
      subst ht
      have hr' := rtg_mono (fun x hx => (phi_out x hx).trans hq) hr
      have o1 : ¬ inBox R (R + 1, R + 1) := by simp only [inBox]; omega
      have o2 : ¬ inBox R (R + 1, R) := by simp only [inBox]; omega
      have s1 : PRel (fun x => phi x = v) (R + 1, R + 1) (R + 1, R) :=
        ⟨(phi_out _ o1).trans hq, (phi_out _ o2).trans hq, by
          have := adjD (R + 1, R + 1); simpa using this⟩
      have s2 : PRel (fun x => phi x = v) (R + 1, R) (R, R) :=
        ⟨(phi_out _ o2).trans hq, (phi_in _ hRR).trans hq, by
          have := adjL (R + 1, R); simpa using this⟩
      obtain ⟨t, ht, hr2⟩ := in_blob v (R, R) hRR hq
      exact ⟨t, ht, ((hr'.tail s1).tail s2).trans hr2⟩
  refine ⟨phi, R, vor B hne (R, R), hR0, phi_out, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨c, hc⟩ := hne v
    exact ⟨c, phi_blob v c hc⟩
  · intro v c c' hc hc'
    obtain ⟨t, ht, hr⟩ := to_blob v c hc
    obtain ⟨t', ht', hr'⟩ := to_blob v c' hc'
    exact (hr.trans (blob_rtg v t ht t' ht')).trans (rtg_symm hr')
  · intro u v huv
    rw [Gphi, SimpleGraph.fromRel_adj]
    refine ⟨G.ne_of_adj huv, Or.inl ?_⟩
    obtain ⟨p, hp, p', hp', hg⟩ := hadj u v huv
    refine ⟨p, p', phi_blob u p hp, phi_blob v p' hp', ?_⟩
    rw [dAdj_iff]
    unfold gAdj at hg
    rcases hg with h | h | h | h <;> subst h <;> dsimp only <;> omega

/-- D4b: filling plus a grid model of the contraction graph -/
theorem filling_model {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (hG : PQL5.HasGridModel G) :
    ∃ (phi : Cell → V) (R : ℤ) (q : V), 0 ≤ R ∧ (∀ c, ¬ inBox R c → phi c = q) ∧
      (∀ v, ∃ c, phi c = v) ∧
      (∀ v c c', phi c = v → phi c' = v → Relation.ReflTransGen (PRel (fun x => phi x = v)) c c') ∧
      G ≤ Gphi phi ∧ PQL5.HasGridModel (Gphi phi) := by
  obtain ⟨phi, R, q, hR, hout, hsurj, hconn, hle⟩ := filling G hG
  obtain ⟨B, h1, h2, h3, h4⟩ := dModel_of_phi phi R hR q hout hsurj hconn
  exact ⟨phi, R, q, hR, hout, hsurj, hconn, hle, gridModel_of_dModel _ B h1 h2 h3 h4⟩

end D4b

end PQT

/-! 8100c3d9 D5a: simple closed Δ-walks as lists, and the chord (theta) split lemma. -/

namespace PQT

section LW

/-- number of directed steps `a → b` of an open cell path -/
def ecount (a b : Cell) : List Cell → ℕ
  | x :: y :: t => (if x = a ∧ y = b then 1 else 0) + ecount a b (y :: t)
  | _ => 0

lemma ecount_nil (a b : Cell) : ecount a b [] = 0 := by simp [ecount]

lemma ecount_single (a b x : Cell) : ecount a b [x] = 0 := by simp [ecount]

lemma ecount_cons (a b x : Cell) (l : List Cell) :
    ecount a b (x :: l) = (if x = a ∧ l.head? = some b then 1 else 0) + ecount a b l := by
  cases l with
  | nil => simp [ecount]
  | cons y t => simp [ecount]

lemma ecount_glue (a b z : Cell) (L1 L2 : List Cell) :
    ecount a b (L1 ++ z :: L2) = ecount a b (L1 ++ [z]) + ecount a b (z :: L2) := by
  induction L1 with
  | nil => simp [ecount_single]
  | cons w t ih =>
    simp only [List.cons_append]
    rw [ecount_cons a b w (t ++ z :: L2), ecount_cons a b w (t ++ [z]), ih, add_assoc]
    congr 1
    cases t <;> simp

lemma ecount_snoc (a b z : Cell) (l : List Cell) :
    ecount a b (l ++ [z]) = ecount a b l + (if l.getLast? = some a ∧ z = b then 1 else 0) := by
  induction l with
  | nil => simp [ecount_single, ecount_nil]
  | cons w t ih =>
    rw [List.cons_append, ecount_cons a b w (t ++ [z]), ecount_cons a b w t, ih]
    cases t with
    | nil => simp [ecount_nil]
    | cons u t' =>
      simp only [List.cons_append, List.head?_cons, List.getLast?_cons_cons]
      ac_rfl

lemma ecount_reverse (a b : Cell) (l : List Cell) : ecount a b l.reverse = ecount b a l := by
  induction l with
  | nil => simp [ecount_nil]
  | cons x t ih =>
    rw [List.reverse_cons, ecount_snoc, ih, ecount_cons, List.getLast?_reverse, add_comm]
    congr 1
    by_cases h1 : x = b <;> by_cases h2 : t.head? = some a <;> simp [h1, h2]

lemma ecount_zero_of_not_mem (a b : Cell) (l : List Cell) (h : a ∉ l.dropLast) : ecount a b l = 0 := by
  induction l with
  | nil => simp [ecount_nil]
  | cons x t ih =>
    cases t with
    | nil => simp [ecount_single]
    | cons u t' =>
      rw [List.dropLast_cons₂, List.mem_cons, not_or] at h
      rw [ecount_cons, ih h.2, if_neg (fun hh => h.1 hh.1.symm)]

lemma ecount_le_one (a b : Cell) (l : List Cell) (h : l.dropLast.Nodup) : ecount a b l ≤ 1 := by
  induction l with
  | nil => simp [ecount_nil]
  | cons x t ih =>
    cases t with
    | nil => simp [ecount_single]
    | cons u t' =>
      rw [List.dropLast_cons₂, List.nodup_cons] at h
      rw [ecount_cons]
      by_cases hx : x = a
      · subst hx
        rw [ecount_zero_of_not_mem _ _ _ h.1]; split_ifs <;> omega
      · rw [if_neg (fun hh => hx hh.1)]; have := ih h.2; omega

lemma ecount_pos_iff (a b : Cell) (l : List Cell) :
    0 < ecount a b l ↔ ∃ i, ∃ h : i + 1 < l.length, l[i] = a ∧ l[i + 1] = b := by
  induction l with
  | nil => simp [ecount_nil]
  | cons x t ih =>
    rw [ecount_cons]
    constructor
    · intro hpos
      by_cases hx : x = a ∧ t.head? = some b
      · obtain ⟨rfl, hb⟩ := hx
        cases t with
        | nil => simp at hb
        | cons u t' =>
          simp only [List.head?_cons, Option.some.injEq] at hb
          exact ⟨0, by simp, rfl, by simp [hb]⟩
      · rw [if_neg hx, zero_add] at hpos
        obtain ⟨i, hi, h1, h2⟩ := ih.1 hpos
        exact ⟨i + 1, by simp; omega, by simpa using h1, by simpa using h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      cases i with
      | zero =>
        cases t with
        | nil => simp at hi
        | cons u t' =>
          have : x = a ∧ (u :: t').head? = some b := ⟨by simpa using h1, by simpa using h2⟩
          rw [if_pos this]; omega
      | succ j =>
        have := ih.2 ⟨j, by simp at hi; omega, by simpa using h1, by simpa using h2⟩
        omega

/-- directed steps of a closed walk (closing step last → first) -/
def ecountC (a b : Cell) (l : List Cell) : ℕ := ecount a b (l ++ l.take 1)

lemma ecountC_le_one (a b : Cell) (l : List Cell) (h : l.Nodup) : ecountC a b l ≤ 1 := by
  unfold ecountC
  cases l with
  | nil => simp [ecount_nil]
  | cons x t =>
    apply ecount_le_one
    simp only [List.take_succ_cons, List.take_zero]
    rw [List.dropLast_concat]; exact h

lemma closed_get (l : List Cell) (i : ℕ) (hi : i < l.length) (h1 : i < (l ++ l.take 1).length) :
    (l ++ l.take 1)[i] = l[i] := by
  rw [List.getElem_append_left hi]

lemma closed_get_succ (l : List Cell) (i : ℕ) (hi : i < l.length)
    (h1 : i + 1 < (l ++ l.take 1).length) (h2 : (i + 1) % l.length < l.length) :
    (l ++ l.take 1)[i + 1] = l[(i + 1) % l.length] := by
  rw [List.getElem_append]
  split_ifs with h
  · simp only [Nat.mod_eq_of_lt h]
  · have he : i + 1 = l.length := by omega
    simp only [he, Nat.mod_self, Nat.sub_self]
    simp [List.getElem_take]

lemma ecountC_pos_iff (a b : Cell) (l : List Cell) (hl : 0 < l.length) :
    0 < ecountC a b l ↔ ∃ i, ∃ hi : i < l.length,
      l[i] = a ∧ l[(i + 1) % l.length]'(Nat.mod_lt _ hl) = b := by
  unfold ecountC
  rw [ecount_pos_iff]
  have hlen : (l ++ l.take 1).length = l.length + 1 := by
    simp; omega
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    have hi' : i < l.length := by omega
    refine ⟨i, hi', ?_, ?_⟩
    · rw [← closed_get l i hi' (by omega)]; exact h1
    · rw [← closed_get_succ l i hi' (by omega)]; exact h2
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, by omega, by rw [closed_get l i hi]; exact h1,
      by rw [closed_get_succ l i hi]; exact h2⟩

/-- a simple closed Δ-walk given as a list -/
def LSimple (l : List Cell) : Prop :=
  l.Nodup ∧ 3 ≤ l.length ∧ ∀ a b, 0 < ecountC a b l → dAdj a b

/-- `S` is a boundary chain of the list walk -/
def LBd (S : Tri → Bool) (l : List Cell) : Prop :=
  IsBd S (fun a b => 0 < ecountC a b l ∨ 0 < ecountC b a l)

/-- `S` contains the left triangle of every step -/
def LNorm (S : Tri → Bool) (l : List Cell) : Prop :=
  ∀ a k, 0 < ecountC a (a + dir k) l → S (triAt a k) = true

lemma LSimple.ne {l : List Cell} (h : LSimple l) : NeZero l.length := ⟨by have := h.2.1; omega⟩

lemma fin_succ_val {m : ℕ} [NeZero m] (h3 : 3 ≤ m) (i : Fin m) : (i + 1).val = (i.val + 1) % m := by
  rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.mpr (by omega)]

/-- the list walk as an `SWalk` -/
noncomputable def LSimple.toW {l : List Cell} (h : LSimple l) : @SWalk l.length h.ne := by
  haveI := h.ne
  refine ⟨fun i => l[i.val], fun i j hij => Fin.ext ((h.1.getElem_inj_iff).1 hij), h.2.1, fun i => ?_⟩
  have hp : 0 < ecountC l[i.val] l[(i + 1).val] l := by
    rw [ecountC_pos_iff _ _ _ (by have := h.2.1; omega)]
    exact ⟨i.val, i.isLt, rfl, by simp only [fin_succ_val h.2.1]⟩
  exact h.2.2 _ _ hp

lemma LSimple.fwd_iff {l : List Cell} (h : LSimple l) (a b : Cell) :
    @SWalk.Fwd l.length h.ne h.toW a b ↔ 0 < ecountC a b l := by
  haveI := h.ne
  have hl : 0 < l.length := by have := h.2.1; omega
  rw [ecountC_pos_iff _ _ _ hl]
  constructor
  · rintro ⟨i, h1, h2⟩
    refine ⟨i.val, i.isLt, h1, ?_⟩
    rw [← h2]
    show l[(i.val + 1) % l.length]'(Nat.mod_lt _ hl) = l[(i + 1).val]
    simp only [fin_succ_val h.2.1]
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨⟨i, hi⟩, h1, ?_⟩
    rw [← h2]
    show l[((⟨i, hi⟩ : Fin l.length) + 1).val] = _
    simp only [fin_succ_val h.2.1]

lemma LSimple.we_iff {l : List Cell} (h : LSimple l) (a b : Cell) :
    @SWalk.WE l.length h.ne h.toW a b ↔ (0 < ecountC a b l ∨ 0 < ecountC b a l) := by
  rw [← h.fwd_iff, ← h.fwd_iff]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨i, h1, h2⟩
    · exact Or.inr ⟨i, h1, h2⟩
  · rintro (⟨i, h1, h2⟩ | ⟨i, h1, h2⟩)
    · exact ⟨i, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨i, Or.inr ⟨h1, h2⟩⟩

/-- Bool as a 0/1 integer -/
def bz (b : Bool) : ℤ := if b then 1 else 0

/-- integer jump of a normalised boundary chain across an edge = the walk flow -/
theorem ljump {l : List Cell} (h : LSimple l) {S : Tri → Bool} (hS : LBd S l) (hN : LNorm S l)
    (a : Cell) (k : Fin 6) :
    bz (S (triAt a k)) - bz (S (triAt a (k - 1))) =
      (ecountC a (a + dir k) l : ℤ) - ecountC (a + dir k) a l := by
  haveI := h.ne
  have hS' : IsBd S (h.toW).WE := fun a k => (hS a k).trans (h.we_iff _ _).symm
  have hL' : ∀ i, S ((h.toW).left i) = true := by
    intro i
    apply hN
    rw [← h.fwd_iff]
    exact ⟨i, rfl, (h.toW).kOut_spec i⟩
  have u1 := ecountC_le_one a (a + dir k) l h.1
  have u2 := ecountC_le_one (a + dir k) a l h.1
  rcases (h.toW).jump hS' hL' a k with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have h4 : ¬ (h.toW).Fwd (a + dir k) a := fun h4 => (h.toW).not_fwd_both h3 h4
    rw [h.fwd_iff] at h3 h4
    rw [h1, h2]; simp only [bz]; push_cast; omega
  · have h4 : ¬ (h.toW).Fwd a (a + dir k) := fun h4 => (h.toW).not_fwd_both h3 h4
    rw [h.fwd_iff] at h3 h4
    rw [h1, h2]; simp only [bz]; push_cast; omega
  · rw [h.fwd_iff] at h2 h3
    rw [h1]; push_cast; omega

/-- existence of a normalised boundary chain for every simple list walk (proved from D1/D2) -/
def ExistsBd : Prop := ∀ l : List Cell, LSimple l → ∃ S, LBd S l ∧ LNorm S l

/-- CHORD SPLIT: a chord `x, Q, y` inside a simple closed walk `x, M, y, B` splits its normalised
region into the regions of `x, M, y, rev Q` and `y, B, x, Q`. -/
theorem chord_split (hex : ExistsBd) (x y : Cell) (M B Q : List Cell) (S : Tri → Bool)
    (hW : LSimple (x :: (M ++ y :: B)))
    (hS : LBd S (x :: (M ++ y :: B))) (hN : LNorm S (x :: (M ++ y :: B)))
    (hQ : Q.Nodup) (hQW : ∀ z ∈ Q, z ∉ x :: (M ++ y :: B))
    (hP : ∀ a b, 0 < ecount a b (x :: (Q ++ [y])) → dAdj a b)
    (hd1 : M ≠ [] ∨ Q ≠ []) (hd2 : B ≠ [] ∨ Q ≠ [])
    (k : Fin 6) (hk : (Q ++ [y]).head? = some (x + dir k)) (hin : S (triAt x k) = true) :
    ∃ S1 S2 : Tri → Bool,
      LSimple (x :: (M ++ y :: Q.reverse)) ∧ LBd S1 (x :: (M ++ y :: Q.reverse)) ∧
        LNorm S1 (x :: (M ++ y :: Q.reverse)) ∧
      LSimple (y :: (B ++ x :: Q)) ∧ LBd S2 (y :: (B ++ x :: Q)) ∧ LNorm S2 (y :: (B ++ x :: Q)) ∧
      ∀ τ, bz (S τ) = bz (S1 τ) + bz (S2 τ) := by
  -- edge counts
  have e0 : ∀ a b, ecountC a b (x :: (M ++ y :: B)) =
      ecount a b ((x :: M) ++ [y]) + ecount a b (y :: (B ++ [x])) := by
    intro a b
    have : (x :: (M ++ y :: B)) ++ (x :: (M ++ y :: B)).take 1 = (x :: M) ++ y :: (B ++ [x]) := by simp
    rw [ecountC, this, ecount_glue]
  have e1 : ∀ a b, ecountC a b (x :: (M ++ y :: Q.reverse)) =
      ecount a b ((x :: M) ++ [y]) + ecount b a (x :: (Q ++ [y])) := by
    intro a b
    have : (x :: (M ++ y :: Q.reverse)) ++ (x :: (M ++ y :: Q.reverse)).take 1 =
        (x :: M) ++ y :: (Q.reverse ++ [x]) := by simp
    have h2 : y :: (Q.reverse ++ [x]) = (x :: (Q ++ [y])).reverse := by simp
    rw [ecountC, this, ecount_glue, h2, ecount_reverse]
  have e2 : ∀ a b, ecountC a b (y :: (B ++ x :: Q)) =
      ecount a b (y :: (B ++ [x])) + ecount a b (x :: (Q ++ [y])) := by
    intro a b
    have : (y :: (B ++ x :: Q)) ++ (y :: (B ++ x :: Q)).take 1 = (y :: B) ++ x :: (Q ++ [y]) := by simp
    rw [ecountC, this, ecount_glue, List.cons_append]
  -- membership facts
  have hWn := hW.1
  have hA : (x :: (M ++ [y])).Nodup := by
    have : x :: (M ++ y :: B) = (x :: (M ++ [y])) ++ B := by simp
    rw [this] at hWn; exact hWn.of_append_left
  have hB : (y :: (B ++ [x])).Nodup := by
    have h0 := hW.1
    simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons, List.mem_singleton,
      not_or] at h0 ⊢
    aesop
  have hl1 : (x :: (M ++ y :: Q.reverse)).length = M.length + Q.length + 2 := by simp; omega
  have hl2 : (y :: (B ++ x :: Q)).length = B.length + Q.length + 2 := by simp; omega
  have hd1' : 1 ≤ M.length ∨ 1 ≤ Q.length := by
    rcases hd1 with h | h
    · left; exact List.length_pos_of_ne_nil h
    · right; exact List.length_pos_of_ne_nil h
  have hd2' : 1 ≤ B.length ∨ 1 ≤ Q.length := by
    rcases hd2 with h | h
    · left; exact List.length_pos_of_ne_nil h
    · right; exact List.length_pos_of_ne_nil h
  have hW1 : LSimple (x :: (M ++ y :: Q.reverse)) := by
    refine ⟨?_, by omega, ?_⟩
    · have : x :: (M ++ y :: Q.reverse) = (x :: (M ++ [y])) ++ Q.reverse := by simp
      rw [this, List.nodup_append]
      refine ⟨hA, List.nodup_reverse.2 hQ, ?_⟩
      intro a ha b hb hab
      subst hab
      rw [List.mem_reverse] at hb
      apply hQW a hb
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · intro a b hab
      rw [e1] at hab
      rcases Nat.eq_zero_or_pos (ecount a b ((x :: M) ++ [y])) with h0 | h0
      · rw [h0, zero_add] at hab; exact dAdj_symm (hP b a hab)
      · exact hW.2.2 a b (by rw [e0]; omega)
  have hW2 : LSimple (y :: (B ++ x :: Q)) := by
    refine ⟨?_, by omega, ?_⟩
    · have : y :: (B ++ x :: Q) = (y :: (B ++ [x])) ++ Q := by simp
      rw [this, List.nodup_append]
      refine ⟨hB, hQ, ?_⟩
      intro a ha b hb hab
      subst hab
      apply hQW a hb
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
    · intro a b hab
      rw [e2] at hab
      rcases Nat.eq_zero_or_pos (ecount a b (y :: (B ++ [x]))) with h0 | h0
      · rw [h0, zero_add] at hab; exact hP a b hab
      · exact hW.2.2 a b (by rw [e0]; omega)
  obtain ⟨S1, hS1, hN1⟩ := hex _ hW1
  obtain ⟨S2, hS2, hN2⟩ := hex _ hW2
  refine ⟨S1, S2, hW1, hS1, hN1, hW2, hS2, hN2, ?_⟩
  have hJ : ∀ a b, (ecountC a b (x :: (M ++ y :: B)) : ℤ) - ecountC b a (x :: (M ++ y :: B)) =
      ((ecountC a b (x :: (M ++ y :: Q.reverse)) : ℤ) - ecountC b a (x :: (M ++ y :: Q.reverse))) +
      ((ecountC a b (y :: (B ++ x :: Q)) : ℤ) - ecountC b a (y :: (B ++ x :: Q))) := by
    intro a b; rw [e0, e0, e1, e1, e2, e2]; push_cast; ring
  have hjf : ∀ a k, (fun τ => bz (S τ) - bz (S1 τ) - bz (S2 τ)) (triAt a k) =
      (fun τ => bz (S τ) - bz (S1 τ) - bz (S2 τ)) (triAt a (k - 1)) := by
    intro a k
    have j0 := ljump hW hS hN a k
    have j1 := ljump hW1 hS1 hN1 a k
    have j2 := ljump hW2 hS2 hN2 a k
    have := hJ a (a + dir k)
    simp only
    linarith
  have hc := const_of_jumpfree (fun τ => bz (S τ) - bz (S1 τ) - bz (S2 τ)) hjf
  -- evaluate at the triangle left of the first chord step
  have hpos : 0 < ecount x (x + dir k) (x :: (Q ++ [y])) := by
    rw [ecount_cons, if_pos ⟨rfl, hk⟩]; omega
  have hs2 : S2 (triAt x k) = true := hN2 x k (by rw [e2]; omega)
  have hs1' : S1 (triAt x (k - 1)) = true := by
    have h3 : (x + dir k) + dir (k + 3) = x := by rw [dir_add3]; abel
    have := hN1 (x + dir k) (k + 3) (by rw [h3, e1]; omega)
    rwa [triAt_add3] at this
  have hs1 : S1 (triAt x k) = false := by
    have hb := (hS1 x k).2 (Or.inr (by rw [e1]; omega))
    rw [hs1'] at hb
    simpa using hb
  have h0 : bz (S (triAt x k)) - bz (S1 (triAt x k)) - bz (S2 (triAt x k)) = 0 := by
    rw [hin, hs1, hs2]; simp [bz]
  intro τ
  have a1 := hc τ
  have a2 := hc (triAt x k)
  linarith

end LW

end PQT

/-! 8100c3d9 D5a': every simple list walk has a normalised boundary chain (from D1/D2). -/

namespace PQT

theorem lexists : ExistsBd := by
  intro l h
  haveI := h.ne
  obtain ⟨S0, hS0⟩ := (h.toW).exists_bd
  obtain ⟨S, hS, hL⟩ := (h.toW).normalize hS0
  refine ⟨S, fun a k => (hS a k).trans (h.we_iff _ _), ?_⟩
  intro a k hp
  rw [← h.fwd_iff] at hp
  obtain ⟨i, h1, h2⟩ := hp
  have hk : (h.toW).kOut i = k := (h.toW).kOut_eq (by rw [h2, h1])
  have := hL i
  rw [SWalk.left, hk, h1] at this
  exact this

end PQT

/-! 8100c3d9 D6a: treewidth ≤ 3 from a parent function (elimination-tree decomposition). -/

namespace PQT

section TWPAR

open RobertsonSeymour1986.GM5

variable {W : Type} [Fintype W] [DecidableEq W]

/-- the parent tree -/
def parTree (w0 : W) (par : W → W) : SimpleGraph W :=
  SimpleGraph.fromRel fun a b => a ≠ w0 ∧ b = par a

lemma parTree_adj {w0 : W} {par : W → W} {ρ : W → ℕ} (hρ : ∀ w, w ≠ w0 → ρ (par w) < ρ w)
    {w : W} (hw : w ≠ w0) : (parTree w0 par).Adj w (par w) := by
  rw [parTree, SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, Or.inl ⟨hw, rfl⟩⟩
  have := hρ w hw
  rw [← h] at this
  exact lt_irrefl _ this

lemma up_walk {w0 : W} {par : W → W} {ρ : W → ℕ} (hρ : ∀ w, w ≠ w0 → ρ (par w) < ρ w)
    (C : W → Prop) (u : W) (hC : ∀ w, C w → w ≠ u → w ≠ w0 ∧ C (par w)) :
    ∀ n w, ρ w = n → C w → ∃ q : (parTree w0 par).Walk w u, ∀ x ∈ q.support, C x := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro w hn hw
  by_cases hu : w = u
  · subst hu
    exact ⟨SimpleGraph.Walk.nil, fun x hx => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx; rw [hx]; exact hw⟩
  · obtain ⟨h0, hp⟩ := hC w hw hu
    obtain ⟨q, hq⟩ := ih (ρ (par w)) (by rw [← hn]; exact hρ w h0) (par w) rfl hp
    refine ⟨SimpleGraph.Walk.cons (parTree_adj hρ h0) q, fun x hx => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hw
    · exact hq x hx

theorem parTree_isTree {w0 : W} {par : W → W} {ρ : W → ℕ} (hρ : ∀ w, w ≠ w0 → ρ (par w) < ρ w) :
    (parTree w0 par).IsTree := by
  classical
  have hconn : (parTree w0 par).Connected := by
    haveI : Nonempty W := ⟨w0⟩
    rw [SimpleGraph.connected_iff]
    refine ⟨fun a b => ?_, inferInstance⟩
    obtain ⟨qa, -⟩ := up_walk hρ (fun _ => True) w0 (fun w _ hw => ⟨hw, trivial⟩) _ a rfl trivial
    obtain ⟨qb, -⟩ := up_walk hρ (fun _ => True) w0 (fun w _ hw => ⟨hw, trivial⟩) _ b rfl trivial
    exact ⟨qa.append qb.reverse⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  let f : {w : W // w ≠ w0} → (parTree w0 par).edgeSet := fun w =>
    ⟨s(w.1, par w.1), parTree_adj hρ w.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have h' : s(a, par a) = s(b, par b) := congrArg Subtype.val hab
      rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h1
      · exfalso
        have x1 := hρ a ha
        have x2 := hρ b hb
        rw [← h1] at x2
        rw [h2] at x1
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h a b =>
        rw [SimpleGraph.mem_edgeSet, parTree, SimpleGraph.fromRel_adj] at he
        rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨⟨a, h1⟩, by simp only [f, h2]⟩
        · exact ⟨⟨b, h1⟩, by simp only [f, h2, Sym2.eq_swap]⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.filter_ne' Finset.univ w0, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  have : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨w0⟩
  omega

/-- treewidth ≤ 3 from a parent function: bags `{w} ∪ N w`, `N w ⊆ {par w} ∪ N (par w)` -/
theorem tw_of_par (H : SimpleGraph W) (w0 : W) (par : W → W) (ρ : W → ℕ)
    (hρ : ∀ w, w ≠ w0 → ρ (par w) < ρ w)
    (N : W → Finset W) (hN0 : N w0 = ∅) (hNc : ∀ w, (N w).card ≤ 3)
    (hNp : ∀ w, w ≠ w0 → N w ⊆ insert (par w) (N (par w)))
    (hadj : ∀ a b, H.Adj a b → a ∈ N b ∨ b ∈ N a) :
    TreewidthLE H 3 := by
  classical
  have hT := parTree_isTree (w0 := w0) (par := par) hρ
  refine ⟨W, inferInstance, parTree w0 par, fun w => insert w (N w), ⟨hT, ?_, ?_, ?_⟩, ?_⟩
  · intro v; exact ⟨v, Finset.mem_insert_self _ _⟩
  · intro a b hab
    rcases hadj a b hab with h | h
    · exact ⟨b, Finset.mem_insert_of_mem h, Finset.mem_insert_self _ _⟩
    · exact ⟨a, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem h⟩
  · intro s s' s'' p hp hs' u hu
    rw [Finset.mem_inter] at hu
    have hC : ∀ w, u ∈ insert w (N w) → w ≠ u → w ≠ w0 ∧ u ∈ insert (par w) (N (par w)) := by
      intro w hw hwu
      rw [Finset.mem_insert] at hw
      rcases hw with hw | hw
      · exact absurd hw.symm hwu
      · refine ⟨fun h => ?_, hNp w ?_ hw⟩
        · subst h; rw [hN0] at hw; simp at hw
        · intro h; subst h; rw [hN0] at hw; simp at hw
    obtain ⟨q1, hq1⟩ := up_walk hρ (fun w => u ∈ insert w (N w)) u hC _ s rfl hu.1
    obtain ⟨q2, hq2⟩ := up_walk hρ (fun w => u ∈ insert w (N w)) u hC _ s'' rfl hu.2
    let q := q1.append q2.reverse
    have huniq := hT.IsAcyclic.path_unique ⟨p, hp⟩ ⟨q.bypass, q.bypass_isPath⟩
    have hpq : p = q.bypass := congrArg Subtype.val huniq
    rw [hpq] at hs'
    have hs2 := SimpleGraph.Walk.support_bypass_subset q hs'
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hs2
    rcases hs2 with h | h
    · exact hq1 s' h
    · exact hq2 s' h
  · intro w
    exact (Finset.card_insert_le _ _).trans (by have := hNc w; omega)

end TWPAR

end PQT

/-! 8100c3d9 D5b: rotation invariance of list walks; side of a non-walk cell. -/

namespace PQT

section LWR

lemma ecountC_rotate1 (a b x : Cell) (t : List Cell) : ecountC a b (t ++ [x]) = ecountC a b (x :: t) := by
  cases t with
  | nil => rfl
  | cons u t' =>
    unfold ecountC
    have h1 : (u :: t') ++ [x] ++ ((u :: t') ++ [x]).take 1 = (u :: t') ++ x :: [u] := by simp
    have h2 : (x :: u :: t') ++ (x :: u :: t').take 1 = x :: ((u :: t') ++ [x]) := by simp
    rw [h1, h2, ecount_glue, show ecount a b [x, u] = if x = a ∧ u = b then 1 else 0 by simp [ecount],
      ecount_cons a b x ((u :: t') ++ [x]), List.cons_append, List.head?_cons]
    generalize ecount a b (u :: (t' ++ [x])) = E
    split_ifs <;> simp_all <;> omega

lemma ecountC_rotate (a b : Cell) (l : List Cell) (n : ℕ) : ecountC a b (l.rotate n) = ecountC a b l := by
  induction n with
  | zero => rw [List.rotate_zero]
  | succ n ih =>
    rw [← List.rotate_rotate, ← ih]
    cases h : l.rotate n with
    | nil => rfl
    | cons x t => rw [List.rotate_cons_succ, List.rotate_zero, ecountC_rotate1]

lemma LSimple.rotate {l : List Cell} (h : LSimple l) (n : ℕ) : LSimple (l.rotate n) :=
  ⟨(List.nodup_rotate).2 h.1, by rw [List.length_rotate]; exact h.2.1,
    fun a b hab => h.2.2 a b (by rwa [ecountC_rotate] at hab)⟩

lemma LBd.rotate {S : Tri → Bool} {l : List Cell} (h : LBd S l) (n : ℕ) : LBd S (l.rotate n) := by
  intro a k
  rw [h a k]; simp only [ecountC_rotate]

lemma LNorm.rotate {S : Tri → Bool} {l : List Cell} (h : LNorm S l) (n : ℕ) : LNorm S (l.rotate n) :=
  fun a k hp => h a k (by rwa [ecountC_rotate] at hp)

lemma ecountC_mem {a b : Cell} {l : List Cell} (h : 0 < ecountC a b l) : a ∈ l ∧ b ∈ l := by
  unfold ecountC at h
  rw [ecount_pos_iff] at h
  obtain ⟨i, hi, h1, h2⟩ := h
  have m1 : a ∈ l ++ l.take 1 := h1 ▸ List.getElem_mem _
  have m2 : b ∈ l ++ l.take 1 := h2 ▸ List.getElem_mem _
  rw [List.mem_append] at m1 m2
  exact ⟨m1.elim id (fun h => List.mem_of_mem_take h), m2.elim id (fun h => List.mem_of_mem_take h)⟩

/-- the six triangles at a non-walk cell lie on one side -/
lemma side_const {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {c : Cell} (hc : c ∉ l) (k : Fin 6) :
    S (triAt c k) = S (triAt c 0) := by
  have e : ∀ j : Fin 6, S (triAt c (j + 1)) = S (triAt c j) := by
    intro j
    by_contra hne
    have := (hS c (j + 1)).1 (by rwa [add_sub_cancel_right])
    rcases this with h | h
    · exact hc (ecountC_mem h).1
    · exact hc (ecountC_mem h).2
  fin_cases k
  · rfl
  · exact e 0
  · exact (e 1).trans (e 0)
  · exact (e 2).trans ((e 1).trans (e 0))
  · exact (e 3).trans ((e 2).trans ((e 1).trans (e 0)))
  · exact (e 4).trans ((e 3).trans ((e 2).trans ((e 1).trans (e 0))))

/-- Δ-adjacent non-walk cells lie on the same side -/
lemma side_adj {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {c d : Cell} (hc : c ∉ l) (hd : d ∉ l)
    (k : Fin 6) (hcd : d = c + dir k) : S (triAt d 0) = S (triAt c 0) := by
  rw [← side_const hS hc k, ← side_const hS hd (k + 2), hcd, triAt_add2]

end LWR

end PQT

/-! 8100c3d9 D6b: abstract assembly of the region recursion. A region type with interior
vertex sets `I`, outer parts `Qs` (≤ 3), and a step lemma (tripod `Y0` + child regions of
smaller measure) yields a partition into `Ok` parts whose quotient has treewidth ≤ 3. -/

namespace PQT

section ASM

open RobertsonSeymour1986.GM5

variable {V : Type} [Fintype V] [DecidableEq V]

/-- a decomposition of the vertex set `A` relative to the outer parts `QS` -/
def Dec (H : SimpleGraph V) (Ok : Finset V → Prop) (A : Finset V) (QS : Finset (Finset V)) :
    Prop :=
  ∃ (Ps : Finset (Finset V)) (N : Finset V → Finset (Finset V)) (par : Finset V → Finset V)
    (rk : Finset V → ℕ),
    (∀ Y ∈ Ps, Ok Y ∧ Y.Nonempty ∧ Y ⊆ A) ∧
    (∀ Y ∈ Ps, ∀ Z ∈ Ps, Y ≠ Z → Disjoint Y Z) ∧
    (∀ v ∈ A, ∃ Y ∈ Ps, v ∈ Y) ∧
    (∀ Y ∈ Ps, N Y ⊆ Ps ∪ QS ∧ (N Y).card ≤ 3) ∧
    (∀ Y ∈ Ps, N Y ⊆ QS ∨ (par Y ∈ Ps ∧ rk (par Y) < rk Y ∧ N Y ⊆ insert (par Y) (N (par Y)))) ∧
    (∀ Y ∈ Ps, ∀ y ∈ Y, ∀ w, H.Adj y w →
      (∃ Z ∈ Ps, w ∈ Z ∧ (Y = Z ∨ Y ∈ N Z ∨ Z ∈ N Y)) ∨ (w ∉ A ∧ ∃ Q ∈ N Y, w ∈ Q))

lemma Dec_empty (H : SimpleGraph V) (Ok : Finset V → Prop) (QS : Finset (Finset V)) :
    Dec H Ok ∅ QS :=
  ⟨∅, fun _ => ∅, id, fun _ => 0, by simp, by simp, by simp, by simp, by simp, by simp⟩

lemma Dec_mono {H : SimpleGraph V} {Ok : Finset V → Prop} {A : Finset V}
    {QS QS' : Finset (Finset V)} (h : Dec H Ok A QS) (hs : QS ⊆ QS') : Dec H Ok A QS' := by
  obtain ⟨Ps, N, par, rk, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Ps, N, par, rk, h1, h2, h3,
    fun Y hY => ⟨(h4 Y hY).1.trans (Finset.union_subset_union (subset_refl _) hs), (h4 Y hY).2⟩,
    fun Y hY => (h5 Y hY).imp_left (fun h => h.trans hs), h6⟩

lemma Dec_union {H : SimpleGraph V} {Ok : Finset V → Prop} {A1 A2 : Finset V}
    {QS1 QS2 : Finset (Finset V)} (d1 : Dec H Ok A1 QS1) (d2 : Dec H Ok A2 QS2)
    (hA : Disjoint A1 A2) (hq1 : ∀ Q ∈ QS1, Disjoint Q A2) (hq2 : ∀ Q ∈ QS2, Disjoint Q A1) :
    Dec H Ok (A1 ∪ A2) (QS1 ∪ QS2) := by
  classical
  obtain ⟨P1, N1, par1, rk1, a1, b1, c1, e1, f1, g1⟩ := d1
  obtain ⟨P2, N2, par2, rk2, a2, b2, c2, e2, f2, g2⟩ := d2
  have hn : ∀ Y ∈ P1, Y ∉ P2 := by
    intro Y h1 h2
    obtain ⟨v, hv⟩ := (a1 Y h1).2.1
    exact Finset.disjoint_left.1 hA ((a1 Y h1).2.2 hv) ((a2 Y h2).2.2 hv)
  let N : Finset V → Finset (Finset V) := fun Y => if Y ∈ P1 then N1 Y else N2 Y
  let par : Finset V → Finset V := fun Y => if Y ∈ P1 then par1 Y else par2 Y
  let rk : Finset V → ℕ := fun Y => if Y ∈ P1 then rk1 Y else rk2 Y
  have hN1 : ∀ Y ∈ P1, N Y = N1 Y := fun Y h => if_pos h
  have hN2 : ∀ Y ∈ P2, N Y = N2 Y := fun Y h => if_neg (fun h1 => hn Y h1 h)
  have hp1 : ∀ Y ∈ P1, par Y = par1 Y := fun Y h => if_pos h
  have hp2 : ∀ Y ∈ P2, par Y = par2 Y := fun Y h => if_neg (fun h1 => hn Y h1 h)
  have hr1 : ∀ Y ∈ P1, rk Y = rk1 Y := fun Y h => if_pos h
  have hr2 : ∀ Y ∈ P2, rk Y = rk2 Y := fun Y h => if_neg (fun h1 => hn Y h1 h)
  refine ⟨P1 ∪ P2, N, par, rk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact ⟨(a1 Y h).1, (a1 Y h).2.1, (a1 Y h).2.2.trans Finset.subset_union_left⟩
    · exact ⟨(a2 Y h).1, (a2 Y h).2.1, (a2 Y h).2.2.trans Finset.subset_union_right⟩
  · intro Y hY Z hZ hYZ
    rcases Finset.mem_union.1 hY with h | h <;> rcases Finset.mem_union.1 hZ with h' | h'
    · exact b1 Y h Z h' hYZ
    · exact Finset.disjoint_of_subset_left (a1 Y h).2.2
        (Finset.disjoint_of_subset_right (a2 Z h').2.2 hA)
    · exact Finset.disjoint_of_subset_left (a2 Y h).2.2
        (Finset.disjoint_of_subset_right (a1 Z h').2.2 hA.symm)
    · exact b2 Y h Z h' hYZ
  · intro v hv
    rcases Finset.mem_union.1 hv with h | h
    · obtain ⟨Y, hY, hvY⟩ := c1 v h; exact ⟨Y, Finset.mem_union_left _ hY, hvY⟩
    · obtain ⟨Y, hY, hvY⟩ := c2 v h; exact ⟨Y, Finset.mem_union_right _ hY, hvY⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · rw [hN1 Y h]
      refine ⟨(e1 Y h).1.trans ?_, (e1 Y h).2⟩
      intro X hX; simp only [Finset.mem_union] at hX ⊢; tauto
    · rw [hN2 Y h]
      refine ⟨(e2 Y h).1.trans ?_, (e2 Y h).2⟩
      intro X hX; simp only [Finset.mem_union] at hX ⊢; tauto
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · rw [hN1 Y h, hp1 Y h, hr1 Y h]
      rcases f1 Y h with h' | ⟨hp, hr, hs⟩
      · exact Or.inl (h'.trans Finset.subset_union_left)
      · exact Or.inr ⟨Finset.mem_union_left _ hp, by rw [hr1 _ hp]; exact hr,
          by rw [hN1 _ hp]; exact hs⟩
    · rw [hN2 Y h, hp2 Y h, hr2 Y h]
      rcases f2 Y h with h' | ⟨hp, hr, hs⟩
      · exact Or.inl (h'.trans Finset.subset_union_right)
      · exact Or.inr ⟨Finset.mem_union_right _ hp, by rw [hr2 _ hp]; exact hr,
          by rw [hN2 _ hp]; exact hs⟩
  · intro Y hY y hy w hw
    rcases Finset.mem_union.1 hY with h | h
    · rcases g1 Y h y hy w hw with ⟨Z, hZ, hwZ, hor⟩ | ⟨hwA, Q, hQ, hwQ⟩
      · left; refine ⟨Z, Finset.mem_union_left _ hZ, hwZ, ?_⟩
        rw [hN1 Y h, hN1 Z hZ]; exact hor
      · by_cases hw2 : w ∈ A2
        · exfalso
          rcases Finset.mem_union.1 ((e1 Y h).1 hQ) with hQ' | hQ'
          · exact hwA ((a1 Q hQ').2.2 hwQ)
          · exact Finset.disjoint_left.1 (hq1 Q hQ') hwQ hw2
        · right
          refine ⟨fun h' => ?_, Q, by rw [hN1 Y h]; exact hQ, hwQ⟩
          rcases Finset.mem_union.1 h' with h'' | h''
          · exact hwA h''
          · exact hw2 h''
    · rcases g2 Y h y hy w hw with ⟨Z, hZ, hwZ, hor⟩ | ⟨hwA, Q, hQ, hwQ⟩
      · left; refine ⟨Z, Finset.mem_union_right _ hZ, hwZ, ?_⟩
        rw [hN2 Y h, hN2 Z hZ]; exact hor
      · by_cases hw1 : w ∈ A1
        · exfalso
          rcases Finset.mem_union.1 ((e2 Y h).1 hQ) with hQ' | hQ'
          · exact hwA ((a2 Q hQ').2.2 hwQ)
          · exact Finset.disjoint_left.1 (hq2 Q hQ') hwQ hw1
        · right
          refine ⟨fun h' => ?_, Q, by rw [hN2 Y h]; exact hQ, hwQ⟩
          rcases Finset.mem_union.1 h' with h'' | h''
          · exact hw1 h''
          · exact hwA h''

lemma disj_foldr {α : Type} (I : α → Finset V) (s : Finset V) :
    ∀ t : List α, (∀ b ∈ t, Disjoint s (I b)) → Disjoint s (t.foldr (fun c u => I c ∪ u) ∅) := by
  intro t
  induction t with
  | nil => intro _; simp
  | cons b t ih =>
    intro h
    rw [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨h b List.mem_cons_self, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))⟩

lemma Dec_list {H : SimpleGraph V} {Ok : Finset V → Prop} {α : Type} (I : α → Finset V)
    (Qs : α → Finset (Finset V)) (Q0 : Finset (Finset V)) :
    ∀ ch : List α, (∀ c ∈ ch, Dec H Ok (I c) (Qs c)) → (∀ c ∈ ch, Qs c ⊆ Q0) →
      (∀ Q ∈ Q0, Disjoint Q (ch.foldr (fun c s => I c ∪ s) ∅)) →
      ch.Pairwise (fun a b => Disjoint (I a) (I b)) →
      Dec H Ok (ch.foldr (fun c s => I c ∪ s) ∅) Q0 := by
  intro ch
  induction ch with
  | nil => intro _ _ _ _; exact Dec_empty H Ok Q0
  | cons c t ih =>
    intro hd hq hQ hpw
    rw [List.pairwise_cons] at hpw
    rw [List.foldr_cons] at hQ ⊢
    have hc := hd c List.mem_cons_self
    have ht := ih (fun b hb => hd b (List.mem_cons_of_mem _ hb))
      (fun b hb => hq b (List.mem_cons_of_mem _ hb))
      (fun Q hQ' => Finset.disjoint_of_subset_right Finset.subset_union_right (hQ Q hQ')) hpw.2
    have hu := Dec_union hc ht (disj_foldr I (I c) t hpw.1)
      (fun Q hQ' => Finset.disjoint_of_subset_right Finset.subset_union_right
        (hQ Q (hq c List.mem_cons_self hQ')))
      (fun Q hQ' => Finset.disjoint_of_subset_right Finset.subset_union_left (hQ Q hQ'))
    exact Dec_mono hu (Finset.union_subset (hq c List.mem_cons_self) (subset_refl _))

lemma Dec_step {H : SimpleGraph V} {Ok : Finset V → Prop} {A Y0 : Finset V}
    {QS QSc : Finset (Finset V)} (hY0 : Y0 ⊆ A) (hne : Y0.Nonempty) (hok : Ok Y0)
    (d : Dec H Ok (A \ Y0) QSc) (hQSc : QSc ⊆ insert Y0 QS) (hQS : ∀ Q ∈ QS, Disjoint Q A)
    (hcard : QS.card ≤ 3) (hnb : ∀ v ∈ A, ∀ w, H.Adj v w → w ∈ A ∨ ∃ Q ∈ QS, w ∈ Q) :
    Dec H Ok A QS := by
  classical
  obtain ⟨P1, N1, par1, rk1, a1, b1, c1, e1, f1, g1⟩ := d
  have hY0n : Y0 ∉ P1 := by
    intro h
    obtain ⟨v, hv⟩ := hne
    exact (Finset.mem_sdiff.1 ((a1 Y0 h).2.2 hv)).2 hv
  have hneY : ∀ Y ∈ P1, Y ≠ Y0 := fun Y h e => hY0n (e ▸ h)
  let N : Finset V → Finset (Finset V) := fun Y => if Y = Y0 then QS else N1 Y
  let par : Finset V → Finset V := fun Y => if N1 Y ⊆ QSc then Y0 else par1 Y
  let rk : Finset V → ℕ := fun Y => if Y = Y0 then 0 else rk1 Y + 1
  have hN0 : N Y0 = QS := if_pos rfl
  have hN1 : ∀ Y ∈ P1, N Y = N1 Y := fun Y h => if_neg (hneY Y h)
  have hr0 : rk Y0 = 0 := if_pos rfl
  have hr1 : ∀ Y ∈ P1, rk Y = rk1 Y + 1 := fun Y h => if_neg (hneY Y h)
  -- a vertex of `Y0` lies in no part of `P1`, nor in an outer part
  have hyQ : ∀ y ∈ Y0, ∀ Q ∈ P1 ∪ QSc, y ∈ Q → Q = Y0 := by
    intro y hy Q hQ hyQ
    rcases Finset.mem_union.1 hQ with h | h
    · exact absurd hy (Finset.mem_sdiff.1 ((a1 Q h).2.2 hyQ)).2
    · rcases Finset.mem_insert.1 (hQSc h) with h' | h'
      · exact h'
      · exact absurd (hY0 hy) (Finset.disjoint_left.1 (hQS Q h') hyQ)
  refine ⟨insert Y0 P1, N, par, rk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y hY
    rcases Finset.mem_insert.1 hY with h | h
    · rw [h]; exact ⟨hok, hne, hY0⟩
    · exact ⟨(a1 Y h).1, (a1 Y h).2.1, (a1 Y h).2.2.trans Finset.sdiff_subset⟩
  · intro Y hY Z hZ hYZ
    rcases Finset.mem_insert.1 hY with h | h <;> rcases Finset.mem_insert.1 hZ with h' | h'
    · exact absurd (h.trans h'.symm) hYZ
    · rw [h]; exact Finset.disjoint_of_subset_right (a1 Z h').2.2 Finset.disjoint_sdiff
    · rw [h']; exact (Finset.disjoint_of_subset_right (a1 Y h).2.2 Finset.disjoint_sdiff).symm
    · exact b1 Y h Z h' hYZ
  · intro v hv
    by_cases h : v ∈ Y0
    · exact ⟨Y0, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨Y, hY, hvY⟩ := c1 v (Finset.mem_sdiff.2 ⟨hv, h⟩)
      exact ⟨Y, Finset.mem_insert_of_mem hY, hvY⟩
  · intro Y hY
    rcases Finset.mem_insert.1 hY with h | h
    · rw [h, hN0]
      exact ⟨Finset.subset_union_right, hcard⟩
    · rw [hN1 Y h]
      refine ⟨(e1 Y h).1.trans ?_, (e1 Y h).2⟩
      intro X hX
      rcases Finset.mem_union.1 hX with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h')
      · rcases Finset.mem_insert.1 (hQSc h') with h'' | h''
        · rw [h'']; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · exact Finset.mem_union_right _ h''
  · intro Y hY
    rcases Finset.mem_insert.1 hY with h | h
    · rw [h, hN0]; exact Or.inl (subset_refl _)
    · right
      rw [hN1 Y h, hr1 Y h]
      by_cases hc : N1 Y ⊆ QSc
      · have hp : par Y = Y0 := if_pos hc
        rw [hp, hr0, hN0]
        exact ⟨Finset.mem_insert_self _ _, Nat.succ_pos _, hc.trans hQSc⟩
      · have hp : par Y = par1 Y := if_neg hc
        rw [hp]
        obtain ⟨hp1, hlt, hs⟩ := (f1 Y h).resolve_left hc
        rw [hr1 _ hp1, hN1 _ hp1]
        exact ⟨Finset.mem_insert_of_mem hp1, by omega, hs⟩
  · intro Y hY y hy w hw
    rcases Finset.mem_insert.1 hY with h | h
    · rw [h] at hy ⊢
      rcases hnb y (hY0 hy) w hw with hwA | ⟨Q, hQ, hwQ⟩
      · by_cases hw0 : w ∈ Y0
        · exact Or.inl ⟨Y0, Finset.mem_insert_self _ _, hw0, Or.inl rfl⟩
        · obtain ⟨Z, hZ, hwZ⟩ := c1 w (Finset.mem_sdiff.2 ⟨hwA, hw0⟩)
          left
          refine ⟨Z, Finset.mem_insert_of_mem hZ, hwZ, Or.inr (Or.inl ?_)⟩
          rw [hN1 Z hZ]
          rcases g1 Z hZ w hwZ y hw.symm with ⟨Z', hZ', hyZ', _⟩ | ⟨_, Q, hQ, hyQ2⟩
          · exact absurd hy (Finset.mem_sdiff.1 ((a1 Z' hZ').2.2 hyZ')).2
          · have := hyQ y hy Q ((e1 Z hZ).1 hQ) hyQ2
            rw [← this]; exact hQ
      · right
        refine ⟨fun hwA => Finset.disjoint_left.1 (hQS Q hQ) hwQ hwA, Q, ?_, hwQ⟩
        rw [hN0]; exact hQ
    · rcases g1 Y h y hy w hw with ⟨Z, hZ, hwZ, hor⟩ | ⟨hwA, Q, hQ, hwQ⟩
      · left; refine ⟨Z, Finset.mem_insert_of_mem hZ, hwZ, ?_⟩
        rw [hN1 Y h, hN1 Z hZ]; exact hor
      · by_cases hw0 : w ∈ Y0
        · left
          refine ⟨Y0, Finset.mem_insert_self _ _, hw0, Or.inr (Or.inr ?_)⟩
          rw [hN1 Y h]
          have := hyQ w hw0 Q ((e1 Y h).1 hQ) hwQ
          rw [← this]; exact hQ
        · right
          refine ⟨fun hA => hwA (Finset.mem_sdiff.2 ⟨hA, hw0⟩), Q, ?_, hwQ⟩
          rw [hN1 Y h]; exact hQ

/-- the region recursion: strong induction on the measure -/
theorem dec_of_step {H : SimpleGraph V} {Ok : Finset V → Prop} {α : Type} (Good : α → Prop)
    (I : α → Finset V) (Qs : α → Finset (Finset V)) (m : α → ℕ)
    (hA1 : ∀ ρ, Good ρ → ∀ Q ∈ Qs ρ, Disjoint Q (I ρ))
    (hA2 : ∀ ρ, Good ρ → ∀ v ∈ I ρ, ∀ w, H.Adj v w → w ∈ I ρ ∨ ∃ Q ∈ Qs ρ, w ∈ Q)
    (hA3 : ∀ ρ, Good ρ → (Qs ρ).card ≤ 3)
    (hA4 : ∀ ρ, Good ρ → ∅ ∉ Qs ρ)
    (hstep : ∀ ρ, Good ρ → (I ρ).Nonempty → ∃ (Y0 : Finset V) (ch : List α),
        Y0 ⊆ I ρ ∧ (Y0.Nonempty → Ok Y0) ∧
        (∀ c ∈ ch, Good c ∧ m c < m ρ ∧ Qs c ⊆ insert Y0 (Qs ρ)) ∧
        ch.Pairwise (fun a b => Disjoint (I a) (I b)) ∧
        ch.foldr (fun c s => I c ∪ s) ∅ = I ρ \ Y0) :
    ∀ ρ, Good ρ → Dec H Ok (I ρ) (Qs ρ) := by
  classical
  have key : ∀ n, ∀ ρ, m ρ = n → Good ρ → Dec H Ok (I ρ) (Qs ρ) := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    intro ρ hn hg
    rcases (I ρ).eq_empty_or_nonempty with he | hne
    · rw [he]; exact Dec_empty H Ok _
    obtain ⟨Y0, ch, hY0, hok, hch, hpw, hU⟩ := hstep ρ hg hne
    have hdc : ∀ c ∈ ch, Dec H Ok (I c) (Qs c) := fun c hc =>
      ih (m c) (hn ▸ (hch c hc).2.1) c rfl (hch c hc).1
    by_cases hY : Y0 = ∅
    · subst hY
      have hD : Dec H Ok (ch.foldr (fun c s => I c ∪ s) ∅) (Qs ρ) := by
        apply Dec_list I Qs (Qs ρ) ch hdc
        · intro c hc X hX
          rcases Finset.mem_insert.1 ((hch c hc).2.2 hX) with h | h
          · exact absurd (h ▸ hX) (hA4 c (hch c hc).1)
          · exact h
        · intro Q hQ
          rw [hU]
          exact Finset.disjoint_of_subset_right Finset.sdiff_subset (hA1 ρ hg Q hQ)
        · exact hpw
      rw [hU, Finset.sdiff_empty] at hD
      exact hD
    · have hne0 : Y0.Nonempty := Finset.nonempty_iff_ne_empty.2 hY
      have hD : Dec H Ok (I ρ \ Y0) (insert Y0 (Qs ρ)) := by
        rw [← hU]
        apply Dec_list I Qs (insert Y0 (Qs ρ)) ch hdc
        · intro c hc; exact (hch c hc).2.2
        · intro Q hQ
          rw [hU]
          rcases Finset.mem_insert.1 hQ with h | h
          · rw [h]; exact Finset.disjoint_sdiff
          · exact Finset.disjoint_of_subset_right Finset.sdiff_subset (hA1 ρ hg Q h)
        · exact hpw
      exact Dec_step hY0 hne0 (hok hne0) hD (subset_refl _) (hA1 ρ hg) (hA3 ρ hg) (hA2 ρ hg)
  intro ρ hg
  exact key _ ρ rfl hg

/-- the final partition: one outer part `T` plus a decomposition of its complement -/
theorem part_of_dec {H : SimpleGraph V} {Ok : Finset V → Prop} {A T : Finset V}
    (d : Dec H Ok A {T}) (hAT : ∀ v, v ∈ A ↔ v ∉ T) (hT : T.Nonempty) (hTok : Ok T) :
    ∃ P : Finpartition (Finset.univ : Finset V), (∀ X ∈ P.parts, Ok X) ∧
      TreewidthLE (PlanarQueue.Planar.quotientGraph H P) 3 := by
  classical
  obtain ⟨Ps, N, par, rk, a1, b1, c1, e1, f1, g1⟩ := d
  have hTn : T ∉ Ps := by
    intro h
    obtain ⟨v, hv⟩ := hT
    exact (hAT v).1 ((a1 T h).2.2 hv) hv
  have hdisj : ((insert T Ps : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    intro X hX Y hY hXY
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hX hY
    rcases hX with rfl | hX <;> rcases hY with rfl | hY
    · exact absurd rfl hXY
    · exact Finset.disjoint_left.2 fun v hvT hvY => (hAT v).1 ((a1 Y hY).2.2 hvY) hvT
    · exact Finset.disjoint_left.2 fun v hvX hvT => (hAT v).1 ((a1 X hX).2.2 hvX) hvT
    · exact b1 X hX Y hY hXY
  let P : Finpartition (Finset.univ : Finset V) :=
    { parts := insert T Ps
      supIndep := Finset.supIndep_iff_pairwiseDisjoint.2 hdisj
      sup_parts := by
        apply Finset.eq_univ_of_forall
        intro v
        rw [Finset.mem_sup]
        by_cases hv : v ∈ T
        · exact ⟨T, Finset.mem_insert_self _ _, hv⟩
        · obtain ⟨Y, hY, hvY⟩ := c1 v ((hAT v).2 hv)
          exact ⟨Y, Finset.mem_insert_of_mem hY, hvY⟩
      bot_notMem := by
        intro h
        rw [Finset.bot_eq_empty] at h
        rcases Finset.mem_insert.1 h with h | h
        · rw [← h] at hT; exact Finset.not_nonempty_empty hT
        · exact Finset.not_nonempty_empty (a1 _ h).2.1 }
  have hPp : P.parts = insert T Ps := rfl
  refine ⟨P, ?_, ?_⟩
  · intro X hX
    rw [hPp] at hX
    rcases Finset.mem_insert.1 hX with h | h
    · rw [h]; exact hTok
    · exact (a1 X h).1
  have hTP : T ∈ P.parts := Finset.mem_insert_self _ _
  have hPs : ∀ X ∈ Ps, X ∈ P.parts := fun X h => Finset.mem_insert_of_mem h
  have hcase : ∀ w : P.parts, w.1 = T ∨ w.1 ∈ Ps := fun w => Finset.mem_insert.1 w.2
  let w0 : P.parts := ⟨T, hTP⟩
  let parW : P.parts → P.parts := fun w =>
    if h : par w.1 ∈ Ps ∧ w.1 ∈ Ps ∧ ¬ N w.1 ⊆ {T} then ⟨par w.1, hPs _ h.1⟩ else w0
  let rkW : P.parts → ℕ := fun w => if w.1 = T then 0 else rk w.1 + 1
  let NW : P.parts → Finset P.parts := fun w =>
    if w.1 = T then ∅ else (N w.1).subtype (· ∈ P.parts)
  have hw0 : ∀ w : P.parts, w ≠ w0 → w.1 ≠ T := fun w hw h => hw (Subtype.ext h)
  have hmemNW : ∀ (w x : P.parts), w.1 ≠ T → (x ∈ NW w ↔ x.1 ∈ N w.1) := by
    intro w x hw
    simp only [NW, if_neg hw, Finset.mem_subtype]
  -- adjacency in the quotient
  have key' : ∀ a b : P.parts, a ≠ b → a.1 ∈ Ps → (∃ v ∈ a.1, ∃ w ∈ b.1, H.Adj v w) →
      a ∈ NW b ∨ b ∈ NW a := by
    intro a b hab ha ⟨v, hv, w, hw, hvw⟩
    have haT : a.1 ≠ T := fun e => hTn (e ▸ ha)
    rcases g1 a.1 ha v hv w hvw with ⟨Z, hZ, hwZ, hor⟩ | ⟨hwA, Q, hQ, hwQ⟩
    · rcases hcase b with hb | hb
      · exact absurd ((a1 Z hZ).2.2 hwZ) ((hAT w).not.2 (not_not.2 (hb ▸ hw)))
      · have hZb : Z = b.1 := by
          by_contra hne
          exact Finset.disjoint_left.1 (b1 Z hZ b.1 hb hne) hwZ hw
        have hbT : b.1 ≠ T := fun e => hTn (e ▸ hb)
        rcases hor with h | h | h
        · exact absurd (Subtype.ext (h.trans hZb)) hab
        · left; rw [hmemNW b a hbT, ← hZb]; exact h
        · right; rw [hmemNW a b haT, ← hZb]; exact h
    · have hwT : w ∈ T := by
        by_contra h; exact hwA ((hAT w).2 h)
      have hbT : b.1 = T := by
        rcases hcase b with hb | hb
        · exact hb
        · exact absurd ((a1 _ hb).2.2 hw) ((hAT w).not.2 (not_not.2 hwT))
      right
      rw [hmemNW a b haT, hbT]
      rcases Finset.mem_union.1 ((e1 a.1 ha).1 hQ) with h | h
      · exact absurd ((a1 Q h).2.2 hwQ) ((hAT w).not.2 (not_not.2 hwT))
      · rw [Finset.mem_singleton] at h; rw [← h]; exact hQ
  refine tw_of_par _ w0 parW rkW ?_ NW ?_ ?_ ?_ ?_
  · intro w hw
    have hT' := hw0 w hw
    have hwP : w.1 ∈ Ps := (hcase w).resolve_left hT'
    have hrw : rkW w = rk w.1 + 1 := if_neg hT'
    rw [hrw]
    by_cases hc : par w.1 ∈ Ps ∧ w.1 ∈ Ps ∧ ¬ N w.1 ⊆ {T}
    · have hp : parW w = ⟨par w.1, hPs _ hc.1⟩ := dif_pos hc
      rw [hp]
      have hpT : par w.1 ≠ T := fun e => hTn (e ▸ hc.1)
      have : rkW ⟨par w.1, hPs _ hc.1⟩ = rk (par w.1) + 1 := if_neg hpT
      rw [this]
      obtain ⟨_, hlt, _⟩ := (f1 w.1 hwP).resolve_left hc.2.2
      omega
    · have hp : parW w = w0 := dif_neg hc
      rw [hp]
      have : rkW w0 = 0 := if_pos rfl
      rw [this]; omega
  · exact if_pos rfl
  · intro w
    by_cases hT' : w.1 = T
    · simp only [NW, if_pos hT', Finset.card_empty]; omega
    · simp only [NW, if_neg hT']
      rw [Finset.card_subtype]
      exact (Finset.card_filter_le _ _).trans (e1 w.1 ((hcase w).resolve_left hT')).2
  · intro w hw x hx
    have hT' := hw0 w hw
    have hwP : w.1 ∈ Ps := (hcase w).resolve_left hT'
    rw [hmemNW w x hT'] at hx
    by_cases hc : par w.1 ∈ Ps ∧ w.1 ∈ Ps ∧ ¬ N w.1 ⊆ {T}
    · have hp : parW w = ⟨par w.1, hPs _ hc.1⟩ := dif_pos hc
      rw [hp]
      have hpT : par w.1 ≠ T := fun e => hTn (e ▸ hc.1)
      obtain ⟨_, _, hs⟩ := (f1 w.1 hwP).resolve_left hc.2.2
      rcases Finset.mem_insert.1 (hs hx) with h | h
      · rw [Finset.mem_insert]; left; exact Subtype.ext h
      · rw [Finset.mem_insert]; right
        rw [hmemNW _ x hpT]; exact h
    · have hp : parW w = w0 := dif_neg hc
      rw [hp]
      rcases f1 w.1 hwP with h | ⟨hp1, _, _⟩
      · have := h hx
        rw [Finset.mem_singleton] at this
        rw [Finset.mem_insert]; left; exact Subtype.ext this
      · by_cases hsub : N w.1 ⊆ {T}
        · have := hsub hx
          rw [Finset.mem_singleton] at this
          rw [Finset.mem_insert]; left; exact Subtype.ext this
        · exact absurd ⟨hp1, hwP, hsub⟩ hc
  · intro a b hab
    simp only [PlanarQueue.Planar.quotientGraph, SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hR⟩ := hab
    rcases hcase a with ha | ha
    · rcases hcase b with hb | hb
      · exact absurd (Subtype.ext (ha.trans hb.symm)) hne
      · rcases hR with ⟨v, hv, w, hw, hvw⟩ | ⟨v, hv, w, hw, hvw⟩
        · exact (key' b a (Ne.symm hne) hb ⟨w, hw, v, hv, hvw.symm⟩).symm
        · exact (key' b a (Ne.symm hne) hb ⟨v, hv, w, hw, hvw⟩).symm
    · rcases hR with ⟨v, hv, w, hw, hvw⟩ | ⟨v, hv, w, hw, hvw⟩
      · exact key' a b hne ha ⟨v, hv, w, hw, hvw⟩
      · exact key' a b hne ha ⟨w, hw, v, hv, hvw.symm⟩

end ASM

end PQT

/-! 8100c3d9 D5c: crossing lemma (a fibre path from an inside cell stays inside until it meets the
walk) and nodup cell paths from `ReflTransGen (PRel Q)` (via `SimpleGraph.Walk.bypass`). -/

namespace PQT

section CR

lemma ecount_chain {R : Cell → Cell → Prop} : ∀ l : List Cell, List.IsChain R l →
    ∀ a b, 0 < ecount a b l → R a b
  | [], _, a, b, h => by simp [ecount_nil] at h
  | [x], _, a, b, h => by simp [ecount_single] at h
  | x :: y :: t, hc, a, b, h => by
    rw [List.isChain_cons_cons] at hc
    simp only [ecount] at h
    by_cases hxy : x = a ∧ y = b
    · rw [← hxy.1, ← hxy.2]; exact hc.1
    · rw [if_neg hxy, zero_add] at h
      exact ecount_chain (y :: t) hc.2 a b h

/-- CROSSING: a `Q`-path starting at an inside cell meets the walk in a `Q`-cell or ends inside -/
lemma cross_path {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {Q : Cell → Prop} {c d : Cell}
    (h : Relation.ReflTransGen (PRel Q) c d) (hc : c ∉ l) (hcS : S (triAt c 0) = true) :
    (∃ w ∈ l, Q w) ∨ (d ∉ l ∧ S (triAt d 0) = true) := by
  induction h with
  | refl => exact Or.inr ⟨hc, hcS⟩
  | @tail b e _ hbe ih =>
    rcases ih with h' | ⟨hb, hbS⟩
    · exact Or.inl h'
    · by_cases he : e ∈ l
      · exact Or.inl ⟨e, he, hbe.2.1⟩
      · obtain ⟨k, hk⟩ := hbe.2.2
        exact Or.inr ⟨he, by rw [side_adj hS hb he k hk]; exact hbS⟩

/-- the simple graph of `Q`-cells -/
def cgr (Q : Cell → Prop) : SimpleGraph Cell := SimpleGraph.fromRel (PRel Q)

/-- a nodup cell path from `a` to `b` inside `Q` (except possibly `a`) -/
lemma fpath (Q : Cell → Prop) {a b : Cell} (h : Relation.ReflTransGen (PRel Q) a b) :
    ∃ p : List Cell, p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup ∧
      (∀ x ∈ p, x = a ∨ Q x) ∧ ∀ x y, 0 < ecount x y p → dAdj x y := by
  classical
  have hr : (cgr Q).Reachable a b := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b e _ hbe ih =>
      by_cases hbe' : b = e
      · rw [← hbe']; exact ih
      · exact ih.tail (by rw [cgr, SimpleGraph.fromRel_adj]; exact ⟨hbe', Or.inl hbe⟩)
  obtain ⟨w⟩ := hr
  have hmem : ∀ {u v : Cell} (q : (cgr Q).Walk u v), ∀ x ∈ q.support, x = u ∨ Q x := by
    intro u v q
    induction q with
    | nil => intro x hx; simp at hx; exact Or.inl hx
    | @cons u' v' w' hadj q ih =>
      intro x hx
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · right
        rcases ih x hx with hx' | hx'
        · rw [hx']
          rw [cgr, SimpleGraph.fromRel_adj] at hadj
          rcases hadj.2 with h' | h'
          · exact h'.2.1
          · exact h'.1
        · exact hx'
  refine ⟨w.bypass.support, ?_, ?_, (w.bypass_isPath).support_nodup, hmem w.bypass, ?_⟩
  · rw [SimpleGraph.Walk.support_eq_cons]; rfl
  · rw [List.getLast?_eq_getLast w.bypass.support_ne_nil, SimpleGraph.Walk.getLast_support]
  · intro x y hxy
    have := ecount_chain _ (SimpleGraph.Walk.isChain_adj_support w.bypass) x y hxy
    rw [cgr, SimpleGraph.fromRel_adj] at this
    rcases this.2 with h' | h'
    · exact h'.2.2
    · exact dAdj_symm h'.2.2

/-- FIRST HIT: a `Q`-path to a `T`-cell can be cut at its first `T`-cell -/
lemma rtg_hit (Q T : Cell → Prop) {a b : Cell} (h : Relation.ReflTransGen (PRel Q) a b) (hb : T b) :
    T a ∨ ∃ c t, Relation.ReflTransGen (PRel (fun x => Q x ∧ ¬ T x)) a c ∧ Q a ∧ ¬ T a ∧
      Q t ∧ T t ∧ dAdj c t := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hb
  | @head a a' hab _ ih =>
    by_cases ha : T a
    · exact Or.inl ha
    · right
      rcases ih with ha' | ⟨c, t, hc, hQa', hTa', hQt, hTt, hct⟩
      · exact ⟨a, a', Relation.ReflTransGen.refl, hab.1, ha, hab.2.1, ha', hab.2.2⟩
      · exact ⟨c, t, Relation.ReflTransGen.head ⟨⟨hab.1, ha⟩, ⟨hQa', hTa'⟩, hab.2.2⟩ hc,
          hab.1, ha, hQt, hTt, hct⟩

/-- a fibre path from an inside cell to a walk cell gives a chord piece: a nodup off-walk path
`p` (starting at `a`) whose last cell is adjacent to a walk cell `t` of the same fibre -/
lemma route_to_walk (Q : Cell → Prop) (l : List Cell) {a b : Cell}
    (h : Relation.ReflTransGen (PRel Q) a b) (hb : b ∈ l) (ha : a ∉ l) :
    ∃ p : List Cell, ∃ t, p.head? = some a ∧ p.Nodup ∧ (∀ x ∈ p, Q x ∧ x ∉ l) ∧
      t ∈ l ∧ Q t ∧ (∀ x y, 0 < ecount x y (p ++ [t]) → dAdj x y) := by
  classical
  rcases rtg_hit Q (· ∈ l) h hb with ha' | ⟨c, t, hc, hQa, _, hQt, hTt, hct⟩
  · exact absurd ha' ha
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5⟩ := fpath (fun x => Q x ∧ x ∉ l) hc
  refine ⟨p, t, hp1, hp3, fun x hx => ?_, hTt, hQt, ?_⟩
  · rcases hp4 x hx with hx' | hx'
    · rw [hx']; exact ⟨hQa, ha⟩
    · exact hx'
  · intro x y hxy
    have hpne : p ≠ [] := by intro h0; rw [h0] at hp1; simp at hp1
    obtain ⟨p', z, hpz⟩ : ∃ p' z, p = p' ++ [z] := ⟨p.dropLast, p.getLast hpne,
      (List.dropLast_append_getLast hpne).symm⟩
    have hz : z = c := by
      rw [hpz, List.getLast?_append] at hp2; simpa using hp2
    rw [hpz, List.append_assoc, List.singleton_append] at hxy
    have hg := ecount_glue x y z p' [t]
    rw [hg] at hxy
    rcases Nat.eq_zero_or_pos (ecount x y (p' ++ [z])) with h0 | h0
    · rw [h0, zero_add] at hxy
      simp only [ecount] at hxy
      by_cases hxyz : z = x ∧ t = y
      · rw [← hxyz.1, ← hxyz.2, hz]; exact hct
      · rw [if_neg hxyz] at hxy; simp [ecount] at hxy
    · exact hp5 x y (by rw [hpz]; exact h0)

end CR

end PQT

/-! 8100c3d9 D5d: the bounded top region: the counter-clockwise ring of the box `[-M, M]²`.
Its normalised side contains every cell of `[-(M-1), M-1]²` and no triangle at a cell outside
`[-M, M]²`. -/

namespace PQT

section TOP

/-- a path keeps the side of its cells until it meets the walk (any side value) -/
lemma cross_path' {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {Q : Cell → Prop} {c d : Cell}
    (h : Relation.ReflTransGen (PRel Q) c d) (hc : c ∉ l) :
    (∃ w ∈ l, Q w) ∨ (d ∉ l ∧ S (triAt d 0) = S (triAt c 0)) := by
  induction h with
  | refl => exact Or.inr ⟨hc, rfl⟩
  | @tail b e _ hbe ih =>
    rcases ih with h' | ⟨hb, hbS⟩
    · exact Or.inl h'
    · by_cases he : e ∈ l
      · exact Or.inl ⟨e, he, hbe.2.1⟩
      · obtain ⟨k, hk⟩ := hbe.2.2
        exact Or.inr ⟨he, by rw [side_adj hS hb he k hk]; exact hbS⟩

/-- the `i`-th cell of the counter-clockwise ring of `[-M, M]²`, starting at `(M, -M)` -/
def ringf (M : ℕ) (i : ℕ) : Cell :=
  if i < 2 * M then ((M : ℤ), -(M : ℤ) + i)
  else if i < 4 * M then ((M : ℤ) - ((i - 2 * M : ℕ) : ℤ), (M : ℤ))
  else if i < 6 * M then (-(M : ℤ), (M : ℤ) - ((i - 4 * M : ℕ) : ℤ))
  else (-(M : ℤ) + ((i - 6 * M : ℕ) : ℤ), -(M : ℤ))

/-- the ring as a list walk -/
def ring (M : ℕ) : List Cell := (List.range (8 * M)).map (ringf M)

lemma ring_length (M : ℕ) : (ring M).length = 8 * M := by simp [ring]

lemma ringf_mem (M : ℕ) (hM : 1 ≤ M) (i : ℕ) (hi : i < 8 * M) :
    inBox M (ringf M i) ∧ ¬ inBox ((M : ℤ) - 1) (ringf M i) := by
  unfold ringf inBox
  split_ifs <;> simp only <;> omega

lemma mem_ring {M : ℕ} (hM : 1 ≤ M) {c : Cell} (hc : c ∈ ring M) :
    inBox M c ∧ ¬ inBox ((M : ℤ) - 1) c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  exact ringf_mem M hM i (List.mem_range.1 hi)

lemma ringf_step (M : ℕ) (hM : 1 ≤ M) (i : ℕ) (hi : i < 8 * M) :
    dAdj (ringf M i) (ringf M ((i + 1) % (8 * M))) := by
  by_cases hlast : i + 1 = 8 * M
  · rw [hlast, Nat.mod_self]
    refine ⟨0, ?_⟩
    unfold ringf
    split_ifs <;> ext <;> simp [dir] <;> omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    by_cases h1 : i < 2 * M
    · refine ⟨1, ?_⟩
      unfold ringf
      split_ifs <;> ext <;> simp [dir] <;> omega
    by_cases h2 : i < 4 * M
    · refine ⟨3, ?_⟩
      unfold ringf
      split_ifs <;> ext <;> simp [dir] <;> omega
    by_cases h3 : i < 6 * M
    · refine ⟨4, ?_⟩
      unfold ringf
      split_ifs <;> ext <;> simp [dir] <;> omega
    · refine ⟨0, ?_⟩
      unfold ringf
      split_ifs <;> ext <;> simp [dir] <;> omega

lemma ring_nodup (M : ℕ) : (ring M).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro x hx y hy h
  rw [List.mem_range] at hx hy
  unfold ringf at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

lemma ring_simple (M : ℕ) (hM : 1 ≤ M) : LSimple (ring M) := by
  refine ⟨ring_nodup M, by rw [ring_length]; omega, fun a b hab => ?_⟩
  have hl : 0 < (ring M).length := by rw [ring_length]; omega
  obtain ⟨i, hi, h1, h2⟩ := (ecountC_pos_iff a b (ring M) hl).1 hab
  have hi' : i < 8 * M := by rw [ring_length] at hi; exact hi
  have e1 : (ring M)[i] = ringf M i := by simp [ring]
  have e2 : (ring M)[(i + 1) % (ring M).length]'(Nat.mod_lt _ hl) = ringf M ((i + 1) % (8 * M)) := by
    simp [ring, ring_length]
  rw [← h1, ← h2, e1, e2]
  exact ringf_step M hM i hi'

lemma box_conn (R : ℤ) {a c : Cell} (ha : inBox R a) (hc : inBox R c) :
    Relation.ReflTransGen (PRel (inBox R)) a c := by
  obtain ⟨t, rfl, ht⟩ := descent (inBox R) (· = c) (fun x => l1 x c)
    (fun x hx hxc => by
      obtain ⟨c', h1, h2, _, h4⟩ := step_toward x c hxc
      exact ⟨c', h4 R hx hc, h1, by omega⟩) _ a rfl ha
  exact ht

lemma out_conn (R : ℤ) (hR : 0 ≤ R) {a : Cell} (ha : ¬ inBox R a) :
    Relation.ReflTransGen (PRel (fun x => ¬ inBox R x)) a (R + 1, R + 1) := by
  obtain ⟨t, rfl, ht⟩ := descent (fun x => ¬ inBox R x) (· = (R + 1, R + 1))
    (fun x => l1 x (R + 1, R + 1))
    (fun x hx hxc => by
      obtain ⟨c', h1, h2, h3⟩ := out_step R hR x hx hxc
      exact ⟨c', h1, h2, h3⟩) _ a rfl ha
  exact ht

/-- TOP REGION: the normalised side of the ring contains `[-(M-1), M-1]²` and nothing outside
`[-M, M]²` -/
theorem top_side (hex : ExistsBd) (M : ℕ) (hM : 1 ≤ M) :
    ∃ S : Tri → Bool, LBd S (ring M) ∧ LNorm S (ring M) ∧
      (∀ c, inBox ((M : ℤ) - 1) c → c ∉ ring M ∧ ∀ k, S (triAt c k) = true) ∧
      (∀ c, ¬ inBox (M : ℤ) c → c ∉ ring M ∧ ∀ k, S (triAt c k) = false) := by
  obtain ⟨S, hS, hN⟩ := hex (ring M) (ring_simple M hM)
  -- the first edge `(M, -M) → (M, -M + 1)`
  set a : Cell := ((M : ℤ), -(M : ℤ)) with ha
  have hl : 0 < (ring M).length := by rw [ring_length]; omega
  have he : 0 < ecountC a (a + dir 1) (ring M) := by
    rw [ecountC_pos_iff _ _ _ hl]
    refine ⟨0, hl, ?_, ?_⟩
    · simp [ring, ringf, ha]; omega
    · have h8 : (0 + 1) % (ring M).length = 1 := by rw [ring_length]; exact Nat.mod_eq_of_lt (by omega)
      simp only [h8]
      simp [ring, ringf, ha, dir]
      all_goals (first | omega | (intro h; exfalso; omega))
  have hL : S (triAt a 1) = true := hN a 1 he
  have hR : S (triAt a 0) = false := by
    have hx := (hS a 1).2 (Or.inl he)
    simp only [show (1 : Fin 6) - 1 = 0 from rfl, hL] at hx
    simpa using hx
  have notmem_in : ∀ c, inBox ((M : ℤ) - 1) c → c ∉ ring M := fun c hc hm => (mem_ring hM hm).2 hc
  have notmem_out : ∀ c, ¬ inBox (M : ℤ) c → c ∉ ring M := fun c hc hm => hc (mem_ring hM hm).1
  -- inside
  set c1 : Cell := a + dir 2 with hc1
  have hc1in : inBox ((M : ℤ) - 1) c1 := by
    simp only [hc1, ha, dir, inBox, Prod.fst_add, Prod.snd_add]; omega
  have hc1S : S (triAt c1 0) = true := by
    have : triAt c1 5 = triAt a 1 := by
      have := triAt_third a 1
      simpa using this
    rw [← side_const hS (notmem_in c1 hc1in) 5, this, hL]
  refine ⟨S, hS, hN, fun c hc => ⟨notmem_in c hc, fun k => ?_⟩,
    fun c hc => ⟨notmem_out c hc, fun k => ?_⟩⟩
  · rcases cross_path hS (box_conn _ hc1in hc) (notmem_in c1 hc1in) hc1S with ⟨w, hw, hwQ⟩ | ⟨_, h⟩
    · exact absurd hw (notmem_in w hwQ)
    · rw [side_const hS (notmem_in c hc) k]; exact h
  · -- outside: the right triangle of the first edge
    set e : Cell := a + dir 0 with hee
    have heout : ¬ inBox (M : ℤ) e := by
      simp only [hee, ha, dir, inBox, Prod.fst_add, Prod.snd_add]; omega
    have heS : S (triAt e 0) = false := by
      rw [← side_const hS (notmem_out e heout) 2]
      have : triAt e 2 = triAt a 0 := by rw [hee]; exact triAt_add2 a 0
      rw [this, hR]
    have hM0 : (0 : ℤ) ≤ M := by omega
    have p1 := out_conn (M : ℤ) hM0 heout
    have p2 := out_conn (M : ℤ) hM0 hc
    have p := p1.trans (rtg_symm p2)
    rcases cross_path' hS p (notmem_out e heout) with ⟨w, hw, hwQ⟩ | ⟨_, h⟩
    · exact absurd hw (notmem_out w hwQ)
    · rw [side_const hS (notmem_out c hc) k, h, heS]

end TOP

end PQT

/-! 8100c3d9 D5e: Sperner for list walks (three arcs given by index ranges). -/

namespace PQT

section SP

theorem lsperner {l : List Cell} (h : LSimple l) {S : Tri → Bool} (hS : LBd S l) (hN : LNorm S l)
    (κ : Cell → ℕ) (C0 : Finset Cell) (hC0 : ∀ a k, κ a = 1 → κ (a + dir k) = 2 → a ∈ C0)
    (hcol : ∀ a k, S (triAt a k) = true → κ a = 1 ∨ κ a = 2 ∨ κ a = 3)
    (s1 s2 : ℕ) (h01 : 0 < s1) (h12 : s1 < s2) (h2n : s2 < l.length)
    (harc : ∀ i (hi : i < l.length), κ l[i] = if i < s1 then 1 else if i < s2 then 2 else 3) :
    ∃ a k, S (triAt a k) = true ∧ κ a = 1 ∧ κ (a + dir k) = 2 ∧ κ (a + dir (k + 1)) = 3 := by
  haveI := h.ne
  have hS' : IsBd S (h.toW).WE := fun a k => (hS a k).trans (h.we_iff _ _).symm
  have hL' : ∀ i, S ((h.toW).left i) = true := by
    intro i
    apply hN
    rw [← h.fwd_iff]
    exact ⟨i, rfl, (h.toW).kOut_spec i⟩
  exact (h.toW).sperner hS' hL' κ C0 hC0 hcol s1 s2 h01 h12 h2n (fun i => harc i.val i.isLt)

end SP

end PQT

/-! 8100c3d9 D5f: BFS parents from a BFS layering. -/

namespace PQT

section BFS

lemma dist_parent {V : Type} {G : SimpleGraph V} {r v : V} (hr : G.Reachable r v) (hne : r ≠ v) :
    ∃ u, G.Adj v u ∧ G.Reachable r u ∧ G.dist r u + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases hq : p.reverse with
  | nil => exact absurd rfl hne
  | @cons _ u _ hvu q' =>
    have hlen : q'.length + 1 = G.dist r v := by
      have := congrArg SimpleGraph.Walk.length hq
      rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons] at this
      omega
    have hru : G.Reachable r u := ⟨q'.reverse⟩
    have h1 : G.dist r u ≤ q'.length := by
      rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_le q'
    obtain ⟨w, hw⟩ := hru.exists_walk_length_eq_dist
    have h2 : G.dist r v ≤ G.dist r u + 1 := by
      have := SimpleGraph.dist_le (w.concat hvu.symm)
      rw [SimpleGraph.Walk.length_concat, hw] at this
      exact this
    exact ⟨u, hvu, hru, by omega⟩

/-- BFS parents: every vertex of positive layer has a neighbour one layer up -/
theorem bfs_parent {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (L : V → ℕ)
    (hL : PlanarQueue.Planar.IsBFSLayering G L) :
    ∃ p : V → V, ∀ v, 0 < L v → G.Adj v (p v) ∧ L (p v) + 1 = L v := by
  classical
  obtain ⟨R, hR1, hR2⟩ := hL
  have key : ∀ v, 0 < L v → ∃ u, G.Adj v u ∧ L u + 1 = L v := by
    intro v hv
    obtain ⟨r, ⟨hrR, hrv⟩, _⟩ := hR1 v
    have hLv := hR2 r hrR v hrv
    have hne : r ≠ v := by
      intro h; subst h; rw [SimpleGraph.dist_self] at hLv; omega
    obtain ⟨u, hvu, hru, hd⟩ := dist_parent hrv hne
    exact ⟨u, hvu, by rw [hR2 r hrR u hru, hLv]; exact hd⟩
  refine ⟨fun v => if h : 0 < L v then Classical.choose (key v h) else v, fun v hv => ?_⟩
  simp only [dif_pos hv]
  exact Classical.choose_spec (key v hv)

end BFS

end PQT

/-! 8100c3d9 D5g: region infrastructure: arc choice from three blocks, inside cells, cell
connectivity of vertex sets, abstract routing forests (iterate a next-cell map down to the walk). -/

namespace PQT

section RG

/-! ### three arcs from three (possibly empty) blocks -/

/-- block index of position `i` for consecutive blocks of lengths `a`, `b`, rest -/
def blk (a b i : ℕ) : ℕ := if i < a then 0 else if i < a + b then 1 else 2

lemma arcs3 (a b n : ℕ) (hn : 3 ≤ n) :
    ∃ s1 s2, 0 < s1 ∧ s1 < s2 ∧ s2 < n ∧
      ∀ i < n, blk a b i = blk a b (if i < s1 then 0 else if i < s2 then s1 else s2) := by
  by_cases h1 : 0 < a ∧ a < n
  · by_cases h2 : 0 < a + b ∧ a + b < n ∧ 0 < b
    · refine ⟨a, a + b, h1.1, by omega, h2.2.1, ?_⟩
      intro i hi; simp only [blk]; split_ifs <;> omega
    · by_cases ha : a = 1
      · refine ⟨1, 2, by omega, by omega, by omega, ?_⟩
        intro i hi; simp only [blk]; split_ifs <;> omega
      · refine ⟨1, a, by omega, by omega, h1.2, ?_⟩
        intro i hi; simp only [blk]; split_ifs <;> omega
  · by_cases h2 : 0 < a + b ∧ a + b < n
    · by_cases hb : a + b = 1
      · refine ⟨1, 2, by omega, by omega, by omega, ?_⟩
        intro i hi; simp only [blk]; split_ifs <;> omega
      · refine ⟨1, a + b, by omega, by omega, h2.2, ?_⟩
        intro i hi; simp only [blk]; split_ifs <;> omega
    · refine ⟨1, 2, by omega, by omega, by omega, ?_⟩
      intro i hi; simp only [blk]; split_ifs <;> omega

/-! ### inside cells -/

/-- `c` is an inside cell of the region `(S, l)` -/
def Ins (S : Tri → Bool) (l : List Cell) (c : Cell) : Prop := c ∉ l ∧ S (triAt c 0) = true

lemma Ins.all {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {c : Cell} (h : Ins S l c)
    (k : Fin 6) : S (triAt c k) = true := (side_const hS h.1 k).trans h.2

lemma Ins.adj {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {c d : Cell} (h : Ins S l c)
    (hd : dAdj c d) : d ∈ l ∨ Ins S l d := by
  by_cases hdl : d ∈ l
  · exact Or.inl hdl
  · obtain ⟨k, hk⟩ := hd
    exact Or.inr ⟨hdl, by rw [side_adj hS h.1 hdl k hk]; exact h.2⟩

/-- every walk cell has a triangle outside the region (the right triangle of its step) -/
lemma walk_false {S : Tri → Bool} {l : List Cell} (h : LSimple l) (hS : LBd S l)
    (hN : LNorm S l) {c : Cell} (hc : c ∈ l) : ∃ k, S (triAt c k) = false := by
  have hl : 0 < l.length := by have := h.2.1; omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hpos : 0 < ecountC l[i] (l[(i + 1) % l.length]'(Nat.mod_lt _ hl)) l :=
    (ecountC_pos_iff _ _ _ hl).2 ⟨i, hi, rfl, rfl⟩
  obtain ⟨k, hk⟩ := h.2.2 _ _ hpos
  rw [hk] at hpos
  refine ⟨k - 1, ?_⟩
  have h1 := hN _ k hpos
  have h2 := (hS l[i] k).2 (Or.inl hpos)
  rw [h1] at h2
  cases hx : S (triAt l[i] (k - 1))
  · rfl
  · rw [hx] at h2; exact absurd rfl h2

/-- a cell set connected through `Q`-steps that has an inside cell and a non-inside cell owns a
walk cell -/
lemma part_walk {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {Q : Cell → Prop}
    (hQ : ∀ x y, Q x → Q y → Relation.ReflTransGen (PRel Q) x y) {c d : Cell}
    (hc : Ins S l c) (hQc : Q c) (hQd : Q d) (hd : ¬ Ins S l d) : ∃ w ∈ l, Q w := by
  rcases cross_path hS (hQ c d hQc hQd) hc.1 hc.2 with h | h
  · exact h
  · exact absurd h hd

/-- a connected cell set owning no walk cell and meeting the inside lies inside -/
lemma blob_inside {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {Q : Cell → Prop}
    (hQ : ∀ x y, Q x → Q y → Relation.ReflTransGen (PRel Q) x y) (hnw : ∀ w ∈ l, ¬ Q w)
    {c d : Cell} (hc : Ins S l c) (hQc : Q c) (hQd : Q d) : Ins S l d := by
  by_contra hd
  obtain ⟨w, hw, hQw⟩ := part_walk hS hQ hc hQc hQd hd
  exact hnw w hw hQw

/-! ### cell connectivity of connected vertex sets -/

lemma prel_mono {P Q : Cell → Prop} (h : ∀ x, P x → Q x) {a b : Cell}
    (hab : Relation.ReflTransGen (PRel P) a b) : Relation.ReflTransGen (PRel Q) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨h _ hbc.1, h _ hbc.2.1, hbc.2.2⟩

lemma cells_conn {V : Type} (phi : Cell → V)
    (hfib : ∀ v c c', phi c = v → phi c' = v →
      Relation.ReflTransGen (PRel (fun x => phi x = v)) c c')
    (Q : Set V) {a b : Q} (hab : Relation.ReflTransGen ((Gphi phi).induce Q).Adj a b) :
    ∀ x y, phi x = a.1 → phi y = b.1 →
      Relation.ReflTransGen (PRel (fun z => phi z ∈ Q)) x y := by
  induction hab with
  | refl =>
    intro x y hx hy
    exact prel_mono (fun u hu => by show phi u ∈ Q; rw [hu]; exact a.2) (hfib a.1 x y hx hy)
  | @tail b e _ hbe ih =>
    intro x y hx hy
    have hbe' : (Gphi phi).Adj b.1 e.1 := hbe
    rw [Gphi, SimpleGraph.fromRel_adj] at hbe'
    obtain ⟨c, c', hc, hc', hcc'⟩ : ∃ c c', phi c = b.1 ∧ phi c' = e.1 ∧ dAdj c c' := by
      rcases hbe'.2 with ⟨c, c', h1, h2, h3⟩ | ⟨c', c, h1, h2, h3⟩
      · exact ⟨c, c', h1, h2, h3⟩
      · exact ⟨c, c', h2, h1, dAdj_symm h3⟩
    have h1 := ih x c hx hc
    have h2 : PRel (fun z => phi z ∈ Q) c c' :=
      ⟨by show phi c ∈ Q; rw [hc]; exact b.2, by show phi c' ∈ Q; rw [hc']; exact e.2, hcc'⟩
    have h3 : Relation.ReflTransGen (PRel (fun z => phi z ∈ Q)) c' y :=
      prel_mono (fun u hu => by show phi u ∈ Q; rw [hu]; exact e.2) (hfib e.1 c' y hc' hy)
    exact (h1.tail h2).trans h3

/-- cells of a connected vertex set are connected through cells of the set -/
lemma cells_conn' {V : Type} (phi : Cell → V)
    (hfib : ∀ v c c', phi c = v → phi c' = v →
      Relation.ReflTransGen (PRel (fun x => phi x = v)) c c')
    (Q : Set V) (hQ : ((Gphi phi).induce Q).Preconnected) :
    ∀ x y, phi x ∈ Q → phi y ∈ Q → Relation.ReflTransGen (PRel (fun z => phi z ∈ Q)) x y := by
  intro x y hx hy
  have h := hQ ⟨phi x, hx⟩ ⟨phi y, hy⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  exact cells_conn phi hfib Q h x y rfl rfl

/-! ### abstract routing forests -/

/-- the iterate list `[c, f c, ..., f^[n] c]` -/
def itl (f : Cell → Cell) : ℕ → Cell → List Cell
  | 0, c => [c]
  | n + 1, c => c :: itl f n (f c)

lemma itl_head (f : Cell → Cell) (n : ℕ) (c : Cell) : (itl f n c).head? = some c := by
  cases n <;> rfl

lemma mem_itl (f : Cell → Cell) : ∀ (n : ℕ) (c x : Cell), x ∈ itl f n c ↔ ∃ i ≤ n, f^[i] c = x
  | 0, c, x => by
    simp only [itl, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨0, le_refl _, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rw [Nat.le_zero.1 hi]; rfl
  | n + 1, c, x => by
    rw [itl, List.mem_cons, mem_itl f n (f c) x]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, Nat.zero_le _, h.symm⟩
      · exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]; exact h⟩
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => left; exact h.symm
      | succ i => right; exact ⟨i, by omega, by rw [Function.iterate_succ_apply] at h; exact h⟩

lemma itl_getLast (f : Cell → Cell) : ∀ (n : ℕ) (c : Cell), (itl f n c).getLast? = some (f^[n] c)
  | 0, c => rfl
  | n + 1, c => by
    have ih := itl_getLast f n (f c)
    rw [itl, List.getLast?_cons, ih, Option.getD_some, Function.iterate_succ_apply]

lemma itl_chain (f : Cell → Cell) (R : Cell → Cell → Prop) :
    ∀ (n : ℕ) (c : Cell), (∀ i < n, R (f^[i] c) (f^[i + 1] c)) → List.IsChain R (itl f n c)
  | 0, c, _ => List.isChain_singleton c
  | n + 1, c, h => by
    have ih := itl_chain f R n (f c) (fun i hi => by
      have := h (i + 1) (by omega)
      simpa only [Function.iterate_succ_apply] using this)
    have h0 : R c (f c) := by simpa using h 0 (by omega)
    cases n with
    | zero => simp only [itl]; exact List.isChain_pair.2 h0
    | succ n =>
      simp only [itl] at ih ⊢
      exact List.isChain_cons_cons.2 ⟨h0, ih⟩

lemma itl_nodup (f : Cell → Cell) : ∀ (n : ℕ) (c : Cell),
    (∀ i j, i < j → j ≤ n → f^[i] c ≠ f^[j] c) → (itl f n c).Nodup
  | 0, c, _ => List.nodup_singleton c
  | n + 1, c, h => by
    rw [itl, List.nodup_cons]
    refine ⟨fun hm => ?_, itl_nodup f n (f c) fun i j hij hjn => ?_⟩
    · obtain ⟨i, hi, hx⟩ := (mem_itl f n (f c) c).1 hm
      exact h 0 (i + 1) (by omega) (by omega)
        (by rw [Function.iterate_zero_apply, Function.iterate_succ_apply, hx])
    · have := h (i + 1) (j + 1) (by omega) (by omega)
      simpa only [Function.iterate_succ_apply] using this

/-- first time the iterates of `f` from `c` meet `W` -/
noncomputable def hit (W : Cell → Prop) (f : Cell → Cell) (c : Cell) : ℕ :=
  sInf {n | W (f^[n] c)}

/-- the landing cell -/
noncomputable def land (W : Cell → Prop) (f : Cell → Cell) (c : Cell) : Cell :=
  f^[hit W f c] c

/-- the route from `c` to its landing cell -/
noncomputable def route (W : Cell → Prop) (f : Cell → Cell) (c : Cell) : List Cell :=
  itl f (hit W f c) c

lemma hit_spec {W : Cell → Prop} {f : Cell → Cell} {c : Cell} (h : ∃ n, W (f^[n] c)) :
    W (land W f c) := Nat.sInf_mem h

lemma hit_min {W : Cell → Prop} {f : Cell → Cell} {c : Cell} {m : ℕ} (hm : m < hit W f c) :
    ¬ W (f^[m] c) := Nat.notMem_of_lt_sInf hm

lemma hit_iter {W : Cell → Prop} {f : Cell → Cell} {c : Cell} (h : ∃ n, W (f^[n] c)) {i : ℕ}
    (hi : i ≤ hit W f c) : hit W f (f^[i] c) = hit W f c - i := by
  apply le_antisymm
  · apply Nat.sInf_le
    show W (f^[hit W f c - i] (f^[i] c))
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi]
    exact hit_spec h
  · apply le_csInf
    · exact ⟨hit W f c - i, by
        show W (f^[hit W f c - i] (f^[i] c))
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi]
        exact hit_spec h⟩
    · intro m hm
      have hm' : W (f^[m + i] c) := by rw [Function.iterate_add_apply]; exact hm
      have := Nat.sInf_le (s := {n | W (f^[n] c)}) hm'
      show hit W f c - i ≤ m
      unfold hit; omega

lemma land_iter {W : Cell → Prop} {f : Cell → Cell} {c : Cell} (h : ∃ n, W (f^[n] c)) {i : ℕ}
    (hi : i ≤ hit W f c) : land W f (f^[i] c) = land W f c := by
  unfold land
  rw [hit_iter h hi, ← Function.iterate_add_apply, Nat.sub_add_cancel hi]

/-- forest hypotheses: `f` moves inside cells (`D`) to `D` or the walk (`W`), along Δ-steps,
decreasing a lexicographic measure inside `D` -/
def FHyp (D W : Cell → Prop) (f : Cell → Cell) (μ1 μ2 : Cell → ℕ) : Prop :=
  (∀ c, D c → ¬ W c) ∧ ∀ c, D c → (D (f c) ∨ W (f c)) ∧ dAdj c (f c) ∧
    (D (f c) → μ1 (f c) < μ1 c ∨ (μ1 (f c) = μ1 c ∧ μ2 (f c) < μ2 c))

section FH

variable {D W : Cell → Prop} {f : Cell → Cell} {μ1 μ2 : Cell → ℕ}

lemma FHyp.ex (h : FHyp D W f μ1 μ2) : ∀ c, D c ∨ W c → ∃ n, W (f^[n] c) := by
  suffices H : ∀ a b c, μ1 c = a → μ2 c = b → D c ∨ W c → ∃ n, W (f^[n] c) from
    fun c hc => H _ _ c rfl rfl hc
  intro a
  induction a using Nat.strong_induction_on with
  | _ a iha =>
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ihb =>
  intro c ha hb hc
  rcases hc with hD | hW
  · obtain ⟨h1, _, h3⟩ := h.2 c hD
    rcases h1 with hD' | hW'
    · rcases h3 hD' with hlt | ⟨heq, hlt⟩
      · obtain ⟨n, hn⟩ := iha _ (ha ▸ hlt) _ (f c) rfl rfl (Or.inl hD')
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
      · obtain ⟨n, hn⟩ := ihb _ (hb ▸ hlt) (f c) (heq.trans ha) rfl (Or.inl hD')
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
    · exact ⟨1, hW'⟩
  · exact ⟨0, hW⟩

lemma FHyp.dom (h : FHyp D W f μ1 μ2) {c : Cell} (hc : D c ∨ W c) :
    ∀ m < hit W f c, D (f^[m] c) := by
  intro m hm
  induction m with
  | zero =>
    rcases hc with hc | hc
    · exact hc
    · exact absurd hc (hit_min (m := 0) hm)
  | succ m ih =>
    have hD := ih (by omega)
    rcases (h.2 _ hD).1 with h' | h'
    · rw [Function.iterate_succ_apply']; exact h'
    · exact absurd (by rw [Function.iterate_succ_apply']; exact h') (hit_min hm)

lemma FHyp.lt (h : FHyp D W f μ1 μ2) {c : Cell} (hc : D c ∨ W c) (i : ℕ) :
    ∀ d, i + 1 + d < hit W f c →
      μ1 (f^[i + 1 + d] c) < μ1 (f^[i] c) ∨
        (μ1 (f^[i + 1 + d] c) = μ1 (f^[i] c) ∧ μ2 (f^[i + 1 + d] c) < μ2 (f^[i] c)) := by
  intro d
  induction d with
  | zero =>
    intro hd
    simp only [Nat.add_zero] at hd ⊢
    have hD := h.dom hc i (by omega)
    have hD' := h.dom hc (i + 1) (by omega)
    rw [Function.iterate_succ_apply'] at hD' ⊢
    exact (h.2 _ hD).2.2 hD'
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have hD := h.dom hc (i + 1 + d) (by omega)
    have hD' := h.dom hc (i + 1 + d + 1) (by omega)
    rw [Function.iterate_succ_apply'] at hD'
    have h2 := (h.2 _ hD).2.2 hD'
    rw [show i + 1 + (d + 1) = (i + 1 + d) + 1 by omega, Function.iterate_succ_apply']
    omega

lemma FHyp.route_nodup (h : FHyp D W f μ1 μ2) {c : Cell} (hc : D c ∨ W c) :
    (route W f c).Nodup := by
  apply itl_nodup
  intro i j hij hj heq
  have hex := h.ex c hc
  rcases Nat.lt_or_ge j (hit W f c) with hj' | hj'
  · have := h.lt hc i (j - i - 1) (by omega)
    rw [show i + 1 + (j - i - 1) = j by omega, ← heq] at this
    omega
  · have hjh : j = hit W f c := by omega
    have hD := h.dom hc i (by omega)
    have hW : W (f^[j] c) := by rw [hjh]; exact hit_spec hex
    rw [← heq] at hW
    exact h.1 _ hD hW

lemma FHyp.route_adj (h : FHyp D W f μ1 μ2) {c : Cell} (hc : D c ∨ W c) :
    ∀ x y, 0 < ecount x y (route W f c) → dAdj x y := by
  apply ecount_chain
  apply itl_chain
  intro i hi
  rw [Function.iterate_succ_apply']
  exact (h.2 _ (h.dom hc i hi)).2.1

lemma route_mem {W : Cell → Prop} {f : Cell → Cell} {c x : Cell} :
    x ∈ route W f c ↔ ∃ i ≤ hit W f c, f^[i] c = x := mem_itl f _ c x

lemma route_head (W : Cell → Prop) (f : Cell → Cell) (c : Cell) :
    (route W f c).head? = some c := itl_head f _ c

lemma route_last (W : Cell → Prop) (f : Cell → Cell) (c : Cell) :
    (route W f c).getLast? = some (land W f c) := itl_getLast f _ c

lemma FHyp.route_dom (h : FHyp D W f μ1 μ2) {c x : Cell} (hc : D c ∨ W c)
    (hx : x ∈ route W f c) : D x ∨ x = land W f c := by
  obtain ⟨i, hi, rfl⟩ := route_mem.1 hx
  rcases Nat.lt_or_ge i (hit W f c) with hi' | hi'
  · exact Or.inl (h.dom hc i hi')
  · right; unfold land; rw [show i = hit W f c by omega]

lemma FHyp.route_merge (h : FHyp D W f μ1 μ2) {c1 c2 x : Cell} (hc1 : D c1 ∨ W c1)
    (hc2 : D c2 ∨ W c2) (h1 : x ∈ route W f c1) (h2 : x ∈ route W f c2) :
    land W f c1 = land W f c2 := by
  obtain ⟨i, hi, rfl⟩ := route_mem.1 h1
  obtain ⟨j, hj, hij⟩ := route_mem.1 h2
  rw [← land_iter (h.ex c1 hc1) hi, ← hij, land_iter (h.ex c2 hc2) hj]

lemma FHyp.land_W (h : FHyp D W f μ1 μ2) {c : Cell} (hc : D c ∨ W c) : W (land W f c) :=
  hit_spec (h.ex c hc)

end FH

/-! ### the concrete routing forest of a region -/

section RT

lemma cgr_reach {Q : Cell → Prop} {a b : Cell} (h : Relation.ReflTransGen (PRel Q) a b) :
    (cgr Q).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b e _ hbe ih =>
    by_cases hbe' : b = e
    · rw [← hbe']; exact ih
    · exact ih.tail (by rw [cgr, SimpleGraph.fromRel_adj]; exact ⟨hbe', Or.inl hbe⟩)

lemma cgr_adj {Q : Cell → Prop} {a b : Cell} (h : (cgr Q).Adj a b) : Q a ∧ Q b ∧ dAdj a b := by
  rw [cgr, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h' | h'
  · exact h'
  · exact ⟨h'.2.1, h'.1, dAdj_symm h'.2.2⟩

lemma dist_step {G : SimpleGraph Cell} {a b : Cell} (hr : G.Reachable a b) (hab : a ≠ b) :
    ∃ y, G.Adj a y ∧ G.dist y b + 1 = G.dist a b := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  cases w with
  | nil => exact absurd rfl hab
  | @cons _ y _ h w' =>
    refine ⟨y, h, ?_⟩
    have h1 := SimpleGraph.dist_le w'
    obtain ⟨w'', hw''⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (G := G) ⟨w'⟩
    have h2 := SimpleGraph.dist_le (SimpleGraph.Walk.cons h w'')
    rw [SimpleGraph.Walk.length_cons] at h2 hw
    omega

/-- a path avoiding the walk from an inside cell stays inside -/
lemma ins_path {S : Tri → Bool} {l : List Cell} (hS : LBd S l) {A : Cell → Prop} {c d : Cell}
    (h : Relation.ReflTransGen (PRel (fun x => A x ∧ x ∉ l)) c d) (hc : Ins S l c) (hA : A c) :
    Relation.ReflTransGen (PRel (fun x => A x ∧ Ins S l x)) c d ∧ Ins S l d := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hc⟩
  | @tail b e _ hbe ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have he : Ins S l e := by
      rcases Ins.adj hS ih2 hbe.2.2 with h' | h'
      · exact absurd h' hbe.2.1.2
      · exact h'
    have hAb : A b := by
      rcases Relation.ReflTransGen.cases_tail ih1 with h' | ⟨z, _, hz⟩
      · rw [h']; exact hA
      · exact hz.2.1.1
    exact ⟨ih1.tail ⟨⟨hAb, ih2⟩, ⟨hbe.2.1.1, he⟩, hbe.2.2⟩, he⟩

/-- routing data of a region -/
structure RData (V : Type) where
  phi : Cell → V
  S : Tri → Bool
  l : List Cell
  asg : V → Prop
  pof : V → Set V
  L : V → ℕ
  p : V → V

variable {V : Type}

structure RData.Good (R : RData V) : Prop where
  hS : LBd R.S R.l
  hfib : ∀ v c c', R.phi c = v → R.phi c' = v →
    Relation.ReflTransGen (PRel (fun x => R.phi x = v)) c c'
  hw : ∀ w ∈ R.l, R.asg (R.phi w)
  hp1 : ∀ u, R.asg u → u ∈ R.pof u
  hp2 : ∀ u, R.asg u → ∀ w ∈ R.pof u, R.asg w ∧ R.pof w = R.pof u
  hpc : ∀ u, R.asg u → ∀ x y, R.phi x ∈ R.pof u → R.phi y ∈ R.pof u →
    Relation.ReflTransGen (PRel (fun z => R.phi z ∈ R.pof u)) x y
  hpw : ∀ u, R.asg u → ∃ w ∈ R.l, R.phi w ∈ R.pof u
  hL : ∀ c, Ins R.S R.l c → ¬ R.asg (R.phi c) → 0 < R.L (R.phi c)
  hpar : ∀ v, 0 < R.L v → (Gphi R.phi).Adj v (R.p v) ∧ R.L (R.p v) + 1 = R.L v

namespace RData

variable (R : RData V)

/-- cells usable by the part `P`: owned by `P`, inside or on the walk -/
def Pq (P : Set V) (x : Cell) : Prop := R.phi x ∈ P ∧ (Ins R.S R.l x ∨ x ∈ R.l)

/-- distance inside the part to the walk -/
noncomputable def dQ (P : Set V) (c : Cell) : ℕ :=
  sInf {n | ∃ w ∈ R.l, ∃ wk : (cgr (R.Pq P)).Walk c w, wk.length = n}

open Classical in
/-- exit cell of the blob of `u` and the adjacent entry cell in the blob of its BFS parent -/
noncomputable def ex (u : V) : Cell × Cell :=
  if h : ∃ ee : Cell × Cell, R.phi ee.1 = u ∧ R.phi ee.2 = R.p u ∧ dAdj ee.1 ee.2 then
    Classical.choose h else (0, 0)

/-- distance inside the blob of `u` to its exit cell -/
noncomputable def db (u : V) (c : Cell) : ℕ := (cgr (fun x => R.phi x = u)).dist c (R.ex u).1

open Classical in
/-- the next cell of the routing forest -/
noncomputable def nx (c : Cell) : Cell :=
  if R.asg (R.phi c) then
    (if h : ∃ y, (cgr (R.Pq (R.pof (R.phi c)))).Adj c y ∧
        (y ∈ R.l ∨ R.dQ (R.pof (R.phi c)) y < R.dQ (R.pof (R.phi c)) c) then
      Classical.choose h else c)
  else if c = (R.ex (R.phi c)).1 then (R.ex (R.phi c)).2
  else (if h : ∃ y, PRel (fun x => R.phi x = R.phi c) c y ∧
      R.db (R.phi c) y + 1 = R.db (R.phi c) c then Classical.choose h else c)

open Classical in
noncomputable def mu1 (c : Cell) : ℕ := if R.asg (R.phi c) then 0 else R.L (R.phi c) + 1

open Classical in
noncomputable def mu2 (c : Cell) : ℕ :=
  if R.asg (R.phi c) then R.dQ (R.pof (R.phi c)) c else R.db (R.phi c) c

variable {R}

lemma ex_spec (hR : R.Good) {u : V} (hu : 0 < R.L u) :
    R.phi (R.ex u).1 = u ∧ R.phi (R.ex u).2 = R.p u ∧ dAdj (R.ex u).1 (R.ex u).2 := by
  have hadj := (hR.hpar u hu).1
  have h : ∃ ee : Cell × Cell, R.phi ee.1 = u ∧ R.phi ee.2 = R.p u ∧ dAdj ee.1 ee.2 := by
    rw [Gphi, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with ⟨c, c', h1, h2, h3⟩ | ⟨c', c, h1, h2, h3⟩
    · exact ⟨(c, c'), h1, h2, h3⟩
    · exact ⟨(c, c'), h2, h1, dAdj_symm h3⟩
  unfold ex; rw [dif_pos h]; exact Classical.choose_spec h

lemma blob_ins (hR : R.Good) {c d : Cell} (hc : Ins R.S R.l c) (hu : ¬ R.asg (R.phi c))
    (hd : R.phi d = R.phi c) : Ins R.S R.l d :=
  blob_inside hR.hS (Q := fun x => R.phi x = R.phi c) (fun x y hx hy => hR.hfib _ x y hx hy)
    (fun w hw hQ => hu (by rw [← hQ]; exact hR.hw w hw)) hc rfl hd

lemma dQ_ex (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c) (ha : R.asg (R.phi c)) :
    ∃ n, ∃ w ∈ R.l, ∃ wk : (cgr (R.Pq (R.pof (R.phi c)))).Walk c w, wk.length = n := by
  obtain ⟨w0, hw0, hP0⟩ := hR.hpw _ ha
  have h := hR.hpc _ ha c w0 (hR.hp1 _ ha) hP0
  rcases rtg_hit (fun z => R.phi z ∈ R.pof (R.phi c)) (· ∈ R.l) h hw0 with h' | h'
  · exact absurd h' hc.1
  obtain ⟨c', t, hcc', hQc, _, hQt, hTt, hadj⟩ := h'
  obtain ⟨h1, h2⟩ := ins_path hR.hS hcc' hc hQc
  have h3 : Relation.ReflTransGen (PRel (R.Pq (R.pof (R.phi c)))) c t := by
    refine (prel_mono (fun x hx => ⟨hx.1, Or.inl hx.2⟩) h1).tail ⟨?_, ⟨hQt, Or.inr hTt⟩, hadj⟩
    rcases Relation.ReflTransGen.cases_tail h1 with h' | ⟨z, _, hz⟩
    · rw [h']; exact ⟨hQc, Or.inl hc⟩
    · exact ⟨hz.2.1.1, Or.inl hz.2.1.2⟩
  obtain ⟨wk⟩ := cgr_reach h3
  exact ⟨_, t, hTt, wk, rfl⟩

lemma dQ_step (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c) (ha : R.asg (R.phi c)) :
    ∃ y, (cgr (R.Pq (R.pof (R.phi c)))).Adj c y ∧
      (y ∈ R.l ∨ R.dQ (R.pof (R.phi c)) y < R.dQ (R.pof (R.phi c)) c) := by
  have hex := dQ_ex hR hc ha
  have hmem : ∃ w ∈ R.l, ∃ wk : (cgr (R.Pq (R.pof (R.phi c)))).Walk c w,
      wk.length = R.dQ (R.pof (R.phi c)) c :=
    Nat.sInf_mem (s := {n | ∃ w ∈ R.l, ∃ wk : (cgr (R.Pq (R.pof (R.phi c)))).Walk c w,
      wk.length = n}) hex
  obtain ⟨w, hw, wk, hlen⟩ := hmem
  cases wk with
  | nil => exact absurd hw hc.1
  | @cons _ y _ h wk' =>
    refine ⟨y, h, ?_⟩
    by_cases hy : y ∈ R.l
    · exact Or.inl hy
    · right
      have h1 : R.dQ (R.pof (R.phi c)) y ≤ wk'.length := Nat.sInf_le ⟨w, hw, wk', rfl⟩
      rw [SimpleGraph.Walk.length_cons] at hlen
      omega

lemma db_step (hR : R.Good) {u : V} {c : Cell} (hu0 : 0 < R.L u) (hc : R.phi c = u)
    (hne : c ≠ (R.ex u).1) :
    ∃ y, PRel (fun x => R.phi x = u) c y ∧ R.db u y + 1 = R.db u c := by
  have hr := cgr_reach (hR.hfib u c (R.ex u).1 hc (ex_spec hR hu0).1)
  obtain ⟨y, hy, hd⟩ := dist_step hr hne
  exact ⟨y, cgr_adj hy, hd⟩

lemma nx_asg_spec (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c) (ha : R.asg (R.phi c)) :
    (cgr (R.Pq (R.pof (R.phi c)))).Adj c (R.nx c) ∧
      (R.nx c ∈ R.l ∨ R.dQ (R.pof (R.phi c)) (R.nx c) < R.dQ (R.pof (R.phi c)) c) := by
  have h := dQ_step hR hc ha
  unfold nx; rw [if_pos ha, dif_pos h]; exact Classical.choose_spec h

lemma nx_exit (hR : R.Good) {c : Cell} (ha : ¬ R.asg (R.phi c)) (he : c = (R.ex (R.phi c)).1) :
    R.nx c = (R.ex (R.phi c)).2 := by
  unfold nx; rw [if_neg ha, if_pos he]

lemma nx_blob_spec (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c) (ha : ¬ R.asg (R.phi c))
    (he : c ≠ (R.ex (R.phi c)).1) :
    PRel (fun x => R.phi x = R.phi c) c (R.nx c) ∧
      R.db (R.phi c) (R.nx c) + 1 = R.db (R.phi c) c := by
  have h := db_step hR (hR.hL c hc ha) rfl he
  unfold nx; rw [if_neg ha, if_neg he, dif_pos h]; exact Classical.choose_spec h

theorem fhyp (hR : R.Good) : FHyp (Ins R.S R.l) (· ∈ R.l) R.nx R.mu1 R.mu2 := by
  refine ⟨fun c hc => hc.1, fun c hc => ?_⟩
  by_cases ha : R.asg (R.phi c)
  · obtain ⟨hadj, hlt⟩ := nx_asg_spec hR hc ha
    obtain ⟨_, h2, h3⟩ := cgr_adj hadj
    refine ⟨h2.2, h3, fun hD => ?_⟩
    have hlt' : R.dQ (R.pof (R.phi c)) (R.nx c) < R.dQ (R.pof (R.phi c)) c := by
      rcases hlt with h' | h'
      · exact absurd h' hD.1
      · exact h'
    obtain ⟨ha', hpof⟩ := hR.hp2 _ ha _ h2.1
    right
    refine ⟨by simp only [mu1, if_pos ha, if_pos ha'], ?_⟩
    simp only [mu2, if_pos ha, if_pos ha', hpof]
    exact hlt'
  · have hL := hR.hL c hc ha
    obtain ⟨he1, he2, he3⟩ := ex_spec hR hL
    by_cases he : c = (R.ex (R.phi c)).1
    · have hnx := nx_exit hR ha he
      have hd : dAdj c (R.nx c) := by rw [hnx]; conv_lhs => rw [he]
                                      exact he3
      refine ⟨(Ins.adj hR.hS hc hd).symm, hd, fun _ => Or.inl ?_⟩
      have hp := (hR.hpar _ hL).2
      have hph : R.phi (R.nx c) = R.p (R.phi c) := by rw [hnx]; exact he2
      unfold mu1
      rw [if_neg ha, hph]
      split_ifs <;> omega
    · obtain ⟨hpr, hdb⟩ := nx_blob_spec hR hc ha he
      have hI := blob_ins hR hc ha hpr.2.1
      have hph : R.phi (R.nx c) = R.phi c := hpr.2.1
      refine ⟨Or.inl hI, hpr.2.2, fun _ => Or.inr ⟨?_, ?_⟩⟩
      · unfold mu1; rw [hph, if_neg ha]
      · unfold mu2; rw [hph, if_neg ha, if_neg ha]
        omega

lemma nx_asg (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c) (ha : R.asg (R.phi c)) :
    R.phi (R.nx c) ∈ R.pof (R.phi c) := (cgr_adj (nx_asg_spec hR hc ha).1).2.1.1

lemma nx_unasg (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c) (ha : ¬ R.asg (R.phi c)) :
    R.phi (R.nx c) = R.phi c ∨ R.phi (R.nx c) = R.p (R.phi c) := by
  by_cases he : c = (R.ex (R.phi c)).1
  · right; rw [nx_exit hR ha he]; exact (ex_spec hR (hR.hL c hc ha)).2.1
  · left; exact (nx_blob_spec hR hc ha he).1.2.1

end RData

end RT

/-! ### owners along a route -/

lemma itl_length (f : Cell → Cell) : ∀ (n : ℕ) (c : Cell), (itl f n c).length = n + 1
  | 0, c => rfl
  | n + 1, c => by rw [itl, List.length_cons, itl_length f n (f c)]

lemma itl_getElem (f : Cell → Cell) : ∀ (n : ℕ) (c : Cell) (i : ℕ) (h : i < (itl f n c).length),
    (itl f n c)[i] = f^[i] c
  | 0, c, i, h => by
    have : i = 0 := by simp [itl] at h; omega
    subst this; rfl
  | n + 1, c, i, h => by
    cases i with
    | zero => rfl
    | succ i =>
      simp only [itl, List.getElem_cons_succ]
      rw [itl_getElem f n (f c) i, Function.iterate_succ_apply]

lemma mem_itl_take (f : Cell → Cell) (n k : ℕ) (c x : Cell) (hx : x ∈ (itl f n c).take k) :
    ∃ i < k, i ≤ n ∧ f^[i] c = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take, itl_length] at hi
  refine ⟨i, by omega, by omega, ?_⟩
  rw [List.getElem_take, itl_getElem]

lemma mem_itl_drop (f : Cell → Cell) (n k : ℕ) (c x : Cell) (hx : x ∈ (itl f n c).drop k) :
    ∃ i, k ≤ i ∧ i ≤ n ∧ f^[i] c = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_drop, itl_length] at hi
  refine ⟨k + i, by omega, by omega, ?_⟩
  rw [List.getElem_drop, itl_getElem]

namespace RData

variable {V : Type} {R : RData V}

lemma route_asg (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c ∨ c ∈ R.l) {i : ℕ}
    (ha : R.asg (R.phi (R.nx^[i] c))) :
    ∀ j, i ≤ j → j ≤ hit (· ∈ R.l) R.nx c →
      R.asg (R.phi (R.nx^[j] c)) ∧ R.pof (R.phi (R.nx^[j] c)) = R.pof (R.phi (R.nx^[i] c)) := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => ⟨ha, rfl⟩
  | succ j hij ih =>
    intro hj
    obtain ⟨ha', hp⟩ := ih (by omega)
    have hI := (fhyp hR).dom hc j (by omega)
    have hm := nx_asg hR hI ha'
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := hR.hp2 _ ha' _ hm
    exact ⟨h1, h2.trans hp⟩

lemma route_unasg (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c ∨ c ∈ R.l) {i : ℕ} :
    ∀ j, i ≤ j → j ≤ hit (· ∈ R.l) R.nx c → ¬ R.asg (R.phi (R.nx^[j] c)) →
      ¬ R.asg (R.phi (R.nx^[i] c)) ∧ R.L (R.phi (R.nx^[j] c)) ≤ R.L (R.phi (R.nx^[i] c)) ∧
        (R.L (R.phi (R.nx^[j] c)) = R.L (R.phi (R.nx^[i] c)) →
          R.phi (R.nx^[j] c) = R.phi (R.nx^[i] c)) := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun _ hu => ⟨hu, le_refl _, fun _ => rfl⟩
  | succ j hij ih =>
    intro hj hu
    have hI := (fhyp hR).dom hc j (by omega)
    have hu' : ¬ R.asg (R.phi (R.nx^[j] c)) := by
      intro ha
      exact hu (route_asg hR hc ha (j + 1) (by omega) hj).1
    obtain ⟨h1, h2, h3⟩ := ih (by omega) hu'
    have hL := hR.hL _ hI hu'
    have hp := (hR.hpar _ hL).2
    rw [Function.iterate_succ_apply'] at hu ⊢
    rcases nx_unasg hR hI hu' with h' | h'
    · rw [h']; exact ⟨h1, h2, h3⟩
    · rw [h']
      exact ⟨h1, by omega, fun h => absurd h (by omega)⟩

lemma land_asg (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c ∨ c ∈ R.l) :
    R.asg (R.phi (land (· ∈ R.l) R.nx c)) := hR.hw _ ((fhyp hR).land_W hc)

/-- the route splits into an unassigned prefix and a suffix inside the part of the landing cell -/
lemma route_split (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c ∨ c ∈ R.l) :
    ∃ k, (∀ x ∈ (route (· ∈ R.l) R.nx c).take k, Ins R.S R.l x ∧ ¬ R.asg (R.phi x)) ∧
      (route (· ∈ R.l) R.nx c).drop k ≠ [] ∧
      ∀ x ∈ (route (· ∈ R.l) R.nx c).drop k,
        R.phi x ∈ R.pof (R.phi (land (· ∈ R.l) R.nx c)) := by
  classical
  have hex : ∃ k, R.asg (R.phi (R.nx^[k] c)) := ⟨_, land_asg hR hc⟩
  set k := Nat.find hex with hk
  have hkh : k ≤ hit (· ∈ R.l) R.nx c := Nat.find_min' hex (land_asg hR hc)
  refine ⟨k, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨i, hik, hin, rfl⟩ := mem_itl_take _ _ _ _ _ hx
    exact ⟨(fhyp hR).dom hc i (by omega), Nat.find_min hex hik⟩
  · intro h0
    have := congrArg List.length h0
    rw [List.length_drop, route, itl_length] at this
    simp at this; omega
  · obtain ⟨i, hki, hin, rfl⟩ := mem_itl_drop _ _ _ _ _ hx
    have hk0 : R.asg (R.phi (R.nx^[k] c)) := Nat.find_spec hex
    obtain ⟨hai, hpi⟩ := route_asg hR hc hk0 i hki hin
    obtain ⟨_, hph⟩ := route_asg hR hc hk0 _ hkh (le_refl _)
    have : R.pof (R.phi (land (· ∈ R.l) R.nx c)) = R.pof (R.phi (R.nx^[i] c)) := by
      unfold land; rw [hph, hpi]
    rw [this]; exact hR.hp1 _ hai

end RData

/-! ### chord split tolerating a degenerate first piece; side along a chain -/

section TS

/-- `chord_split` without the non-degeneracy side conditions: when the first piece is the bare
walk edge `x → y` it is empty, and the second piece is a rotation of the walk -/
theorem chord_split' (hex : ExistsBd) (x y : Cell) (M B Q : List Cell) (S : Tri → Bool)
    (hW : LSimple (x :: (M ++ y :: B)))
    (hS : LBd S (x :: (M ++ y :: B))) (hN : LNorm S (x :: (M ++ y :: B)))
    (hQ : Q.Nodup) (hQW : ∀ z ∈ Q, z ∉ x :: (M ++ y :: B))
    (hP : ∀ a b, 0 < ecount a b (x :: (Q ++ [y])) → dAdj a b)
    (k : Fin 6) (hk : (Q ++ [y]).head? = some (x + dir k)) (hin : S (triAt x k) = true) :
    ∃ S1 S2 : Tri → Bool,
      ((M = [] ∧ Q = [] ∧ ∀ τ, S1 τ = false) ∨
        (LSimple (x :: (M ++ y :: Q.reverse)) ∧ LBd S1 (x :: (M ++ y :: Q.reverse)) ∧
          LNorm S1 (x :: (M ++ y :: Q.reverse)))) ∧
      LSimple (y :: (B ++ x :: Q)) ∧ LBd S2 (y :: (B ++ x :: Q)) ∧ LNorm S2 (y :: (B ++ x :: Q)) ∧
      ∀ τ, bz (S τ) = bz (S1 τ) + bz (S2 τ) := by
  by_cases hd1 : M ≠ [] ∨ Q ≠ []
  · have hd2 : B ≠ [] ∨ Q ≠ [] := by
      by_contra hc
      push_neg at hc
      obtain ⟨hB, hQ0⟩ := hc
      subst hB; subst hQ0
      have hy : y = x + dir k := by simpa using hk
      have he : 0 < ecountC y x (x :: (M ++ y :: [])) := by
        have : (x :: (M ++ y :: [])) ++ (x :: (M ++ y :: [])).take 1 = (x :: M) ++ y :: [x] := by
          simp
        rw [ecountC, this, ecount_glue]
        have : ecount y x [y, x] = 1 := by simp [ecount]
        omega
      have h1 := (hS x k).2 (Or.inr (by rw [← hy]; exact he))
      have hk3 : x = y + dir (k + 3) := by rw [hy, dir_add3]; abel
      have h2 := hN y (k + 3) (by rw [← hk3]; exact he)
      rw [hy, triAt_add3] at h2
      rw [hin, h2] at h1
      exact h1 rfl
    obtain ⟨S1, S2, h1, h2, h3, h4, h5, h6, h7⟩ :=
      chord_split hex x y M B Q S hW hS hN hQ hQW hP hd1 hd2 k hk hin
    exact ⟨S1, S2, Or.inr ⟨h1, h2, h3⟩, h4, h5, h6, h7⟩
  · push_neg at hd1
    obtain ⟨hM, hQ0⟩ := hd1
    subst hM; subst hQ0
    have hrot : (x :: ([] ++ y :: B)).rotate 1 = y :: (B ++ x :: []) := by
      simp [List.rotate_cons_succ]
    refine ⟨fun _ => false, S, Or.inl ⟨rfl, rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [← hrot]; exact hW.rotate 1
    · rw [← hrot]; exact hS.rotate 1
    · rw [← hrot]; exact hN.rotate 1
    · intro τ; simp [bz]

/-- along a Δ-chain of non-walk cells the side is constant -/
lemma side_chain {S : Tri → Bool} {l : List Cell} (hS : LBd S l) :
    ∀ (P : List Cell) (a : Cell), List.IsChain dAdj (a :: P) → (∀ z ∈ a :: P, z ∉ l) →
      ∀ z ∈ a :: P, S (triAt z 0) = S (triAt a 0)
  | [], a, _, _, z, hz => by rw [List.mem_singleton.1 hz]
  | b :: P, a, hc, hl, z, hz => by
    rw [List.isChain_cons_cons] at hc
    obtain ⟨k, hk⟩ := hc.1
    have hab : S (triAt b 0) = S (triAt a 0) :=
      side_adj hS (hl a (by simp)) (hl b (by simp)) k hk
    rcases List.mem_cons.1 hz with rfl | hz'
    · rfl
    · rw [side_chain hS P b hc.2 (fun w hw => hl w (List.mem_cons_of_mem _ hw)) z hz', hab]

/-- a non-walk cell from which a horizontal ray avoids the walk is outside any region whose
chain vanishes far away -/
lemma ray_out {S : Tri → Bool} {l : List Cell} (hS : LBd S l) (Rb : ℤ)
    (hfar : ∀ c, ¬ inBox Rb c → S (triAt c 0) = false) (z : Cell) (s : Fin 6)
    (hs : s = 0 ∨ s = 3) (hray : ∀ n : ℕ, z + (n : ℤ) • dir s ∉ l) : S (triAt z 0) = false := by
  have hstep : ∀ n : ℕ, S (triAt (z + (n : ℤ) • dir s) 0) = S (triAt z 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      apply side_adj hS (hray n) (hray (n + 1)) s
      push_cast; rw [add_smul, one_smul, add_assoc]
  have hout : ¬ inBox Rb (z + ((Rb.toNat + |z.1|.toNat + 1 : ℕ) : ℤ) • dir s) := by
    have h1 := le_abs_self z.1
    have h2 := neg_abs_le z.1
    rcases hs with rfl | rfl <;> simp only [inBox, dir, Prod.smul_mk, Prod.fst_add, Prod.snd_add,
      smul_eq_mul] <;> push_cast <;> omega
  rw [← hstep (Rb.toNat + |z.1|.toNat + 1)]
  exact hfar _ hout

end TS

/-! ### the tripod split: three routes from a triangle `t0` cut a region into three pieces and `t0` -/

section TRI3

lemma dir_sum (k : Fin 6) : dir (k + 1) = dir k + dir (k + 2) := by fin_cases k <;> decide

lemma dir_add4 (k : Fin 6) : dir (k + 4) = - dir (k + 1) := by fin_cases k <;> decide

lemma ecount_pos_mid (a b : Cell) (L1 L2 : List Cell) : 0 < ecount a b (L1 ++ a :: b :: L2) := by
  rw [ecount_glue]
  have : 0 < ecount a b (a :: b :: L2) := by simp [ecount]
  omega

lemma ecount_le_C (a b : Cell) (l : List Cell) : ecount a b l ≤ ecountC a b l := by
  unfold ecountC
  cases l with
  | nil => simp
  | cons x t =>
    have : (x :: t).take 1 = [x] := by simp
    rw [this, ecount_snoc]; omega

/-- first chord step out of a landing cell `g` into the last cell of a nonempty route interior -/
lemma first_step {S : Tri → Bool} {l : List Cell} (hS : LBd S l) (g : Cell) (E : List Cell)
    (z : Cell) (hch : List.IsChain dAdj (E ++ [z] ++ [g])) (hz : z ∉ l)
    (hzS : S (triAt z 0) = true) :
    ∃ j : Fin 6, z = g + dir j ∧ S (triAt g j) = true := by
  have hzg : dAdj z g := by
    have : E ++ [z] ++ [g] = E ++ z :: g :: [] := by simp
    rw [this, List.isChain_append_cons_cons] at hch
    exact hch.2.1
  obtain ⟨j, hj⟩ := hzg
  refine ⟨j + 3, ?_, ?_⟩
  · rw [hj, dir_add3]; abel
  · have h1 : z = g + dir (j + 3) := by rw [hj, dir_add3]; abel
    rw [← triAt_add2 g (j + 3), ← h1, side_const hS hz, hzS]

theorem tripod_split (hex : ExistsBd) (S : Tri → Bool) (g1 g2 g3 c1 : Cell) (k : Fin 6)
    (M B1 B2 D1 D2 D3 : List Cell)
    (hW : LSimple (g1 :: (M ++ g2 :: (B1 ++ g3 :: B2))))
    (hS : LBd S (g1 :: (M ++ g2 :: (B1 ++ g3 :: B2))))
    (hN : LNorm S (g1 :: (M ++ g2 :: (B1 ++ g3 :: B2))))
    (h1 : (D1 ++ [g1]).head? = some c1) (h2 : (D2 ++ [g2]).head? = some (c1 + dir k))
    (h3 : (D3 ++ [g3]).head? = some (c1 + dir (k + 1)))
    (hc1 : List.IsChain dAdj (D1 ++ [g1])) (hc2 : List.IsChain dAdj (D2 ++ [g2]))
    (hc3 : List.IsChain dAdj (D3 ++ [g3]))
    (hI : ∀ x ∈ D1 ++ D2 ++ D3, Ins S (g1 :: (M ++ g2 :: (B1 ++ g3 :: B2))) x)
    (hnd : (D1 ++ D2 ++ D3).Nodup) (ht0 : S (triAt c1 k) = true) :
    ∃ S12 S31 S23 S0 : Tri → Bool,
      ((∀ τ, S12 τ = false) ∨ (LSimple (g1 :: (M ++ g2 :: (D2.reverse ++ D1))) ∧
        LBd S12 (g1 :: (M ++ g2 :: (D2.reverse ++ D1))) ∧
        LNorm S12 (g1 :: (M ++ g2 :: (D2.reverse ++ D1))))) ∧
      ((∀ τ, S31 τ = false) ∨ (LSimple (g3 :: (B2 ++ g1 :: (D1.reverse ++ D3))) ∧
        LBd S31 (g3 :: (B2 ++ g1 :: (D1.reverse ++ D3))) ∧
        LNorm S31 (g3 :: (B2 ++ g1 :: (D1.reverse ++ D3))))) ∧
      ((∀ τ, S23 τ = false) ∨ (LSimple (D2 ++ g2 :: (B1 ++ g3 :: D3.reverse)) ∧
        LBd S23 (D2 ++ g2 :: (B1 ++ g3 :: D3.reverse)) ∧
        LNorm S23 (D2 ++ g2 :: (B1 ++ g3 :: D3.reverse)))) ∧
      LSimple [c1 + dir (k + 1), c1, c1 + dir k] ∧ LBd S0 [c1 + dir (k + 1), c1, c1 + dir k] ∧
      LNorm S0 [c1 + dir (k + 1), c1, c1 + dir k] ∧
      ∀ τ, bz (S τ) = bz (S12 τ) + bz (S31 τ) + bz (S23 τ) + bz (S0 τ) := by
  set L0 := g1 :: (M ++ g2 :: (B1 ++ g3 :: B2)) with hL0
  set c2 := c1 + dir k with hc2d
  set c3 := c1 + dir (k + 1) with hc3d
  have hnd' := hnd
  rw [List.nodup_append, List.nodup_append] at hnd'
  obtain ⟨⟨hn1, hn2, hd12⟩, hn3, hd3⟩ := hnd'
  have hI1 : ∀ x ∈ D1, Ins S L0 x := fun x hx => hI x (by simp [hx])
  have hI2 : ∀ x ∈ D2, Ins S L0 x := fun x hx => hI x (by simp [hx])
  have hI3 : ∀ x ∈ D3, Ins S L0 x := fun x hx => hI x (by simp [hx])
  -- ===== split A: chord g1 ⇝ c1 → c2 ⇝ g2
  have hQA : (D1.reverse ++ D2).Nodup := by
    rw [List.nodup_append]
    exact ⟨List.nodup_reverse.2 hn1, hn2, fun a ha b hb => hd12 a (List.mem_reverse.1 ha) b hb⟩
  have hQAW : ∀ z ∈ D1.reverse ++ D2, z ∉ L0 := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact (hI1 z (List.mem_reverse.1 hz)).1
    · exact (hI2 z hz).1
  have hPA : ∀ a b, 0 < ecount a b (g1 :: ((D1.reverse ++ D2) ++ [g2])) → dAdj a b := by
    apply ecount_chain
    have e : g1 :: ((D1.reverse ++ D2) ++ [g2]) = (D1 ++ [g1]).reverse ++ (D2 ++ [g2]) := by simp
    rw [e]
    apply List.IsChain.append
    · rw [List.isChain_reverse]; exact hc1.imp (fun a b h => dAdj_symm h)
    · exact hc2
    · intro x hx y hy
      rw [List.getLast?_reverse, h1] at hx
      rw [h2] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      rw [← hx, ← hy]; exact ⟨k, rfl⟩
  have hkA : ∃ kA : Fin 6, ((D1.reverse ++ D2) ++ [g2]).head? = some (g1 + dir kA) ∧
      S (triAt g1 kA) = true := by
    rcases List.eq_nil_or_concat D1 with hD | ⟨E, z, hD⟩
    · subst hD
      have : g1 = c1 := by simpa using h1
      refine ⟨k, ?_, by rw [this]; exact ht0⟩
      rw [List.reverse_nil, List.nil_append, h2, this]
    · rw [List.concat_eq_append] at hD
      subst hD
      have hz : z ∈ E ++ [z] := by simp
      obtain ⟨j, hj, hjS⟩ := first_step hS g1 E z hc1 (hI1 z hz).1 (hI1 z hz).2
      exact ⟨j, by simp [hj], hjS⟩
  obtain ⟨kA, hkA1, hkA2⟩ := hkA
  obtain ⟨S12, S2, hA1, hA2, hA3, hA4, hA5⟩ :=
    chord_split' hex g1 g2 M (B1 ++ g3 :: B2) (D1.reverse ++ D2) S hW hS hN hQA hQAW hPA kA hkA1 hkA2
  have eA : (D1.reverse ++ D2).reverse = D2.reverse ++ D1 := by simp
  rw [eA] at hA1
  -- ===== split B: rotate to g3, chord g3 ⇝ c3 → c1
  obtain ⟨E1, hE1⟩ : ∃ E1, g1 :: D1.reverse = E1 ++ [c1] := by
    cases D1 with
    | nil => exact ⟨[], by simpa using h1⟩
    | cons a T =>
      have : a = c1 := by simpa using h1
      exact ⟨g1 :: T.reverse, by simp [this]⟩
  obtain ⟨F2, hF2⟩ : ∃ F2, D2 ++ [g2] = c2 :: F2 := by
    cases D2 with
    | nil => exact ⟨[], by simpa using h2⟩
    | cons a T =>
      have : a = c2 := by simpa using h2
      exact ⟨T ++ [g2], by simp [this]⟩
  set W2 := g2 :: ((B1 ++ g3 :: B2) ++ g1 :: (D1.reverse ++ D2)) with hW2d
  set W2' := g3 :: ((B2 ++ E1) ++ c1 :: (D2 ++ g2 :: B1)) with hW2'd
  have hrotB : W2.rotate (B1.length + 1) = W2' := by
    have e1 : W2 = (g2 :: B1) ++ (g3 :: (B2 ++ g1 :: (D1.reverse ++ D2))) := by simp [hW2d]
    have e2 : (g2 :: B1).length = B1.length + 1 := by simp
    rw [e1, ← e2, List.rotate_append_length_eq]
    have e3 : g1 :: (D1.reverse ++ D2) = (g1 :: D1.reverse) ++ D2 := by simp
    rw [e3, hE1, hW2'd]
    simp
  have hB2 : LSimple W2' := hrotB ▸ hA2.rotate _
  have hB3 : LBd S2 W2' := hrotB ▸ hA3.rotate _
  have hB4 : LNorm S2 W2' := hrotB ▸ hA4.rotate _
  have hmemW2' : ∀ z, z ∈ W2' → z ∈ L0 ∨ z ∈ D1 ∨ z ∈ D2 := by
    intro z hz
    rw [← hrotB, List.mem_rotate] at hz
    simp only [hW2d, hL0, List.mem_cons, List.mem_append, List.mem_reverse] at hz ⊢
    tauto
  have hnotW2' : ∀ z ∈ D3, z ∉ W2' := by
    intro z hz hzW
    rcases hmemW2' z hzW with h' | h' | h'
    · exact (hI3 z hz).1 h'
    · exact hd3 z (by simp [h']) z hz rfl
    · exact hd3 z (by simp [h']) z hz rfl
  have hQB : D3.reverse.Nodup := List.nodup_reverse.2 hn3
  have hQBW : ∀ z ∈ D3.reverse, z ∉ W2' := fun z hz => hnotW2' z (List.mem_reverse.1 hz)
  have hc31 : c1 = c3 + dir (k + 4) := by rw [hc3d, dir_add4]; abel
  have hPB : ∀ a b, 0 < ecount a b (g3 :: (D3.reverse ++ [c1])) → dAdj a b := by
    apply ecount_chain
    have e : g3 :: (D3.reverse ++ [c1]) = (D3 ++ [g3]).reverse ++ [c1] := by simp
    rw [e]
    apply List.IsChain.append
    · rw [List.isChain_reverse]; exact hc3.imp (fun a b h => dAdj_symm h)
    · exact List.isChain_singleton _
    · intro x hx y hy
      rw [List.getLast?_reverse, h3] at hx
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
      rw [← hx, ← hy, hc31]; exact ⟨k + 4, rfl⟩
  -- t0 is in S2 (left of the step c1 → c2 of W2')
  have ht0B : S2 (triAt c1 k) = true := by
    apply hB4 c1 k
    apply lt_of_lt_of_le _ (ecount_le_C _ _ _)
    have e : W2' = (g3 :: (B2 ++ E1)) ++ c1 :: c2 :: (F2 ++ B1) := by
      rw [hW2'd]
      have : D2 ++ g2 :: B1 = (D2 ++ [g2]) ++ B1 := by simp
      rw [this, hF2]; simp
    rw [e]; exact ecount_pos_mid _ _ _ _
  have hkB : ∃ kB : Fin 6, (D3.reverse ++ [c1]).head? = some (g3 + dir kB) ∧
      S2 (triAt g3 kB) = true := by
    rcases List.eq_nil_or_concat D3 with hD | ⟨E, z, hD⟩
    · subst hD
      have hg3 : g3 = c3 := by simpa using h3
      refine ⟨k + 4, by simp [← hg3, hc31], ?_⟩
      rw [hg3, hc3d, triAt_third]; exact ht0B
    · rw [List.concat_eq_append] at hD
      subst hD
      have hz : z ∈ E ++ [z] := by simp
      -- the side of S2 along D3 equals the side at c3, which sees t0
      obtain ⟨P3, hP3⟩ : ∃ P3, E ++ [z] = c3 :: P3 := by
        cases E with
        | nil => exact ⟨[], by simpa using h3⟩
        | cons a T =>
          have : a = c3 := by simpa using h3
          exact ⟨T ++ [z], by simp [this]⟩
      have hch3 : List.IsChain dAdj (c3 :: P3) := by
        rw [← hP3]; exact hc3.left_of_append
      have hoff3 : ∀ w ∈ c3 :: P3, w ∉ W2' := by
        intro w hw; rw [← hP3] at hw; exact hnotW2' w hw
      have hzc : S2 (triAt z 0) = S2 (triAt c3 0) :=
        side_chain hB3 P3 c3 hch3 hoff3 z (by rw [← hP3]; exact hz)
      have hc3S : S2 (triAt c3 0) = true := by
        rw [← side_const hB3 (hoff3 c3 (by simp)) (k + 4), hc3d, triAt_third]; exact ht0B
      obtain ⟨j, hj, hjS⟩ := first_step hB3 g3 E z hc3 (hnotW2' z hz) (by rw [hzc, hc3S])
      exact ⟨j, by simp [hj], hjS⟩
  obtain ⟨kB, hkB1, hkB2⟩ := hkB
  obtain ⟨S31, S4, hB1', hC2, hC3, hC4, hC5⟩ :=
    chord_split' hex g3 c1 (B2 ++ E1) (D2 ++ g2 :: B1) D3.reverse S2 hB2 hB3 hB4 hQB hQBW hPB
      kB hkB1 hkB2
  have eB : g3 :: ((B2 ++ E1) ++ c1 :: D3.reverse.reverse) = g3 :: (B2 ++ g1 :: (D1.reverse ++ D3)) := by
    have : g1 :: (D1.reverse ++ D3) = (g1 :: D1.reverse) ++ D3 := by simp
    rw [this, hE1]; simp
  rw [eB] at hB1'
  -- ===== split C: rotate W4 by one, chord c2 → c3
  obtain ⟨F3, hF3⟩ : ∃ F3, g3 :: D3.reverse = F3 ++ [c3] := by
    rcases List.eq_nil_or_concat D3 with hD | ⟨E, z, hD⟩
    · subst hD; exact ⟨[], by simpa using h3⟩
    · rw [List.concat_eq_append] at hD; subst hD
      cases E with
      | nil =>
        have : z = c3 := by simpa using h3
        exact ⟨[g3], by simp [this]⟩
      | cons a T =>
        have : a = c3 := by simpa using h3
        exact ⟨g3 :: z :: T.reverse, by simp [this]⟩
  set W4 := c1 :: ((D2 ++ g2 :: B1) ++ g3 :: D3.reverse) with hW4d
  set MM := F2 ++ B1 ++ F3 with hMM
  have hrotC : W4.rotate 1 = c2 :: (MM ++ c3 :: [c1]) := by
    have e : W4 = [c1] ++ (c2 :: (MM ++ [c3])) := by
      rw [hW4d, hMM]
      have : (D2 ++ g2 :: B1) ++ g3 :: D3.reverse = (D2 ++ [g2]) ++ B1 ++ (g3 :: D3.reverse) := by
        simp
      rw [this, hF2, hF3]; simp
    rw [e, show (1 : ℕ) = [c1].length from rfl, List.rotate_append_length_eq]; simp
  have hD2 : LSimple (c2 :: (MM ++ c3 :: [c1])) := hrotC ▸ hC2.rotate _
  have hD3 : LBd S4 (c2 :: (MM ++ c3 :: [c1])) := hrotC ▸ hC3.rotate _
  have hD4 : LNorm S4 (c2 :: (MM ++ c3 :: [c1])) := hrotC ▸ hC4.rotate _
  have hc23 : c3 = c2 + dir (k + 2) := by rw [hc3d, hc2d, dir_sum]; abel
  have hPC : ∀ a b, 0 < ecount a b (c2 :: ([] ++ [c3])) → dAdj a b := by
    intro a b hab
    simp only [List.nil_append, ecount, ecount_single] at hab
    split_ifs at hab with hh
    · rw [← hh.1, ← hh.2, hc23]; exact ⟨k + 2, rfl⟩
    · omega
  have ht0C : S4 (triAt c2 (k + 2)) = true := by
    rw [hc2d, triAt_add2]
    apply hC4 c1 k
    apply lt_of_lt_of_le _ (ecount_le_C _ _ _)
    have e : W4 = [] ++ c1 :: c2 :: (F2 ++ B1 ++ g3 :: D3.reverse) := by
      rw [hW4d]
      have : D2 ++ g2 :: B1 = (D2 ++ [g2]) ++ B1 := by simp
      rw [this, hF2]; simp
    rw [e]; exact ecount_pos_mid _ _ _ _
  obtain ⟨S23, S0, hE1', hE2, hE3, hE4, hE5⟩ :=
    chord_split' hex c2 c3 MM [c1] [] S4 hD2 hD3 hD4 List.nodup_nil (by simp) hPC (k + 2)
      (by simp [hc23]) ht0C
  have eC : c2 :: (MM ++ c3 :: ([] : List Cell).reverse) = D2 ++ g2 :: (B1 ++ g3 :: D3.reverse) := by
    have : D2 ++ g2 :: (B1 ++ g3 :: D3.reverse) = (D2 ++ [g2]) ++ B1 ++ (g3 :: D3.reverse) := by simp
    rw [this, hF2, hF3, hMM]; simp
  rw [eC] at hE1'
  have eD : c3 :: ([c1] ++ c2 :: ([] : List Cell)) = [c3, c1, c2] := by simp
  rw [eD] at hE2 hE3 hE4
  refine ⟨S12, S31, S23, S0, ?_, ?_, ?_, hE2, hE3, hE4, ?_⟩
  · rcases hA1 with h | h
    · exact Or.inl h.2.2
    · exact Or.inr h
  · rcases hB1' with h | h
    · exact Or.inl h.2.2
    · exact Or.inr h
  · rcases hE1' with h | h
    · exact Or.inl h.2.2
    · exact Or.inr h
  · intro τ
    have a1 := hA5 τ
    have a2 := hC5 τ
    have a3 := hE5 τ
    omega

end TRI3

end RG

end PQT

/-! 8100c3d9 D5g2: the triangle piece of a tripod split has no inside cell. -/

namespace PQT

section TRI0

lemma tri_no_inside {S0 : Tri → Bool} (c1 : Cell) (k : Fin 6)
    (hS0 : LBd S0 [c1 + dir (k + 1), c1, c1 + dir k]) (Rb : ℤ)
    (hfar : ∀ c, ¬ inBox Rb c → S0 (triAt c 0) = false) (z : Cell)
    (hz : z ∉ [c1 + dir (k + 1), c1, c1 + dir k]) : S0 (triAt z 0) = false := by
  have key : ∀ n m : ℕ, z + (n : ℤ) • dir 0 ∈ [c1 + dir (k + 1), c1, c1 + dir k] →
      z + (m : ℤ) • dir 3 ∈ [c1 + dir (k + 1), c1, c1 + dir k] → False := by
    intro n m hn hm
    obtain ⟨a, b⟩ := z
    obtain ⟨i, j⟩ := c1
    fin_cases k <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff, dir, Prod.smul_mk,
        smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Fin.isValue] at hn hm hz <;>
      push_cast at hn hm hz <;> omega
  by_cases hR : ∀ n : ℕ, z + (n : ℤ) • dir 0 ∉ [c1 + dir (k + 1), c1, c1 + dir k]
  · exact ray_out hS0 Rb hfar z 0 (Or.inl rfl) hR
  · push_neg at hR
    obtain ⟨n, hn⟩ := hR
    exact ray_out hS0 Rb hfar z 3 (Or.inr rfl) (fun m hm => key n m hn hm)

end TRI0

end PQT

/-! 8100c3d9 D5h: the region record of the tripod recursion, its bridge to `RData`, the
abstract-interface axioms of `dec_of_step`, the generic child lemma and the partition lemma. -/

namespace PQT

section ST

variable {V : Type}

/-- global data: grid model `phi`, box radius, BFS layering `L` with parent `p` and root `r` -/
structure Ctx (V : Type) where
  phi : Cell → V
  Rb : ℤ
  L : V → ℕ
  p : V → V
  r : V

structure Ctx.Good (X : Ctx V) : Prop where
  hfib : ∀ v c c', X.phi c = v → X.phi c' = v →
    Relation.ReflTransGen (PRel (fun x => X.phi x = v)) c c'
  hpar : ∀ v, 0 < X.L v → (Gphi X.phi).Adj v (X.p v) ∧ X.L (X.p v) + 1 = X.L v
  hroot : ∀ c, X.L (X.phi c) = 0 → X.phi c = X.r

/-- a region: list walk, side, three arc parts (arcs `[0,s1)`, `[s1,s2)`, `[s2,n)`), assigned set -/
structure Rg (V : Type) where
  l : List Cell
  S : Tri → Bool
  prt : Fin 3 → Finset V
  s1 : ℕ
  s2 : ℕ
  A : Finset V

def arcOf (s1 s2 i : ℕ) : Fin 3 := if i < s1 then 0 else if i < s2 then 1 else 2

def arcRep (s1 s2 : ℕ) (j : Fin 3) : ℕ := if j = 0 then 0 else if j = 1 then s1 else s2

lemma arcRep_lt {s1 s2 n : ℕ} (h12 : s1 < s2) (h2n : s2 < n) (j : Fin 3) : arcRep s1 s2 j < n := by
  unfold arcRep; split_ifs <;> omega

lemma arcOf_rep {s1 s2 : ℕ} (h01 : 0 < s1) (h12 : s1 < s2) (j : Fin 3) :
    arcOf s1 s2 (arcRep s1 s2 j) = j := by
  unfold arcOf arcRep
  fin_cases j <;> simp <;> (try split_ifs) <;> omega

lemma rep_arcOf (s1 s2 i : ℕ) :
    arcRep s1 s2 (arcOf s1 s2 i) = if i < s1 then 0 else if i < s2 then s1 else s2 := by
  unfold arcOf arcRep
  split_ifs <;> simp_all

structure Rg.Good (X : Ctx V) (ρ : Rg V) : Prop where
  hl : LSimple ρ.l
  hS : LBd ρ.S ρ.l
  hN : LNorm ρ.S ρ.l
  hfar : ∀ τ : Tri, ρ.S τ = true → -X.Rb ≤ τ.1 ∧ τ.1 ≤ X.Rb ∧ -X.Rb ≤ τ.2.1 ∧ τ.2.1 ≤ X.Rb
  h01 : 0 < ρ.s1
  h12 : ρ.s1 < ρ.s2
  h2n : ρ.s2 < ρ.l.length
  harc : ∀ i (hi : i < ρ.l.length), X.phi ρ.l[i] ∈ ρ.prt (arcOf ρ.s1 ρ.s2 i)
  hpA : ∀ j, ρ.prt j ⊆ ρ.A
  hpc : ∀ j, ((Gphi X.phi).induce (ρ.prt j : Set V)).Preconnected
  hpd : ∀ i j, ρ.prt i = ρ.prt j ∨ Disjoint (ρ.prt i) (ρ.prt j)
  hinv : ∀ c, Ins ρ.S ρ.l c → X.phi c ∈ ρ.A → ∃ j, X.phi c ∈ ρ.prt j
  hr : X.r ∈ ρ.A

open Classical in
/-- interior vertices: owners of inside cells that are not yet assigned -/
noncomputable def Rg.I [Fintype V] (X : Ctx V) (ρ : Rg V) : Finset V :=
  Finset.univ.filter (fun v => (∃ c, X.phi c = v ∧ Ins ρ.S ρ.l c) ∧ v ∉ ρ.A)

open Classical in
noncomputable def Rg.Qs (ρ : Rg V) : Finset (Finset V) := Finset.univ.image ρ.prt

open Classical in
/-- measure: number of side triangles in the box -/
noncomputable def Rg.m (X : Ctx V) (ρ : Rg V) : ℕ :=
  ((Finset.Icc (-X.Rb) X.Rb ×ˢ (Finset.Icc (-X.Rb) X.Rb ×ˢ (Finset.univ : Finset Bool))).filter
    (fun τ => ρ.S τ = true)).card

lemma Rg.mem_I [Fintype V] {X : Ctx V} {ρ : Rg V} {v : V} :
    v ∈ ρ.I X ↔ (∃ c, X.phi c = v ∧ Ins ρ.S ρ.l c) ∧ v ∉ ρ.A := by
  classical
  unfold Rg.I; simp

namespace Rg

variable {X : Ctx V} {ρ : Rg V}

lemma Good.part_ne (hρ : ρ.Good X) (j : Fin 3) :
    X.phi (ρ.l[arcRep ρ.s1 ρ.s2 j]'(arcRep_lt hρ.h12 hρ.h2n j)) ∈ ρ.prt j := by
  have := hρ.harc _ (arcRep_lt hρ.h12 hρ.h2n j)
  rwa [arcOf_rep hρ.h01 hρ.h12] at this

lemma Good.walk_asg (hρ : ρ.Good X) {w : Cell} (hw : w ∈ ρ.l) : ∃ j, X.phi w ∈ ρ.prt j := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  exact ⟨_, hρ.harc i hi⟩

lemma Good.walk_A (hρ : ρ.Good X) {w : Cell} (hw : w ∈ ρ.l) : X.phi w ∈ ρ.A := by
  obtain ⟨j, hj⟩ := hρ.walk_asg hw
  exact hρ.hpA j hj

/-- a walk cell of `ρ` off a sub-walk `W` is not on the inner side of `W` -/
lemma Good.walk_out (hρ : ρ.Good X) {W : List Cell} {Sc : Tri → Bool} (hSc : LBd Sc W)
    (hle : ∀ τ, Sc τ = true → ρ.S τ = true) {x : Cell} (hx : x ∈ ρ.l) (hxW : x ∉ W) :
    Sc (triAt x 0) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  obtain ⟨k, hk⟩ := walk_false hρ.hl hρ.hS hρ.hN hx
  have : Sc (triAt x k) = true := (side_const hSc hxW k).trans h
  rw [hle _ this] at hk
  exact absurd hk (by simp)

/-- an inside cell of a sub-walk is an inside cell of `ρ` -/
lemma Good.ins_of_sub (hρ : ρ.Good X) {W : List Cell} {Sc : Tri → Bool} (hSc : LBd Sc W)
    (hle : ∀ τ, Sc τ = true → ρ.S τ = true) {c : Cell} (hc : Ins Sc W c) : Ins ρ.S ρ.l c := by
  refine ⟨fun hcl => ?_, hle _ hc.2⟩
  have := hρ.walk_out hSc hle hcl hc.1
  rw [hc.2] at this
  exact absurd this (by simp)

open Classical in
/-- the routing data of a region -/
noncomputable def toR (X : Ctx V) (ρ : Rg V) : RData V where
  phi := X.phi
  S := ρ.S
  l := ρ.l
  asg v := ∃ j, v ∈ ρ.prt j
  pof u := if h : ∃ j, u ∈ ρ.prt j then (ρ.prt h.choose : Set V) else ∅
  L := X.L
  p := X.p

lemma toR_pof {u : V} (h : ∃ j, u ∈ ρ.prt j) : (toR X ρ).pof u = (ρ.prt h.choose : Set V) := by
  classical
  simp only [toR]; rw [dif_pos h]

theorem Good.rdata (hX : X.Good) (hρ : ρ.Good X) : (toR X ρ).Good := by
  classical
  refine ⟨hρ.hS, hX.hfib, fun w hw => hρ.walk_asg hw, ?_, ?_, ?_, ?_, ?_, hX.hpar⟩
  · intro u hu
    show u ∈ (toR X ρ).pof u
    rw [toR_pof hu]; exact hu.choose_spec
  · intro u hu w hw
    rw [toR_pof hu] at hw
    have hw' : ∃ j, w ∈ ρ.prt j := ⟨_, hw⟩
    refine ⟨hw', ?_⟩
    show (toR X ρ).pof w = (toR X ρ).pof u
    rw [toR_pof hu, toR_pof hw']
    rcases hρ.hpd hw'.choose hu.choose with he | hd
    · rw [he]
    · exact absurd (Finset.disjoint_left.1 hd hw'.choose_spec hw) (by simp)
  · intro u hu x y hx hy
    show Relation.ReflTransGen (PRel (fun z => X.phi z ∈ (toR X ρ).pof u)) x y
    have hx' : X.phi x ∈ (toR X ρ).pof u := hx
    have hy' : X.phi y ∈ (toR X ρ).pof u := hy
    rw [toR_pof hu] at hx' hy' ⊢
    exact cells_conn' X.phi hX.hfib _ (hρ.hpc _) x y hx' hy'
  · intro u hu
    show ∃ w ∈ ρ.l, X.phi w ∈ (toR X ρ).pof u
    rw [toR_pof hu]
    exact ⟨_, List.getElem_mem _, hρ.part_ne _⟩
  · intro c hc hna
    show 0 < X.L (X.phi c)
    by_contra h0
    have hr := hX.hroot c (Nat.eq_zero_of_not_pos h0)
    apply hna
    exact hρ.hinv c hc (hr ▸ hρ.hr)

/-! ### the interface axioms of `dec_of_step` -/

lemma hA1 [Fintype V] (hρ : ρ.Good X) : ∀ Q ∈ ρ.Qs, Disjoint Q (ρ.I X) := by
  classical
  intro Q hQ
  simp only [Qs, Finset.mem_image, Finset.mem_univ, true_and] at hQ
  obtain ⟨j, rfl⟩ := hQ
  rw [Finset.disjoint_left]
  intro v hv hvI
  exact (mem_I.1 hvI).2 (hρ.hpA j hv)

lemma hA2 [Fintype V] (hX : X.Good) (hρ : ρ.Good X) :
    ∀ v ∈ ρ.I X, ∀ w, (Gphi X.phi).Adj v w → w ∈ ρ.I X ∨ ∃ Q ∈ ρ.Qs, w ∈ Q := by
  classical
  intro v hv w hvw
  obtain ⟨⟨c0, hc0, hins⟩, hvA⟩ := mem_I.1 hv
  -- every cell of `v` is inside
  have hall : ∀ c, X.phi c = v → Ins ρ.S ρ.l c := by
    intro c hc
    rcases cross_path' hρ.hS (hX.hfib v c0 c hc0 hc) hins.1 with ⟨w', hw', hw'v⟩ | ⟨h1, h2⟩
    · exact absurd (hw'v ▸ hρ.walk_A hw') hvA
    · exact ⟨h1, h2.trans hins.2⟩
  have hQ : ∀ j, ρ.prt j ∈ ρ.Qs := fun j => by simp [Qs]
  have key : ∀ c d, X.phi c = v → X.phi d = w → dAdj c d →
      w ∈ ρ.I X ∨ ∃ Q ∈ ρ.Qs, w ∈ Q := by
    intro c d hc hd hcd
    rcases Ins.adj hρ.hS (hall c hc) hcd with hdl | hdi
    · obtain ⟨j, hj⟩ := hρ.walk_asg hdl
      exact Or.inr ⟨_, hQ j, hd ▸ hj⟩
    · by_cases hwA : w ∈ ρ.A
      · obtain ⟨j, hj⟩ := hρ.hinv d hdi (hd ▸ hwA)
        exact Or.inr ⟨_, hQ j, hd ▸ hj⟩
      · exact Or.inl (mem_I.2 ⟨⟨d, hd, hdi⟩, hwA⟩)
  rw [Gphi, SimpleGraph.fromRel_adj] at hvw
  rcases hvw.2 with ⟨c, d, hc, hd, hcd⟩ | ⟨d, c, hd, hc, hdc⟩
  · exact key c d hc hd hcd
  · exact key c d hc hd (dAdj_symm hdc)

lemma hA3 (_hρ : ρ.Good X) : ρ.Qs.card ≤ 3 := by
  classical
  unfold Qs
  exact (Finset.card_image_le).trans (by simp)

lemma hA4 (hρ : ρ.Good X) : ∅ ∉ ρ.Qs := by
  classical
  intro h
  simp only [Qs, Finset.mem_image, Finset.mem_univ, true_and] at h
  obtain ⟨j, hj⟩ := h
  have := hρ.part_ne j
  rw [hj] at this
  simp at this

/-! ### the generic child lemma -/

/-- a path from an inside cell of `W` to a cell that is not inside meets `W` -/
lemma hit_walk {Sc : Tri → Bool} {W : List Cell} (hSc : LBd Sc W) {Q : Cell → Prop} {c x : Cell}
    (h : Relation.ReflTransGen (PRel Q) c x) (hc : Ins Sc W c)
    (hx : x ∉ W → Sc (triAt x 0) = false) : ∃ z ∈ W, Q z := by
  rcases cross_path' hSc h hc.1 with h1 | ⟨h1, h2⟩
  · exact h1
  · have := hx h1
    rw [h2, hc.2] at this
    exact absurd this (by simp)

theorem child_good [Fintype V] [DecidableEq V] (hX : X.Good) (hρ : ρ.Good X)
    (W : List Cell) (Sc : Tri → Bool) (hW : LSimple W) (hSc : LBd Sc W) (hNc : LNorm Sc W)
    (hle : ∀ τ, Sc τ = true → ρ.S τ = true)
    (Y0 : Finset V) (hYA : Disjoint Y0 ρ.A)
    (hYc : ((Gphi X.phi).induce (Y0 : Set V)).Preconnected)
    (hY : ∀ y ∈ Y0, ∃ x, X.phi x = y ∧ (x ∉ W → Sc (triAt x 0) = false))
    (B : ℕ → Finset V) (hB : ∀ j, (∃ i, B j = ρ.prt i) ∨ B j = Y0)
    (a b : ℕ) (hblk : ∀ i (hi : i < W.length), X.phi W[i] ∈ B (blk a b i)) :
    ∃ ρ' : Rg V, ρ'.Good X ∧ ρ'.l = W ∧ ρ'.S = Sc ∧ ρ'.A = ρ.A ∪ Y0 ∧
      ρ'.Qs ⊆ insert Y0 ρ.Qs := by
  classical
  obtain ⟨s1, s2, h01, h12, h2n, hs⟩ := arcs3 a b W.length hW.2.1
  let P : Fin 3 → Finset V := fun j => B (blk a b (arcRep s1 s2 j))
  have hPa : ∀ i (hi : i < W.length), X.phi W[i] ∈ P (arcOf s1 s2 i) := by
    intro i hi
    show X.phi W[i] ∈ B (blk a b (arcRep s1 s2 (arcOf s1 s2 i)))
    rw [rep_arcOf, ← hs i hi]
    exact hblk i hi
  have hPc : ∀ j, (∃ i, P j = ρ.prt i) ∨ P j = Y0 := fun j => hB _
  have hPA : ∀ j, P j ⊆ ρ.A ∪ Y0 := by
    intro j
    rcases hPc j with ⟨i, hi⟩ | hi
    · rw [hi]; exact (hρ.hpA i).trans Finset.subset_union_left
    · rw [hi]; exact Finset.subset_union_right
  -- membership in a part via a walk cell
  have hwalk : ∀ z ∈ W, ∃ j, X.phi z ∈ P j := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    exact ⟨_, hPa i hi⟩
  refine ⟨⟨W, Sc, P, s1, s2, ρ.A ∪ Y0⟩, ⟨hW, hSc, hNc, fun τ hτ => hρ.hfar τ (hle τ hτ),
    h01, h12, h2n, hPa, hPA, ?_, ?_, ?_, Finset.mem_union_left _ hρ.hr⟩, rfl, rfl, rfl, ?_⟩
  · intro j
    rcases hPc j with ⟨i, hi⟩ | hi
    · show ((Gphi X.phi).induce (P j : Set V)).Preconnected
      rw [hi]; exact hρ.hpc i
    · show ((Gphi X.phi).induce (P j : Set V)).Preconnected
      rw [hi]; exact hYc
  · intro i j
    show P i = P j ∨ Disjoint (P i) (P j)
    rcases hPc i with ⟨i', hi⟩ | hi <;> rcases hPc j with ⟨j', hj⟩ | hj
    · rw [hi, hj]; exact hρ.hpd i' j'
    · right; rw [hi, hj]
      exact Finset.disjoint_of_subset_left (hρ.hpA i') hYA.symm
    · right; rw [hi, hj]
      exact Finset.disjoint_of_subset_right (hρ.hpA j') hYA
    · left; rw [hi, hj]
  · intro c hc hcA
    show ∃ j, X.phi c ∈ P j
    rcases Finset.mem_union.1 hcA with hA | hY0
    · obtain ⟨j, hj⟩ := hρ.hinv c (hρ.ins_of_sub hSc hle hc) hA
      have hx := hρ.part_ne j
      set x := ρ.l[arcRep ρ.s1 ρ.s2 j]'(arcRep_lt hρ.h12 hρ.h2n j)
      have hpath := cells_conn' X.phi hX.hfib _ (hρ.hpc j) c x hj hx
      obtain ⟨z, hzW, hz⟩ := hit_walk hSc hpath hc
        (fun hxW => hρ.walk_out hSc hle (List.getElem_mem _) hxW)
      obtain ⟨i, hi⟩ := hwalk z hzW
      rcases hPc i with ⟨i', hi'⟩ | hi'
      · rw [hi'] at hi
        rcases hρ.hpd i' j with he | hd
        · exact ⟨i, by rw [hi', he]; exact hj⟩
        · exact absurd (Finset.disjoint_left.1 hd hi hz) (by simp)
      · rw [hi'] at hi
        exact absurd (hρ.hpA j hz) (Finset.disjoint_left.1 hYA hi)
    · obtain ⟨x, hx, hxo⟩ := hY _ hY0
      have hpath := hX.hfib (X.phi c) c x rfl hx
      obtain ⟨z, hzW, hz⟩ := hit_walk hSc hpath hc hxo
      obtain ⟨i, hi⟩ := hwalk z hzW
      exact ⟨i, by rw [← hz]; exact hi⟩
  · intro Q hQ
    simp only [Qs, Finset.mem_image, Finset.mem_univ, true_and] at hQ
    obtain ⟨j, rfl⟩ := hQ
    rcases hPc j with ⟨i, hi⟩ | hi
    · rw [hi]; exact Finset.mem_insert_of_mem (by simp [Qs])
    · rw [hi]; exact Finset.mem_insert_self _ _

/-! ### the partition of the interior among the children -/

lemma bz_le_one (b : Bool) : bz b ≤ 1 := by cases b <;> simp [bz]
lemma bz_nonneg (b : Bool) : 0 ≤ bz b := by cases b <;> simp [bz]
lemma bz_true {b : Bool} : bz b = 1 ↔ b = true := by cases b <;> simp [bz]

/-- two regions over disjoint sides with walks owned by their common assigned set have disjoint
interiors -/
lemma I_disj [Fintype V] (hX : X.Good) {c c' : Rg V} (hS : LBd c.S c.l) (hS' : LBd c'.S c'.l)
    (hsum : ∀ τ, bz (c.S τ) + bz (c'.S τ) ≤ 1)
    (hown : ∀ x ∈ c.l, X.phi x ∈ c.A) : Disjoint (c.I X) (c'.I X) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨⟨x, hx, hxi⟩, hvA⟩ := mem_I.1 hv
  obtain ⟨⟨y, hy, hyi⟩, _⟩ := mem_I.1 hv'
  rcases cross_path' hS (hX.hfib v x y hx hy) hxi.1 with ⟨w, hw, hwv⟩ | ⟨_, h2⟩
  · exact hvA (hwv ▸ hown w hw)
  · have := hsum (triAt y 0)
    rw [h2, hxi.2, hyi.2] at this
    simp [bz] at this

lemma mem_foldrI [Fintype V] [DecidableEq V] (ch : List (Rg V)) (v : V) :
    v ∈ ch.foldr (fun c s => c.I X ∪ s) ∅ ↔ ∃ c ∈ ch, v ∈ c.I X := by
  classical
  induction ch with
  | nil => simp
  | cons c t ih => simp [List.foldr_cons, Finset.mem_union, ih]

lemma sum_pos_mem (ch : List (Rg V)) (τ : Tri) (h : 0 < (ch.map (fun c => bz (c.S τ))).sum) :
    ∃ c ∈ ch, c.S τ = true := by
  induction ch with
  | nil => simp at h
  | cons c t ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hc : c.S τ = true
    · exact ⟨c, by simp, hc⟩
    · have : bz (c.S τ) = 0 := by simp [bz, hc]
      obtain ⟨d, hd, hd'⟩ := ih (by omega)
      exact ⟨d, by simp [hd], hd'⟩

lemma sum_nonneg' (ch : List (Rg V)) (τ : Tri) : 0 ≤ (ch.map (fun c => bz (c.S τ))).sum :=
  List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨c, _, rfl⟩; exact bz_nonneg _)

lemma pairwise_I [Fintype V] (hX : X.Good) : ∀ (ch : List (Rg V)),
    (∀ c ∈ ch, LBd c.S c.l) → (∀ c ∈ ch, ∀ x ∈ c.l, X.phi x ∈ c.A) →
    (∀ τ, (ch.map (fun c => bz (c.S τ))).sum ≤ 1) →
    ch.Pairwise (fun a b => Disjoint (a.I X) (b.I X)) := by
  intro ch
  induction ch with
  | nil => intros; exact List.Pairwise.nil
  | cons c t ih =>
    intro hS hown hsum
    refine List.pairwise_cons.2 ⟨fun c' hc' => ?_, ih (fun d hd => hS d (by simp [hd]))
      (fun d hd => hown d (by simp [hd])) (fun τ => ?_)⟩
    · refine I_disj hX (hS c (by simp)) (hS c' (by simp [hc'])) (fun τ => ?_) (hown c (by simp))
      have h1 := hsum τ
      simp only [List.map_cons, List.sum_cons] at h1
      have h2 : bz (c'.S τ) ≤ (t.map (fun c => bz (c.S τ))).sum :=
        List.single_le_sum (by simp only [List.mem_map]; rintro _ ⟨c, _, rfl⟩; exact bz_nonneg _) _
          (List.mem_map.2 ⟨c', hc', rfl⟩)
      omega
    · have h1 := hsum τ
      simp only [List.map_cons, List.sum_cons] at h1
      have := bz_nonneg (c.S τ)
      omega

/-- the partition of the interior among the children of a step -/
theorem I_partition [Fintype V] [DecidableEq V] (hX : X.Good) (hρ : ρ.Good X) (Y0 : Finset V)
    (S0 : Tri → Bool) (ch : List (Rg V))
    (hsum : ∀ τ, bz (ρ.S τ) = (ch.map (fun c => bz (c.S τ))).sum + bz (S0 τ))
    (hcS : ∀ c ∈ ch, LBd c.S c.l) (hcA : ∀ c ∈ ch, c.A = ρ.A ∪ Y0)
    (hown : ∀ c ∈ ch, ∀ x ∈ c.l, X.phi x ∈ ρ.A ∪ Y0)
    (hS0 : ∀ x, S0 (triAt x 0) = true → Ins ρ.S ρ.l x → X.phi x ∈ ρ.A ∪ Y0) :
    ch.Pairwise (fun a b => Disjoint (a.I X) (b.I X)) ∧
      ch.foldr (fun c s => c.I X ∪ s) ∅ = ρ.I X \ Y0 := by
  classical
  have hs1 : ∀ τ, (ch.map (fun c => bz (c.S τ))).sum ≤ 1 := by
    intro τ
    have h1 := hsum τ; have h2 := bz_le_one (ρ.S τ); have h3 := bz_nonneg (S0 τ); omega
  refine ⟨pairwise_I hX ch hcS (fun c hc x hx => (hcA c hc).symm ▸ hown c hc x hx) hs1, ?_⟩
  ext v
  rw [mem_foldrI, Finset.mem_sdiff]
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨⟨x, hx, hxi⟩, hvA⟩ := mem_I.1 hv
    rw [hcA c hc] at hvA
    have hle : ∀ τ, c.S τ = true → ρ.S τ = true := by
      intro τ hτ
      have h1 := hsum τ
      have h2 : bz (c.S τ) ≤ (ch.map (fun c => bz (c.S τ))).sum :=
        List.single_le_sum (by simp only [List.mem_map]; rintro _ ⟨c, _, rfl⟩; exact bz_nonneg _) _
          (List.mem_map.2 ⟨c, hc, rfl⟩)
      rw [bz_true.2 hτ] at h2
      have := bz_nonneg (S0 τ); have := bz_le_one (ρ.S τ)
      exact bz_true.1 (by omega)
    refine ⟨mem_I.2 ⟨⟨x, hx, hρ.ins_of_sub (hcS c hc) hle hxi⟩,
      fun h => hvA (Finset.mem_union_left _ h)⟩, fun h => hvA (Finset.mem_union_right _ h)⟩
  · rintro ⟨hv, hvY⟩
    obtain ⟨⟨x, hx, hxi⟩, hvA⟩ := mem_I.1 hv
    have hnot : X.phi x ∉ ρ.A ∪ Y0 := by
      rw [hx]; simp [hvA, hvY]
    have h1 := hsum (triAt x 0)
    rw [hxi.2] at h1
    have hS0f : S0 (triAt x 0) = false := by
      by_contra h; rw [Bool.not_eq_false] at h; exact hnot (hS0 x h hxi)
    rw [hS0f] at h1
    have e1 : bz true = 1 := rfl
    have e0 : bz false = 0 := rfl
    rw [e1, e0] at h1
    obtain ⟨c, hc, hcx⟩ := sum_pos_mem ch (triAt x 0) (by omega)
    refine ⟨c, hc, mem_I.2 ⟨⟨x, hx, fun hxl => hnot (hown c hc x hxl), hcx⟩, ?_⟩⟩
    rw [hcA c hc]; rw [← hx]; exact hnot

end Rg

end ST

end PQT

/-! 8100c3d9 D5i: child lemmas in block / tripod-shape form, the measure drop, connectivity of a
cell set's owners, and side constancy along an off-walk chain. -/

namespace PQT

section ST2

variable {V : Type}

lemma FHyp.route_chain {D W : Cell → Prop} {f : Cell → Cell} {μ1 μ2 : Cell → ℕ}
    (h : FHyp D W f μ1 μ2) {c : Cell} (hc : D c ∨ W c) : List.IsChain dAdj (route W f c) := by
  apply itl_chain
  intro i hi
  rw [Function.iterate_succ_apply']
  exact (h.2 _ (h.dom hc i hi)).2.1

/-- side constancy along a chain of cells off the walk -/
lemma chain_out {Sc : Tri → Bool} {W : List Cell} (hS : LBd Sc W) :
    ∀ (U : List Cell), List.IsChain dAdj U → (∀ x ∈ U, x ∉ W) →
      (∀ a t, U = a :: t → Sc (triAt a 0) = false) → ∀ x ∈ U, Sc (triAt x 0) = false := by
  intro U
  induction U with
  | nil => intros; simp_all
  | cons a t ih =>
    intro hch hoff hhd x hx
    have ha := hhd a t rfl
    rcases List.mem_cons.1 hx with rfl | hxt
    · exact ha
    · cases t with
      | nil => simp at hxt
      | cons b t' =>
        rw [List.isChain_cons_cons] at hch
        obtain ⟨⟨k, hk⟩, hch'⟩ := hch
        refine ih hch' (fun y hy => hoff y (List.mem_cons_of_mem _ hy)) ?_ x hxt
        rintro a' t'' he
        rw [← (List.cons.inj he).1, side_adj hS (hoff a (by simp)) (hoff b (by simp)) k hk, ha]

/-- the owners of a cell-connected list of cells induce a preconnected subgraph -/
lemma conn_of_cells [DecidableEq V] (phi : Cell → V) (C : List Cell)
    (h : ∀ x ∈ C, ∀ y ∈ C, Relation.ReflTransGen (PRel (· ∈ C)) x y) :
    ((Gphi phi).induce ((C.map phi).toFinset : Set V)).Preconnected := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  have hu' : u ∈ (C.map phi).toFinset := hu
  have hv' : v ∈ (C.map phi).toFinset := hv
  simp only [List.mem_toFinset, List.mem_map] at hu' hv'
  obtain ⟨x, hx, rfl⟩ := hu'
  obtain ⟨y, hy, rfl⟩ := hv'
  have key : ∀ z, Relation.ReflTransGen (PRel (· ∈ C)) x z → ∀ hz : phi z ∈
      ((C.map phi).toFinset : Set V),
      ((Gphi phi).induce ((C.map phi).toFinset : Set V)).Reachable ⟨phi x, hu⟩ ⟨phi z, hz⟩ := by
    intro z hxz
    induction hxz with
    | refl => intro _; rfl
    | tail hab hbc ih =>
      rename_i b c
      intro hc
      have hb : phi b ∈ ((C.map phi).toFinset : Set V) := by
        show phi b ∈ (C.map phi).toFinset
        simp only [List.mem_toFinset, List.mem_map]; exact ⟨b, hbc.1, rfl⟩
      refine (ih hb).trans ?_
      by_cases he : phi b = phi c
      · have : (⟨phi b, hb⟩ : ((C.map phi).toFinset : Set V)) = ⟨phi c, hc⟩ := Subtype.ext he
        rw [this]
      · apply SimpleGraph.Adj.reachable
        show (Gphi phi).Adj (phi b) (phi c)
        rw [Gphi, SimpleGraph.fromRel_adj]
        exact ⟨he, Or.inl ⟨b, c, rfl, rfl, hbc.2.2⟩⟩
  exact key y (h x hx y hy) hv

namespace Rg

variable {X : Ctx V} {ρ : Rg V}

/-- the measure drops when the side shrinks strictly -/
lemma m_lt (hρ : ρ.Good X) {c : Rg V} (hle : ∀ τ, c.S τ = true → ρ.S τ = true) (τ0 : Tri)
    (h0 : ρ.S τ0 = true) (h1 : c.S τ0 = false) : c.m X < ρ.m X := by
  classical
  unfold m
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨τ0, ?_, ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hρ.hfar τ0 h0
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
      exact ⟨⟨⟨a1, a2⟩, a3, a4⟩, h0⟩
    · simp [h1]
  · intro τ hτ
    simp only [Finset.mem_filter] at hτ ⊢
    exact ⟨hτ.1, hle τ hτ.2⟩

/-- the child lemma with the walk given as three blocks -/
theorem child_blocks [Fintype V] [DecidableEq V] (hX : X.Good) (hρ : ρ.Good X)
    (X1 X2 X3 : List Cell) (Sc : Tri → Bool) (hW : LSimple (X1 ++ X2 ++ X3))
    (hSc : LBd Sc (X1 ++ X2 ++ X3)) (hNc : LNorm Sc (X1 ++ X2 ++ X3))
    (hle : ∀ τ, Sc τ = true → ρ.S τ = true)
    (Y0 : Finset V) (hYA : Disjoint Y0 ρ.A)
    (hYc : ((Gphi X.phi).induce (Y0 : Set V)).Preconnected)
    (hY : ∀ y ∈ Y0, ∃ x, X.phi x = y ∧ (x ∉ X1 ++ X2 ++ X3 → Sc (triAt x 0) = false))
    (P1 P2 : Finset V) (hP1 : ∃ i, P1 = ρ.prt i) (hP2 : ∃ i, P2 = ρ.prt i)
    (h1 : ∀ x ∈ X1, X.phi x ∈ P1) (h2 : ∀ x ∈ X2, X.phi x ∈ P2) (h3 : ∀ x ∈ X3, X.phi x ∈ Y0) :
    ∃ ρ' : Rg V, ρ'.Good X ∧ ρ'.l = X1 ++ X2 ++ X3 ∧ ρ'.S = Sc ∧ ρ'.A = ρ.A ∪ Y0 ∧
      ρ'.Qs ⊆ insert Y0 ρ.Qs := by
  refine child_good hX hρ _ Sc hW hSc hNc hle Y0 hYA hYc hY
    (fun j => if j = 0 then P1 else if j = 1 then P2 else Y0) ?_ X1.length X2.length ?_
  · intro j
    by_cases h0 : j = 0
    · left; simp only [h0, if_true]; exact hP1
    · by_cases h1' : j = 1
      · left; simp only [h1', if_true, show (1 : ℕ) ≠ 0 by omega, if_false]; exact hP2
      · right; simp [h0, h1']
  · intro i hi
    unfold blk
    by_cases ha : i < X1.length
    · simp only [ha, if_true]
      rw [List.getElem_append_left (by simp only [List.length_append]; omega),
        List.getElem_append_left ha]
      exact h1 _ (List.getElem_mem _)
    · by_cases hb : i < X1.length + X2.length
      · simp only [ha, hb, if_true, if_false, show (1 : ℕ) ≠ 0 by omega]
        rw [List.getElem_append_left (by simp only [List.length_append]; omega),
          List.getElem_append_right (by omega)]
        exact h2 _ (List.getElem_mem _)
      · simp only [ha, hb, if_false, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega]
        rw [List.getElem_append_right (by simp only [List.length_append]; omega)]
        exact h3 _ (List.getElem_mem _)

/-- the child lemma for a tripod-shaped child walk (possibly degenerate); returns the list of
its (zero or one) regions -/
theorem child_shape [Fintype V] [DecidableEq V] (hX : X.Good) (hρ : ρ.Good X)
    (ga gb : Cell) (Ma Mb Ua Aa Ub Ab : List Cell) (Sc : Tri → Bool) (t0 : Tri)
    (hdeg : (∀ τ, Sc τ = false) ∨
      (LSimple (ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa)))) ∧
       LBd Sc (ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa)))) ∧
       LNorm Sc (ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa))))))
    (hle : ∀ τ, Sc τ = true → ρ.S τ = true) (ht0 : Sc t0 = false)
    (Y0 : Finset V) (hYA : Disjoint Y0 ρ.A)
    (hYc : ((Gphi X.phi).induce (Y0 : Set V)).Preconnected)
    (hY : ∀ y ∈ Y0, ∃ x, X.phi x = y ∧
      (x ∉ ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa))) →
        Sc (triAt x 0) = false))
    (Pa Pb : Finset V) (hPa : ∃ i, Pa = ρ.prt i) (hPb : ∃ i, Pb = ρ.prt i)
    (hga : X.phi ga ∈ Pa) (hMa : ∀ x ∈ Ma, X.phi x ∈ Pa) (hAa : ∀ x ∈ Aa, X.phi x ∈ Pa)
    (hgb : X.phi gb ∈ Pb) (hMb : ∀ x ∈ Mb, X.phi x ∈ Pb) (hAb : ∀ x ∈ Ab, X.phi x ∈ Pb)
    (hUa : ∀ x ∈ Ua, X.phi x ∈ Y0) (hUb : ∀ x ∈ Ub, X.phi x ∈ Y0) :
    ∃ ch : List (Rg V), (∀ c ∈ ch, c.Good X ∧ c.A = ρ.A ∪ Y0 ∧ c.Qs ⊆ insert Y0 ρ.Qs ∧
        (∀ x ∈ c.l, X.phi x ∈ ρ.A ∪ Y0) ∧ (∀ τ, c.S τ = true → ρ.S τ = true) ∧
        c.S t0 = false ∧ LBd c.S c.l) ∧
      ∀ τ, (ch.map (fun c => bz (c.S τ))).sum = bz (Sc τ) := by
  rcases hdeg with h0 | ⟨hW, hSc, hNc⟩
  · exact ⟨[], by simp, fun τ => by simp [h0 τ, bz]⟩
  set P := ga :: (Ma ++ Mb ++ gb :: (Ab.reverse ++ Ub.reverse ++ Ua)) with hP
  have hWP : ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa))) = P ++ Aa := by
    simp [hP, List.reverse_append, List.append_assoc]
  have hW' : (Aa ++ ga :: Ma) ++ (Mb ++ gb :: Ab.reverse) ++ (Ub.reverse ++ Ua) = Aa ++ P := by
    simp [hP, List.append_assoc]
  have hrot : (Aa ++ ga :: Ma) ++ (Mb ++ gb :: Ab.reverse) ++ (Ub.reverse ++ Ua) =
      (ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa)))).rotate P.length := by
    rw [hW', hWP, List.rotate_append_length_eq]
  have hmem : ∀ x, x ∈ (Aa ++ ga :: Ma) ++ (Mb ++ gb :: Ab.reverse) ++ (Ub.reverse ++ Ua) ↔
      x ∈ ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa))) := by
    intro x; rw [hrot, List.mem_rotate]
  have hPaA : Pa ⊆ ρ.A := by obtain ⟨i, rfl⟩ := hPa; exact hρ.hpA i
  have hPbA : Pb ⊆ ρ.A := by obtain ⟨i, rfl⟩ := hPb; exact hρ.hpA i
  have hX1 : ∀ x ∈ Aa ++ ga :: Ma, X.phi x ∈ Pa := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hAa x hx
    · exact hga
    · exact hMa x hx
  have hX2 : ∀ x ∈ Mb ++ gb :: Ab.reverse, X.phi x ∈ Pb := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hx
    rcases hx with hx | rfl | hx
    · exact hMb x hx
    · exact hgb
    · exact hAb x hx
  have hX3 : ∀ x ∈ Ub.reverse ++ Ua, X.phi x ∈ Y0 := by
    intro x hx
    simp only [List.mem_append, List.mem_reverse] at hx
    rcases hx with hx | hx
    · exact hUb x hx
    · exact hUa x hx
  obtain ⟨ρ', hg, hl, hS, hA, hQ⟩ := child_blocks hX hρ _ _ _ Sc
    (by rw [hrot]; exact hW.rotate _) (by rw [hrot]; exact hSc.rotate _)
    (by rw [hrot]; exact hNc.rotate _) hle Y0 hYA hYc
    (fun y hy => by
      obtain ⟨x, hx, hx'⟩ := hY y hy
      exact ⟨x, hx, fun hn => hx' (fun hm => hn ((hmem x).2 hm))⟩)
    Pa Pb hPa hPb hX1 hX2 hX3
  refine ⟨[ρ'], ?_, fun τ => by simp [hS]⟩
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  refine ⟨hg, hA, hQ, ?_, by rw [hS]; exact hle, by rw [hS]; exact ht0, hg.hS⟩
  intro x hx
  rw [hl] at hx
  rcases List.mem_append.1 hx with hx' | hx
  · rcases List.mem_append.1 hx' with hx | hx
    · exact Finset.mem_union_left _ (hPaA (hX1 x hx))
    · exact Finset.mem_union_left _ (hPbA (hX2 x hx))
  · exact Finset.mem_union_right _ (hX3 x hx)

end Rg

end ST2

end PQT

/-! 8100c3d9 D5j: helpers for the region step: list segments and the 3-point rotation, the
assigned/unassigned split of a route, side constancy along another route, and the `Ok` facts
for the new part `Y0` (at most one vertex per layer per route; connected). -/

namespace PQT

section ST3

variable {V : Type}

lemma land_self {W : Cell → Prop} {f : Cell → Cell} {c : Cell} (h : W c) : land W f c = c := by
  have : hit W f c = 0 := Nat.sInf_eq_zero.2 (Or.inl (by show W (f^[0] c); exact h))
  simp [land, this]

/-- the segment of indices `[a, b)` -/
def seg (l : List Cell) (a b : ℕ) : List Cell := (l.drop a).take (b - a)

lemma seg_split (l : List Cell) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    seg l a c = seg l a b ++ seg l b c := by
  unfold seg
  rw [show c - a = (b - a) + (c - b) by omega, List.take_add, List.drop_drop]
  first | rw [Nat.add_sub_cancel' hab] | rw [Nat.sub_add_cancel hab]

lemma seg_single (l : List Cell) (i : ℕ) (hi : i < l.length) : seg l i (i + 1) = [l[i]] := by
  unfold seg
  rw [show i + 1 - i = 1 by omega, List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero]

lemma seg_mem {l : List Cell} {a b : ℕ} {x : Cell} (hx : x ∈ seg l a b) :
    ∃ j, ∃ hj : j < l.length, a ≤ j ∧ j < b ∧ l[j] = x := by
  unfold seg at hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take, List.length_drop] at hi
  refine ⟨a + i, by omega, by omega, by omega, ?_⟩
  simp [List.getElem_take, List.getElem_drop]

lemma rotate_seg (l : List Cell) (i : ℕ) (hi : i ≤ l.length) :
    l.rotate i = seg l i l.length ++ seg l 0 i := by
  rw [List.rotate_eq_drop_append_take hi]
  unfold seg
  congr 1
  exact (List.take_of_length_le (by simp)).symm

/-- rotating a list to start at `l[i1]` exposes `l[i2]` and `l[i3]` -/
lemma rot3 (l : List Cell) {i1 i2 i3 : ℕ} (h12 : i1 < i2) (h23 : i2 < i3) (h3 : i3 < l.length) :
    l.rotate i1 = l[i1] :: (seg l (i1 + 1) i2 ++ l[i2] :: (seg l (i2 + 1) i3 ++
      l[i3] :: (seg l (i3 + 1) l.length ++ seg l 0 i1))) := by
  rw [rotate_seg l i1 (by omega), seg_split l (show i1 ≤ i1 + 1 by omega) (show i1 + 1 ≤ l.length by omega),
    seg_single l i1 (by omega),
    seg_split l (show i1 + 1 ≤ i2 by omega) (show i2 ≤ l.length by omega),
    seg_split l (show i2 ≤ i2 + 1 by omega) (show i2 + 1 ≤ l.length by omega),
    seg_single l i2 (by omega),
    seg_split l (show i2 + 1 ≤ i3 by omega) (show i3 ≤ l.length by omega),
    seg_split l (show i3 ≤ i3 + 1 by omega) (show i3 + 1 ≤ l.length by omega),
    seg_single l i3 h3]
  simp [List.append_assoc]

/-- side constancy along an off-walk chain starting at a cell with an outer triangle -/
lemma route_off {Sc : Tri → Bool} {W : List Cell} (hdeg : (∀ τ, Sc τ = false) ∨ LBd Sc W)
    (D : List Cell) (c : Cell) (j : Fin 6) (hhd : ∀ a t, D = a :: t → a = c)
    (hch : List.IsChain dAdj D) (hoff : ∀ x ∈ D, x ∉ W) (ht : Sc (triAt c j) = false) :
    ∀ x ∈ D, Sc (triAt x 0) = false := by
  rcases hdeg with h | hS
  · intro x _; exact h _
  apply chain_out hS D hch hoff
  intro a t he
  have hac := hhd a t he
  subst hac
  rw [← side_const hS (hoff a (by rw [he]; simp)) j]
  exact ht

lemma chain_rtg {C : Cell → Prop} : ∀ (a : Cell) (t : List Cell), List.IsChain dAdj (a :: t) →
    (∀ x ∈ a :: t, C x) → ∀ x ∈ a :: t, Relation.ReflTransGen (PRel C) a x
  | a, [], _, _, x, hx => by
    rw [List.mem_singleton] at hx; subst hx; exact Relation.ReflTransGen.refl
  | a, b :: t, hch, hC, x, hx => by
    rw [List.isChain_cons_cons] at hch
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact Relation.ReflTransGen.refl
    · have := chain_rtg b t hch.2 (fun y hy => hC y (List.mem_cons_of_mem _ hy)) x hx'
      exact Relation.ReflTransGen.head ⟨hC a (by simp), hC b (by simp), hch.1⟩ this

/-- three chains from the corners of a triangle form a connected cell set -/
lemma tri_cells_conn (U1 U2 U3 : List Cell) (c1 c2 c3 : Cell)
    (h1 : List.IsChain dAdj U1) (h2 : List.IsChain dAdj U2) (h3 : List.IsChain dAdj U3)
    (e1 : ∀ a t, U1 = a :: t → a = c1) (e2 : ∀ a t, U2 = a :: t → a = c2)
    (e3 : ∀ a t, U3 = a :: t → a = c3)
    (a12 : dAdj c1 c2) (a13 : dAdj c1 c3) (a23 : dAdj c2 c3) :
    ∀ x ∈ U1 ++ U2 ++ U3, ∀ y ∈ U1 ++ U2 ++ U3,
      Relation.ReflTransGen (PRel (· ∈ U1 ++ U2 ++ U3)) x y := by
  set C := U1 ++ U2 ++ U3 with hC
  have hub : ∀ U : List Cell, ∀ c : Cell, List.IsChain dAdj U → (∀ a t, U = a :: t → a = c) →
      (∀ x ∈ U, x ∈ C) → ∀ x ∈ U, c ∈ C ∧ Relation.ReflTransGen (PRel (· ∈ C)) c x := by
    intro U c hch he hsub x hx
    cases U with
    | nil => simp at hx
    | cons a t =>
      have := he a t rfl
      subst this
      exact ⟨hsub a (by simp), chain_rtg a t hch hsub x hx⟩
  have adj : ∀ a b, (a = c1 ∨ a = c2 ∨ a = c3) → (b = c1 ∨ b = c2 ∨ b = c3) → a ∈ C → b ∈ C →
      Relation.ReflTransGen (PRel (· ∈ C)) a b := by
    intro a b ha hb haC hbC
    by_cases hab : a = b
    · subst hab; exact Relation.ReflTransGen.refl
    have hd : dAdj a b := by
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first | exact absurd rfl hab | assumption | exact dAdj_symm (by assumption)
    exact Relation.ReflTransGen.single ⟨haC, hbC, hd⟩
  have hx : ∀ x ∈ C, ∃ c, (c = c1 ∨ c = c2 ∨ c = c3) ∧ c ∈ C ∧
      Relation.ReflTransGen (PRel (· ∈ C)) c x := by
    intro x hxC
    have hs1 : ∀ z ∈ U1, z ∈ C := fun z hz => by simp [hC, hz]
    have hs2 : ∀ z ∈ U2, z ∈ C := fun z hz => by simp [hC, hz]
    have hs3 : ∀ z ∈ U3, z ∈ C := fun z hz => by simp [hC, hz]
    rcases List.mem_append.1 hxC with h12' | hx3
    · rcases List.mem_append.1 h12' with hx1 | hx2
      · exact ⟨c1, Or.inl rfl, hub U1 c1 h1 e1 hs1 x hx1⟩
      · exact ⟨c2, Or.inr (Or.inl rfl), hub U2 c2 h2 e2 hs2 x hx2⟩
    · exact ⟨c3, Or.inr (Or.inr rfl), hub U3 c3 h3 e3 hs3 x hx3⟩
  intro x hxC y hyC
  obtain ⟨a, ha, haC, hax⟩ := hx x hxC
  obtain ⟨b, hb, hbC, hby⟩ := hx y hyC
  exact ((rtg_symm hax).trans (adj a b ha hb haC hbC)).trans hby

/-- at most three vertices per layer -/
lemma layer3 [DecidableEq V] (phi : Cell → V) (L : V → ℕ) (U1 U2 U3 : List Cell)
    (h1 : ∀ x ∈ U1, ∀ y ∈ U1, L (phi x) = L (phi y) → phi x = phi y)
    (h2 : ∀ x ∈ U2, ∀ y ∈ U2, L (phi x) = L (phi y) → phi x = phi y)
    (h3 : ∀ x ∈ U3, ∀ y ∈ U3, L (phi x) = L (phi y) → phi x = phi y) (i : ℕ) :
    (((U1 ++ U2 ++ U3).map phi).toFinset.filter (fun v => L v = i)).card ≤ 3 := by
  have one : ∀ U : List Cell, (∀ x ∈ U, ∀ y ∈ U, L (phi x) = L (phi y) → phi x = phi y) →
      ((U.map phi).toFinset.filter (fun v => L v = i)).card ≤ 1 := by
    intro U hU
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map] at ha hb
    obtain ⟨⟨x, hx, rfl⟩, hxi⟩ := ha
    obtain ⟨⟨y, hy, rfl⟩, hyi⟩ := hb
    exact hU x hx y hy (by rw [hxi, hyi])
  rw [List.map_append, List.map_append, List.toFinset_append, List.toFinset_append,
    Finset.filter_union, Finset.filter_union]
  have := one U1 h1; have := one U2 h2; have := one U3 h3
  calc _ ≤ ((U1.map phi).toFinset.filter (fun v => L v = i) ∪
          (U2.map phi).toFinset.filter (fun v => L v = i)).card +
        ((U3.map phi).toFinset.filter (fun v => L v = i)).card := Finset.card_union_le _ _
    _ ≤ _ := by
      have := Finset.card_union_le ((U1.map phi).toFinset.filter (fun v => L v = i))
        ((U2.map phi).toFinset.filter (fun v => L v = i))
      omega

namespace RData

variable {R : RData V}

/-- a route = unassigned prefix `U` ++ part segment `Aa` ++ landing cell -/
lemma route_decomp (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c ∨ c ∈ R.l) :
    ∃ U Aa : List Cell, route (· ∈ R.l) R.nx c = U ++ Aa ++ [land (· ∈ R.l) R.nx c] ∧
      (∀ x ∈ U, Ins R.S R.l x ∧ ¬ R.asg (R.phi x)) ∧
      (∀ x ∈ Aa, R.phi x ∈ R.pof (R.phi (land (· ∈ R.l) R.nx c)) ∧ Ins R.S R.l x) ∧
      ∀ x ∈ U ++ Aa, Ins R.S R.l x := by
  obtain ⟨k, h1, h2, h3⟩ := route_split hR hc
  set r := route (· ∈ R.l) R.nx c with hr
  have hrne : r ≠ [] := by
    intro h; have := route_head (· ∈ R.l) R.nx c; rw [← hr, h] at this; simp at this
  have hlast : r.getLast hrne = land (· ∈ R.l) R.nx c := by
    have := route_last (· ∈ R.l) R.nx c
    rw [← hr, List.getLast?_eq_getLast hrne] at this
    exact Option.some.inj this
  have heq : r = List.take k r ++ (List.drop k r).dropLast ++ [land (· ∈ R.l) R.nx c] := by
    conv_lhs => rw [← List.dropLast_append_getLast hrne]
    rw [hlast]
    congr 1
    conv_lhs => rw [← List.take_append_drop k r]
    exact List.dropLast_append_of_ne_nil h2
  have hnd := (fhyp hR).route_nodup hc
  rw [← hr, heq] at hnd
  have hins : ∀ x ∈ List.take k r ++ (List.drop k r).dropLast, Ins R.S R.l x := by
    intro x hx
    have hxr : x ∈ r := by rw [heq]; exact List.mem_append_left _ hx
    rcases (fhyp hR).route_dom hc hxr with h | h
    · exact h
    · exact absurd (List.mem_singleton.2 h) (List.disjoint_of_nodup_append hnd hx)
  refine ⟨List.take k r, (List.drop k r).dropLast, heq, h1, fun x hx => ⟨h3 x
    (List.dropLast_subset _ hx), hins x (List.mem_append_right _ hx)⟩, hins⟩

/-- along the unassigned prefix of a route, equal layers mean equal owners -/
lemma unasg_layer (hR : R.Good) {c : Cell} (hc : Ins R.S R.l c ∨ c ∈ R.l) (U : List Cell) (k : ℕ)
    (hU : U = (route (· ∈ R.l) R.nx c).take k) (hna : ∀ x ∈ U, ¬ R.asg (R.phi x)) :
    ∀ x ∈ U, ∀ y ∈ U, R.L (R.phi x) = R.L (R.phi y) → R.phi x = R.phi y := by
  have key : ∀ i j, i ≤ j → j ≤ hit (· ∈ R.l) R.nx c → R.nx^[j] c ∈ U →
      R.L (R.phi (R.nx^[i] c)) = R.L (R.phi (R.nx^[j] c)) →
      R.phi (R.nx^[i] c) = R.phi (R.nx^[j] c) := by
    intro i j hij hj hjU hL
    exact ((route_unasg hR hc j hij hj (hna _ hjU)).2.2 hL.symm).symm
  intro x hx y hy hxy
  have hx' := hx; have hy' := hy
  rw [hU] at hx' hy'
  obtain ⟨i, -, hi, rfl⟩ := mem_itl_take _ _ _ _ _ hx'
  obtain ⟨j, -, hj, rfl⟩ := mem_itl_take _ _ _ _ _ hy'
  rcases le_total i j with h | h
  · exact key i j h hj hy hxy
  · exact (key j i h hi hx hxy.symm).symm

end RData

end ST3

end PQT

/-! 8100c3d9 D5k: Sperner corners of a region and the packaged corner routes. -/

namespace PQT

section ST4

variable {V : Type}

namespace Rg

variable {X : Ctx V} {ρ : Rg V}

@[simp] lemma toR_phi : (toR X ρ).phi = X.phi := rfl
@[simp] lemma toR_S : (toR X ρ).S = ρ.S := rfl
@[simp] lemma toR_l : (toR X ρ).l = ρ.l := rfl
@[simp] lemma toR_L : (toR X ρ).L = X.L := rfl
@[simp] lemma toR_asg (v : V) : (toR X ρ).asg v ↔ ∃ j, v ∈ ρ.prt j := Iff.rfl

/-- `c` is inside or on the walk and its route lands in arc `j` -/
def Hits (X : Ctx V) (ρ : Rg V) (c : Cell) (j : Fin 3) : Prop :=
  (Ins ρ.S ρ.l c ∨ c ∈ ρ.l) ∧ arcOf ρ.s1 ρ.s2 (ρ.l.idxOf (land (· ∈ ρ.l) (toR X ρ).nx c)) = j

open Classical in
/-- Sperner on a region: a side triangle whose three corners route to the three arcs -/
theorem corners (hρ : ρ.Good X) :
    ∃ c1 : Cell, ∃ k : Fin 6, ρ.S (triAt c1 k) = true ∧ Hits X ρ c1 0 ∧
      Hits X ρ (c1 + dir k) 1 ∧ Hits X ρ (c1 + dir (k + 1)) 2 := by
  let κ : Cell → ℕ := fun c => if Ins ρ.S ρ.l c ∨ c ∈ ρ.l then
    (arcOf ρ.s1 ρ.s2 (ρ.l.idxOf (land (· ∈ ρ.l) (toR X ρ).nx c))).val + 1 else 0
  have hk : ∀ c (j : Fin 3), κ c = j.val + 1 → Hits X ρ c j := by
    intro c j h
    simp only [κ] at h
    split_ifs at h with hc
    · exact ⟨hc, Fin.ext (by omega)⟩
  have hk0 : ∀ c, κ c ≠ 0 → Ins ρ.S ρ.l c ∨ c ∈ ρ.l := by
    intro c h
    simp only [κ] at h
    split_ifs at h with hc
    · exact hc
    · exact absurd rfl h
  obtain ⟨a, k, h1, h2, h3, h4⟩ := lsperner hρ.hl hρ.hS hρ.hN κ
    (ρ.l.toFinset ∪ boxF X.Rb) (fun a k ha _ => by
      rcases hk0 a (by omega) with hi | hl
      · obtain ⟨b1, b2, b3, b4⟩ := hρ.hfar _ hi.2
        simp only [triAt] at b1 b2 b3 b4
        simp only [Finset.mem_union, boxF, Finset.mem_product, Finset.mem_Icc]
        exact Or.inr ⟨⟨b1, b2⟩, b3, b4⟩
      · exact Finset.mem_union_left _ (List.mem_toFinset.2 hl))
    (fun a k ha => by
      have hc : Ins ρ.S ρ.l a ∨ a ∈ ρ.l := by
        by_cases hl : a ∈ ρ.l
        · exact Or.inr hl
        · exact Or.inl ⟨hl, (side_const hρ.hS hl k).symm.trans ha⟩
      simp only [κ, hc, if_true]
      have := (arcOf ρ.s1 ρ.s2 (ρ.l.idxOf (land (· ∈ ρ.l) (toR X ρ).nx a))).isLt
      omega)
    ρ.s1 ρ.s2 hρ.h01 hρ.h12 hρ.h2n (fun i hi => by
      have hm : ρ.l[i] ∈ ρ.l := List.getElem_mem _
      simp only [κ, hm, or_true, if_true]
      rw [land_self (W := (· ∈ ρ.l)) hm, hρ.hl.1.idxOf_getElem]
      unfold arcOf
      split_ifs <;> rfl)
  exact ⟨a, k, h1, hk a 0 h2, hk _ 1 h3, hk _ 2 h4⟩

/-- the packaged route of a corner -/
theorem corner_route (hX : X.Good) (hρ : ρ.Good X) {c : Cell} {j : Fin 3} (h : Hits X ρ c j) :
    ∃ U Aa : List Cell, ∃ g : Cell,
      route (· ∈ ρ.l) (toR X ρ).nx c = U ++ Aa ++ [g] ∧
      land (· ∈ ρ.l) (toR X ρ).nx c = g ∧ g ∈ ρ.l ∧ arcOf ρ.s1 ρ.s2 (ρ.l.idxOf g) = j ∧
      (∀ x ∈ U, Ins ρ.S ρ.l x ∧ X.phi x ∉ ρ.A) ∧
      (∀ x ∈ Aa, X.phi x ∈ ρ.prt j ∧ Ins ρ.S ρ.l x) ∧
      (∀ x ∈ U, ∀ y ∈ U, X.L (X.phi x) = X.L (X.phi y) → X.phi x = X.phi y) ∧
      List.IsChain dAdj (U ++ Aa ++ [g]) ∧ (U ++ Aa ++ [g]).Nodup ∧
      (U ++ Aa ++ [g]).head? = some c := by
  have hR := hρ.rdata hX
  have F := RData.fhyp hR
  have hc : Ins (toR X ρ).S (toR X ρ).l c ∨ c ∈ (toR X ρ).l := h.1
  obtain ⟨U, Aa, he, hU, hA, -⟩ := RData.route_decomp hR hc
  simp only [toR_l, toR_S, toR_phi] at he hU hA
  set g := land (· ∈ ρ.l) (toR X ρ).nx c with hg
  have hgl : g ∈ ρ.l := F.land_W hc
  have hgi : ρ.l.idxOf g < ρ.l.length := List.idxOf_lt_length_of_mem hgl
  have hgp : X.phi g ∈ ρ.prt j := by
    have := hρ.harc _ hgi
    rw [List.getElem_idxOf hgi, h.2] at this
    exact this
  have hpof : (toR X ρ).pof (X.phi g) = (ρ.prt j : Set V) := by
    have hex : ∃ j', X.phi g ∈ ρ.prt j' := ⟨j, hgp⟩
    rw [toR_pof hex]
    rcases hρ.hpd hex.choose j with e | d
    · rw [e]
    · exact absurd (Finset.disjoint_left.1 d hex.choose_spec hgp) (by simp)
  have hrU : U = (route (· ∈ ρ.l) (toR X ρ).nx c).take U.length := by
    rw [he]; simp [List.append_assoc]
  refine ⟨U, Aa, g, he, rfl, hgl, h.2, fun x hx => ⟨(hU x hx).1, fun hxA => (hU x hx).2
    (hρ.hinv x (hU x hx).1 hxA)⟩, fun x hx => ⟨?_, (hA x hx).2⟩,
    RData.unasg_layer hR hc U U.length hrU (fun x hx => (hU x hx).2), ?_, ?_, ?_⟩
  · have := (hA x hx).1
    rw [hpof] at this
    exact this
  · have := F.route_chain hc; simp only [toR_l] at this; rw [he] at this; exact this
  · have := F.route_nodup hc; simp only [toR_l] at this; rw [he] at this; exact this
  · rw [← he]; exact route_head _ _ _

/-- routes of corners landing in different arcs are disjoint -/
lemma corner_disj (hX : X.Good) (hρ : ρ.Good X) {c c' : Cell} {j j' : Fin 3} (h : Hits X ρ c j)
    (h' : Hits X ρ c' j') (hne : j ≠ j') {x : Cell} (hx : x ∈ route (· ∈ ρ.l) (toR X ρ).nx c)
    (hx' : x ∈ route (· ∈ ρ.l) (toR X ρ).nx c') : False := by
  have F := RData.fhyp (hρ.rdata hX)
  have := F.route_merge h.1 h'.1 hx hx'
  simp only [toR_l] at this
  apply hne
  rw [← h.2, ← h'.2, this]

end Rg

end ST4

end PQT

/-! 8100c3d9 D5j: the region step (Sperner triangle, three corner routes, tripod split). -/

namespace PQT

section ST5

variable {V : Type}

lemma arcOf_eq0 {s1 s2 i : ℕ} (h : arcOf s1 s2 i = 0) : i < s1 := by
  unfold arcOf at h
  split_ifs at h <;> first | assumption | exact absurd h (by decide)

lemma arcOf_eq1 {s1 s2 i : ℕ} (h : arcOf s1 s2 i = 1) : s1 ≤ i ∧ i < s2 := by
  unfold arcOf at h
  split_ifs at h <;> first | omega | exact absurd h (by decide)

lemma arcOf_eq2 {s1 s2 i : ℕ} (h : arcOf s1 s2 i = 2) : s1 ≤ i ∧ s2 ≤ i := by
  unfold arcOf at h
  split_ifs at h <;> first | omega | exact absurd h (by decide)

lemma arcOf_v0 {s1 s2 i : ℕ} (h : i < s1) : arcOf s1 s2 i = 0 := by
  unfold arcOf; rw [if_pos h]

lemma arcOf_v1 {s1 s2 i : ℕ} (h1 : s1 ≤ i) (h2 : i < s2) : arcOf s1 s2 i = 1 := by
  unfold arcOf; rw [if_neg (by omega), if_pos h2]

lemma arcOf_v2 {s1 s2 i : ℕ} (h1 : s1 ≤ i) (h2 : s2 ≤ i) : arcOf s1 s2 i = 2 := by
  unfold arcOf; rw [if_neg (by omega), if_neg (by omega)]

lemma seg_sub {l : List Cell} {a b : ℕ} {x : Cell} (hx : x ∈ seg l a b) : x ∈ l := by
  obtain ⟨j, hj, -, -, rfl⟩ := seg_mem hx
  exact List.getElem_mem _

lemma bsum4 {a b c d e : Bool} (h : bz a = bz b + bz c + bz d + bz e) :
    (b = true → a = true) ∧ (c = true → a = true) ∧ (d = true → a = true) ∧
      (e = true → a = true) := by
  revert h; cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

lemma bsum4t {b c d : Bool} (h : bz true = bz b + bz c + bz d + bz true) :
    b = false ∧ c = false ∧ d = false := by
  revert h; cases b <;> cases c <;> cases d <;> decide

lemma chain_pre {U A : List Cell} {g : Cell} (h : List.IsChain dAdj (U ++ A ++ [g])) :
    List.IsChain dAdj (U ++ A) := (List.isChain_append.1 h).1

lemma chain_preU {U A : List Cell} {g : Cell} (h : List.IsChain dAdj (U ++ A ++ [g])) :
    List.IsChain dAdj U := (List.isChain_append.1 (chain_pre h)).1

lemma head_pre {U A : List Cell} {g c : Cell} (h : (U ++ A ++ [g]).head? = some c) :
    ∀ a t, U ++ A = a :: t → a = c := by
  intro a t e
  rw [e] at h
  simpa using h

lemma head_preU {U A : List Cell} {g c : Cell} (h : (U ++ A ++ [g]).head? = some c) :
    ∀ a t, U = a :: t → a = c := by
  intro a t e
  rw [e] at h
  simpa using h

lemma head_cases {U A : List Cell} {g c : Cell} (h : (U ++ A ++ [g]).head? = some c) :
    c ∈ U ∨ c ∈ A ∨ c = g := by
  rcases U with _ | ⟨a, t⟩
  · rcases A with _ | ⟨b, s⟩
    · simp at h; subst h; simp
    · simp at h; subst h; simp
  · simp at h; subst h; simp

lemma off_walk {l : List Cell} (ga gb : Cell) (Ma Mb Da Db Dc : List Cell) (hga : ga ∈ l)
    (hgb : gb ∈ l) (hMa : ∀ x ∈ Ma, x ∈ l) (hMb : ∀ x ∈ Mb, x ∈ l) (hc : ∀ x ∈ Dc, x ∉ l)
    (hca : ∀ x ∈ Dc, x ∉ Da) (hcb : ∀ x ∈ Dc, x ∉ Db) :
    ∀ x ∈ Dc, x ∉ ga :: ((Ma ++ Mb) ++ gb :: (Db.reverse ++ Da)) := by
  intro x hx hxW
  simp only [List.mem_cons, List.mem_append, List.mem_reverse] at hxW
  rcases hxW with h | (h | h) | h | h | h
  · exact hc x hx (by rw [h]; exact hga)
  · exact hc x hx (hMa x h)
  · exact hc x hx (hMb x h)
  · exact hc x hx (by rw [h]; exact hgb)
  · exact hcb x hx h
  · exact hca x hx h

lemma hY_tri [DecidableEq V] (phi : Cell → V) (Sc : Tri → Bool) (ga gb : Cell)
    (Ma Mb Ua Aa Ub Ab U1 U2 U3 : List Cell)
    (h : ∀ x ∈ U1 ++ U2 ++ U3, x ∈ Ua ∨ x ∈ Ub ∨ Sc (triAt x 0) = false) :
    ∀ y ∈ ((U1 ++ U2 ++ U3).map phi).toFinset, ∃ x, phi x = y ∧
      (x ∉ ga :: ((Ma ++ Mb) ++ gb :: ((Ub ++ Ab).reverse ++ (Ua ++ Aa))) →
        Sc (triAt x 0) = false) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
  refine ⟨x, rfl, fun hW => ?_⟩
  rcases h x hx with h' | h' | h'
  · exact absurd (by simp [h']) hW
  · exact absurd (by simp [h']) hW
  · exact h'

namespace Rg

variable {X : Ctx V} {ρ : Rg V}

lemma seg_arc (hρ : ρ.Good X) {a b : ℕ} (j0 : Fin 3)
    (h : ∀ j, a ≤ j → j < b → arcOf ρ.s1 ρ.s2 j = j0) :
    ∀ x ∈ seg ρ.l a b, X.phi x ∈ ρ.prt j0 := by
  intro x hx
  obtain ⟨j, hj, h1, h2, rfl⟩ := seg_mem hx
  have := hρ.harc j hj
  rwa [h j h1 h2] at this

lemma g_prt (hρ : ρ.Good X) {g : Cell} {j : Fin 3} (hg : g ∈ ρ.l)
    (ha : arcOf ρ.s1 ρ.s2 (ρ.l.idxOf g) = j) : X.phi g ∈ ρ.prt j := by
  have hi := List.idxOf_lt_length_of_mem hg
  have := hρ.harc _ hi
  rwa [List.getElem_idxOf hi, ha] at this

set_option maxHeartbeats 4000000 in
/-- THE REGION STEP: a Sperner triangle, its three corner routes and the tripod split give the
new part `Y0` (connected, at most three vertices per layer) and the child regions. -/
theorem step [Fintype V] [DecidableEq V] (hex : ExistsBd) (hX : X.Good) (hρ : ρ.Good X) :
    ∃ (Y0 : Finset V) (ch : List (Rg V)),
      Y0 ⊆ ρ.I X ∧
      (Y0.Nonempty → ((Gphi X.phi).induce (Y0 : Set V)).Connected ∧
        ∀ i, (Y0.filter (fun v => X.L v = i)).card ≤ 3) ∧
      (∀ c ∈ ch, c.Good X ∧ c.m X < ρ.m X ∧ c.Qs ⊆ insert Y0 ρ.Qs) ∧
      ch.Pairwise (fun a b => Disjoint (a.I X) (b.I X)) ∧
      ch.foldr (fun c s => c.I X ∪ s) ∅ = ρ.I X \ Y0 := by
  obtain ⟨c1, k, ht0, hh1, hh2, hh3⟩ := corners hρ
  obtain ⟨U1, A1, g1, hr1, -, hg1, ha1, hU1, hA1, hL1, hch1, hnd1, hhd1⟩ := corner_route hX hρ hh1
  obtain ⟨U2, A2, g2, hr2, -, hg2, ha2, hU2, hA2, hL2, hch2, hnd2, hhd2⟩ := corner_route hX hρ hh2
  obtain ⟨U3, A3, g3, hr3, -, hg3, ha3, hU3, hA3, hL3, hch3, hnd3, hhd3⟩ := corner_route hX hρ hh3
  have hs01 := hρ.h01
  have hs12 := hρ.h12
  have hs2n := hρ.h2n
  -- indices of the landing cells
  have hi1 : ρ.l.idxOf g1 < ρ.l.length := List.idxOf_lt_length_of_mem hg1
  have hi2 : ρ.l.idxOf g2 < ρ.l.length := List.idxOf_lt_length_of_mem hg2
  have hi3 : ρ.l.idxOf g3 < ρ.l.length := List.idxOf_lt_length_of_mem hg3
  have hb1 := arcOf_eq0 ha1
  have hb2 := arcOf_eq1 ha2
  have hb3 := arcOf_eq2 ha3
  have hrot := rot3 ρ.l (show ρ.l.idxOf g1 < ρ.l.idxOf g2 by omega)
    (show ρ.l.idxOf g2 < ρ.l.idxOf g3 by omega) hi3
  rw [List.getElem_idxOf hi1, List.getElem_idxOf hi2, List.getElem_idxOf hi3] at hrot
  -- the route pieces are inside cells, pairwise disjoint
  have hI1 : ∀ x ∈ U1 ++ A1, Ins ρ.S ρ.l x := by
    intro x hx; rcases List.mem_append.1 hx with h | h
    exacts [(hU1 x h).1, (hA1 x h).2]
  have hI2 : ∀ x ∈ U2 ++ A2, Ins ρ.S ρ.l x := by
    intro x hx; rcases List.mem_append.1 hx with h | h
    exacts [(hU2 x h).1, (hA2 x h).2]
  have hI3 : ∀ x ∈ U3 ++ A3, Ins ρ.S ρ.l x := by
    intro x hx; rcases List.mem_append.1 hx with h | h
    exacts [(hU3 x h).1, (hA3 x h).2]
  have d12 : ∀ x ∈ U1 ++ A1, x ∉ U2 ++ A2 := fun x h h' =>
    corner_disj hX hρ hh1 hh2 (by decide) (by rw [hr1]; exact List.mem_append_left _ h)
      (by rw [hr2]; exact List.mem_append_left _ h')
  have d13 : ∀ x ∈ U1 ++ A1, x ∉ U3 ++ A3 := fun x h h' =>
    corner_disj hX hρ hh1 hh3 (by decide) (by rw [hr1]; exact List.mem_append_left _ h)
      (by rw [hr3]; exact List.mem_append_left _ h')
  have d23 : ∀ x ∈ U2 ++ A2, x ∉ U3 ++ A3 := fun x h h' =>
    corner_disj hX hρ hh2 hh3 (by decide) (by rw [hr2]; exact List.mem_append_left _ h)
      (by rw [hr3]; exact List.mem_append_left _ h')
  have hn1 : (U1 ++ A1).Nodup := (List.nodup_append.1 hnd1).1
  have hn2 : (U2 ++ A2).Nodup := (List.nodup_append.1 hnd2).1
  have hn3 : (U3 ++ A3).Nodup := (List.nodup_append.1 hnd3).1
  have hnd : ((U1 ++ A1) ++ (U2 ++ A2) ++ (U3 ++ A3)).Nodup := by
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hn1, hn2, fun a ha b hb e => d12 a ha (e ▸ hb)⟩,
      hn3, fun a ha b hb e => ?_⟩
    rcases List.mem_append.1 ha with h | h
    · exact d13 a h (e ▸ hb)
    · exact d23 a h (e ▸ hb)
  have hI : ∀ x ∈ (U1 ++ A1) ++ (U2 ++ A2) ++ (U3 ++ A3),
      Ins ρ.S (g1 :: (seg ρ.l (ρ.l.idxOf g1 + 1) (ρ.l.idxOf g2) ++ g2 ::
        (seg ρ.l (ρ.l.idxOf g2 + 1) (ρ.l.idxOf g3) ++ g3 ::
          (seg ρ.l (ρ.l.idxOf g3 + 1) ρ.l.length ++ seg ρ.l 0 (ρ.l.idxOf g1))))) x := by
    intro x hx
    have hx' : Ins ρ.S ρ.l x := by
      simp only [List.mem_append] at hx
      rcases hx with (h | h) | h
      exacts [hI1 x (List.mem_append.2 h), hI2 x (List.mem_append.2 h),
        hI3 x (List.mem_append.2 h)]
    refine ⟨fun hm => hx'.1 ?_, hx'.2⟩
    rw [← hrot, List.mem_rotate] at hm
    exact hm
  have hW0 := hρ.hl.rotate (ρ.l.idxOf g1)
  have hS0 := hρ.hS.rotate (ρ.l.idxOf g1)
  have hN0 := hρ.hN.rotate (ρ.l.idxOf g1)
  rw [hrot] at hW0 hS0 hN0
  obtain ⟨S12, S31, S23, S0, hd12, hd31, hd23, hT1, hT2, hT3, hsum⟩ :=
    tripod_split hex ρ.S g1 g2 g3 c1 k _ _ _ (U1 ++ A1) (U2 ++ A2) (U3 ++ A3)
      hW0 hS0 hN0 hhd1 hhd2 hhd3 hch1 hch2 hch3 hI hnd ht0
  -- the triangle piece contains t0
  have hS0t : S0 (triAt c1 k) = true := hT3 c1 k (by
    show 0 < ecount c1 (c1 + dir k) ([c1 + dir (k + 1), c1, c1 + dir k] ++
      [c1 + dir (k + 1), c1, c1 + dir k].take 1)
    exact ecount_pos_mid c1 (c1 + dir k) [c1 + dir (k + 1)] [c1 + dir (k + 1)])
  have a23 : dAdj (c1 + dir k) (c1 + dir (k + 1)) := hT1.2.2 _ _ (by
    show 0 < ecount (c1 + dir k) (c1 + dir (k + 1)) ([c1 + dir (k + 1), c1, c1 + dir k] ++
      [c1 + dir (k + 1), c1, c1 + dir k].take 1)
    exact ecount_pos_mid (c1 + dir k) (c1 + dir (k + 1)) [c1 + dir (k + 1), c1] [])
  have hz := hsum (triAt c1 k)
  rw [ht0, hS0t] at hz
  obtain ⟨f12, f31, f23⟩ := bsum4t hz
  have hle12 : ∀ τ, S12 τ = true → ρ.S τ = true := fun τ => (bsum4 (hsum τ)).1
  have hle31 : ∀ τ, S31 τ = true → ρ.S τ = true := fun τ => (bsum4 (hsum τ)).2.1
  have hle23 : ∀ τ, S23 τ = true → ρ.S τ = true := fun τ => (bsum4 (hsum τ)).2.2.1
  have hle0 : ∀ τ, S0 τ = true → ρ.S τ = true := fun τ => (bsum4 (hsum τ)).2.2.2
  -- the new part
  set Y0 : Finset V := ((U1 ++ U2 ++ U3).map X.phi).toFinset with hY0def
  have hmemY : ∀ y, y ∈ Y0 ↔ ∃ x ∈ U1 ++ U2 ++ U3, X.phi x = y := by
    intro y; rw [hY0def, List.mem_toFinset, List.mem_map]
  have hUall : ∀ x ∈ U1 ++ U2 ++ U3, Ins ρ.S ρ.l x ∧ X.phi x ∉ ρ.A := by
    intro x hx; simp only [List.mem_append] at hx
    rcases hx with (h | h) | h
    exacts [hU1 x h, hU2 x h, hU3 x h]
  have hYA : Disjoint Y0 ρ.A := Finset.disjoint_left.2 fun y hy hyA => by
    obtain ⟨x, hx, rfl⟩ := (hmemY y).1 hy
    exact (hUall x hx).2 hyA
  have hYsub : Y0 ⊆ ρ.I X := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmemY y).1 hy
    rw [Rg.mem_I]
    exact ⟨⟨x, rfl, (hUall x hx).1⟩, (hUall x hx).2⟩
  have hYc : ((Gphi X.phi).induce (Y0 : Set V)).Preconnected :=
    conn_of_cells X.phi (U1 ++ U2 ++ U3) (tri_cells_conn U1 U2 U3 c1 (c1 + dir k) (c1 + dir (k + 1))
      (chain_preU hch1) (chain_preU hch2) (chain_preU hch3) (head_preU hhd1) (head_preU hhd2)
      (head_preU hhd3) ⟨k, rfl⟩ ⟨k + 1, rfl⟩ a23)
  have hYU1 : ∀ x ∈ U1, X.phi x ∈ Y0 := fun x hx => (hmemY _).2 ⟨x, by simp [hx], rfl⟩
  have hYU2 : ∀ x ∈ U2, X.phi x ∈ Y0 := fun x hx => (hmemY _).2 ⟨x, by simp [hx], rfl⟩
  have hYU3 : ∀ x ∈ U3, X.phi x ∈ Y0 := fun x hx => (hmemY _).2 ⟨x, by simp [hx], rfl⟩
  have hok : Y0.Nonempty → ((Gphi X.phi).induce (Y0 : Set V)).Connected ∧
      ∀ i, (Y0.filter (fun v => X.L v = i)).card ≤ 3 := by
    intro hne
    refine ⟨(SimpleGraph.connected_iff _).2 ⟨hYc, ?_⟩, fun i => layer3 X.phi X.L U1 U2 U3 hL1 hL2 hL3 i⟩
    obtain ⟨y, hy⟩ := hne
    exact ⟨⟨y, hy⟩⟩
  -- landing cells and arc segments
  have hpg1 := g_prt hρ hg1 ha1
  have hpg2 := g_prt hρ hg2 ha2
  have hpg3 := g_prt hρ hg3 ha3
  have hsl : ∀ a b, ∀ x ∈ seg ρ.l a b, x ∈ ρ.l := fun a b x hx => seg_sub hx
  have hoffI : ∀ (D : List Cell), (∀ x ∈ D, Ins ρ.S ρ.l x) → ∀ x ∈ D, x ∉ ρ.l :=
    fun D h x hx => (h x hx).1
  -- ===== child 12
  rw [seg_split ρ.l (show ρ.l.idxOf g1 + 1 ≤ ρ.s1 by omega) (show ρ.s1 ≤ ρ.l.idxOf g2 by omega)]
    at hd12
  have hdg12 : (∀ τ, S12 τ = false) ∨ LBd S12 (g1 :: ((seg ρ.l (ρ.l.idxOf g1 + 1) ρ.s1 ++
      seg ρ.l ρ.s1 (ρ.l.idxOf g2)) ++ g2 :: ((U2 ++ A2).reverse ++ (U1 ++ A1)))) :=
    hd12.imp id (fun h => h.2.1)
  have o12 : ∀ x ∈ U3 ++ A3, S12 (triAt x 0) = false :=
    route_off hdg12 (U3 ++ A3) (c1 + dir (k + 1)) (k + 4) (head_pre hhd3) (chain_pre hch3)
      (off_walk g1 g2 _ _ (U1 ++ A1) (U2 ++ A2) (U3 ++ A3) hg1 hg2 (hsl _ _) (hsl _ _)
        (hoffI _ hI3) (fun x hx h => d13 x h hx) (fun x hx h => d23 x h hx))
      (by rw [triAt_third]; exact f12)
  obtain ⟨ch12, hc12, hs12'⟩ := child_shape hX hρ g1 g2 _ _ U1 A1 U2 A2 S12 (triAt c1 k) hd12
    hle12 f12 Y0 hYA hYc
    (hY_tri X.phi S12 g1 g2 _ _ U1 A1 U2 A2 U1 U2 U3 (by
      intro x hx; simp only [List.mem_append] at hx
      rcases hx with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (o12 x (List.mem_append_left _ h)))))
    (ρ.prt 0) (ρ.prt 1) ⟨0, rfl⟩ ⟨1, rfl⟩ hpg1
    (seg_arc hρ 0 (fun j _ h2 => arcOf_v0 h2)) (fun x hx => (hA1 x hx).1) hpg2
    (seg_arc hρ 1 (fun j h1 h2 => arcOf_v1 h1 (by omega))) (fun x hx => (hA2 x hx).1) hYU1 hYU2
  -- ===== child 31
  have hdg31 : (∀ τ, S31 τ = false) ∨ LBd S31 (g3 :: ((seg ρ.l (ρ.l.idxOf g3 + 1) ρ.l.length ++
      seg ρ.l 0 (ρ.l.idxOf g1)) ++ g1 :: ((U1 ++ A1).reverse ++ (U3 ++ A3)))) :=
    hd31.imp id (fun h => h.2.1)
  have o31 : ∀ x ∈ U2 ++ A2, S31 (triAt x 0) = false :=
    route_off hdg31 (U2 ++ A2) (c1 + dir k) (k + 2) (head_pre hhd2) (chain_pre hch2)
      (off_walk g3 g1 _ _ (U3 ++ A3) (U1 ++ A1) (U2 ++ A2) hg3 hg1 (hsl _ _) (hsl _ _)
        (hoffI _ hI2) (fun x hx h => d23 x hx h) (fun x hx h => d12 x h hx))
      (by rw [triAt_add2]; exact f31)
  obtain ⟨ch31, hc31, hs31'⟩ := child_shape hX hρ g3 g1 _ _ U3 A3 U1 A1 S31 (triAt c1 k) hd31
    hle31 f31 Y0 hYA hYc
    (hY_tri X.phi S31 g3 g1 _ _ U3 A3 U1 A1 U1 U2 U3 (by
      intro x hx; simp only [List.mem_append] at hx
      rcases hx with (h | h) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (o31 x (List.mem_append_left _ h)))
      · exact Or.inl h))
    (ρ.prt 2) (ρ.prt 0) ⟨2, rfl⟩ ⟨0, rfl⟩ hpg3
    (seg_arc hρ 2 (fun j h1 _ => arcOf_v2 (by omega) (by omega))) (fun x hx => (hA3 x hx).1) hpg1
    (seg_arc hρ 0 (fun j _ h2 => arcOf_v0 (by omega))) (fun x hx => (hA1 x hx).1) hYU3 hYU1
  -- ===== child 23 (rotate the tripod piece to start at g2)
  rw [seg_split ρ.l (show ρ.l.idxOf g2 + 1 ≤ ρ.s2 by omega) (show ρ.s2 ≤ ρ.l.idxOf g3 by omega)]
    at hd23
  have hrE : ((U2 ++ A2) ++ g2 :: ((seg ρ.l (ρ.l.idxOf g2 + 1) ρ.s2 ++ seg ρ.l ρ.s2 (ρ.l.idxOf g3))
      ++ g3 :: (U3 ++ A3).reverse)).rotate (U2 ++ A2).length =
      g2 :: ((seg ρ.l (ρ.l.idxOf g2 + 1) ρ.s2 ++ seg ρ.l ρ.s2 (ρ.l.idxOf g3)) ++
        g3 :: ((U3 ++ A3).reverse ++ (U2 ++ A2))) := by
    rw [List.rotate_append_length_eq]
    simp only [List.cons_append, List.append_assoc]
  have hd23' : (∀ τ, S23 τ = false) ∨
      (LSimple (g2 :: ((seg ρ.l (ρ.l.idxOf g2 + 1) ρ.s2 ++ seg ρ.l ρ.s2 (ρ.l.idxOf g3)) ++
        g3 :: ((U3 ++ A3).reverse ++ (U2 ++ A2)))) ∧
      LBd S23 (g2 :: ((seg ρ.l (ρ.l.idxOf g2 + 1) ρ.s2 ++ seg ρ.l ρ.s2 (ρ.l.idxOf g3)) ++
        g3 :: ((U3 ++ A3).reverse ++ (U2 ++ A2)))) ∧
      LNorm S23 (g2 :: ((seg ρ.l (ρ.l.idxOf g2 + 1) ρ.s2 ++ seg ρ.l ρ.s2 (ρ.l.idxOf g3)) ++
        g3 :: ((U3 ++ A3).reverse ++ (U2 ++ A2))))) := by
    rcases hd23 with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · right
      rw [← hrE]
      exact ⟨h1.rotate _, h2.rotate _, h3.rotate _⟩
  have hdg23 := hd23'.imp id (fun h => h.2.1)
  have o23 : ∀ x ∈ U1 ++ A1, S23 (triAt x 0) = false :=
    route_off hdg23 (U1 ++ A1) c1 k (head_pre hhd1) (chain_pre hch1)
      (off_walk g2 g3 _ _ (U2 ++ A2) (U3 ++ A3) (U1 ++ A1) hg2 hg3 (hsl _ _) (hsl _ _)
        (hoffI _ hI1) (fun x hx h => d12 x hx h) (fun x hx h => d13 x hx h))
      f23
  obtain ⟨ch23, hc23, hs23'⟩ := child_shape hX hρ g2 g3 _ _ U2 A2 U3 A3 S23 (triAt c1 k) hd23'
    hle23 f23 Y0 hYA hYc
    (hY_tri X.phi S23 g2 g3 _ _ U2 A2 U3 A3 U1 U2 U3 (by
      intro x hx; simp only [List.mem_append] at hx
      rcases hx with (h | h) | h
      · exact Or.inr (Or.inr (o23 x (List.mem_append_left _ h)))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)))
    (ρ.prt 1) (ρ.prt 2) ⟨1, rfl⟩ ⟨2, rfl⟩ hpg2
    (seg_arc hρ 1 (fun j h1 h2 => arcOf_v1 (by omega) h2)) (fun x hx => (hA2 x hx).1) hpg3
    (seg_arc hρ 2 (fun j h1 _ => arcOf_v2 (by omega) h1)) (fun x hx => (hA3 x hx).1) hYU2 hYU3
  -- ===== assemble
  have hall : ∀ c ∈ ch12 ++ ch31 ++ ch23, c.Good X ∧ c.A = ρ.A ∪ Y0 ∧ c.Qs ⊆ insert Y0 ρ.Qs ∧
      (∀ x ∈ c.l, X.phi x ∈ ρ.A ∪ Y0) ∧ (∀ τ, c.S τ = true → ρ.S τ = true) ∧
      c.S (triAt c1 k) = false ∧ LBd c.S c.l := by
    intro c hc; simp only [List.mem_append] at hc
    rcases hc with (h | h) | h
    exacts [hc12 c h, hc31 c h, hc23 c h]
  have hcorner : ∀ (U A : List Cell) (g c : Cell) (j : Fin 3), (U ++ A ++ [g]).head? = some c →
      (∀ x ∈ U, X.phi x ∈ Y0) → (∀ x ∈ A, X.phi x ∈ ρ.prt j) → g ∈ ρ.l →
      X.phi c ∈ ρ.A ∪ Y0 := by
    intro U A g c j hh hU hA hg
    rcases head_cases hh with h | h | h
    · exact Finset.mem_union_right _ (hU c h)
    · exact Finset.mem_union_left _ (hρ.hpA j (hA c h))
    · rw [h]; exact Finset.mem_union_left _ (hρ.walk_A hg)
  have hIP := I_partition hX hρ Y0 S0 (ch12 ++ ch31 ++ ch23)
    (fun τ => by
      rw [List.map_append, List.map_append, List.sum_append, List.sum_append, hs12', hs31',
        hs23']
      exact hsum τ)
    (fun c hc => (hall c hc).2.2.2.2.2.2) (fun c hc => (hall c hc).2.1)
    (fun c hc => (hall c hc).2.2.2.1)
    (by
      intro x hx _
      have hfar0 : ∀ c, ¬ inBox X.Rb c → S0 (triAt c 0) = false := by
        intro c hc
        by_contra hc'
        rw [Bool.not_eq_false] at hc'
        obtain ⟨b1, b2, b3, b4⟩ := hρ.hfar _ (hle0 _ hc')
        simp only [triAt] at b1 b2 b3 b4
        exact hc ⟨b1, b2, b3, b4⟩
      have hxT : x ∈ [c1 + dir (k + 1), c1, c1 + dir k] := by
        by_contra h
        rw [tri_no_inside c1 k hT2 X.Rb hfar0 x h] at hx
        exact absurd hx (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxT
      rcases hxT with rfl | rfl | rfl
      · exact hcorner U3 A3 g3 _ 2 hhd3 hYU3 (fun x hx => (hA3 x hx).1) hg3
      · exact hcorner U1 A1 g1 _ 0 hhd1 hYU1 (fun x hx => (hA1 x hx).1) hg1
      · exact hcorner U2 A2 g2 _ 1 hhd2 hYU2 (fun x hx => (hA2 x hx).1) hg2)
  refine ⟨Y0, ch12 ++ ch31 ++ ch23, hYsub, hok, fun c hc => ?_, hIP.1, hIP.2⟩
  obtain ⟨g, -, hq, -, hle, ht, -⟩ := hall c hc
  exact ⟨g, m_lt hρ hle (triAt c1 k) ht0 ht, hq⟩

end Rg

end ST5

end PQT

/-! 8100c3d9 D5k: the region recursion instantiated, the top region (ring of a box, parent path
of the outer owner), and the per-component core `top_core`. -/

namespace PQT

section TQ

variable {V : Type}

/-- the part predicate: connected in `H`, at most three vertices per layer -/
def OkG (H : SimpleGraph V) (L : V → ℕ) (Y : Finset V) : Prop :=
  (H.induce (Y : Set V)).Connected ∧ ∀ i, (Y.filter (fun v => L v = i)).card ≤ 3

namespace Rg

variable {X : Ctx V}

theorem dec_all [Fintype V] [DecidableEq V] (hex : ExistsBd) (hX : X.Good) :
    ∀ ρ : Rg V, ρ.Good X → Dec (Gphi X.phi) (OkG (Gphi X.phi) X.L) (ρ.I X) ρ.Qs :=
  dec_of_step (fun ρ : Rg V => ρ.Good X) (fun ρ => ρ.I X) Rg.Qs (fun ρ => ρ.m X)
    (fun _ h => hA1 h) (fun _ h => hA2 hX h) (fun _ h => hA3 h) (fun _ h => hA4 h)
    (fun _ h _ => by
      obtain ⟨Y0, ch, h1, h2, h3, h4, h5⟩ := step hex hX h
      exact ⟨Y0, ch, h1, h2, h3, h4, h5⟩)

end Rg

lemma gphi_img {phi : Cell → V} {u v : V} (h : (Gphi phi).Adj u v) : ∃ c, phi c = v := by
  rw [Gphi, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨c, c', -, h2, -⟩ | ⟨c, c', h1, -, -⟩
  · exact ⟨c', h2⟩
  · exact ⟨c, h1⟩

/-- the parent path from the outer owner: connected, one vertex per layer, ends at the root -/
theorem ppath_ok [Fintype V] [DecidableEq V] (phi : Cell → V) (L : V → ℕ) (p : V → V) (r q : V)
    (hq : ∃ c, phi c = q)
    (hpar : ∀ v, 0 < L v → (Gphi phi).Adj v (p v) ∧ L (p v) + 1 = L v)
    (hroot : ∀ c, L (phi c) = 0 → phi c = r) :
    let T : Finset V := ((List.range (L q + 1)).map (fun i => p^[i] q)).toFinset
    q ∈ T ∧ r ∈ T ∧ OkG (Gphi phi) L T ∧ ∀ v ∈ T, ∃ c, phi c = v := by
  intro T
  have hmemT : ∀ v, v ∈ T ↔ ∃ i, i ≤ L q ∧ p^[i] q = v := by
    intro v
    simp only [T, List.mem_toFinset, List.mem_map, List.mem_range, Nat.lt_succ_iff]
  -- layers and images along the path
  have hlay : ∀ i, i ≤ L q → L (p^[i] q) + i = L q ∧ ∃ c, phi c = p^[i] q := by
    intro i
    induction i with
    | zero => intro _; simpa using hq
    | succ i ih =>
      intro hi
      obtain ⟨h1, -⟩ := ih (by omega)
      have hpos : 0 < L (p^[i] q) := by omega
      obtain ⟨hadj, hL⟩ := hpar _ hpos
      rw [Function.iterate_succ_apply']
      exact ⟨by omega, gphi_img hadj⟩
  have hT0 : q ∈ T := (hmemT q).2 ⟨0, by omega, rfl⟩
  refine ⟨hT0, ?_, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨h1, c, hc⟩ := hlay (L q) le_rfl
    have := hroot c (by rw [hc]; omega)
    rw [hc] at this
    exact (hmemT r).2 ⟨L q, le_rfl, this⟩
  · -- connected: every vertex is reachable from `q`
    have hreach : ∀ i (hi : i ≤ L q), ((Gphi phi).induce (T : Set V)).Reachable ⟨q, hT0⟩
        ⟨p^[i] q, (hmemT _).2 ⟨i, hi, rfl⟩⟩ := by
      intro i
      induction i with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ i ih =>
        intro hi
        refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        have hpos : 0 < L (p^[i] q) := by have := (hlay i (by omega)).1; omega
        show (Gphi phi).Adj (p^[i] q) (p^[i + 1] q)
        rw [Function.iterate_succ_apply']
        exact (hpar _ hpos).1
    have hpre : ((Gphi phi).induce (T : Set V)).Preconnected := by
      intro a b
      obtain ⟨i, hi, hia⟩ := (hmemT a.1).1 a.2
      obtain ⟨j, hj, hjb⟩ := (hmemT b.1).1 b.2
      have ha : a = ⟨p^[i] q, (hmemT _).2 ⟨i, hi, rfl⟩⟩ := Subtype.ext hia.symm
      have hb : b = ⟨p^[j] q, (hmemT _).2 ⟨j, hj, rfl⟩⟩ := Subtype.ext hjb.symm
      rw [ha, hb]
      exact (hreach i hi).symm.trans (hreach j hj)
    exact (SimpleGraph.connected_iff _).2 ⟨hpre, ⟨⟨q, hT0⟩⟩⟩
  · intro k
    refine le_trans (Finset.card_le_one.2 ?_) (by norm_num)
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    obtain ⟨i, hi, rfl⟩ := (hmemT a).1 ha.1
    obtain ⟨j, hj, rfl⟩ := (hmemT b).1 hb.1
    have e1 := (hlay i hi).1
    have e2 := (hlay j hj).1
    have : i = j := by omega
    rw [this]
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := (hmemT v).1 hv
    exact (hlay i hi).2

open Classical in
/-- THE PER-COMPONENT CORE: the outer part `T` plus a decomposition of the rest of the image. -/
theorem top_core [Fintype V] [DecidableEq V] (hex : ExistsBd) (phi : Cell → V) (R : ℤ)
    (hR : 0 ≤ R) (q : V) (hout : ∀ c, ¬ inBox R c → phi c = q)
    (hfib : ∀ v c c', phi c = v → phi c' = v →
      Relation.ReflTransGen (PRel (fun x => phi x = v)) c c')
    (L : V → ℕ) (p : V → V) (r : V)
    (hpar : ∀ v, 0 < L v → (Gphi phi).Adj v (p v) ∧ L (p v) + 1 = L v)
    (hroot : ∀ c, L (phi c) = 0 → phi c = r) :
    ∃ T : Finset V, T.Nonempty ∧ OkG (Gphi phi) L T ∧ (∀ v ∈ T, ∃ c, phi c = v) ∧
      Dec (Gphi phi) (OkG (Gphi phi) L)
        (Finset.univ.filter (fun v => (∃ c, phi c = v) ∧ v ∉ T)) {T} := by
  classical
  have hq : ∃ c, phi c = q := ⟨(R + 1, 0), hout _ (fun h => by unfold inBox at h; omega)⟩
  obtain ⟨hqT, hrT, hTok, hTimg⟩ := ppath_ok phi L p r q hq hpar hroot
  set T : Finset V := ((List.range (L q + 1)).map (fun i => p^[i] q)).toFinset with hTdef
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = R + 2 := ⟨(R + 2).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hM1 : 1 ≤ M := by omega
  obtain ⟨S, hS, hN, hin, hfar'⟩ := top_side hex M hM1
  let X : Ctx V := ⟨phi, (M : ℤ) + 1, L, p, r⟩
  have hX : X.Good := ⟨hfib, hpar, hroot⟩
  let ρ : Rg V := ⟨ring M, S, fun _ => T, 1, 2, T⟩
  have hring : ∀ c ∈ ring M, phi c = q := by
    intro c hc
    obtain ⟨-, h2⟩ := mem_ring hM1 hc
    apply hout
    intro h
    apply h2
    unfold inBox at h ⊢
    omega
  have hρ : ρ.Good X := by
    refine ⟨ring_simple M hM1, hS, hN, ?_, (by show 0 < 1; omega), (by show 1 < 2; omega), ?_, ?_, fun _ => subset_refl _,
      fun _ => hTok.1.preconnected, fun _ _ => Or.inl rfl, fun c _ h => ⟨0, h⟩, hrT⟩
    · rintro ⟨i, j, b⟩ hτ0
      have hτ : S (i, j, b) = true := hτ0
      show -((M : ℤ) + 1) ≤ i ∧ i ≤ (M : ℤ) + 1 ∧ -((M : ℤ) + 1) ≤ j ∧ j ≤ (M : ℤ) + 1
      cases b
      · by_cases hb : inBox M (i, j)
        · unfold inBox at hb; simp only at hb; omega
        · have := (hfar' (i, j) hb).2 0
          simp only [triAt] at this
          rw [this] at hτ; exact absurd hτ (by decide)
      · by_cases hb : inBox M (i + 1, j + 1)
        · unfold inBox at hb; simp only at hb; omega
        · have := (hfar' (i + 1, j + 1) hb).2 3
          simp only [triAt, add_sub_cancel_right] at this
          rw [this] at hτ; exact absurd hτ (by decide)
    · show 2 < (ring M).length
      rw [ring_length]; omega
    · intro i hi
      show phi (ring M)[i] ∈ T
      rw [hring _ (List.getElem_mem _)]
      exact hqT
  have hD := Rg.dec_all hex hX ρ hρ
  have hQs : ρ.Qs = {T} := by
    ext Q
    simp only [Rg.Qs, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl; exact ⟨0, rfl⟩
  have hI : ρ.I X = Finset.univ.filter (fun v => (∃ c, phi c = v) ∧ v ∉ T) := by
    ext v
    rw [Rg.mem_I, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c, hc, -⟩, hv⟩
      exact ⟨Finset.mem_univ _, ⟨c, hc⟩, hv⟩
    · rintro ⟨-, ⟨c, hc⟩, hv⟩
      refine ⟨⟨c, hc, ?_⟩, hv⟩
      have hcb : inBox ((M : ℤ) - 1) c := by
        by_contra h
        have hcq : phi c = q := hout c (fun h' => h (by unfold inBox at h' ⊢; omega))
        exact hv (hc ▸ hcq ▸ hqT)
      exact ⟨(hin c hcb).1, (hin c hcb).2 0⟩
  rw [hQs, hI] at hD
  exact ⟨T, ⟨q, hqT⟩, hTok, hTimg, hD⟩

end TQ

end PQT

/-! 8100c3d9 D7a: one connected component at a time (filling on the subtype, pushed back to `V`),
and the union of translated Δ-models. -/

namespace PQT

section D7a

variable {V : Type}

lemma Dec_congr [Fintype V] [DecidableEq V] {H H0 : SimpleGraph V} {Ok Ok0 : Finset V → Prop}
    {A : Finset V} {QS : Finset (Finset V)} (d : Dec H0 Ok0 A QS)
    (hH : ∀ y ∈ A, ∀ w, H.Adj y w → H0.Adj y w) (hOk : ∀ Y ⊆ A, Ok0 Y → Ok Y) :
    Dec H Ok A QS := by
  obtain ⟨Ps, N, par, rk, h1, h2, h3, h4, h5, h6⟩ := d
  exact ⟨Ps, N, par, rk, fun Y hY => ⟨hOk Y (h1 Y hY).2.2 (h1 Y hY).1, (h1 Y hY).2⟩, h2, h3, h4,
    h5, fun Y hY y hy w hw => h6 Y hY y hy w (hH y ((h1 Y hY).2.2 hy) w hw)⟩

lemma mem_foldr_union [DecidableEq V] {α : Type} (I : α → Finset V) (v : V) :
    ∀ ch : List α, v ∈ ch.foldr (fun c s => I c ∪ s) ∅ ↔ ∃ c ∈ ch, v ∈ I c := by
  intro ch
  induction ch with
  | nil => simp
  | cons a t ih => rw [List.foldr_cons, Finset.mem_union, ih]; simp

lemma gphi_val {K : Finset V} (phi' : Cell → {v // v ∈ K}) (a b : {v // v ∈ K}) :
    (Gphi phi').Adj a b ↔ (Gphi (fun c => (phi' c).1)).Adj a.1 b.1 := by
  simp only [Gphi, SimpleGraph.fromRel_adj, ne_eq, Subtype.ext_iff]

lemma rtg_gen {α β : Type} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (h : ∀ a b, r a b → s (f a) (f b)) {a b : α} (hab : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen s (f a) (f b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

lemma dAdj_add {a b : Cell} (t : Cell) (h : dAdj a b) : dAdj (a + t) (b + t) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hk]; abel⟩

open Classical in
/-- one component: a filling with values in `K`, its Δ-model, the outer part `T` and a
decomposition of `K \ T` -/
theorem comp_core [Fintype V] [DecidableEq V] (hex : ExistsBd) (G : SimpleGraph V)
    (hG : PQL5.HasGridModel G) (L : V → ℕ) (p : V → V)
    (hp : ∀ v, 0 < L v → G.Adj v (p v) ∧ L (p v) + 1 = L v) (K : Finset V) (r : V) (hr : r ∈ K)
    (hcl : ∀ u v, u ∈ K → G.Adj u v → v ∈ K) (hroot : ∀ v ∈ K, L v = 0 → v = r) :
    ∃ phi : Cell → V, (∀ c, phi c ∈ K) ∧ (∀ u v, u ∈ K → G.Adj u v → (Gphi phi).Adj u v) ∧
      (∃ B : V → Finset Cell, (∀ v ∈ K, ∀ w ∈ K, v ≠ w → Disjoint (B v) (B w)) ∧
        (∀ v ∈ K, ∀ a ∈ B v, ∀ b ∈ B v, Relation.ReflTransGen (DRel (B v)) a b) ∧
        (∀ v ∈ K, (B v).Nonempty) ∧
        (∀ v w, (Gphi phi).Adj v w → ∃ a ∈ B v, ∃ b ∈ B w, dAdj a b)) ∧
      ∃ T : Finset V, T.Nonempty ∧ T ⊆ K ∧ OkG (Gphi phi) L T ∧
        Dec (Gphi phi) (OkG (Gphi phi) L) (K \ T) {T} := by
  haveI : Nonempty {v // v ∈ K} := ⟨⟨r, hr⟩⟩
  let Gk : SimpleGraph {v // v ∈ K} := G.comap Subtype.val
  have hGk : PQL5.HasGridModel Gk := by
    obtain ⟨B, h1, h2, h3, h4⟩ := hG
    exact ⟨fun a => B a.1, fun a b hab => h1 _ _ (fun e => hab (Subtype.ext e)),
      fun a => h2 a.1, fun a => h3 a.1, fun a b hab => h4 _ _ hab⟩
  obtain ⟨phi', R, q, hR, hout, hsurj, hfib, hle⟩ := filling Gk hGk
  obtain ⟨B', d1, d2, d3, d4⟩ := dModel_of_phi phi' R hR q hout hsurj hfib
  have himg : ∀ c, (phi' c).1 ∈ K := fun c => (phi' c).2
  have hadjK : ∀ u v, (Gphi (fun c => (phi' c).1)).Adj u v → ∃ (hu : u ∈ K) (hv : v ∈ K),
      (Gphi phi').Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v huv
    obtain ⟨c, hc⟩ := gphi_img huv
    obtain ⟨c', hc'⟩ := gphi_img huv.symm
    refine ⟨hc' ▸ himg c', hc ▸ himg c, ?_⟩
    exact (gphi_val phi' _ _).2 huv
  have hGadj : ∀ u v, u ∈ K → G.Adj u v → (Gphi (fun c => (phi' c).1)).Adj u v := by
    intro u v hu huv
    have := hle (show Gk.Adj ⟨u, hu⟩ ⟨v, hcl u v hu huv⟩ from huv)
    exact (gphi_val phi' _ _).1 this
  -- masked layering
  let LK : V → ℕ := fun v => if v ∈ K then L v else 0
  have hLK : ∀ v ∈ K, LK v = L v := fun v hv => if_pos hv
  have hpar : ∀ v, 0 < LK v →
      (Gphi (fun c => (phi' c).1)).Adj v (p v) ∧ LK (p v) + 1 = LK v := by
    intro v hv
    have hvK : v ∈ K := by
      by_contra h
      have : LK v = 0 := if_neg h
      omega
    rw [hLK v hvK] at hv ⊢
    obtain ⟨h1, h2⟩ := hp v hv
    exact ⟨hGadj v (p v) hvK h1, by rw [hLK _ (hcl v (p v) hvK h1)]; exact h2⟩
  have hroot' : ∀ c, LK (phi' c).1 = 0 → (phi' c).1 = r := fun c h =>
    hroot _ (himg c) (by rw [← hLK _ (himg c)]; exact h)
  have hout' : ∀ c, ¬ inBox R c → (phi' c).1 = q.1 := fun c h => by rw [hout c h]
  have hfib' : ∀ v c c', (phi' c).1 = v → (phi' c').1 = v →
      Relation.ReflTransGen (PRel (fun x => (phi' x).1 = v)) c c' := by
    intro v c c' hc hc'
    have e : phi' c' = phi' c := Subtype.ext (hc'.trans hc.symm)
    refine rtg_gen (r := PRel (fun x => phi' x = phi' c)) (s := PRel (fun x => (phi' x).1 = v))
      id (fun a b h => ?_) (hfib (phi' c) c c' rfl e)
    refine ⟨?_, ?_, h.2.2⟩
    · show (phi' a).1 = v
      rw [← hc]; exact congrArg Subtype.val h.1
    · show (phi' b).1 = v
      rw [← hc]; exact congrArg Subtype.val h.2.1
  obtain ⟨T, hTne, hTok, hTimg, hD⟩ :=
    top_core hex (fun c => (phi' c).1) R hR q.1 hout' hfib' LK p r hpar hroot'
  have himgset : (Finset.univ.filter (fun v => (∃ c, (phi' c).1 = v) ∧ v ∉ T)) = K \ T := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨c, rfl⟩, h⟩; exact ⟨himg c, h⟩
    · rintro ⟨hv, h⟩
      obtain ⟨c, hc⟩ := hsurj ⟨v, hv⟩
      exact ⟨⟨c, by rw [hc]⟩, h⟩
  have hOkK : ∀ Y ⊆ K, OkG (Gphi (fun c => (phi' c).1)) LK Y →
      OkG (Gphi (fun c => (phi' c).1)) L Y := by
    intro Y hY h
    refine ⟨h.1, fun i => ?_⟩
    have e : Y.filter (fun v => L v = i) = Y.filter (fun v => LK v = i) :=
      Finset.filter_congr (fun v hv => by rw [hLK v (hY hv)])
    rw [e]; exact h.2 i
  have hTK : T ⊆ K := fun v hv => by obtain ⟨c, rfl⟩ := hTimg v hv; exact himg c
  rw [himgset] at hD
  refine ⟨fun c => (phi' c).1, himg, hGadj,
    ⟨fun v => if h : v ∈ K then B' ⟨v, h⟩ else ∅, ?_, ?_, ?_, ?_⟩,
    T, hTne, hTK, hOkK T hTK hTok,
    Dec_congr hD (fun _ _ _ h => h)
      (fun Y hY h => hOkK Y (fun v hv => (Finset.mem_sdiff.1 (hY hv)).1) h)⟩
  · intro v hv w hw hvw
    simp only [dif_pos hv, dif_pos hw]
    exact d1 _ _ (fun e => hvw (congrArg Subtype.val e))
  · intro v hv a ha b hb
    simp only [dif_pos hv] at ha hb ⊢
    exact d2 _ a ha b hb
  · intro v hv; simp only [dif_pos hv]; exact d3 _
  · intro v w hvw
    obtain ⟨hv, hw, h⟩ := hadjK v w hvw
    simp only [dif_pos hv, dif_pos hw]
    exact d4 _ _ h

/-- union of Δ-models translated apart -/
lemma dmodel_glue {ι : Type} (H : SimpleGraph V) (rt : V → ι) (idx : ι → ℕ)
    (hidx : Function.Injective idx) (D : ℤ) (B : ι → V → Finset Cell)
    (hb : ∀ v, ∀ c ∈ B (rt v) v, -D ≤ c.1 ∧ c.1 ≤ D)
    (hdisj : ∀ v w, rt v = rt w → v ≠ w → Disjoint (B (rt v) v) (B (rt w) w))
    (hconn : ∀ v, ∀ a ∈ B (rt v) v, ∀ b ∈ B (rt v) v,
      Relation.ReflTransGen (DRel (B (rt v) v)) a b)
    (hne : ∀ v, (B (rt v) v).Nonempty)
    (hadj : ∀ v w, H.Adj v w → rt v = rt w ∧ ∃ a ∈ B (rt v) v, ∃ b ∈ B (rt w) w, dAdj a b) :
    PQL5.HasGridModel H := by
  classical
  let t : V → Cell := fun v => ((2 * D + 1) * (idx (rt v) : ℤ), 0)
  refine gridModel_of_dModel H (fun v => (B (rt v) v).image (· + t v)) ?_ ?_ ?_ ?_
  · intro v w hvw
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb', hab⟩ := Finset.mem_image.1 hx'
    by_cases hr : rt v = rt w
    · have e : t w = t v := by simp only [t, hr]
      rw [e] at hab
      have hba : b = a := add_right_cancel hab
      rw [hba] at hb'
      exact Finset.disjoint_left.1 (hdisj v w hr hvw) ha hb'
    · have hi : idx (rt v) ≠ idx (rt w) := fun e => hr (hidx e)
      have h1 := hb v a ha
      have h2 := hb w b hb'
      have hx1 : b.1 + (2 * D + 1) * (idx (rt w) : ℤ) = a.1 + (2 * D + 1) * (idx (rt v) : ℤ) := by
        have := congrArg Prod.fst hab
        simpa [t] using this
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · have h' : (idx (rt v) : ℤ) + 1 ≤ idx (rt w) := by exact_mod_cast h
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * D + 1 by linarith [h1.1, h1.2])
          (show (0 : ℤ) ≤ idx (rt w) - idx (rt v) - 1 by linarith)]
      · have h' : (idx (rt w) : ℤ) + 1 ≤ idx (rt v) := by exact_mod_cast h
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * D + 1 by linarith [h1.1, h1.2])
          (show (0 : ℤ) ≤ idx (rt v) - idx (rt w) - 1 by linarith)]
  · intro v x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hy
    exact rtg_gen (r := DRel (B (rt v) v)) (s := DRel ((B (rt v) v).image (· + t v))) (· + t v) (fun c d h => ⟨Finset.mem_image_of_mem _ h.1,
      Finset.mem_image_of_mem _ h.2.1, dAdj_add (t v) h.2.2⟩) (hconn v a ha b hb')
  · intro v; exact (hne v).image _
  · intro v w hvw
    obtain ⟨hr, a, ha, b, hb', hab⟩ := hadj v w hvw
    have e : t w = t v := by simp only [t, hr]
    refine ⟨a + t v, Finset.mem_image_of_mem _ ha, b + t w, Finset.mem_image_of_mem _ hb', ?_⟩
    rw [e]; exact dAdj_add (t v) hab

end D7a

end PQT

/-! 8100c3d9 D7b: all components together -> `CoreStmtM`. -/

namespace PQT

section D7b

open PlanarQueue.Planar

/-- the empty vertex type -/
theorem coreM_empty {V : Type} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V)
    (hG : PQL5.HasGridModel G) (L : V → ℕ) :
    ∃ (G' : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)),
      G ≤ G' ∧ PQL5.HasGridModel G' ∧
      (∀ A ∈ P.parts, (G'.induce (A : Set V)).Connected) ∧
      (∀ A ∈ P.parts, ∀ i : ℕ, (A.filter fun v => L v = i).card ≤ 3) ∧
      RobertsonSeymour1986.GM5.TreewidthLE (quotientGraph G' P) 3 := by
  classical
  let P : Finpartition (Finset.univ : Finset V) := ⊥
  have hno : ∀ A ∈ P.parts, False := fun A hA => by
    obtain ⟨v, -⟩ := P.nonempty_of_mem_parts hA
    exact IsEmpty.false v
  refine ⟨G, P, le_rfl, hG, fun A hA => (hno A hA).elim, fun A hA => (hno A hA).elim, ?_⟩
  refine ⟨Unit, inferInstance, ⊥, fun _ => ∅, ⟨⟨?_, ?_⟩, fun v => (hno v.1 v.2).elim,
    fun x _ _ => (hno x.1 x.2).elim, fun _ _ _ _ _ _ => by simp⟩, fun _ => by simp⟩
  · exact (SimpleGraph.connected_iff _).2 ⟨fun a b => by rw [Subsingleton.elim a b], ⟨()⟩⟩
  · intro v c hc
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons h _ => exact absurd h (by simp)

open Classical in
theorem coreM_holds (hex : ExistsBd) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hGM : PQL5.HasGridModel G) (L : V → ℕ) (hL : IsBFSLayering G L) :
      ∃ (G' : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)),
        G ≤ G' ∧ PQL5.HasGridModel G' ∧
        (∀ A ∈ P.parts, (G'.induce (A : Set V)).Connected) ∧
        (∀ A ∈ P.parts, ∀ i : ℕ, (A.filter fun v => L v = i).card ≤ 3) ∧
        RobertsonSeymour1986.GM5.TreewidthLE (quotientGraph G' P) 3 := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact coreM_empty G hGM L
  obtain ⟨Rr, hR1, hR2⟩ := hL
  obtain ⟨p, hp⟩ := bfs_parent G L ⟨Rr, hR1, hR2⟩
  let K : V → Finset V := fun r => Finset.univ.filter (fun v => G.Reachable r v)
  have hK : ∀ r v, v ∈ K r ↔ G.Reachable r v := fun r v => by simp [K]
  -- the root of a vertex
  let rt : V → V := fun v => (hR1 v).exists.choose
  have hrt : ∀ v, rt v ∈ Rr ∧ G.Reachable (rt v) v := fun v => (hR1 v).exists.choose_spec
  have hrtu : ∀ r v, r ∈ Rr → v ∈ K r → rt v = r := fun r v hr hv =>
    ((hR1 v).unique (hrt v) ⟨hr, (hK r v).1 hv⟩)
  have hvK : ∀ v, v ∈ K (rt v) := fun v => (hK _ _).2 (hrt v).2
  -- one component at a time
  have hcomp : ∀ r : V, ∃ phi : Cell → V, ∃ B : V → Finset Cell, ∃ T : Finset V, r ∈ Rr →
      (∀ c, phi c ∈ K r) ∧ (∀ u v, u ∈ K r → G.Adj u v → (Gphi phi).Adj u v) ∧
      ((∀ v ∈ K r, ∀ w ∈ K r, v ≠ w → Disjoint (B v) (B w)) ∧
        (∀ v ∈ K r, ∀ a ∈ B v, ∀ b ∈ B v, Relation.ReflTransGen (DRel (B v)) a b) ∧
        (∀ v ∈ K r, (B v).Nonempty) ∧
        (∀ v w, (Gphi phi).Adj v w → ∃ a ∈ B v, ∃ b ∈ B w, dAdj a b)) ∧
      T.Nonempty ∧ T ⊆ K r ∧ OkG (Gphi phi) L T ∧
        Dec (Gphi phi) (OkG (Gphi phi) L) (K r \ T) {T} := by
    intro r
    by_cases hr : r ∈ Rr
    · obtain ⟨phi, h1, h2, ⟨B, b1, b2, b3, b4⟩, T, t1, t2, t3, t4⟩ :=
        comp_core hex G hGM L p hp (K r) r ((hK r r).2 (SimpleGraph.Reachable.refl _))
          (fun u v hu huv => (hK r v).2 (((hK r u).1 hu).trans huv.reachable))
          (fun v hv h0 => by
            have hre := (hK r v).1 hv
            rw [hR2 r hr v hre] at h0
            exact ((SimpleGraph.Reachable.dist_eq_zero_iff hre).1 h0).symm)
      exact ⟨phi, B, T, fun _ => ⟨h1, h2, ⟨b1, b2, b3, b4⟩, t1, t2, t3, t4⟩⟩
    · exact ⟨fun _ => r, fun _ => ∅, ∅, fun h => absurd h hr⟩
  choose phiF BF TF hF using hcomp
  -- the union graph
  let H : SimpleGraph V := SimpleGraph.fromRel (fun u v => ∃ r ∈ Rr, (Gphi (phiF r)).Adj u v)
  have hH1 : ∀ r ∈ Rr, ∀ u v, (Gphi (phiF r)).Adj u v → H.Adj u v := fun r hr u v h =>
    (SimpleGraph.fromRel_adj _ _ _).2 ⟨h.ne, Or.inl ⟨r, hr, h⟩⟩
  have himgK : ∀ r ∈ Rr, ∀ u v, (Gphi (phiF r)).Adj u v → u ∈ K r ∧ v ∈ K r := by
    intro r hr u v h
    obtain ⟨c, hc⟩ := gphi_img h
    obtain ⟨c', hc'⟩ := gphi_img h.symm
    exact ⟨hc' ▸ (hF r hr).1 c', hc ▸ (hF r hr).1 c⟩
  have hH2 : ∀ u v, H.Adj u v → (Gphi (phiF (rt u))).Adj u v := by
    intro u v h
    rcases ((SimpleGraph.fromRel_adj _ _ _).1 h).2 with ⟨r, hr, h'⟩ | ⟨r, hr, h'⟩
    · rw [hrtu r u hr (himgK r hr u v h').1]; exact h'
    · rw [hrtu r u hr (himgK r hr v u h').2]; exact h'.symm
  have hGH : G ≤ H := fun u v h =>
    hH1 (rt u) (hrt u).1 u v ((hF _ (hrt u).1).2.1 u v (hvK u) h)
  have hOk : ∀ r ∈ Rr, ∀ Y : Finset V, OkG (Gphi (phiF r)) L Y → OkG H L Y := by
    intro r hr Y h
    refine ⟨h.1.mono ?_, h.2⟩
    intro a b hab
    exact hH1 r hr _ _ hab
  -- the top part
  let r0 := rt (Classical.arbitrary V)
  have hr0 : r0 ∈ Rr := (hrt _).1
  let T := TF r0
  have hT := (hF r0 hr0).2.2.2
  have hdisjK : ∀ r ∈ Rr, ∀ r' ∈ Rr, r ≠ r' → ∀ v, v ∈ K r → v ∉ K r' := by
    intro r hr r' hr' hne v hv hv'
    exact hne ((hrtu r v hr hv).symm.trans (hrtu r' v hr' hv'))
  let I : V → Finset V := fun r => if r = r0 then K r \ TF r else K r
  have hIK : ∀ r, I r ⊆ K r := fun r => by
    by_cases h : r = r0
    · simp only [I, if_pos h]; exact Finset.sdiff_subset
    · simp only [I, if_neg h]; exact subset_refl _
  have hDec : ∀ r ∈ Rr.toList, Dec H (OkG H L) (I r) {T} := by
    intro r hrl
    have hr : r ∈ Rr := Finset.mem_toList.1 hrl
    have dr : Dec H (OkG H L) (K r \ TF r) {TF r} :=
      Dec_congr (hF r hr).2.2.2.2.2.2 (fun y hy w hw => by
        have := hH2 y w hw
        rwa [hrtu r y hr (Finset.mem_sdiff.1 hy).1] at this)
        (fun Y _ h => hOk r hr Y h)
    by_cases h : r = r0
    · simp only [I, if_pos h]
      rw [h] at dr ⊢
      exact dr
    · simp only [I, if_neg h]
      refine Dec_step (hF r hr).2.2.2.2.1 (hF r hr).2.2.2.1 (hOk r hr _ (hF r hr).2.2.2.2.2.1) dr
        (by intro Q hQ; rw [Finset.mem_singleton] at hQ; rw [hQ]; exact Finset.mem_insert_self _ _)
        ?_ (by simp) ?_
      · intro Q hQ
        rw [Finset.mem_singleton] at hQ
        rw [hQ, Finset.disjoint_left]
        intro v hv hvr
        exact hdisjK r0 hr0 r hr (Ne.symm h) v (hT.2.1 hv) hvr
      · intro v hv w hw
        left
        have := hH2 v w hw
        rw [hrtu r v hr hv] at this
        exact (himgK r hr v w this).2
  have hmem : ∀ v, v ∈ Rr.toList.foldr (fun c s => I c ∪ s) ∅ ↔ v ∉ T := by
    intro v
    rw [mem_foldr_union]
    constructor
    · rintro ⟨r, hrl, hv⟩ hvT
      have hr : r ∈ Rr := Finset.mem_toList.1 hrl
      by_cases h : r = r0
      · simp only [I, if_pos h] at hv
        rw [h] at hv
        exact (Finset.mem_sdiff.1 hv).2 hvT
      · simp only [I, if_neg h] at hv
        exact hdisjK r0 hr0 r hr (Ne.symm h) v (hT.2.1 hvT) hv
    · intro hvT
      refine ⟨rt v, Finset.mem_toList.2 (hrt v).1, ?_⟩
      by_cases h : rt v = r0
      · simp only [I, if_pos h]
        rw [h]
        exact Finset.mem_sdiff.2 ⟨h ▸ hvK v, hvT⟩
      · simp only [I, if_neg h]; exact hvK v
  have hd := Dec_list I (fun _ => ({T} : Finset (Finset V))) {T} Rr.toList hDec
    (fun _ _ => subset_refl _)
    (fun Q hQ => by
      rw [Finset.mem_singleton] at hQ
      rw [hQ, Finset.disjoint_left]
      intro v hv hv'
      exact (hmem v).1 hv' hv)
    ((Finset.nodup_toList Rr).pairwise_of_forall_ne (fun a ha b hb hab => by
      rw [Finset.disjoint_left]
      intro v hva hvb
      exact hdisjK a (Finset.mem_toList.1 ha) b (Finset.mem_toList.1 hb) hab v (hIK a hva)
        (hIK b hvb)))
  obtain ⟨P, hPok, htw⟩ := part_of_dec hd hmem hT.1 (hOk r0 hr0 _ hT.2.2.1)
  -- the grid model of the union graph
  have hgrid : PQL5.HasGridModel H := by
    let D : ℤ := ∑ r ∈ Rr, ∑ v, ∑ c ∈ BF r v, |c.1|
    refine dmodel_glue H rt (fun r => (Fintype.equivFin V r : ℕ))
      (fun a b h => (Fintype.equivFin V).injective (Fin.ext h)) D BF ?_ ?_ ?_ ?_ ?_
    · intro v c hc
      have h1 : |c.1| ≤ ∑ c ∈ BF (rt v) v, |c.1| :=
        Finset.single_le_sum (f := fun c : Cell => |c.1|) (fun c _ => abs_nonneg _) hc
      have h2 : ∑ c ∈ BF (rt v) v, |c.1| ≤ ∑ w, ∑ c ∈ BF (rt v) w, |c.1| :=
        Finset.single_le_sum (f := fun w => ∑ c ∈ BF (rt v) w, |c.1|)
          (fun w _ => Finset.sum_nonneg (fun c _ => abs_nonneg _)) (Finset.mem_univ v)
      have h3 : ∑ w, ∑ c ∈ BF (rt v) w, |c.1| ≤ D :=
        Finset.single_le_sum (f := fun r => ∑ w, ∑ c ∈ BF r w, |c.1|)
          (fun r _ => Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun c _ => abs_nonneg _)))
          (hrt v).1
      exact abs_le.1 (h1.trans (h2.trans h3))
    · intro v w hvw hne
      have hw : w ∈ K (rt v) := hvw ▸ hvK w
      rw [← hvw]
      exact (hF _ (hrt v).1).2.2.1.1 v (hvK v) w hw hne
    · intro v
      exact (hF _ (hrt v).1).2.2.1.2.1 v (hvK v)
    · intro v
      exact (hF _ (hrt v).1).2.2.1.2.2.1 v (hvK v)
    · intro v w hvw
      have h := hH2 v w hvw
      have hw : rt w = rt v := hrtu (rt v) w (hrt v).1 (himgK _ (hrt v).1 v w h).2
      refine ⟨hw.symm, ?_⟩
      rw [hw]
      exact (hF _ (hrt v).1).2.2.1.2.2.2 v w h
  exact ⟨H, P, hGH, hgrid, fun A hA => (hPok A hA).1, fun A hA i => (hPok A hA).2 i, htw⟩

end D7b

end PQT

open PlanarQueue.Planar in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (fun a b : ℤ × ℤ => a ∈ B v ∧ b ∈ B v ∧
        (b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1))) p q) ∧
      (∀ v, (B v).Nonempty) ∧
      (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w,
        (q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)))))
    (L : V → ℕ) (hL : IsBFSLayering G L) :
    ∃ (G' : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)),
      G ≤ G' ∧
    (∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (fun a b : ℤ × ℤ => a ∈ B v ∧ b ∈ B v ∧
        (b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1))) p q) ∧
      (∀ v, (B v).Nonempty) ∧
      (∀ v w, G'.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w,
        (q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)))) ∧
      (∀ A ∈ P.parts, (G'.induce (A : Set V)).Connected) ∧
      (∀ A ∈ P.parts, ∀ i : ℕ, (A.filter fun v => L v = i).card ≤ 3) ∧
      RobertsonSeymour1986.GM5.TreewidthLE (quotientGraph G' P) 3 := by
  exact PQT.coreM_holds PQT.lexists G hG L hL
