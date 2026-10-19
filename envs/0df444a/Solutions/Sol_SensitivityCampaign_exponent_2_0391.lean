-- Prove2me | solution 1 for SensitivityCampaign.exponent_2_0391
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T10:46:34.74121+00:00
-- url     : https://prove2.me/submissions/157e0151-e62a-4c18-91fc-8b4c41efbdd4

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate


-- ===== module Defs =====

/-!
# Sensitivity, block sensitivity, nested families and their profiles

`flip`, `sensitivityAt`, `sensitivity`, `blockSensitivityAt` and `blockSensitivity` are verbatim the definitions of the
published comparator statement for the superquadratic separation. A *nested family* on an input type `I` is a
sequence of predicates `P q`, `1 ≤ q ≤ H`, whose accepting sets decrease in `q`. `Profile` records upper bounds on
the four sensitivity profiles `S₀, S₁, J₀, J₁` of a nested family.
-/

noncomputable section
open scoped Classical

namespace BSSep

def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i

def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card

def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0

def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)

/-- A nested family with indices `1 ≤ q ≤ H`: acceptance at a larger index implies acceptance at a smaller one. -/
structure Nested (I : Type) where
  H : ℕ
  P : ℕ → (I → Bool) → Bool
  nested : ∀ q q' x, 1 ≤ q → q ≤ q' → q' ≤ H → P q' x = true → P q x = true

/-- Upper bounds `(S₀, S₁, J₀, J₁)` on the ordinary and joint sensitivity profiles of a nested family. `S b` bounds the
number of single-bit flips taking one predicate from `b` to `!b`; `J b` bounds the flips taking two distinct predicates
of the family, both equal to `b`, simultaneously to `!b`. -/
structure Profile {I : Type} [Fintype I] (F : Nested I) (S0 S1 J0 J1 : ℕ) : Prop where
  s0 : ∀ q x, 1 ≤ q → q ≤ F.H → F.P q x = false →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = true).card ≤ S0
  s1 : ∀ q x, 1 ≤ q → q ≤ F.H → F.P q x = true →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = false).card ≤ S1
  j0 : ∀ q q' x, 1 ≤ q → q < q' → q' ≤ F.H → F.P q x = false → F.P q' x = false →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = true ∧ F.P q' (flip x {a}) = true).card ≤ J0
  j1 : ∀ q q' x, 1 ≤ q → q < q' → q' ≤ F.H → F.P q x = true → F.P q' x = true →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = false ∧ F.P q' (flip x {a}) = false).card ≤ J1

/-- Index-dependent profile bounds: `S b q` for predicate `q`, `J b q q'` for the pair `q < q'`. -/
structure IProfile {I : Type} [Fintype I] (F : Nested I) (S0 S1 : ℕ → ℕ) (J0 J1 : ℕ → ℕ → ℕ) : Prop where
  s0 : ∀ q x, 1 ≤ q → q ≤ F.H → F.P q x = false →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = true).card ≤ S0 q
  s1 : ∀ q x, 1 ≤ q → q ≤ F.H → F.P q x = true →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = false).card ≤ S1 q
  j0 : ∀ q q' x, 1 ≤ q → q < q' → q' ≤ F.H → F.P q x = false → F.P q' x = false →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = true ∧ F.P q' (flip x {a}) = true).card ≤ J0 q q'
  j1 : ∀ q q' x, 1 ≤ q → q < q' → q' ≤ F.H → F.P q x = true → F.P q' x = true →
    (Finset.univ.filter fun a => F.P q (flip x {a}) = false ∧ F.P q' (flip x {a}) = false).card ≤ J1 q q'

/-- `N` pairwise disjoint nonempty blocks at the all-false input, each of which, flipped, makes every predicate of the
family accept; and every predicate rejects the all-false input. -/
structure ZeroBlocks {I : Type} (F : Nested I) (N : ℕ) : Prop where
  zero : ∀ q, 1 ≤ q → q ≤ F.H → F.P q (fun _ => false) = false
  blocks : ∃ B : Fin N → Finset I, (∀ u, (B u).Nonempty) ∧ (∀ u v, u ≠ v → Disjoint (B u) (B v)) ∧
    ∀ u q, 1 ≤ q → q ≤ F.H → F.P q (flip (fun _ => false) (B u)) = true

@[simp] lemma flip_apply {I : Type} (x : I → Bool) (B : Finset I) (i : I) :
    flip x B i = if i ∈ B then !(x i) else x i := rfl

lemma flip_empty {I : Type} (x : I → Bool) : flip x ∅ = x := by
  funext i; simp [flip]

lemma flip_single_ne {I : Type} (x : I → Bool) (a i : I) (h : i ≠ a) : flip x {a} i = x i := by
  simp [flip, h]

end BSSep

-- ===== module Base =====

/-!
# The base family: unions of Hamming balls around separated centres

Inputs are `Fin M × Fin (d+2)` (M blocks of length `d+2`). Centre `z j` is the indicator of block `j`; distinct centres
are at Hamming distance `2(d+2)`. Predicate `q` (`1 ≤ q ≤ d+1`) accepts iff some centre lies within distance
`d+1-q`, written `hd x (z j) + q ≤ d+1` to avoid truncated subtraction.
-/

noncomputable section
open scoped Classical

namespace BSSep

variable {M d : ℕ}

/-- Hamming distance. -/
abbrev hd {I : Type} [Fintype I] (x y : I → Bool) : ℕ := hammingDist x y

/-- Centre `j`: the indicator of block `j`. -/
def z (M d : ℕ) (j : Fin M) : Fin M × Fin (d+2) → Bool := fun p => decide (p.1 = j)

/-- The base nested family. -/
def baseFam (M d : ℕ) : Nested (Fin M × Fin (d+2)) where
  H := d + 1
  P q x := decide (∃ j : Fin M, hd x (z M d j) + q ≤ d + 1)
  nested := by
    intro q q' x _ hqq' _ h
    simp only [decide_eq_true_eq] at h ⊢
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by omega⟩

lemma baseFam_P (q : ℕ) (x : Fin M × Fin (d+2) → Bool) :
    (baseFam M d).P q x = true ↔ ∃ j : Fin M, hd x (z M d j) + q ≤ d + 1 := by
  simp [baseFam]

lemma baseFam_P_false (q : ℕ) (x : Fin M × Fin (d+2) → Bool) :
    (baseFam M d).P q x = false ↔ ∀ j : Fin M, d + 1 < hd x (z M d j) + q := by
  rw [← Bool.not_eq_true, baseFam_P]; push Not; rfl

/-! ### Hamming-distance facts -/

section general
variable {I : Type} [Fintype I] [DecidableEq I]

/-- One flip moves a point by distance at most one. -/
lemma hd_flip_self (x : I → Bool) (a : I) : hd (flip x {a}) x ≤ 1 := by
  unfold hd hammingDist
  calc (Finset.univ.filter fun i => flip x {a} i ≠ x i).card ≤ ({a} : Finset I).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra h
        exact hi (flip_single_ne x a i (by simpa using h))
    _ = 1 := by simp

lemma hd_flip_le (x y : I → Bool) (a : I) : hd (flip x {a}) y ≤ hd x y + 1 := by
  have := hammingDist_triangle (flip x {a}) x y
  have := hd_flip_self x a
  unfold hd at *; omega

lemma hd_le_flip (x y : I → Bool) (a : I) : hd x y ≤ hd (flip x {a}) y + 1 := by
  have := hammingDist_triangle x (flip x {a}) y
  have h1 := hd_flip_self x a
  unfold hd at *
  rw [hammingDist_comm] at h1
  omega

/-- Flipping a bit where `x` agrees with `y` moves exactly one step away from `y`. -/
lemma hd_flip_agree (x y : I → Bool) (a : I) (h : x a = y a) : hd (flip x {a}) y = hd x y + 1 := by
  unfold hd hammingDist
  have hset : (Finset.univ.filter fun i => flip x {a} i ≠ y i) =
      insert a (Finset.univ.filter fun i => x i ≠ y i) := by
    ext i
    by_cases hi : i = a
    · subst hi; cases hx : x i <;> cases hy : y i <;> simp_all [flip]
    · simp [hi]
  rw [hset, Finset.card_insert_of_notMem (by simp [h])]

end general

lemma block_card (j : Fin M) :
    (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j).card = d + 2 := by
  have : (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j) = {j} ×ˢ Finset.univ := by
    ext p; obtain ⟨p1, p2⟩ := p; simp [eq_comm]
  rw [this, Finset.card_product]; simp

lemma hd_zero_z (j : Fin M) : hd (fun _ => false) (z M d j) = d + 2 := by
  unfold hd hammingDist
  have : (Finset.univ.filter fun p : Fin M × Fin (d+2) => (fun _ => false) p ≠ z M d j p) =
      Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j := by
    ext p; simp [z, eq_comm]
  rw [this, block_card]

/-- Distinct centres are at distance at least `2(d+2)`. -/
lemma hd_z_z (j j' : Fin M) (h : j ≠ j') : 2 * (d + 2) ≤ hd (z M d j) (z M d j') := by
  unfold hd hammingDist
  have hsub : (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j) ∪
      (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j') ⊆
      Finset.univ.filter fun p => z M d j p ≠ z M d j' p := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with hp | hp <;> subst hp <;> simp [z, h, Ne.symm h]
  have hdisj : Disjoint (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j)
      (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j') := by
    rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h (h1.symm.trans h2)
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, block_card, block_card] at this
  omega

/-- No point is within distance `d+1` of two distinct centres. -/
lemma centre_unique (x : Fin M × Fin (d+2) → Bool) (j j' : Fin M)
    (h1 : hd x (z M d j) ≤ d + 1) (h2 : hd x (z M d j') ≤ d + 1) : j = j' := by
  by_contra h
  have := hd_z_z (d := d) j j' h
  have ht := hammingDist_triangle (z M d j) x (z M d j')
  rw [hammingDist_comm (z M d j) x] at ht
  unfold hd at *; omega

/-! ### Main results -/

theorem base_profile (M d : ℕ) : Profile (baseFam M d) (d+1) (M*(d+2)) 0 0 where
  s0 := by
    intro q x hq _ hx
    rw [baseFam_P_false] at hx
    set S := Finset.univ.filter fun a => (baseFam M d).P q (flip x {a}) = true
    rcases S.eq_empty_or_nonempty with hS | ⟨a, ha⟩
    · rw [hS]; simp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, baseFam_P] at ha
    obtain ⟨j, hj⟩ := ha
    have hxj : hd x (z M d j) ≤ d + 1 := by
      have := hd_le_flip x (z M d j) a; omega
    calc S.card ≤ (Finset.univ.filter fun i => x i ≠ z M d j i).card := by
          apply Finset.card_le_card
          intro b hb
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, baseFam_P] at hb ⊢
          obtain ⟨j', hj'⟩ := hb
          have hxj' : hd x (z M d j') ≤ d + 1 := by
            have := hd_le_flip x (z M d j') b; omega
          have hjj := centre_unique x j j' hxj hxj'
          subst hjj
          intro hagree
          have := hd_flip_agree x (z M d j) b hagree
          have := hx j
          omega
      _ = hd x (z M d j) := rfl
      _ ≤ d + 1 := hxj
  s1 := by
    intro q x _ _ _
    calc _ ≤ (Finset.univ : Finset (Fin M × Fin (d+2))).card := Finset.card_le_univ _
      _ = M * (d+2) := by simp
  j0 := by
    intro q q' x _ hqq' _ hx _
    apply Nat.le_zero.mpr
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a - ⟨-, h'⟩
    rw [baseFam_P] at h'
    rw [baseFam_P_false] at hx
    obtain ⟨j, hj⟩ := h'
    have := hd_le_flip x (z M d j) a
    have := hx j
    omega
  j1 := by
    intro q q' x _ hqq' _ _ hx'
    apply Nat.le_zero.mpr
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a - ⟨h, -⟩
    rw [baseFam_P] at hx'
    rw [baseFam_P_false] at h
    obtain ⟨j, hj⟩ := hx'
    have := hd_flip_le x (z M d j) a
    have := h j
    omega

theorem base_zero (M d : ℕ) : ZeroBlocks (baseFam M d) M where
  zero := by
    intro q hq _
    rw [baseFam_P_false]
    intro j
    rw [hd_zero_z]; omega
  blocks := by
    refine ⟨fun j => Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j, ?_, ?_, ?_⟩
    · intro j; exact ⟨(j, 0), by simp⟩
    · intro u v huv
      rw [Finset.disjoint_filter]; intro p _ h1 h2; exact huv (h1.symm.trans h2)
    · intro j q _ hq
      rw [baseFam_P]
      refine ⟨j, ?_⟩
      have : flip (fun _ => false) (Finset.univ.filter fun p : Fin M × Fin (d+2) => p.1 = j) = z M d j := by
        funext p; by_cases hp : p.1 = j <;> simp [flip, z, hp]
      rw [this]
      simp only [hd, hammingDist_self]
      simpa [baseFam] using hq

end BSSep

-- ===== module Labels =====

/-!
# Labels for the gated cyclic tournament

`cyc D` is the cyclic tournament on `Fin (2D+1)`: `i → j` iff `j - i mod (2D+1)` lies in `[1, D]`. A labelling
`a : Fin k → Fin k → Fin r` is *consistent* on a row set `T` if every edge inside `T` carries a label depending only on
its head. `labels_exist` is the union bound: if `C(k,t) r^t < r^C(t,2)` (stated with `k.descFactorial t = t! C(k,t)`),
some labelling is inconsistent on every row set of size at least `t`.

For concrete parameters the hypothesis is a closed `Nat` inequality; `decide +kernel` checks it in milliseconds
(e.g. `D = 2^40, r = 8, t = 46`), as does `norm_num [Nat.descFactorial, Nat.factorial, Nat.choose]` under
`set_option exponentiation.threshold 5000`.
-/

namespace BSSep

open scoped Classical

/-- The cyclic tournament on `Fin (2D+1)`. -/
def cyc (D : ℕ) (i j : Fin (2*D+1)) : Prop :=
  1 ≤ (j.val + (2*D+1) - i.val) % (2*D+1) ∧ (j.val + (2*D+1) - i.val) % (2*D+1) ≤ D

instance (D : ℕ) : DecidableRel (cyc D) := fun i j => by unfold cyc; infer_instance

lemma cyc_dist (D : ℕ) (i j : Fin (2*D+1)) :
    (j.val + (2*D+1) - i.val) % (2*D+1) =
      if i.val ≤ j.val then j.val - i.val else j.val + (2*D+1) - i.val := by
  have hi := i.isLt; have hj := j.isLt
  split_ifs with h
  · have e : j.val + (2*D+1) - i.val = (j.val - i.val) + (2*D+1) := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma cyc_irrefl (D : ℕ) (i : Fin (2*D+1)) : ¬ cyc D i i := by
  unfold cyc; rw [cyc_dist]; simp

lemma cyc_total (D : ℕ) {i j : Fin (2*D+1)} (h : i ≠ j) : cyc D i j ∨ cyc D j i := by
  have hne : i.val ≠ j.val := fun e => h (Fin.ext e)
  have hi := i.isLt; have hj := j.isLt
  unfold cyc; rw [cyc_dist, cyc_dist]
  split_ifs <;> omega

lemma cyc_asymm (D : ℕ) {i j : Fin (2*D+1)} (h : cyc D i j) : ¬ cyc D j i := by
  have hi := i.isLt; have hj := j.isLt
  unfold cyc at *; simp only [cyc_dist] at *
  split_ifs at * <;> omega

lemma cyc_outdeg (D : ℕ) (i : Fin (2*D+1)) :
    (Finset.univ.filter (fun j => cyc D i j)).card ≤ D := by
  have hi := i.isLt
  have hle := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun j => cyc D i j)) (t := Finset.range D)
    (fun j : Fin (2*D+1) => (j.val + (2*D+1) - i.val) % (2*D+1) - 1)
    (by
      intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_coe, Finset.mem_range]
      unfold cyc at hj
      omega)
    (by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have ha' := a.isLt; have hb' := b.isLt
      unfold cyc at ha hb
      simp only at hab
      rw [cyc_dist] at ha hab; rw [cyc_dist] at hb hab
      apply Fin.ext
      split_ifs at ha hb hab <;> omega)
  simpa using hle

/-- `a` is consistent on `T` for the relation `E`: the label of every edge inside `T` depends only on its head. -/
def Consistent {k r : ℕ} (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (T : Finset (Fin k)) : Prop :=
  ∃ m : Fin k → Fin r, ∀ i ∈ T, ∀ j ∈ T, E i j → a i j = m j

lemma Consistent.mono {k r : ℕ} {E : Fin k → Fin k → Prop} {a : Fin k → Fin k → Fin r}
    {T T' : Finset (Fin k)} (hsub : T' ⊆ T) (hc : Consistent E a T) : Consistent E a T' := by
  obtain ⟨m, hm⟩ := hc
  exact ⟨m, fun i hi j hj e => hm i (hsub hi) j (hsub hj) e⟩

/-- The ordered edge pairs of `cyc D` inside `T`. -/
def edgesIn (D : ℕ) (T : Finset (Fin (2*D+1))) : Finset (Fin (2*D+1) × Fin (2*D+1)) :=
  T.offDiag.filter (fun p => cyc D p.1 p.2)

/-- A tournament has exactly `C(|T|, 2)` edges inside `T`. -/
lemma card_edgesIn (D : ℕ) (T : Finset (Fin (2*D+1))) : (edgesIn D T).card = T.card.choose 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := T.offDiag) (fun p => cyc D p.1 p.2)
  have hswap : T.offDiag.filter (fun p => ¬ cyc D p.1 p.2) =
      (edgesIn D T).map (Equiv.prodComm _ _).toEmbedding := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_map_equiv, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Prod.swap_prod_mk, edgesIn]
    constructor
    · rintro ⟨⟨hx, hy, hne⟩, hn⟩
      exact ⟨⟨hy, hx, Ne.symm hne⟩, (cyc_total D hne).resolve_left hn⟩
    · rintro ⟨⟨hy, hx, hne⟩, hc⟩
      exact ⟨⟨hx, hy, Ne.symm hne⟩, cyc_asymm D hc⟩
  rw [hswap, Finset.card_map, Finset.offDiag_card] at hsplit
  change (edgesIn D T).card + (edgesIn D T).card = _ at hsplit
  rw [Nat.choose_two_right, Nat.mul_sub_one, ← hsplit]
  omega

theorem labels_exist (D r t : ℕ) (hr : 1 ≤ r) (_ht : 2 ≤ t)
    (h : (2*D+1).descFactorial t * r ^ t < t.factorial * r ^ (t.choose 2)) :
    ∃ a : Fin (2*D+1) → Fin (2*D+1) → Fin r,
      ∀ T : Finset (Fin (2*D+1)), t ≤ T.card → ¬ Consistent (cyc D) a T := by
  rcases lt_or_ge (2*D+1) t with hkt | hkt
  · -- no row set has `t` elements
    refine ⟨fun _ _ => ⟨0, hr⟩, fun T hT _ => ?_⟩
    have := T.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  set k := 2*D+1 with hk
  -- labellings consistent with the row set `T` and head labels `m`
  let good : (T : Finset (Fin k)) → (T → Fin r) → Finset (Fin k → Fin k → Fin r) := fun T m =>
    Finset.univ.filter (fun a => ∀ i (hi : i ∈ T) j (hj : j ∈ T), cyc D i j → a i j = m ⟨j, hj⟩)
  have hgood : ∀ T : Finset (Fin k), T.card = t → ∀ m : T → Fin r,
      (good T m).card ≤ r ^ (k*k - t.choose 2) := by
    intro T hT m
    let S := edgesIn D T
    have hS : S.card = t.choose 2 := by rw [card_edgesIn, hT]
    let f : (Fin k → Fin k → Fin r) → ((Sᶜ : Finset _) → Fin r) := fun a p => a p.1.1 p.1.2
    have hinj : Set.InjOn f (good T m) := by
      intro a ha b hb hab
      simp only [good, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      funext i j
      by_cases hp : (i, j) ∈ S
      · simp only [S, edgesIn, Finset.mem_filter, Finset.mem_offDiag] at hp
        obtain ⟨⟨hi, hj, -⟩, hc⟩ := hp
        rw [ha i hi j hj hc, hb i hi j hj hc]
      · exact congrFun hab ⟨(i, j), Finset.mem_compl.2 hp⟩
    calc (good T m).card ≤ (Finset.univ : Finset ((Sᶜ : Finset _) → Fin r)).card :=
          Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
      _ = r ^ (k*k - t.choose 2) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
            Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hS]
  -- every labelling consistent on some `t`-set lies in `bad`
  let bad := (Finset.powersetCard t (Finset.univ : Finset (Fin k))).biUnion
    (fun T => (Finset.univ : Finset (T → Fin r)).biUnion (fun m => good T m))
  have hbad : bad.card ≤ k.choose t * (r ^ t * r ^ (k*k - t.choose 2)) := by
    refine Finset.card_biUnion_le.trans ?_
    have hT : ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin k)),
        ((Finset.univ : Finset (T → Fin r)).biUnion (fun m => good T m)).card ≤
          r ^ t * r ^ (k*k - t.choose 2) := by
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum (fun m _ => hgood T hT.2 m)).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
        Fintype.card_fin, hT.2]
    refine (Finset.sum_le_sum hT).trans ?_
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hlt : k.choose t * (r ^ t * r ^ (k*k - t.choose 2)) < r ^ (k*k) := by
    have h1 : k.choose t * r ^ t < r ^ (t.choose 2) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc] at h
      exact Nat.lt_of_mul_lt_mul_left h
    have hle : t.choose 2 ≤ k*k := by
      rw [Nat.choose_two_right]
      calc t * (t - 1) / 2 ≤ t * (t - 1) := Nat.div_le_self _ _
        _ ≤ t * t := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ k * k := Nat.mul_le_mul hkt hkt
    have hpos : 0 < r ^ (k*k - t.choose 2) := pow_pos hr _
    calc k.choose t * (r ^ t * r ^ (k*k - t.choose 2))
        = (k.choose t * r ^ t) * r ^ (k*k - t.choose 2) := by rw [mul_assoc]
      _ < r ^ (t.choose 2) * r ^ (k*k - t.choose 2) := Nat.mul_lt_mul_of_pos_right h1 hpos
      _ = r ^ (k*k) := by rw [← pow_add, Nat.add_sub_cancel' hle]
  have hex : ∃ a, a ∉ bad := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin k → Fin k → Fin r)) ⊆ bad := fun a _ => hcon a
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul] at hc
    exact absurd (hc.trans hbad) (not_le.2 hlt)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, fun T hT hc => ha ?_⟩
  obtain ⟨T', hT'T, hT'⟩ := Finset.exists_subset_card_eq hT
  obtain ⟨m, hm⟩ := hc.mono hT'T
  simp only [bad, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_univ, true_and]
  refine ⟨T', ⟨Finset.subset_univ _, hT'⟩, fun x => m x.1, ?_⟩
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi j hj e => hm i hi j hj e

end BSSep

-- ===== module Step =====

/-!
# The recursive step

Rows `j : Fin k`, positions `c : Fin r`; the parent input is `Fin k × Fin r × I`, child `(j, c)` reads the bits
`(j, c, ·)`. `E` is a tournament on the rows with outdegree at most `D`; `a i j` is the position, in row `j`, of the gate
child of the edge `i → j`. With `Q = H + 1` the child family's top index, clause `i` at index `q` asserts
`P_Q = 1` on every child of row `i` (targets) and `P_{Q-q} = 0` on the gate child of every out-edge `i → j` (gates);
the parent predicate at `q` is the OR of the clauses.
-/

noncomputable section
open scoped Classical

set_option linter.unusedSectionVars false

namespace BSSep

variable {I : Type} [Fintype I] {k r : ℕ} {i : Fin k} {α : Type}

/-- Child `(j, c)` of a parent input. -/
def child (y : Fin k × Fin r × I → Bool) (j : Fin k) (c : Fin r) : I → Bool := fun i => y (j, c, i)

/-- A tournament on the rows. -/
structure Tourn (E : Fin k → Fin k → Prop) : Prop where
  irrefl : ∀ i, ¬ E i i
  total : ∀ i j, i ≠ j → E i j ∨ E j i
  asymm : ∀ i j, E i j → ¬ E j i

/-- No `t` rows admit choices `m` consistent with the labels on all internal edges. -/
def NoConsistent (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) : Prop :=
  ∀ T : Finset (Fin k), t ≤ T.card → ¬ ∃ m : Fin k → Fin r, ∀ i ∈ T, ∀ j ∈ T, E i j → a i j = m j

/-- Clause `i` of the parent at index `q`. -/
def clause (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (q : ℕ)
    (y : Fin k × Fin r × I → Bool) (i : Fin k) : Prop :=
  (∀ c, F.P F.H (child y i c) = true) ∧ (∀ j, E i j → F.P (F.H - q) (child y j (a i j)) = false)


lemma child_flip_same (y : Fin k × Fin r × I → Bool) (j : Fin k) (c : Fin r) (ι : I) :
    child (flip y {(j, c, ι)}) j c = flip (child y j c) {ι} := by
  funext ι'; simp [child, flip]

lemma child_flip_ne (y : Fin k × Fin r × I → Bool) {j j' : Fin k} {c c' : Fin r} (ι : I)
    (h : ¬ (j' = j ∧ c' = c)) : child (flip y {(j, c, ι)}) j' c' = child y j' c' := by
  funext ι'; simp only [child, flip, Finset.mem_singleton, Prod.mk.injEq]
  split_ifs with h1
  · exact absurd ⟨h1.1, h1.2.1⟩ h
  · rfl

/-- Contrapositive form of nesting: rejection at a smaller index forces rejection at a larger one. -/
lemma Nested.false_of_false (F : Nested I) {g g' : ℕ} (x : I → Bool) (hg : 1 ≤ g) (hgg : g ≤ g') (hg' : g' ≤ F.H)
    (h : F.P g x = false) : F.P g' x = false := by
  cases h' : F.P g' x
  · rfl
  · rw [F.nested g g' x hg hgg hg' h'] at h; exact absurd h (by decide)

lemma clause_mono (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) {q q' : ℕ}
    (y : Fin k × Fin r × I → Bool) (i : Fin k) (hq : 1 ≤ q) (hqq : q ≤ q') (hq' : q' + 1 ≤ F.H)
    (h : clause F E a q' y i) : clause F E a q y i := by
  refine ⟨h.1, fun j hj => ?_⟩
  exact F.false_of_false _ (by omega) (by omega) (by omega) (h.2 j hj)

/-- Every single-bit flip that makes a rejected parent predicate accept repairs the unique failed condition of some
clause: either a target `(i, c)` (all gates and other targets of `i` already hold), or a gate `i → j` on the child
`(j, a i j)` (all targets and other gates of `i` already hold). -/
lemma to_true_cases (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (hE : Tourn E) {q : ℕ}
    (y : Fin k × Fin r × I → Bool) (hy : ¬ clause F E a q y i) {j : Fin k} {c : Fin r} {ι : I}
    (hi : clause F E a q (flip y {(j, c, ι)}) i) :
    (j = i ∧ F.P F.H (child y i c) = false ∧ (∀ c', c' ≠ c → F.P F.H (child y i c') = true) ∧
        (∀ j', E i j' → F.P (F.H - q) (child y j' (a i j')) = false) ∧
        F.P F.H (flip (child y i c) {ι}) = true) ∨
    (E i j ∧ c = a i j ∧ (∀ c', F.P F.H (child y i c') = true) ∧ F.P (F.H - q) (child y j c) = true ∧
        (∀ j', E i j' → j' ≠ j → F.P (F.H - q) (child y j' (a i j')) = false) ∧
        F.P (F.H - q) (flip (child y j c) {ι}) = false) := by
  obtain ⟨hT, hG⟩ := hi
  by_cases hji : j = i
  · subst hji
    left
    have gates : ∀ j', E j j' → F.P (F.H - q) (child y j' (a j j')) = false := by
      intro j' hj'
      have hne : ¬ (j' = j ∧ a j j' = c) := fun h => hE.irrefl j (h.1 ▸ hj')
      have := hG j' hj'; rwa [child_flip_ne y ι hne] at this
    have others : ∀ c', c' ≠ c → F.P F.H (child y j c') = true := by
      intro c' hc'
      have := hT c'; rwa [child_flip_ne y ι (fun h => hc' h.2)] at this
    have after : F.P F.H (flip (child y j c) {ι}) = true := by
      have := hT c; rwa [child_flip_same] at this
    refine ⟨rfl, ?_, others, gates, after⟩
    cases hb : F.P F.H (child y j c)
    · rfl
    · exact absurd ⟨fun c' => if h : c' = c then h ▸ hb else others c' h, gates⟩ hy
  · right
    have targets : ∀ c', F.P F.H (child y i c') = true := by
      intro c'
      have := hT c'; rwa [child_flip_ne y ι (fun h => hji h.1.symm)] at this
    have others : ∀ j', E i j' → j' ≠ j → F.P (F.H - q) (child y j' (a i j')) = false := by
      intro j' hj' hne
      have := hG j' hj'; rwa [child_flip_ne y ι (fun h => hne h.1)] at this
    by_cases hgate : E i j ∧ c = a i j
    · obtain ⟨hEij, hc⟩ := hgate
      subst hc
      have after : F.P (F.H - q) (flip (child y j (a i j)) {ι}) = false := by
        have := hG j hEij; rwa [child_flip_same] at this
      refine ⟨hEij, rfl, targets, ?_, others, after⟩
      cases hb : F.P (F.H - q) (child y j (a i j))
      · exact absurd ⟨targets, fun j' hj' => if h : j' = j then h ▸ hb else others j' hj' h⟩ hy
      · rfl
    · exfalso; apply hy
      refine ⟨targets, fun j' hj' => ?_⟩
      by_cases h : j' = j
      · subst h
        have hc : ¬ (j' = j' ∧ a i j' = c) := fun h' => hgate ⟨hj', h'.2.symm⟩
        have := hG j' hj'; rwa [child_flip_ne y ι hc] at this
      · exact others j' hj' h

/-- The embedding of child `(j, c)` into the parent input. -/
def emb (j : Fin k) (c : Fin r) : I ↪ Fin k × Fin r × I := ⟨fun ι => (j, c, ι), fun _ _ h => by simpa using h⟩

@[simp] lemma emb_apply (j : Fin k) (c : Fin r) (ι : I) : emb j c ι = (j, c, ι) := rfl

lemma mem_rowBlock {j : Fin k} {B : Finset I} {x : Fin k × Fin r × I} :
    x ∈ (Finset.univ : Finset (Fin r)).biUnion (fun c => B.map (emb j c)) ↔ x.1 = j ∧ x.2.2 ∈ B := by
  obtain ⟨j', c', ι'⟩ := x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map, emb_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨c, ι, h, rfl, rfl, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨c', ι', h, rfl, rfl, rfl⟩

/-- Bits of a child input whose flip sets predicate `g` to `b`. -/
def sset (F : Nested I) (z : I → Bool) (g : ℕ) (b : Bool) : Finset I :=
  Finset.univ.filter fun ι => F.P g (flip z {ι}) = b

/-- Bits of a child input whose flip sets both predicates `g, g'` to `b`. -/
def jset (F : Nested I) (z : I → Bool) (g g' : ℕ) (b : Bool) : Finset I :=
  Finset.univ.filter fun ι => F.P g (flip z {ι}) = b ∧ F.P g' (flip z {ι}) = b

lemma mem_emb_image {W : Finset α} {φ : α → Fin k × Fin r} {U : α → Finset I} {x : α} {ι : I}
    (hx : x ∈ W) (hι : ι ∈ U x) :
    ((φ x).1, (φ x).2, ι) ∈ W.biUnion (fun x => (U x).map (emb (φ x).1 (φ x).2)) :=
  Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_map.mpr ⟨ι, hι, rfl⟩⟩

lemma card_biUnion_emb_le {W : Finset α} {φ : α → Fin k × Fin r} {U : α → Finset I} (w : α → ℕ)
    (hw : ∀ x ∈ W, (U x).card ≤ w x) :
    (W.biUnion (fun x => (U x).map (emb (φ x).1 (φ x).2))).card ≤ ∑ x ∈ W, w x :=
  (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun x hx => by rw [Finset.card_map]; exact hw x hx)

lemma card_biUnion_map_le {β : Type} [DecidableEq β] {W : Finset α} (g : α → I ↪ β) {U : α → Finset I} (w : α → ℕ)
    (hw : ∀ x ∈ W, (U x).card ≤ w x) :
    (W.biUnion (fun x => (U x).map (g x))).card ≤ ∑ x ∈ W, w x :=
  (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun x hx => by rw [Finset.card_map]; exact hw x hx)

lemma s1_bound (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D) {S0 S1 J0 J1 : ℕ} (hP : Profile F S0 S1 J0 J1)
    {q : ℕ} (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) (i0 : Fin k)
    (h0 : clause F E a q y i0) :
    (Finset.univ.filter fun b => ¬ ∃ i, clause F E a q (flip y {b}) i).card ≤ D * S0 + r * S1 := by
  set A := (Finset.univ : Finset (Fin r)).biUnion
    (fun c => (sset F (child y i0 c) F.H false).map (emb ((fun c => (i0, c)) c).1 ((fun c => (i0, c)) c).2))
  set B := (Finset.univ.filter fun j => E i0 j).biUnion
    (fun j => (sset F (child y j (a i0 j)) (F.H - q) true).map
      (emb ((fun j => (j, a i0 j)) j).1 ((fun j => (j, a i0 j)) j).2))
  have cover : (Finset.univ.filter fun b => ¬ ∃ i, clause F E a q (flip y {b}) i) ⊆ A ∪ B := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hb
    by_contra hAB
    simp only [Finset.mem_union, not_or] at hAB
    apply hb i0
    refine ⟨fun c' => ?_, fun j' hj' => ?_⟩
    · by_cases h : i0 = j ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P F.H (flip (child y i0 c') {ι})
        · exact absurd (mem_emb_image (φ := fun c => (i0, c)) (Finset.mem_univ c')
            (by simp [sset, hv])) hAB.1
        · rfl
      · rw [child_flip_ne y ι h]; exact h0.1 c'
    · by_cases h : j' = j ∧ a i0 j' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P (F.H - q) (flip (child y j' (a i0 j')) {ι})
        · rfl
        · exact absurd (mem_emb_image (φ := fun j => (j, a i0 j))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) (by simp [sset, hv])) hAB.2
      · rw [child_flip_ne y ι h]; exact h0.2 j' hj'
  have hA : A.card ≤ r * S1 := by
    refine (card_biUnion_emb_le (fun _ => S1) fun c _ => ?_).trans (by simp)
    exact hP.s1 _ _ (by omega) le_rfl (h0.1 c)
  have hB : B.card ≤ D * S0 := by
    refine (card_biUnion_emb_le (fun _ => S0) fun j hj => ?_).trans ?_
    · exact hP.s0 _ _ (by omega) (by omega) (h0.2 j (Finset.mem_filter.mp hj).2)
    · rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD i0)
  calc _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ D * S0 + r * S1 := by omega

lemma j1_bound (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D) {S0 S1 J0 J1 : ℕ} (hP : Profile F S0 S1 J0 J1)
    {q q' : ℕ} (hq : 1 ≤ q) (hqq : q < q') (hqH : q' + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) (i0 : Fin k)
    (h0' : clause F E a q' y i0) :
    (Finset.univ.filter fun b => (¬ ∃ i, clause F E a q (flip y {b}) i) ∧
      (¬ ∃ i, clause F E a q' (flip y {b}) i)).card ≤ D * J0 + r * S1 := by
  have h0 := clause_mono F E a y i0 hq hqq.le hqH h0'
  set A := (Finset.univ : Finset (Fin r)).biUnion
    (fun c => (sset F (child y i0 c) F.H false).map (emb ((fun c => (i0, c)) c).1 ((fun c => (i0, c)) c).2))
  set B := (Finset.univ.filter fun j => E i0 j).biUnion
    (fun j => (jset F (child y j (a i0 j)) (F.H - q') (F.H - q) true).map
      (emb ((fun j => (j, a i0 j)) j).1 ((fun j => (j, a i0 j)) j).2))
  have cover : (Finset.univ.filter fun b => (¬ ∃ i, clause F E a q (flip y {b}) i) ∧
      (¬ ∃ i, clause F E a q' (flip y {b}) i)) ⊆ A ∪ B := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hb
    by_contra hAB
    simp only [Finset.mem_union, not_or] at hAB
    apply hb.1 i0
    refine ⟨fun c' => ?_, fun j' hj' => ?_⟩
    · by_cases h : i0 = j ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P F.H (flip (child y i0 c') {ι})
        · exact absurd (mem_emb_image (φ := fun c => (i0, c)) (Finset.mem_univ c')
            (by simp [sset, hv])) hAB.1
        · rfl
      · rw [child_flip_ne y ι h]; exact h0.1 c'
    · by_cases h : j' = j ∧ a i0 j' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P (F.H - q) (flip (child y j' (a i0 j')) {ι})
        · rfl
        · have hv' := F.nested (F.H - q') (F.H - q) _ (by omega) (by omega) (by omega) hv
          exact absurd (mem_emb_image (φ := fun j => (j, a i0 j))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) (by simp [jset, hv, hv'])) hAB.2
      · rw [child_flip_ne y ι h]; exact h0.2 j' hj'
  have hA : A.card ≤ r * S1 := by
    refine (card_biUnion_emb_le (fun _ => S1) fun c _ => ?_).trans (by simp)
    exact hP.s1 _ _ (by omega) le_rfl (h0.1 c)
  have hB : B.card ≤ D * J0 := by
    refine (card_biUnion_emb_le (fun _ => J0) fun j hj => ?_).trans ?_
    · have hj := (Finset.mem_filter.mp hj).2
      exact hP.j0 _ _ _ (by omega) (by omega) (by omega) (h0'.2 j hj) (h0.2 j hj)
    · rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD i0)
  calc _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ D * J0 + r * S1 := by omega

/-- Twice the number of edges of a tournament inside `S` is `|S| (|S| - 1)`. -/
lemma tourn_count {E : Fin k → Fin k → Prop} (hE : Tourn E) (S : Finset (Fin k)) :
    2 * ((S ×ˢ S).filter fun p => E p.1 p.2).card = S.card * (S.card - 1) := by
  set P := (S ×ˢ S).filter fun p => E p.1 p.2
  set Q := P.image Prod.swap
  have hQ : Q.card = P.card := Finset.card_image_of_injective _ Prod.swap_injective
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]; intro p hp hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq
    exact hE.asymm _ _ (Finset.mem_filter.mp hp').2 (Finset.mem_filter.mp hp).2
  have hunion : P ∪ Q = S.offDiag := by
    ext ⟨u, v⟩
    simp only [Finset.mem_union, Finset.mem_offDiag, P, Q, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (⟨⟨hu, hv⟩, h⟩ | ⟨x, y, ⟨⟨hx, hy⟩, h⟩, rfl, rfl⟩)
      · exact ⟨hu, hv, fun e => hE.irrefl u (e ▸ h)⟩
      · exact ⟨hy, hx, fun e => hE.irrefl x (e ▸ h)⟩
    · rintro ⟨hu, hv, hne⟩
      rcases hE.total u v hne with h | h
      · exact Or.inl ⟨⟨hu, hv⟩, h⟩
      · exact Or.inr ⟨v, u, ⟨⟨hv, hu⟩, h⟩, rfl, rfl⟩
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.offDiag_card, hQ] at this
  rw [Nat.mul_sub, mul_one]; omega

/-- Clauses failing exactly one target `(i, c)` and no gate. -/
def Tset (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (q : ℕ)
    (y : Fin k × Fin r × I → Bool) : Finset (Fin k × Fin r) :=
  Finset.univ.filter fun p => F.P F.H (child y p.1 p.2) = false ∧
    (∀ c', c' ≠ p.2 → F.P F.H (child y p.1 c') = true) ∧
    ∀ j', E p.1 j' → F.P (F.H - q) (child y j' (a p.1 j')) = false

/-- Clauses failing exactly one gate `i → j` and no target. -/
def Gset (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (q : ℕ)
    (y : Fin k × Fin r × I → Bool) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun p => E p.1 p.2 ∧ (∀ c', F.P F.H (child y p.1 c') = true) ∧
    F.P (F.H - q) (child y p.2 (a p.1 p.2)) = true ∧
    ∀ j', E p.1 j' → j' ≠ p.2 → F.P (F.H - q) (child y j' (a p.1 j')) = false

lemma Tset_card_lt (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) {q t : ℕ}
    (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (ht : 1 ≤ t) (ha : NoConsistent E a t) (y : Fin k × Fin r × I → Bool) :
    (Tset F E a q y).card < t := by
  by_contra hlt; push Not at hlt
  have hne : (Tset F E a q y).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨i0, c0⟩, -⟩ := hne
  have inj : Set.InjOn Prod.fst (Tset F E a q y : Set (Fin k × Fin r)) := by
    rintro ⟨i, c⟩ hp ⟨i', c'⟩ hp' (h : i = i')
    subst h
    simp only [Finset.coe_filter, Tset, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    by_contra hcc
    have hc : c' ≠ c := fun e => hcc (by rw [e])
    rw [hp.2.1 c' hc] at hp'; exact absurd hp'.1 (by decide)
  set R := (Tset F E a q y).image Prod.fst
  have hR : R.card = (Tset F E a q y).card := Finset.card_image_of_injOn inj
  let m : Fin k → Fin r := fun j => if h : ∃ c, (j, c) ∈ Tset F E a q y then h.choose else c0
  have hm : ∀ j ∈ R, (j, m j) ∈ Tset F E a q y := by
    intro j hj
    obtain ⟨⟨j', c⟩, hc, rfl⟩ := Finset.mem_image.mp hj
    have h : ∃ c, (j', c) ∈ Tset F E a q y := ⟨c, hc⟩
    simp only [m, dif_pos h]; exact h.choose_spec
  apply ha R (by omega)
  refine ⟨m, fun i hi j hj hij => ?_⟩
  have hiT := hm i hi; have hjT := hm j hj
  simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and] at hiT hjT
  have gate := hiT.2.2 j hij
  have tgt : F.P F.H (child y j (a i j)) = false := F.false_of_false _ (by omega) (by omega) le_rfl gate
  by_contra hne
  rw [hjT.2.1 _ hne] at tgt; exact absurd tgt (by decide)

lemma Gset_injOn (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (q : ℕ)
    (y : Fin k × Fin r × I → Bool) : Set.InjOn Prod.fst (Gset F E a q y : Set (Fin k × Fin k)) := by
  rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' (h : i = i')
  subst h
  simp only [Finset.coe_filter, Gset, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
  by_contra hjj
  have hj : j' ≠ j := fun e => hjj (by rw [e])
  rw [hp.2.2.2 j' hp'.1 hj] at hp'; exact absurd hp'.2.2.1 (by decide)

/-- Inside the rows of `G`, every edge `i → j` is the unique failed gate of `i`. -/
lemma Gset_edge (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) {q : ℕ}
    (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) {i j : Fin k}
    (hi : i ∈ (Gset F E a q y).image Prod.fst) (hj : j ∈ (Gset F E a q y).image Prod.fst) (hij : E i j) :
    (i, j) ∈ Gset F E a q y := by
  obtain ⟨⟨i', ji⟩, hpi, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨⟨j', jj⟩, hpj, rfl⟩ := Finset.mem_image.mp hj
  have hpi' := hpi
  simp only [Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hpi hpj
  have fails : F.P (F.H - q) (child y j' (a i' j')) = true :=
    F.nested _ _ _ (by omega) (by omega) le_rfl (hpj.2.1 _)
  by_cases h : j' = ji
  · subst h; exact hpi'
  · rw [hpi.2.2.2 j' hij h] at fails; exact absurd fails (by decide)

lemma Gset_count (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (hE : Tourn E) {q : ℕ}
    (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) :
    2 * ((Gset F E a q y).filter fun p => p.2 ∈ (Gset F E a q y).image Prod.fst).card =
      (Gset F E a q y).card * ((Gset F E a q y).card - 1) := by
  set G := Gset F E a q y
  set R := G.image Prod.fst
  have hR : R.card = G.card := Finset.card_image_of_injOn (Gset_injOn F E a q y)
  have heq : (G.filter fun p => p.2 ∈ R) = (R ×ˢ R).filter fun p => E p.1 p.2 := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨hp, hv⟩
      exact ⟨⟨Finset.mem_image.mpr ⟨_, hp, rfl⟩, hv⟩,
        (by simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp.1)⟩
    · rintro ⟨⟨hu, hv⟩, h⟩
      exact ⟨Gset_edge F E a hq hqH y hu hv h, hv⟩
  rw [heq, tourn_count hE, hR]

lemma g_arith (m e S J : ℕ) (h2 : 2 * e = m * (m - 1)) (hem : e ≤ m) :
    e * J + (m - e) * S ≤ max (3 * J) (S + J) ∧ m ≤ 3 := by
  have hm : m ≤ 3 := by
    by_contra h; push Not at h
    have : m * 3 ≤ m * (m - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨?_, hm⟩
  interval_cases m
  · have : e = 0 := by omega
    subst this; simp <;> omega
  · have : e = 0 := by omega
    subst this; simp <;> omega
  · have : e = 1 := by omega
    subst this; simp <;> omega
  · have : e = 3 := by omega
    subst this; simp <;> omega

lemma s0_bound (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) (hE : Tourn E)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 J0 J1 : ℕ} (hP : Profile F S0 S1 J0 J1)
    {q : ℕ} (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) (hy : ∀ i, ¬ clause F E a q y i) :
    (Finset.univ.filter fun b => ∃ i, clause F E a q (flip y {b}) i).card ≤
      (t - 1) * S0 + max (3 * J1) (S1 + J1) := by
  set T := Tset F E a q y
  set G := Gset F E a q y
  set R := G.image Prod.fst
  set AT := T.biUnion (fun p => (sset F (child y p.1 p.2) F.H true).map (emb p.1 p.2))
  set AG := G.biUnion (fun p => (sset F (child y p.2 (a p.1 p.2)) (F.H - q) false).map (emb p.2 (a p.1 p.2)))
  have cover : (Finset.univ.filter fun b => ∃ i, clause F E a q (flip y {b}) i) ⊆ AT ∪ AG := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨i, hi⟩ := hb
    rcases to_true_cases F E a hE y (hy i) hi with ⟨rfl, h1, h2, h3, h4⟩ | ⟨h1, rfl, h2, h3, h4, h5⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(j, c), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h4
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3, h4⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h5
  have hT : AT.card ≤ (t - 1) * S0 := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin r => emb p.1 p.2) (fun _ => S0) fun p hp => ?_).trans ?_
    · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hP.s0 _ _ (by omega) le_rfl hp.1
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by have : T.card < t := Tset_card_lt F E a hq hqH ht ha y; omega)
  have hG : AG.card ≤ ∑ p ∈ G, (if p.2 ∈ R then J1 else S1) := by
    refine card_biUnion_map_le (fun p : Fin k × Fin k => emb p.2 (a p.1 p.2)) _ fun p hp => ?_
    have hp' := hp
    simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    split_ifs with hR
    · obtain ⟨⟨u, v⟩, hpu, huv⟩ := Finset.mem_image.mp hR
      have rowv : ∀ c', F.P F.H (child y p.2 c') = true := by
        simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hpu
        intro c'; rw [← huv]; exact hpu.2.1 c'
      refine le_trans (Finset.card_le_card fun ι hι => ?_)
        (hP.j1 (F.H - q) F.H _ (by omega) (by omega) le_rfl hp.2.2.1 (rowv _))
      simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and] at hι
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hι, F.false_of_false _ (by omega) (by omega) le_rfl hι⟩
    · exact hP.s1 _ _ (by omega) (by omega) hp.2.2.1
  have hsum : ∑ p ∈ G, (if p.2 ∈ R then J1 else S1) =
      (G.filter fun p => p.2 ∈ R).card * J1 + (G.card - (G.filter fun p => p.2 ∈ R).card) * S1 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
      Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  have harith : (G.filter fun p => p.2 ∈ R).card * J1 + (G.card - (G.filter fun p => p.2 ∈ R).card) * S1 ≤
      max (3 * J1) (S1 + J1) :=
    (g_arith G.card _ S1 J1 (Gset_count F E a hE hq hqH y) (Finset.card_le_card (Finset.filter_subset _ _))).1
  calc _ ≤ (AT ∪ AG).card := Finset.card_le_card cover
    _ ≤ AT.card + AG.card := Finset.card_union_le _ _
    _ ≤ (t - 1) * S0 + max (3 * J1) (S1 + J1) := by rw [hsum] at hG; omega

lemma j0_bound (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) (hE : Tourn E)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 J0 J1 : ℕ} (hP : Profile F S0 S1 J0 J1)
    {q q' : ℕ} (hq : 1 ≤ q) (hqq : q < q') (hqH : q' + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool)
    (hy : ∀ i, ¬ clause F E a q y i) :
    (Finset.univ.filter fun b => (∃ i, clause F E a q (flip y {b}) i) ∧
      (∃ i, clause F E a q' (flip y {b}) i)).card ≤ (t - 1) * S0 + 3 * J1 := by
  set T := Tset F E a q y
  set G := Gset F E a q y
  set AT := T.biUnion (fun p => (sset F (child y p.1 p.2) F.H true).map (emb p.1 p.2))
  set AG := G.biUnion (fun p => (jset F (child y p.2 (a p.1 p.2)) (F.H - q') (F.H - q) false).map
    (emb p.2 (a p.1 p.2)))
  have cover : (Finset.univ.filter fun b => (∃ i, clause F E a q (flip y {b}) i) ∧
      (∃ i, clause F E a q' (flip y {b}) i)) ⊆ AT ∪ AG := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨-, i, hi'⟩ := hb
    have hi := clause_mono F E a _ i hq hqq.le hqH hi'
    rcases to_true_cases F E a hE y (hy i) hi with ⟨rfl, h1, h2, h3, h4⟩ | ⟨h1, rfl, h2, h3, h4, h5⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(j, c), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h4
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3, h4⟩
      · have h6 := hi'.2 j h1
        rw [child_flip_same] at h6
        simp only [jset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h6, h5⟩
  have hT : AT.card ≤ (t - 1) * S0 := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin r => emb p.1 p.2) (fun _ => S0) fun p hp => ?_).trans ?_
    · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hP.s0 _ _ (by omega) le_rfl hp.1
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by have : T.card < t := Tset_card_lt F E a hq (by omega) ht ha y; omega)
  have hG : AG.card ≤ G.card * J1 := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin k => emb p.2 (a p.1 p.2)) (fun _ => J1) fun p hp => ?_).trans
      (by rw [Finset.sum_const, smul_eq_mul])
    simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hP.j1 _ _ _ (by omega) (by omega) (by omega)
      (F.nested _ _ _ (by omega) (by omega) (by omega) hp.2.2.1) hp.2.2.1
  have hm : G.card ≤ 3 := (g_arith G.card _ S1 J1 (Gset_count F E a hE hq (by omega) y)
    (Finset.card_le_card (Finset.filter_subset _ _))).2
  calc _ ≤ (AT ∪ AG).card := Finset.card_le_card cover
    _ ≤ AT.card + AG.card := Finset.card_union_le _ _
    _ ≤ (t - 1) * S0 + 3 * J1 := by
      have : G.card * J1 ≤ 3 * J1 := Nat.mul_le_mul_right _ hm
      omega

/-- The parent family: `H = F.H - 1`, `P q = ⋁ᵢ clause i q`. -/
def parent (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) :
    Nested (Fin k × Fin r × I) where
  H := F.H - 1
  P q y := decide (∃ i, clause F E a q y i)
  nested := by
    intro q q' y hq hqq hq' h
    simp only [decide_eq_true_eq] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact ⟨i, clause_mono F E a y i hq hqq (by omega) hi⟩

theorem step_profile (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D t : ℕ)
    (hH : 2 ≤ F.H) (hE : Tourn E) (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 J0 J1 : ℕ} (hP : Profile F S0 S1 J0 J1) :
    Profile (parent F E a) ((t - 1) * S0 + max (3 * J1) (S1 + J1)) (D * S0 + r * S1)
      ((t - 1) * S0 + 3 * J1) (D * J0 + r * S1) where
  s0 := by
    intro q y hq hqH hy
    simp only [parent, decide_eq_false_iff_not, not_exists, decide_eq_true_eq] at hy hqH ⊢
    exact s0_bound F E a t hE ht ha hP hq (by omega) y hy
  s1 := by
    intro q y hq hqH hy
    simp only [parent, decide_eq_true_eq, decide_eq_false_iff_not] at hy hqH ⊢
    obtain ⟨i0, h0⟩ := hy
    exact s1_bound F E a D hD hP hq (by omega) y i0 h0
  j0 := by
    intro q q' y hq hqq hqH hy hy'
    simp only [parent, decide_eq_false_iff_not, not_exists, decide_eq_true_eq] at hy hy' hqH ⊢
    exact j0_bound F E a t hE ht ha hP hq hqq (by omega) y hy
  j1 := by
    intro q q' y hq hqq hqH hy hy'
    simp only [parent, decide_eq_true_eq, decide_eq_false_iff_not] at hy hy' hqH ⊢
    obtain ⟨i0, h0⟩ := hy'
    exact j1_bound F E a D hD hP hq hqq (by omega) y i0 h0

theorem step_zero (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r)
    (hH : 2 ≤ F.H) (hE : Tourn E) (hr : 1 ≤ r) {N : ℕ} (hZ : ZeroBlocks F N) :
    ZeroBlocks (parent F E a) (k * N) where
  zero := by
    intro q hq hqH
    simp only [parent, decide_eq_false_iff_not, not_exists] at hqH ⊢
    intro i hi
    have := hi.1 ⟨0, hr⟩
    rw [show child (fun _ => false) i ⟨0, hr⟩ = (fun _ => false) from rfl,
      hZ.zero F.H (by omega) le_rfl] at this
    exact absurd this (by decide)
  blocks := by
    obtain ⟨B, hne, hdisj, hacc⟩ := hZ.blocks
    -- block (i, u): the copies of child block `B u` in every child of row `i`
    let blk : Fin k × Fin N → Finset (Fin k × Fin r × I) := fun p =>
      (Finset.univ : Finset (Fin r)).biUnion fun c => (B p.2).map (emb p.1 c)
    let e : Fin (k * N) ≃ Fin k × Fin N := finProdFinEquiv.symm
    refine ⟨fun u => blk (e u), fun u => ?_, fun u v huv => ?_, fun u q hq hqH => ?_⟩
    · obtain ⟨ι, hι⟩ := hne (e u).2
      exact ⟨((e u).1, ⟨0, hr⟩, ι), Finset.mem_biUnion.mpr ⟨⟨0, hr⟩, Finset.mem_univ _,
        Finset.mem_map.mpr ⟨ι, hι, rfl⟩⟩⟩
    · have hne' : e u ≠ e v := fun h => huv (e.injective h)
      rw [Finset.disjoint_left]
      rintro x h1 h2
      rw [mem_rowBlock] at h1 h2
      by_cases hp : (e u).2 = (e v).2
      · exact hne' (Prod.ext (h1.1.symm.trans h2.1) hp)
      · exact Finset.disjoint_left.mp (hdisj _ _ hp) h1.2 h2.2
    · simp only [parent, decide_eq_true_eq] at hqH ⊢
      refine ⟨(e u).1, fun c => ?_, fun j hj => ?_⟩
      · have hc : child (flip (fun _ => false) (blk (e u))) (e u).1 c = flip (fun _ => false) (B (e u).2) := by
          funext ι
          simp only [child, flip, blk, mem_rowBlock]
          simp
        rw [hc]; exact hacc _ _ (by omega) le_rfl
      · have hc : child (flip (fun _ => false) (blk (e u))) j (a (e u).1 j) = fun _ => false := by
          funext ι
          simp only [child, flip, blk, mem_rowBlock]
          have : j ≠ (e u).1 := fun h => hE.irrefl j (by rw [h] at hj ⊢; exact hj)
          simp [this]
        rw [hc]; exact hZ.zero _ (by omega) (by omega)

end BSSep

-- ===== module StepI =====

/-!
# The recursive step with index-dependent profiles

The bounds of `Step`, with each child bound taken at the index where it is charged: targets at the top child index
`Q`, gates at `Q - q`, internal gates at the pair `(Q - q, Q)`, joint gates at `(Q - q', Q - q)`.
-/

noncomputable section
open scoped Classical

set_option linter.unusedSectionVars false

namespace BSSep

variable {I : Type} [Fintype I] {k r : ℕ} {α : Type}

lemma s1_boundI (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {q : ℕ} (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) (i0 : Fin k)
    (h0 : clause F E a q y i0) :
    (Finset.univ.filter fun b => ¬ ∃ i, clause F E a q (flip y {b}) i).card ≤ D * S0 (F.H - q) + r * S1 F.H := by
  set A := (Finset.univ : Finset (Fin r)).biUnion
    (fun c => (sset F (child y i0 c) F.H false).map (emb ((fun c => (i0, c)) c).1 ((fun c => (i0, c)) c).2))
  set B := (Finset.univ.filter fun j => E i0 j).biUnion
    (fun j => (sset F (child y j (a i0 j)) (F.H - q) true).map
      (emb ((fun j => (j, a i0 j)) j).1 ((fun j => (j, a i0 j)) j).2))
  have cover : (Finset.univ.filter fun b => ¬ ∃ i, clause F E a q (flip y {b}) i) ⊆ A ∪ B := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hb
    by_contra hAB
    simp only [Finset.mem_union, not_or] at hAB
    apply hb i0
    refine ⟨fun c' => ?_, fun j' hj' => ?_⟩
    · by_cases h : i0 = j ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P F.H (flip (child y i0 c') {ι})
        · exact absurd (mem_emb_image (φ := fun c => (i0, c)) (Finset.mem_univ c')
            (by simp [sset, hv])) hAB.1
        · rfl
      · rw [child_flip_ne y ι h]; exact h0.1 c'
    · by_cases h : j' = j ∧ a i0 j' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P (F.H - q) (flip (child y j' (a i0 j')) {ι})
        · rfl
        · exact absurd (mem_emb_image (φ := fun j => (j, a i0 j))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) (by simp [sset, hv])) hAB.2
      · rw [child_flip_ne y ι h]; exact h0.2 j' hj'
  have hA : A.card ≤ r * S1 F.H := by
    refine (card_biUnion_emb_le (fun _ => S1 F.H) fun c _ => ?_).trans (by simp)
    exact hP.s1 _ _ (by omega) le_rfl (h0.1 c)
  have hB : B.card ≤ D * S0 (F.H - q) := by
    refine (card_biUnion_emb_le (fun _ => S0 (F.H - q)) fun j hj => ?_).trans ?_
    · exact hP.s0 _ _ (by omega) (by omega) (h0.2 j (Finset.mem_filter.mp hj).2)
    · rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD i0)
  calc _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ D * S0 (F.H - q) + r * S1 F.H := by omega

lemma j1_boundI (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {q q' : ℕ} (hq : 1 ≤ q) (hqq : q < q') (hqH : q' + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) (i0 : Fin k)
    (h0' : clause F E a q' y i0) :
    (Finset.univ.filter fun b => (¬ ∃ i, clause F E a q (flip y {b}) i) ∧
      (¬ ∃ i, clause F E a q' (flip y {b}) i)).card ≤ D * J0 (F.H - q') (F.H - q) + r * S1 F.H := by
  have h0 := clause_mono F E a y i0 hq hqq.le hqH h0'
  set A := (Finset.univ : Finset (Fin r)).biUnion
    (fun c => (sset F (child y i0 c) F.H false).map (emb ((fun c => (i0, c)) c).1 ((fun c => (i0, c)) c).2))
  set B := (Finset.univ.filter fun j => E i0 j).biUnion
    (fun j => (jset F (child y j (a i0 j)) (F.H - q') (F.H - q) true).map
      (emb ((fun j => (j, a i0 j)) j).1 ((fun j => (j, a i0 j)) j).2))
  have cover : (Finset.univ.filter fun b => (¬ ∃ i, clause F E a q (flip y {b}) i) ∧
      (¬ ∃ i, clause F E a q' (flip y {b}) i)) ⊆ A ∪ B := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hb
    by_contra hAB
    simp only [Finset.mem_union, not_or] at hAB
    apply hb.1 i0
    refine ⟨fun c' => ?_, fun j' hj' => ?_⟩
    · by_cases h : i0 = j ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P F.H (flip (child y i0 c') {ι})
        · exact absurd (mem_emb_image (φ := fun c => (i0, c)) (Finset.mem_univ c')
            (by simp [sset, hv])) hAB.1
        · rfl
      · rw [child_flip_ne y ι h]; exact h0.1 c'
    · by_cases h : j' = j ∧ a i0 j' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P (F.H - q) (flip (child y j' (a i0 j')) {ι})
        · rfl
        · have hv' := F.nested (F.H - q') (F.H - q) _ (by omega) (by omega) (by omega) hv
          exact absurd (mem_emb_image (φ := fun j => (j, a i0 j))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) (by simp [jset, hv, hv'])) hAB.2
      · rw [child_flip_ne y ι h]; exact h0.2 j' hj'
  have hA : A.card ≤ r * S1 F.H := by
    refine (card_biUnion_emb_le (fun _ => S1 F.H) fun c _ => ?_).trans (by simp)
    exact hP.s1 _ _ (by omega) le_rfl (h0.1 c)
  have hB : B.card ≤ D * J0 (F.H - q') (F.H - q) := by
    refine (card_biUnion_emb_le (fun _ => J0 (F.H - q') (F.H - q)) fun j hj => ?_).trans ?_
    · have hj := (Finset.mem_filter.mp hj).2
      exact hP.j0 _ _ _ (by omega) (by omega) (by omega) (h0'.2 j hj) (h0.2 j hj)
    · rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD i0)
  calc _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ D * J0 (F.H - q') (F.H - q) + r * S1 F.H := by omega

lemma s0_boundI (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) (hE : Tourn E)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {q : ℕ} (hq : 1 ≤ q) (hqH : q + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool) (hy : ∀ i, ¬ clause F E a q y i) :
    (Finset.univ.filter fun b => ∃ i, clause F E a q (flip y {b}) i).card ≤
      (t - 1) * S0 F.H + max (3 * J1 (F.H - q) F.H) (S1 (F.H - q) + J1 (F.H - q) F.H) := by
  set T := Tset F E a q y
  set G := Gset F E a q y
  set R := G.image Prod.fst
  set AT := T.biUnion (fun p => (sset F (child y p.1 p.2) F.H true).map (emb p.1 p.2))
  set AG := G.biUnion (fun p => (sset F (child y p.2 (a p.1 p.2)) (F.H - q) false).map (emb p.2 (a p.1 p.2)))
  have cover : (Finset.univ.filter fun b => ∃ i, clause F E a q (flip y {b}) i) ⊆ AT ∪ AG := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨i, hi⟩ := hb
    rcases to_true_cases F E a hE y (hy i) hi with ⟨rfl, h1, h2, h3, h4⟩ | ⟨h1, rfl, h2, h3, h4, h5⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(j, c), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h4
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3, h4⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h5
  have hT : AT.card ≤ (t - 1) * S0 F.H := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin r => emb p.1 p.2) (fun _ => S0 F.H) fun p hp => ?_).trans ?_
    · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hP.s0 _ _ (by omega) le_rfl hp.1
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by have : T.card < t := Tset_card_lt F E a hq hqH ht ha y; omega)
  have hG : AG.card ≤ ∑ p ∈ G, (if p.2 ∈ R then J1 (F.H - q) F.H else S1 (F.H - q)) := by
    refine card_biUnion_map_le (fun p : Fin k × Fin k => emb p.2 (a p.1 p.2)) _ fun p hp => ?_
    have hp' := hp
    simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    split_ifs with hR
    · obtain ⟨⟨u, v⟩, hpu, huv⟩ := Finset.mem_image.mp hR
      have rowv : ∀ c', F.P F.H (child y p.2 c') = true := by
        simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hpu
        intro c'; rw [← huv]; exact hpu.2.1 c'
      refine le_trans (Finset.card_le_card fun ι hι => ?_)
        (hP.j1 (F.H - q) F.H _ (by omega) (by omega) le_rfl hp.2.2.1 (rowv _))
      simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and] at hι
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hι, F.false_of_false _ (by omega) (by omega) le_rfl hι⟩
    · exact hP.s1 _ _ (by omega) (by omega) hp.2.2.1
  have hsum : ∑ p ∈ G, (if p.2 ∈ R then J1 (F.H - q) F.H else S1 (F.H - q)) =
      (G.filter fun p => p.2 ∈ R).card * J1 (F.H - q) F.H + (G.card - (G.filter fun p => p.2 ∈ R).card) * S1 (F.H - q) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
      Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  have harith : (G.filter fun p => p.2 ∈ R).card * J1 (F.H - q) F.H + (G.card - (G.filter fun p => p.2 ∈ R).card) * S1 (F.H - q) ≤
      max (3 * J1 (F.H - q) F.H) (S1 (F.H - q) + J1 (F.H - q) F.H) :=
    (g_arith G.card _ (S1 (F.H - q)) (J1 (F.H - q) F.H) (Gset_count F E a hE hq hqH y) (Finset.card_le_card (Finset.filter_subset _ _))).1
  calc _ ≤ (AT ∪ AG).card := Finset.card_le_card cover
    _ ≤ AT.card + AG.card := Finset.card_union_le _ _
    _ ≤ (t - 1) * S0 F.H + max (3 * J1 (F.H - q) F.H) (S1 (F.H - q) + J1 (F.H - q) F.H) := by rw [hsum] at hG; omega

lemma j0_boundI (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) (hE : Tourn E)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {q q' : ℕ} (hq : 1 ≤ q) (hqq : q < q') (hqH : q' + 1 ≤ F.H) (y : Fin k × Fin r × I → Bool)
    (hy : ∀ i, ¬ clause F E a q y i) :
    (Finset.univ.filter fun b => (∃ i, clause F E a q (flip y {b}) i) ∧
      (∃ i, clause F E a q' (flip y {b}) i)).card ≤ (t - 1) * S0 F.H + 3 * J1 (F.H - q') (F.H - q) := by
  set T := Tset F E a q y
  set G := Gset F E a q y
  set AT := T.biUnion (fun p => (sset F (child y p.1 p.2) F.H true).map (emb p.1 p.2))
  set AG := G.biUnion (fun p => (jset F (child y p.2 (a p.1 p.2)) (F.H - q') (F.H - q) false).map
    (emb p.2 (a p.1 p.2)))
  have cover : (Finset.univ.filter fun b => (∃ i, clause F E a q (flip y {b}) i) ∧
      (∃ i, clause F E a q' (flip y {b}) i)) ⊆ AT ∪ AG := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨-, i, hi'⟩ := hb
    have hi := clause_mono F E a _ i hq hqq.le hqH hi'
    rcases to_true_cases F E a hE y (hy i) hi with ⟨rfl, h1, h2, h3, h4⟩ | ⟨h1, rfl, h2, h3, h4, h5⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(j, c), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h4
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3, h4⟩
      · have h6 := hi'.2 j h1
        rw [child_flip_same] at h6
        simp only [jset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h6, h5⟩
  have hT : AT.card ≤ (t - 1) * S0 F.H := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin r => emb p.1 p.2) (fun _ => S0 F.H) fun p hp => ?_).trans ?_
    · simp only [T, Tset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hP.s0 _ _ (by omega) le_rfl hp.1
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by have : T.card < t := Tset_card_lt F E a hq (by omega) ht ha y; omega)
  have hG : AG.card ≤ G.card * J1 (F.H - q') (F.H - q) := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin k => emb p.2 (a p.1 p.2)) (fun _ => J1 (F.H - q') (F.H - q)) fun p hp => ?_).trans
      (by rw [Finset.sum_const, smul_eq_mul])
    simp only [G, Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hP.j1 _ _ _ (by omega) (by omega) (by omega)
      (F.nested _ _ _ (by omega) (by omega) (by omega) hp.2.2.1) hp.2.2.1
  have hm : G.card ≤ 3 := (g_arith G.card _ 0 0 (Gset_count F E a hE hq (by omega) y)
    (Finset.card_le_card (Finset.filter_subset _ _))).2
  calc _ ≤ (AT ∪ AG).card := Finset.card_le_card cover
    _ ≤ AT.card + AG.card := Finset.card_union_le _ _
    _ ≤ (t - 1) * S0 F.H + 3 * J1 (F.H - q') (F.H - q) := by
      have : G.card * J1 (F.H - q') (F.H - q) ≤ 3 * J1 (F.H - q') (F.H - q) := Nat.mul_le_mul_right _ hm
      omega

theorem step_iprofile (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D t : ℕ)
    (hH : 2 ≤ F.H) (hE : Tourn E) (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1) :
    IProfile (parent F E a)
      (fun q => (t - 1) * S0 F.H + max (3 * J1 (F.H - q) F.H) (S1 (F.H - q) + J1 (F.H - q) F.H))
      (fun q => D * S0 (F.H - q) + r * S1 F.H)
      (fun q q' => (t - 1) * S0 F.H + 3 * J1 (F.H - q') (F.H - q))
      (fun q q' => D * J0 (F.H - q') (F.H - q) + r * S1 F.H) where
  s0 := by
    intro q y hq hqH hy
    simp only [parent, decide_eq_false_iff_not, not_exists, decide_eq_true_eq] at hy hqH ⊢
    exact s0_boundI F E a t hE ht ha hP hq (by omega) y hy
  s1 := by
    intro q y hq hqH hy
    simp only [parent, decide_eq_true_eq, decide_eq_false_iff_not] at hy hqH ⊢
    obtain ⟨i0, h0⟩ := hy
    exact s1_boundI F E a D hD hP hq (by omega) y i0 h0
  j0 := by
    intro q q' y hq hqq hqH hy hy'
    simp only [parent, decide_eq_false_iff_not, not_exists, decide_eq_true_eq] at hy hy' hqH ⊢
    exact j0_boundI F E a t hE ht ha hP hq hqq (by omega) y hy
  j1 := by
    intro q q' y hq hqq hqH hy hy'
    simp only [parent, decide_eq_true_eq, decide_eq_false_iff_not] at hy hy' hqH ⊢
    obtain ⟨i0, h0⟩ := hy'
    exact j1_boundI F E a D hD hP hq hqq (by omega) y i0 h0

end BSSep

-- ===== module Top =====

/-!
# The top level of the separation and the finishing facts

`orTop F c` is the OR of `c` disjoint copies of the index-1 predicate of a nested family. Its sensitivity is at most
`max (c * S₀) S₁` and its block sensitivity at the all-false input is at least `c * N`. Generic facts: two disjoint
sensitive blocks force sensitivity at least 2; reindexing the input along an equivalence preserves sensitivity and
does not decrease block sensitivity; a real-exponent finishing inequality; and the packaged separation statement.
-/

noncomputable section
open scoped Classical

namespace BSSep

lemma blockSensitivityAt_le_blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool)
    (x : I → Bool) : blockSensitivityAt f x ≤ blockSensitivity f :=
  Finset.le_sup (f := blockSensitivityAt f) (Finset.mem_univ x)

section OrTop

variable {I : Type}

/-- OR of `c` disjoint copies of the index-1 predicate. -/
def orTop (F : Nested I) (c : ℕ) : ((Fin c × I) → Bool) → Bool :=
  fun z => decide (∃ u : Fin c, F.P 1 (fun i => z (u, i)) = true)

lemma orTop_true_iff (F : Nested I) (c : ℕ) (z : (Fin c × I) → Bool) :
    orTop F c z = true ↔ ∃ u : Fin c, F.P 1 (fun i => z (u, i)) = true := by
  simp [orTop]

lemma orTop_false_iff (F : Nested I) (c : ℕ) (z : (Fin c × I) → Bool) :
    orTop F c z = false ↔ ∀ u : Fin c, F.P 1 (fun i => z (u, i)) = false := by
  simp [orTop]

/-- Flipping the bit `(u, i)` changes only copy `u`. -/
lemma copy_flip {c : ℕ} (z : (Fin c × I) → Bool) (u v : Fin c) (i : I) :
    (fun i' => flip z {(u, i)} (v, i')) =
      if v = u then flip (fun i' => z (u, i')) {i} else (fun i' => z (v, i')) := by
  split_ifs with h
  · subst h; funext i'; simp [flip]
  · funext i'; simp [flip, h]

theorem orTop_sensitivity_le [Fintype I] (F : Nested I) (hH : 1 ≤ F.H) {S0 S1 J0 J1 : ℕ}
    (hP : Profile F S0 S1 J0 J1) (c : ℕ) :
    sensitivity (orTop F c) ≤ max (c * S0) S1 := by
  unfold sensitivity
  refine Finset.sup_le fun z _ => ?_
  unfold sensitivityAt
  cases hz : orTop F c z with
  | false =>
    -- every copy rejects; a sensitive bit makes its own copy accept
    have hall : ∀ u, F.P 1 (fun i => z (u, i)) = false := (orTop_false_iff F c z).1 hz
    refine le_trans ?_ (le_max_left _ _)
    calc (Finset.univ.filter fun a => orTop F c (flip z {a}) ≠ false).card
        ≤ (Finset.univ.biUnion fun u : Fin c =>
            ((Finset.univ.filter fun i => F.P 1 (flip (fun i' => z (u, i')) {i}) = true).image
              fun i => (u, i))).card := by
          apply Finset.card_le_card
          rintro ⟨u, i⟩ ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Bool.not_eq_false] at ha
          obtain ⟨v, hv⟩ := (orTop_true_iff F c _).1 ha
          rw [copy_flip] at hv
          split_ifs at hv with hvu
          · subst hvu
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_filter]
            exact ⟨v, i, hv, rfl⟩
          · rw [hall v] at hv; exact absurd hv (by simp)
      _ ≤ ∑ u : Fin c, ((Finset.univ.filter fun i =>
              F.P 1 (flip (fun i' => z (u, i')) {i}) = true).image fun i => (u, i)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _u : Fin c, S0 := by
          apply Finset.sum_le_sum; intro u _
          exact Finset.card_image_le.trans (hP.s0 1 _ le_rfl hH (hall u))
      _ = c * S0 := by simp
  | true =>
    -- some copy `u` accepts; a sensitive bit must lie in copy `u` and make it reject
    obtain ⟨u, hu⟩ := (orTop_true_iff F c z).1 hz
    refine le_trans ?_ (le_max_right _ _)
    calc (Finset.univ.filter fun a => orTop F c (flip z {a}) ≠ true).card
        ≤ ((Finset.univ.filter fun i => F.P 1 (flip (fun i' => z (u, i')) {i}) = false).image
            fun i => (u, i)).card := by
          apply Finset.card_le_card
          rintro ⟨w, i⟩ ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Bool.not_eq_true] at ha
          have hu' := (orTop_false_iff F c _).1 ha u
          rw [copy_flip] at hu'
          split_ifs at hu' with huw
          · subst huw
            exact Finset.mem_image.2 ⟨i, by simpa using hu', rfl⟩
          · rw [hu] at hu'; exact absurd hu' (by simp)
      _ ≤ S1 := Finset.card_image_le.trans (hP.s1 1 _ le_rfl hH hu)

theorem orTop_zeroBlocks [Fintype I] (F : Nested I) (hH : 1 ≤ F.H) {N : ℕ} (hZ : ZeroBlocks F N) (c : ℕ) :
    c * N ≤ blockSensitivityAt (orTop F c) (fun _ => false) := by
  obtain ⟨B, hne, hdisj, hacc⟩ := hZ.blocks
  -- the block `B v` placed in copy `u`
  let blk : Fin c × Fin N → Finset (Fin c × I) := fun p => (B p.2).image fun i => (p.1, i)
  have hmem : ∀ p w i, (w, i) ∈ blk p ↔ w = p.1 ∧ i ∈ B p.2 := by
    intro p w i
    simp only [blk, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨rfl, ha⟩
    · rintro ⟨rfl, hi⟩; exact ⟨i, hi, rfl, rfl⟩
  have hB2 : ∀ v v' i, i ∈ B v → i ∈ B v' → v = v' := by
    intro v v' i hi hi'
    by_contra hvv
    exact Finset.disjoint_left.1 (hdisj v v' hvv) hi hi'
  have hinj : Function.Injective blk := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    obtain ⟨i, hi⟩ := hne v
    have h1 : (u, i) ∈ blk (u', v') := h ▸ (hmem (u, v) u i).2 ⟨rfl, hi⟩
    obtain ⟨rfl, hi'⟩ := (hmem _ _ _).1 h1
    rw [hB2 v v' i hi hi']
  have hz0 : orTop F c (fun _ => false) = false :=
    (orTop_false_iff _ _ _).2 fun _ => hZ.zero 1 le_rfl hH
  have hflip : ∀ p, orTop F c (flip (fun _ => false) (blk p)) = true := by
    intro p
    refine (orTop_true_iff _ _ _).2 ⟨p.1, ?_⟩
    have : (fun i => flip (fun _ => false) (blk p) (p.1, i)) = flip (fun _ => false) (B p.2) := by
      funext i; simp only [flip_apply, hmem, true_and]
    rw [this]; exact hacc p.2 1 le_rfl hH
  let blocks : Finset (Finset (Fin c × I)) := Finset.univ.image blk
  have hcard : blocks.card = c * N := by
    simp [blocks, Finset.card_image_of_injective _ hinj]
  unfold blockSensitivityAt
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ blocks))
  split_ifs with hc
  · exact hcard.ge
  · exfalso; apply hc
    refine ⟨?_, ?_⟩
    · intro A hA A' hA' hAA'
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hA
      obtain ⟨p', -, rfl⟩ := Finset.mem_image.1 hA'
      refine Finset.disjoint_left.2 ?_
      rintro ⟨w, i⟩ h1 h2
      obtain ⟨rfl, hi⟩ := (hmem _ _ _).1 h1
      obtain ⟨hw, hi'⟩ := (hmem _ _ _).1 h2
      apply hAA'
      have hv := hB2 _ _ _ hi hi'
      rw [show p = p' from Prod.ext hw hv]
    · intro A hA
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hA
      refine ⟨?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne p.2
        exact ⟨(p.1, i), (hmem _ _ _).2 ⟨rfl, hi⟩⟩
      · rw [hflip p, hz0]; simp

theorem orTop_blockSensitivity [Fintype I] (F : Nested I) (hH : 1 ≤ F.H) {N : ℕ} (hZ : ZeroBlocks F N) (c : ℕ) :
    c * N ≤ blockSensitivity (orTop F c) :=
  le_trans (orTop_zeroBlocks F hH hZ c) (blockSensitivityAt_le_blockSensitivity _ _)

end OrTop

section Generic

lemma sensitivityAt_le_sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (f := sensitivityAt f) (Finset.mem_univ x)

lemma flip_flip_erase {I : Type} (x : I → Bool) (S : Finset I) (a : I) (ha : a ∈ S) :
    flip (flip x S) {a} = flip x (S.erase a) := by
  funext i
  by_cases h : i = a
  · subst h; simp [flip, ha]
  · simp [flip, h, Finset.mem_erase]

/-- A sensitive block contains a single sensitive bit, unless sensitivity is already at least 2. -/
lemma sensitive_bit_or_two {I : Type} [Fintype I] (f : (I → Bool) → Bool) (x : I → Bool) (B : Finset I)
    (hB : f (flip x B) ≠ f x) : 2 ≤ sensitivity f ∨ ∃ a ∈ B, f (flip x {a}) ≠ f x := by
  obtain ⟨S, hSmem, hSmin⟩ := Finset.exists_min_image
    (B.powerset.filter fun S => f (flip x S) ≠ f x) Finset.card ⟨B, by simp [hB]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hSmem hSmin
  obtain ⟨hSB, hS⟩ := hSmem
  -- at `flip x S` every bit of `S` is sensitive, by minimality
  have hsens : S ⊆ Finset.univ.filter fun a => f (flip (flip x S) {a}) ≠ f (flip x S) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [flip_flip_erase x S a ha]
    have : f (flip x (S.erase a)) = f x := by
      by_contra hne
      have := hSmin (S.erase a) ⟨(Finset.erase_subset a S).trans hSB, hne⟩
      have := Finset.card_erase_lt_of_mem ha
      omega
    rw [this]; exact fun h => hS h.symm
  have hcardS : S.card ≤ sensitivity f :=
    (Finset.card_le_card hsens).trans (sensitivityAt_le_sensitivity f _)
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl; exact hS (by rw [flip_empty])
  by_cases h2 : 2 ≤ S.card
  · exact Or.inl (h2.trans hcardS)
  · right
    have h1 : S.card = 1 := by have := hSne.card_pos; omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
    exact ⟨a, hSB (Finset.mem_singleton_self a), hS⟩

theorem two_le_sensitivity_of_blocks {I : Type} [Fintype I] (f : (I → Bool) → Bool) (x : I → Bool)
    (B₁ B₂ : Finset I) (hd : Disjoint B₁ B₂) (h₁ : f (flip x B₁) ≠ f x) (h₂ : f (flip x B₂) ≠ f x) :
    2 ≤ sensitivity f := by
  rcases sensitive_bit_or_two f x B₁ h₁ with h | ⟨a, ha, hfa⟩
  · exact h
  rcases sensitive_bit_or_two f x B₂ h₂ with h | ⟨b, hb, hfb⟩
  · exact h
  have hab : a ≠ b := by
    rintro rfl; exact Finset.disjoint_left.1 hd ha hb
  have hsub : ({a, b} : Finset I) ⊆ Finset.univ.filter fun i => f (flip x {i}) ≠ f x := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [hfa, hfb]
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at this
  exact this.trans (sensitivityAt_le_sensitivity f x)

/-- Block sensitivity at least 2 forces sensitivity at least 2. -/
theorem two_le_sensitivity_of_bs {I : Type} [Fintype I] (f : (I → Bool) → Bool)
    (h : 2 ≤ blockSensitivity f) : 2 ≤ sensitivity f := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (I → Bool))
    Finset.univ_nonempty (blockSensitivityAt f)
  unfold blockSensitivity at h
  rw [hx] at h
  unfold blockSensitivityAt at h
  obtain ⟨blocks, -, hb⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Finset I)))
    Finset.univ_nonempty (fun blocks : Finset (Finset I) =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0)
  rw [hb] at h
  split_ifs at h with hc
  · obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.1 (by omega : 1 < blocks.card)
    exact two_le_sensitivity_of_blocks f x A B (hc.1 A hA B hB hAB) (hc.2 A hA).2 (hc.2 B hB).2
  · omega

end Generic

section Reindex

variable {I J : Type}

lemma flip_map_comp (e : I ≃ J) (x : I → Bool) (B : Finset I) :
    flip (x ∘ e.symm) (B.map e.toEmbedding) ∘ e = flip x B := by
  funext k; simp [flip]

lemma sensitivity_le_reindex [Fintype I] [Fintype J] (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity f ≤ sensitivity (fun y : J → Bool => f (y ∘ e)) := by
  refine Finset.sup_le fun x _ => le_trans ?_ (sensitivityAt_le_sensitivity _ (x ∘ e.symm))
  unfold sensitivityAt
  have hx : x ∘ e.symm ∘ e = x := by funext k; simp
  refine le_trans (le_of_eq (Finset.card_map e.toEmbedding).symm) (Finset.card_le_card ?_)
  intro j hj
  rw [Finset.mem_map_equiv] at hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  have h1 := flip_map_comp e x {e.symm j}
  rw [Finset.map_singleton] at h1
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] at h1
  rw [h1, Function.comp_assoc, hx]
  exact hj

lemma blockSensitivity_le_reindex [Fintype I] [Fintype J] (e : I ≃ J) (f : (I → Bool) → Bool) :
    blockSensitivity f ≤ blockSensitivity (fun y : J → Bool => f (y ∘ e)) := by
  refine Finset.sup_le fun x _ => le_trans ?_
    (Finset.le_sup (f := blockSensitivityAt _) (Finset.mem_univ (x ∘ e.symm)))
  have hx : x ∘ e.symm ∘ e = x := by funext k; simp
  unfold blockSensitivityAt
  refine Finset.sup_le fun blocks _ => ?_
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (blocks.image fun B => B.map e.toEmbedding)))
  dsimp only
  split_ifs with hc'
  · rw [Finset.card_image_of_injective _ (Finset.map_injective e.toEmbedding)]
  · exfalso; apply hc'
    refine ⟨?_, ?_⟩
    · intro A' hA' B' hB' hne
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hA'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      have hAB : A ≠ B := fun h => hne (h ▸ rfl)
      exact (Finset.disjoint_map _).2 (hc.1 A hA B hB hAB)
    · intro B' hB'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      refine ⟨Finset.map_nonempty.2 (hc.2 B hB).1, ?_⟩
      rw [Function.comp_assoc, hx, flip_map_comp]
      exact (hc.2 B hB).2

theorem sensitivity_reindex [Fintype I] [Fintype J] (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (fun y : J → Bool => f (y ∘ e)) = sensitivity f := by
  refine le_antisymm ?_ (sensitivity_le_reindex e f)
  have := sensitivity_le_reindex e.symm (fun y : J → Bool => f (y ∘ e))
  have hf : (fun x : I → Bool => (fun y : J → Bool => f (y ∘ e)) (x ∘ e.symm)) = f := by
    funext x; show f _ = f x; congr 1; funext k; simp
  rwa [hf] at this

theorem blockSensitivity_reindex_ge [Fintype I] [Fintype J] (e : I ≃ J) (f : (I → Bool) → Bool) :
    blockSensitivity f ≤ blockSensitivity (fun y : J → Bool => f (y ∘ e)) :=
  blockSensitivity_le_reindex e f

end Reindex

/-- Real-exponent finishing step. -/
theorem rpow_le_of_pow_le (s A B bs p q : ℕ) (hq : 0 < q) (hs : 1 ≤ s) (hsA : s ≤ A) (hB : B ≤ bs)
    (h : A ^ p ≤ B ^ q) : (s : ℝ) ^ ((p : ℝ) / q) ≤ bs := by
  have _ := hs
  calc (s : ℝ) ^ ((p : ℝ) / q) ≤ (A : ℝ) ^ ((p : ℝ) / q) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hsA) (by positivity)
    _ = ((A : ℝ) ^ p) ^ ((q : ℝ)⁻¹) := by
        rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ ≤ ((B : ℝ) ^ q) ^ ((q : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by positivity)
    _ = B := Real.pow_rpow_inv_natCast (by positivity) hq.ne'
    _ ≤ bs := by exact_mod_cast hB

/-- The packaged separation: a nested family with profile `(S₀, S₁, J₀, J₁)` and `N` zero blocks yields a function on
`Fin n` with sensitivity above 1 and `s ^ (p / q) ≤ bs`. -/
theorem separation_of_family {I : Type} [Fintype I] (F : Nested I) (hH : 1 ≤ F.H) {S0 S1 J0 J1 N : ℕ}
    (hP : Profile F S0 S1 J0 J1) (hZ : ZeroBlocks F N) (c A p q : ℕ) (hq : 0 < q) (h2 : 2 ≤ c * N)
    (hA : max (c * S0) S1 ≤ A) (hpow : A ^ p ≤ (c * N) ^ q) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
      (sensitivity f : ℝ) ^ ((p : ℝ) / q) ≤ (blockSensitivity f : ℝ) := by
  let e := Fintype.equivFin (Fin c × I)
  refine ⟨Fintype.card (Fin c × I), fun y => orTop F c (y ∘ e), ?_⟩
  have hbs := orTop_blockSensitivity F hH hZ c
  have hs2 : 2 ≤ sensitivity (orTop F c) := two_le_sensitivity_of_bs _ (h2.trans hbs)
  have hseq := sensitivity_reindex e (orTop F c)
  have hbsg := blockSensitivity_reindex_ge e (orTop F c)
  have hsA := (orTop_sensitivity_le F hH hP c).trans hA
  refine ⟨by omega, ?_⟩
  exact rpow_le_of_pow_le _ A (c * N) _ p q hq (by omega) (by omega) (hbs.trans hbsg) hpow

end BSSep


-- ===== module Chain =====

/-!
# Iterating the recursive step

A level is a triple `(D, r, t)`: a cyclic tournament on `2D+1` rows of `r` children, with labels admitting no consistent
`t` rows. A list of levels, outermost first, over the Hamming-ball base of `M` centres and depth `d`, determines the input
type `Inp M d ps`, and `prof M d ps` is the profile bound produced by the tightened recurrence.
-/

noncomputable section
open scoped Classical

namespace BSSep

/-- The input type of the family built from the levels `ps` (outermost first). -/
def Inp (M d : ℕ) : List (ℕ × ℕ × ℕ) → Type
  | [] => Fin M × Fin (d + 2)
  | (D, r, _) :: ps => Fin (2 * D + 1) × Fin r × Inp M d ps

instance instFintypeInp (M d : ℕ) : (ps : List (ℕ × ℕ × ℕ)) → Fintype (Inp M d ps)
  | [] => inferInstanceAs (Fintype (Fin M × Fin (d + 2)))
  | (D, r, _) :: ps =>
    letI := instFintypeInp M d ps
    inferInstanceAs (Fintype (Fin (2 * D + 1) × Fin r × Inp M d ps))

/-- Profile bounds `(S₀, S₁, J₀, J₁)` given by the tightened recurrence. -/
def prof (M d : ℕ) : List (ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ
  | [] => (d + 1, M * (d + 2), 0, 0)
  | (D, r, t) :: ps =>
    let p := prof M d ps
    ((t - 1) * p.1 + max (3 * p.2.2.2) (p.2.1 + p.2.2.2), D * p.1 + r * p.2.1,
      (t - 1) * p.1 + 3 * p.2.2.2, D * p.2.2.1 + r * p.2.1)

/-- Number of disjoint zero blocks. -/
def nblocks (M : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => M
  | (D, _, _) :: ps => (2 * D + 1) * nblocks M ps

/-- A level is admissible when its label condition holds. -/
def LevelOK (x : ℕ × ℕ × ℕ) : Prop :=
  1 ≤ x.2.1 ∧ 2 ≤ x.2.2 ∧
    (2 * x.1 + 1).descFactorial x.2.2 * x.2.1 ^ x.2.2 < x.2.2.factorial * x.2.1 ^ (x.2.2.choose 2)

instance : DecidablePred LevelOK := fun _ => by unfold LevelOK; infer_instance

theorem chain (M d : ℕ) : ∀ ps : List (ℕ × ℕ × ℕ), ps.length ≤ d → (∀ x ∈ ps, LevelOK x) →
    ∃ F : Nested (Inp M d ps), F.H = d + 1 - ps.length ∧
      Profile F (prof M d ps).1 (prof M d ps).2.1 (prof M d ps).2.2.1 (prof M d ps).2.2.2 ∧
      ZeroBlocks F (nblocks M ps)
  | [], _, _ => ⟨baseFam M d, rfl, base_profile M d, base_zero M d⟩
  | (D, r, t) :: ps, hlen, hok => by
    obtain ⟨F, hH, hP, hZ⟩ := chain M d ps (by simp at hlen; omega) (fun x hx => hok x (by simp [hx]))
    have hk := hok (D, r, t) (by simp)
    simp only [LevelOK] at hk
    obtain ⟨hr, ht, hlab⟩ := hk
    obtain ⟨a, ha⟩ := labels_exist D r t hr ht hlab
    have hE : Tourn (cyc D) := ⟨cyc_irrefl D, fun _ _ h => cyc_total D h, fun _ _ h => cyc_asymm D h⟩
    have hF2 : 2 ≤ F.H := by simp at hlen; omega
    have ha' : NoConsistent (cyc D) a t := fun T hT h => ha T hT h
    refine ⟨parent F (cyc D) a, ?_, ?_, ?_⟩
    · simp only [parent, hH, List.length_cons]; omega
    · exact step_profile F (cyc D) a D t hF2 hE (fun i => by convert cyc_outdeg D i) (by omega) ha' hP
    · exact step_zero F (cyc D) a hF2 hE hr hZ

/-- The separation theorem for an admissible list of `d` levels and `c` top copies. -/
theorem separation_of_levels (M d c p q : ℕ) (ps : List (ℕ × ℕ × ℕ)) (hlen : ps.length = d)
    (hok : ∀ x ∈ ps, LevelOK x) (hq : 0 < q) (h2 : 2 ≤ c * nblocks M ps)
    (hpow : (max (c * (prof M d ps).1) (prof M d ps).2.1) ^ p ≤ (c * nblocks M ps) ^ q) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
      (sensitivity f : ℝ) ^ ((p : ℝ) / q) ≤ (blockSensitivity f : ℝ) := by
  obtain ⟨F, hH, hP, hZ⟩ := chain M d ps hlen.le hok
  exact separation_of_family F (by omega) hP hZ c _ p q hq h2 le_rfl hpow

end BSSep

-- ===== module ChainI =====

/-!
# Iterating the step with index-dependent profiles

Profile tables are lists indexed by the predicate index (entry `0` unused), so that the recurrence on a concrete list
of levels is evaluated by the kernel.
-/

noncomputable section
open scoped Classical

namespace BSSep

/-- Weakening of index-dependent bounds on the relevant index range. -/
lemma IProfile.mono {I : Type} [Fintype I] {F : Nested I} {S0 S1 S0' S1' : ℕ → ℕ} {J0 J1 J0' J1' : ℕ → ℕ → ℕ}
    (h : IProfile F S0 S1 J0 J1)
    (h0 : ∀ q, 1 ≤ q → q ≤ F.H → S0 q ≤ S0' q) (h1 : ∀ q, 1 ≤ q → q ≤ F.H → S1 q ≤ S1' q)
    (h2 : ∀ q q', 1 ≤ q → q < q' → q' ≤ F.H → J0 q q' ≤ J0' q q')
    (h3 : ∀ q q', 1 ≤ q → q < q' → q' ≤ F.H → J1 q q' ≤ J1' q q') :
    IProfile F S0' S1' J0' J1' where
  s0 q x a b c := (h.s0 q x a b c).trans (h0 q a b)
  s1 q x a b c := (h.s1 q x a b c).trans (h1 q a b)
  j0 q q' x a b c d e := (h.j0 q q' x a b c d e).trans (h2 q q' a b c)
  j1 q q' x a b c d e := (h.j1 q q' x a b c d e).trans (h3 q q' a b c)

/-- At top height one only the index-one bounds matter. -/
lemma IProfile.toProfile {I : Type} [Fintype I] {F : Nested I} {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ}
    (h : IProfile F S0 S1 J0 J1) (hH : F.H = 1) : Profile F (S0 1) (S1 1) 0 0 where
  s0 q x a b c := by obtain rfl : q = 1 := by omega
                     exact h.s0 1 x a b c
  s1 q x a b c := by obtain rfl : q = 1 := by omega
                     exact h.s1 1 x a b c
  j0 q q' x a b c := by omega
  j1 q q' x a b c := by omega

theorem base_iprofile (M d : ℕ) :
    IProfile (baseFam M d) (fun q => d + 2 - q) (fun _ => M * (d + 2)) (fun _ _ => 0) (fun _ _ => 0) where
  s0 := by
    intro q x hq _ hx
    rw [baseFam_P_false] at hx
    set S := Finset.univ.filter fun a => (baseFam M d).P q (flip x {a}) = true
    rcases S.eq_empty_or_nonempty with hS | ⟨a, ha⟩
    · rw [hS]; simp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, baseFam_P] at ha
    obtain ⟨j, hj⟩ := ha
    have hxj : hd x (z M d j) ≤ d + 1 := by
      have := hd_le_flip x (z M d j) a; omega
    have hxq : hd x (z M d j) ≤ d + 2 - q := by
      have := hd_le_flip x (z M d j) a; omega
    calc S.card ≤ (Finset.univ.filter fun i => x i ≠ z M d j i).card := by
          apply Finset.card_le_card
          intro b hb
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, baseFam_P] at hb ⊢
          obtain ⟨j', hj'⟩ := hb
          have hxj' : hd x (z M d j') ≤ d + 1 := by
            have := hd_le_flip x (z M d j') b; omega
          have hjj := centre_unique x j j' hxj hxj'
          subst hjj
          intro hagree
          have := hd_flip_agree x (z M d j) b hagree
          have := hx j
          omega
      _ = hd x (z M d j) := rfl
      _ ≤ d + 2 - q := hxq
  s1 := (base_profile M d).s1
  j0 := (base_profile M d).j0
  j1 := (base_profile M d).j1

/-- Profile tables: `S₀, S₁` and `J₀, J₁` as lists indexed by the predicate index. -/
abbrev Tab := List ℕ × List ℕ × List (List ℕ) × List (List ℕ)

def gS (L : List ℕ) (u : ℕ) : ℕ := L.getD u 0
def gJ (L : List (List ℕ)) (u v : ℕ) : ℕ := (L.getD u []).getD v 0

/-- One level of the indexed recurrence; `Q` is the child's top index. -/
def stepTab (D r t Q : ℕ) (T : Tab) : Tab :=
  ((List.range Q).map fun q => (t - 1) * gS T.1 Q + max (3 * gJ T.2.2.2 (Q - q) Q) (gS T.2.1 (Q - q) + gJ T.2.2.2 (Q - q) Q),
   (List.range Q).map fun q => D * gS T.1 (Q - q) + r * gS T.2.1 Q,
   (List.range Q).map fun q => (List.range Q).map fun q' => (t - 1) * gS T.1 Q + 3 * gJ T.2.2.2 (Q - q') (Q - q),
   (List.range Q).map fun q => (List.range Q).map fun q' => D * gJ T.2.2.1 (Q - q') (Q - q) + r * gS T.2.1 Q)

def baseTab (M d : ℕ) : Tab :=
  ((List.range (d + 2)).map fun q => d + 2 - q, (List.range (d + 2)).map fun _ => M * (d + 2),
   (List.range (d + 2)).map fun _ => (List.range (d + 2)).map fun _ => 0,
   (List.range (d + 2)).map fun _ => (List.range (d + 2)).map fun _ => 0)

def tab (M d : ℕ) : List (ℕ × ℕ × ℕ) → Tab
  | [] => baseTab M d
  | (D, r, t) :: ps => stepTab D r t (d + 1 - ps.length) (tab M d ps)

lemma gS_map_range {n u : ℕ} (f : ℕ → ℕ) (hu : u < n) : gS ((List.range n).map f) u = f u := by
  simp [gS, List.getD_eq_getElem?_getD, hu]

lemma gJ_map_range {n u v : ℕ} (f : ℕ → ℕ → ℕ) (hu : u < n) (hv : v < n) :
    gJ ((List.range n).map fun q => (List.range n).map fun q' => f q q') u v = f u v := by
  simp [gJ, List.getD_eq_getElem?_getD, hu, hv]

theorem chainI (M d : ℕ) : ∀ ps : List (ℕ × ℕ × ℕ), ps.length ≤ d → (∀ x ∈ ps, LevelOK x) →
    ∃ F : Nested (Inp M d ps), F.H = d + 1 - ps.length ∧
      IProfile F (gS (tab M d ps).1) (gS (tab M d ps).2.1) (gJ (tab M d ps).2.2.1) (gJ (tab M d ps).2.2.2) ∧
      ZeroBlocks F (nblocks M ps)
  | [], _, _ => by
    refine ⟨baseFam M d, rfl, (base_iprofile M d).mono ?_ ?_ ?_ ?_, base_zero M d⟩
    · intro q _ hq; simp only [tab, baseTab]; rw [gS_map_range _ (by simp [baseFam] at hq; omega)]
    · intro q _ hq; simp only [tab, baseTab]; rw [gS_map_range _ (by simp [baseFam] at hq; omega)]
    · intro q q' _ _ _; exact Nat.zero_le _
    · intro q q' _ _ _; exact Nat.zero_le _
  | (D, r, t) :: ps, hlen, hok => by
    obtain ⟨F, hH, hP, hZ⟩ := chainI M d ps (by simp at hlen; omega) (fun x hx => hok x (by simp [hx]))
    have hk := hok (D, r, t) (by simp)
    simp only [LevelOK] at hk
    obtain ⟨hr, ht, hlab⟩ := hk
    obtain ⟨a, ha⟩ := labels_exist D r t hr ht hlab
    have hE : Tourn (cyc D) := ⟨cyc_irrefl D, fun _ _ h => cyc_total D h, fun _ _ h => cyc_asymm D h⟩
    have hF2 : 2 ≤ F.H := by simp at hlen; omega
    have ha' : NoConsistent (cyc D) a t := fun T hT h => ha T hT h
    have hPH : (parent F (cyc D) a).H = F.H - 1 := rfl
    refine ⟨parent F (cyc D) a, ?_, ?_, step_zero F (cyc D) a hF2 hE hr hZ⟩
    · simp only [hPH, hH, List.length_cons]; omega
    · refine (step_iprofile F (cyc D) a D t hF2 hE (fun i => by convert cyc_outdeg D i) (by omega) ha' hP).mono
        ?_ ?_ ?_ ?_ <;> simp only [hPH, tab, stepTab, hH] <;> intros <;>
        first
        | (rw [gS_map_range _ (by omega)])
        | (rw [gJ_map_range _ (by omega) (by omega)])

theorem separation_of_levelsI (M d c p q : ℕ) (ps : List (ℕ × ℕ × ℕ)) (hlen : ps.length = d)
    (hok : ∀ x ∈ ps, LevelOK x) (hq : 0 < q) (h2 : 2 ≤ c * nblocks M ps)
    (hpow : (max (c * gS (tab M d ps).1 1) (gS (tab M d ps).2.1 1)) ^ p ≤ (c * nblocks M ps) ^ q) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
      (sensitivity f : ℝ) ^ ((p : ℝ) / q) ≤ (blockSensitivity f : ℝ) := by
  obtain ⟨F, hH, hP, hZ⟩ := chainI M d ps hlen.le hok
  have hH1 : F.H = 1 := by omega
  exact separation_of_family F (by omega) (hP.toProfile hH1) hZ c _ p q hq h2 le_rfl hpow

end BSSep

-- ===== module StepG =====

/-!
# The recursive step with general index maps

The parent has height `H`; at parent index `q` clause `i` asks the targets of row `i` at child index `T q` and the
gates of its out-edges at child index `g q`. For `1 ≤ q ≤ q' ≤ H` the maps satisfy `1 ≤ g q < T q ≤ F.H`,
`T q ≤ T q'` and `g q' ≤ g q`. Joint child bounds are charged at pairs of child indices that may coincide; `Jx`
extends a joint bound to the diagonal by the single-predicate bound.
-/

namespace BSSep

/-- Diagonal extension of a joint bound: `S u` on the diagonal, `J` on the ordered pair otherwise. -/
def Jx (J : ℕ → ℕ → ℕ) (S : ℕ → ℕ) (u v : ℕ) : ℕ :=
  if u = v then S u else if u < v then J u v else J v u

end BSSep

noncomputable section
open scoped Classical

set_option linter.unusedSectionVars false

namespace BSSep

variable {I : Type} [Fintype I] {k r : ℕ} {i : Fin k}

lemma IProfile.j1_le_Jx {F : Nested I} {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {u v : ℕ} (x : I → Bool) (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : u ≤ F.H) (hv' : v ≤ F.H)
    (hxu : F.P u x = true) (hxv : F.P v x = true) :
    (Finset.univ.filter fun a => F.P u (flip x {a}) = false ∧ F.P v (flip x {a}) = false).card ≤
      Jx J1 S1 u v := by
  unfold Jx
  split_ifs with h1 h2
  · subst h1
    refine le_trans (Finset.card_le_card fun a ha => ?_) (hP.s1 u x hu hu' hxu)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact ha.1
  · exact hP.j1 u v x hu h2 hv' hxu hxv
  · refine le_trans (le_of_eq ?_) (hP.j1 v u x hv (by omega) hu' hxv hxu)
    congr 1; ext a; simp [and_comm]

lemma IProfile.j0_le_Jx {F : Nested I} {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {u v : ℕ} (x : I → Bool) (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : u ≤ F.H) (hv' : v ≤ F.H)
    (hxu : F.P u x = false) (hxv : F.P v x = false) :
    (Finset.univ.filter fun a => F.P u (flip x {a}) = true ∧ F.P v (flip x {a}) = true).card ≤
      Jx J0 S0 u v := by
  unfold Jx
  split_ifs with h1 h2
  · subst h1
    refine le_trans (Finset.card_le_card fun a ha => ?_) (hP.s0 u x hu hu' hxu)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact ha.1
  · exact hP.j0 u v x hu h2 hv' hxu hxv
  · refine le_trans (le_of_eq ?_) (hP.j0 v u x hv (by omega) hu' hxv hxu)
    congr 1; ext a; simp [and_comm]

/-- Clause `i` with target index `τ` and gate index `γ`. -/
def clauseG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (τ γ : ℕ)
    (y : Fin k × Fin r × I → Bool) (i : Fin k) : Prop :=
  (∀ c, F.P τ (child y i c) = true) ∧ (∀ j, E i j → F.P γ (child y j (a i j)) = false)

/-- Weaker targets (`τ ≤ τ'`) and a larger gate index (`γ' ≤ γ`) give a weaker clause. -/
lemma clauseG_mono (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) {τ γ τ' γ' : ℕ}
    (y : Fin k × Fin r × I → Bool) (i : Fin k) (hτ : 1 ≤ τ) (hττ : τ ≤ τ') (hτ' : τ' ≤ F.H)
    (hγ' : 1 ≤ γ') (hγγ : γ' ≤ γ) (hγ : γ ≤ F.H) (h : clauseG F E a τ' γ' y i) : clauseG F E a τ γ y i :=
  ⟨fun c => F.nested τ τ' _ hτ hττ hτ' (h.1 c), fun j hj => F.false_of_false _ hγ' hγγ hγ (h.2 j hj)⟩

lemma to_true_casesG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (hE : Tourn E)
    {τ γ : ℕ} (y : Fin k × Fin r × I → Bool) (hy : ¬ clauseG F E a τ γ y i) {j : Fin k} {c : Fin r} {ι : I}
    (hi : clauseG F E a τ γ (flip y {(j, c, ι)}) i) :
    (j = i ∧ F.P τ (child y i c) = false ∧ (∀ c', c' ≠ c → F.P τ (child y i c') = true) ∧
        (∀ j', E i j' → F.P γ (child y j' (a i j')) = false) ∧
        F.P τ (flip (child y i c) {ι}) = true) ∨
    (E i j ∧ c = a i j ∧ (∀ c', F.P τ (child y i c') = true) ∧ F.P γ (child y j c) = true ∧
        (∀ j', E i j' → j' ≠ j → F.P γ (child y j' (a i j')) = false) ∧
        F.P γ (flip (child y j c) {ι}) = false) := by
  obtain ⟨hT, hG⟩ := hi
  by_cases hji : j = i
  · subst hji
    left
    have gates : ∀ j', E j j' → F.P γ (child y j' (a j j')) = false := by
      intro j' hj'
      have hne : ¬ (j' = j ∧ a j j' = c) := fun h => hE.irrefl j (h.1 ▸ hj')
      have := hG j' hj'; rwa [child_flip_ne y ι hne] at this
    have others : ∀ c', c' ≠ c → F.P τ (child y j c') = true := by
      intro c' hc'
      have := hT c'; rwa [child_flip_ne y ι (fun h => hc' h.2)] at this
    have after : F.P τ (flip (child y j c) {ι}) = true := by
      have := hT c; rwa [child_flip_same] at this
    refine ⟨rfl, ?_, others, gates, after⟩
    cases hb : F.P τ (child y j c)
    · rfl
    · exact absurd ⟨fun c' => if h : c' = c then h ▸ hb else others c' h, gates⟩ hy
  · right
    have targets : ∀ c', F.P τ (child y i c') = true := by
      intro c'
      have := hT c'; rwa [child_flip_ne y ι (fun h => hji h.1.symm)] at this
    have others : ∀ j', E i j' → j' ≠ j → F.P γ (child y j' (a i j')) = false := by
      intro j' hj' hne
      have := hG j' hj'; rwa [child_flip_ne y ι (fun h => hne h.1)] at this
    by_cases hgate : E i j ∧ c = a i j
    · obtain ⟨hEij, hc⟩ := hgate
      subst hc
      have after : F.P γ (flip (child y j (a i j)) {ι}) = false := by
        have := hG j hEij; rwa [child_flip_same] at this
      refine ⟨hEij, rfl, targets, ?_, others, after⟩
      cases hb : F.P γ (child y j (a i j))
      · exact absurd ⟨targets, fun j' hj' => if h : j' = j then h ▸ hb else others j' hj' h⟩ hy
      · rfl
    · exfalso; apply hy
      refine ⟨targets, fun j' hj' => ?_⟩
      by_cases h : j' = j
      · subst h
        have hc : ¬ (j' = j' ∧ a i j' = c) := fun h' => hgate ⟨hj', h'.2.symm⟩
        have := hG j' hj'; rwa [child_flip_ne y ι hc] at this
      · exact others j' hj' h

/-- Clauses failing exactly one target `(i, c)` and no gate. -/
def TsetG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (τ γ : ℕ)
    (y : Fin k × Fin r × I → Bool) : Finset (Fin k × Fin r) :=
  Finset.univ.filter fun p => F.P τ (child y p.1 p.2) = false ∧
    (∀ c', c' ≠ p.2 → F.P τ (child y p.1 c') = true) ∧
    ∀ j', E p.1 j' → F.P γ (child y j' (a p.1 j')) = false

/-- Clauses failing exactly one gate `i → j` and no target. -/
def GsetG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (τ γ : ℕ)
    (y : Fin k × Fin r × I → Bool) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun p => E p.1 p.2 ∧ (∀ c', F.P τ (child y p.1 c') = true) ∧
    F.P γ (child y p.2 (a p.1 p.2)) = true ∧
    ∀ j', E p.1 j' → j' ≠ p.2 → F.P γ (child y j' (a p.1 j')) = false

lemma TsetG_card_lt (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) {τ γ t : ℕ}
    (hγ : 1 ≤ γ) (hγτ : γ ≤ τ) (hτ : τ ≤ F.H) (ht : 1 ≤ t) (ha : NoConsistent E a t)
    (y : Fin k × Fin r × I → Bool) : (TsetG F E a τ γ y).card < t := by
  by_contra hlt; push Not at hlt
  have hne : (TsetG F E a τ γ y).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨i0, c0⟩, -⟩ := hne
  have inj : Set.InjOn Prod.fst (TsetG F E a τ γ y : Set (Fin k × Fin r)) := by
    rintro ⟨i, c⟩ hp ⟨i', c'⟩ hp' (h : i = i')
    subst h
    simp only [Finset.coe_filter, TsetG, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    by_contra hcc
    have hc : c' ≠ c := fun e => hcc (by rw [e])
    rw [hp.2.1 c' hc] at hp'; exact absurd hp'.1 (by decide)
  set R := (TsetG F E a τ γ y).image Prod.fst
  have hR : R.card = (TsetG F E a τ γ y).card := Finset.card_image_of_injOn inj
  let m : Fin k → Fin r := fun j => if h : ∃ c, (j, c) ∈ TsetG F E a τ γ y then h.choose else c0
  have hm : ∀ j ∈ R, (j, m j) ∈ TsetG F E a τ γ y := by
    intro j hj
    obtain ⟨⟨j', c⟩, hc, rfl⟩ := Finset.mem_image.mp hj
    have h : ∃ c, (j', c) ∈ TsetG F E a τ γ y := ⟨c, hc⟩
    simp only [m, h, ↓reduceDIte]; exact h.choose_spec
  apply ha R (by omega)
  refine ⟨m, fun i hi j hj hij => ?_⟩
  have hiT := hm i hi; have hjT := hm j hj
  simp only [TsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hiT hjT
  have gate := hiT.2.2 j hij
  have tgt : F.P τ (child y j (a i j)) = false := F.false_of_false _ hγ hγτ hτ gate
  by_contra hne
  rw [hjT.2.1 _ hne] at tgt; exact absurd tgt (by decide)

lemma GsetG_injOn (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (τ γ : ℕ)
    (y : Fin k × Fin r × I → Bool) : Set.InjOn Prod.fst (GsetG F E a τ γ y : Set (Fin k × Fin k)) := by
  rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' (h : i = i')
  subst h
  simp only [Finset.coe_filter, GsetG, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
  by_contra hjj
  have hj : j' ≠ j := fun e => hjj (by rw [e])
  rw [hp.2.2.2 j' hp'.1 hj] at hp'; exact absurd hp'.2.2.1 (by decide)

lemma GsetG_edge (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) {τ γ : ℕ}
    (hγ : 1 ≤ γ) (hγτ : γ ≤ τ) (hτ : τ ≤ F.H) (y : Fin k × Fin r × I → Bool) {i j : Fin k}
    (hi : i ∈ (GsetG F E a τ γ y).image Prod.fst) (hj : j ∈ (GsetG F E a τ γ y).image Prod.fst) (hij : E i j) :
    (i, j) ∈ GsetG F E a τ γ y := by
  obtain ⟨⟨i', ji⟩, hpi, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨⟨j', jj⟩, hpj, rfl⟩ := Finset.mem_image.mp hj
  have hpi' := hpi
  simp only [GsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hpi hpj
  have fails : F.P γ (child y j' (a i' j')) = true := F.nested _ _ _ hγ hγτ hτ (hpj.2.1 _)
  by_cases h : j' = ji
  · subst h; exact hpi'
  · rw [hpi.2.2.2 j' hij h] at fails; exact absurd fails (by decide)

lemma GsetG_count (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (hE : Tourn E)
    {τ γ : ℕ} (hγ : 1 ≤ γ) (hγτ : γ ≤ τ) (hτ : τ ≤ F.H) (y : Fin k × Fin r × I → Bool) :
    2 * ((GsetG F E a τ γ y).filter fun p => p.2 ∈ (GsetG F E a τ γ y).image Prod.fst).card =
      (GsetG F E a τ γ y).card * ((GsetG F E a τ γ y).card - 1) := by
  set G := GsetG F E a τ γ y
  set R := G.image Prod.fst
  have hR : R.card = G.card := Finset.card_image_of_injOn (GsetG_injOn F E a τ γ y)
  have heq : (G.filter fun p => p.2 ∈ R) = (R ×ˢ R).filter fun p => E p.1 p.2 := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨hp, hv⟩
      exact ⟨⟨Finset.mem_image.mpr ⟨_, hp, rfl⟩, hv⟩,
        (by simp only [G, GsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp.1)⟩
    · rintro ⟨⟨hu, hv⟩, h⟩
      exact ⟨GsetG_edge F E a hγ hγτ hτ y hu hv h, hv⟩
  rw [heq, tourn_count hE, hR]

lemma s1_boundG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ}
    (hP : IProfile F S0 S1 J0 J1) {τ γ : ℕ} (hγ : 1 ≤ γ) (hγτ : γ < τ) (hτ : τ ≤ F.H)
    (y : Fin k × Fin r × I → Bool) (i0 : Fin k) (h0 : clauseG F E a τ γ y i0) :
    (Finset.univ.filter fun b => ¬ ∃ i, clauseG F E a τ γ (flip y {b}) i).card ≤ D * S0 γ + r * S1 τ := by
  set A := (Finset.univ : Finset (Fin r)).biUnion
    (fun c => (sset F (child y i0 c) τ false).map (emb ((fun c => (i0, c)) c).1 ((fun c => (i0, c)) c).2))
  set B := (Finset.univ.filter fun j => E i0 j).biUnion
    (fun j => (sset F (child y j (a i0 j)) γ true).map
      (emb ((fun j => (j, a i0 j)) j).1 ((fun j => (j, a i0 j)) j).2))
  have cover : (Finset.univ.filter fun b => ¬ ∃ i, clauseG F E a τ γ (flip y {b}) i) ⊆ A ∪ B := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hb
    by_contra hAB
    simp only [Finset.mem_union, not_or] at hAB
    apply hb i0
    refine ⟨fun c' => ?_, fun j' hj' => ?_⟩
    · by_cases h : i0 = j ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P τ (flip (child y i0 c') {ι})
        · exact absurd (mem_emb_image (φ := fun c => (i0, c)) (Finset.mem_univ c')
            (by simp [sset, hv])) hAB.1
        · rfl
      · rw [child_flip_ne y ι h]; exact h0.1 c'
    · by_cases h : j' = j ∧ a i0 j' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P γ (flip (child y j' (a i0 j')) {ι})
        · rfl
        · exact absurd (mem_emb_image (φ := fun j => (j, a i0 j))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) (by simp [sset, hv])) hAB.2
      · rw [child_flip_ne y ι h]; exact h0.2 j' hj'
  have hA : A.card ≤ r * S1 τ := by
    refine (card_biUnion_emb_le (fun _ => S1 τ) fun c _ => ?_).trans (by simp)
    exact hP.s1 _ _ (by omega) hτ (h0.1 c)
  have hB : B.card ≤ D * S0 γ := by
    refine (card_biUnion_emb_le (fun _ => S0 γ) fun j hj => ?_).trans ?_
    · exact hP.s0 _ _ hγ (by omega) (h0.2 j (Finset.mem_filter.mp hj).2)
    · rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD i0)
  calc _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ D * S0 γ + r * S1 τ := by omega

/-- Joint `1 → 0` bound for the clause pairs `(τ, γ)` (smaller parent index) and `(τ', γ')`. -/
lemma j1_boundG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ}
    (hP : IProfile F S0 S1 J0 J1) {τ γ τ' γ' : ℕ} (hγ : 1 ≤ γ) (hγτ : γ < τ) (hτ : τ ≤ F.H)
    (hγ' : 1 ≤ γ') (hγτ' : γ' < τ') (hτ' : τ' ≤ F.H) (hττ : τ ≤ τ') (hγγ : γ' ≤ γ)
    (y : Fin k × Fin r × I → Bool) (i0 : Fin k) (h0' : clauseG F E a τ' γ' y i0) :
    (Finset.univ.filter fun b => (¬ ∃ i, clauseG F E a τ γ (flip y {b}) i) ∧
      (¬ ∃ i, clauseG F E a τ' γ' (flip y {b}) i)).card ≤ D * Jx J0 S0 γ' γ + r * Jx J1 S1 τ τ' := by
  have h0 := clauseG_mono F E a y i0 (by omega) hττ hτ' hγ' hγγ (by omega) h0'
  set A := (Finset.univ : Finset (Fin r)).biUnion
    (fun c => (jset F (child y i0 c) τ τ' false).map (emb ((fun c => (i0, c)) c).1 ((fun c => (i0, c)) c).2))
  set B := (Finset.univ.filter fun j => E i0 j).biUnion
    (fun j => (jset F (child y j (a i0 j)) γ' γ true).map
      (emb ((fun j => (j, a i0 j)) j).1 ((fun j => (j, a i0 j)) j).2))
  have cover : (Finset.univ.filter fun b => (¬ ∃ i, clauseG F E a τ γ (flip y {b}) i) ∧
      (¬ ∃ i, clauseG F E a τ' γ' (flip y {b}) i)) ⊆ A ∪ B := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hb
    by_contra hAB
    simp only [Finset.mem_union, not_or] at hAB
    apply hb.1 i0
    refine ⟨fun c' => ?_, fun j' hj' => ?_⟩
    · by_cases h : i0 = j ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P τ (flip (child y i0 c') {ι})
        · have hv' := F.false_of_false _ (by omega) hττ hτ' hv
          exact absurd (mem_emb_image (φ := fun c => (i0, c)) (Finset.mem_univ c')
            (by simp [jset, hv, hv'])) hAB.1
        · rfl
      · rw [child_flip_ne y ι h]; exact h0.1 c'
    · by_cases h : j' = j ∧ a i0 j' = c
      · obtain ⟨rfl, rfl⟩ := h
        rw [child_flip_same]
        cases hv : F.P γ (flip (child y j' (a i0 j')) {ι})
        · rfl
        · have hv' := F.nested γ' γ _ hγ' hγγ (by omega) hv
          exact absurd (mem_emb_image (φ := fun j => (j, a i0 j))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) (by simp [jset, hv, hv'])) hAB.2
      · rw [child_flip_ne y ι h]; exact h0.2 j' hj'
  have hA : A.card ≤ r * Jx J1 S1 τ τ' := by
    refine (card_biUnion_emb_le (fun _ => Jx J1 S1 τ τ') fun c _ => ?_).trans (by simp)
    exact hP.j1_le_Jx _ (by omega) (by omega) hτ hτ' (h0.1 c) (h0'.1 c)
  have hB : B.card ≤ D * Jx J0 S0 γ' γ := by
    refine (card_biUnion_emb_le (fun _ => Jx J0 S0 γ' γ) fun j hj => ?_).trans ?_
    · have hj := (Finset.mem_filter.mp hj).2
      exact hP.j0_le_Jx _ hγ' hγ (by omega) (by omega) (h0'.2 j hj) (h0.2 j hj)
    · rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD i0)
  calc _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ D * Jx J0 S0 γ' γ + r * Jx J1 S1 τ τ' := by omega

lemma s0_boundG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) (hE : Tourn E)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {τ γ : ℕ} (hγ : 1 ≤ γ) (hγτ : γ < τ) (hτ : τ ≤ F.H) (y : Fin k × Fin r × I → Bool)
    (hy : ∀ i, ¬ clauseG F E a τ γ y i) :
    (Finset.univ.filter fun b => ∃ i, clauseG F E a τ γ (flip y {b}) i).card ≤
      (t - 1) * S0 τ + max (3 * Jx J1 S1 γ τ) (S1 γ + Jx J1 S1 γ τ) := by
  set T := TsetG F E a τ γ y
  set G := GsetG F E a τ γ y
  set R := G.image Prod.fst
  set AT := T.biUnion (fun p => (sset F (child y p.1 p.2) τ true).map (emb p.1 p.2))
  set AG := G.biUnion (fun p => (sset F (child y p.2 (a p.1 p.2)) γ false).map (emb p.2 (a p.1 p.2)))
  have cover : (Finset.univ.filter fun b => ∃ i, clauseG F E a τ γ (flip y {b}) i) ⊆ AT ∪ AG := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨i, hi⟩ := hb
    rcases to_true_casesG F E a hE y (hy i) hi with ⟨rfl, h1, h2, h3, h4⟩ | ⟨h1, rfl, h2, h3, h4, h5⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(j, c), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [T, TsetG, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h4
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [G, GsetG, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3, h4⟩
      · simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h5
  have hT : AT.card ≤ (t - 1) * S0 τ := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin r => emb p.1 p.2) (fun _ => S0 τ) fun p hp => ?_).trans ?_
    · simp only [T, TsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hP.s0 _ _ (by omega) hτ hp.1
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _
        (by have : T.card < t := TsetG_card_lt F E a hγ hγτ.le hτ ht ha y; omega)
  have hG : AG.card ≤ ∑ p ∈ G, (if p.2 ∈ R then Jx J1 S1 γ τ else S1 γ) := by
    refine card_biUnion_map_le (fun p : Fin k × Fin k => emb p.2 (a p.1 p.2)) _ fun p hp => ?_
    simp only [G, GsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    split_ifs with hR
    · obtain ⟨⟨u, v⟩, hpu, huv⟩ := Finset.mem_image.mp hR
      have rowv : ∀ c', F.P τ (child y p.2 c') = true := by
        simp only [G, GsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hpu
        intro c'; rw [← huv]; exact hpu.2.1 c'
      refine le_trans (Finset.card_le_card fun ι hι => ?_)
        (hP.j1_le_Jx _ hγ (by omega) (by omega) hτ hp.2.2.1 (rowv _))
      simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and] at hι
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hι, F.false_of_false _ hγ hγτ.le hτ hι⟩
    · exact hP.s1 _ _ hγ (by omega) hp.2.2.1
  have hsum : ∑ p ∈ G, (if p.2 ∈ R then Jx J1 S1 γ τ else S1 γ) =
      (G.filter fun p => p.2 ∈ R).card * Jx J1 S1 γ τ +
        (G.card - (G.filter fun p => p.2 ∈ R).card) * S1 γ := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
      Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  have harith : (G.filter fun p => p.2 ∈ R).card * Jx J1 S1 γ τ +
      (G.card - (G.filter fun p => p.2 ∈ R).card) * S1 γ ≤
      max (3 * Jx J1 S1 γ τ) (S1 γ + Jx J1 S1 γ τ) :=
    (g_arith G.card _ (S1 γ) (Jx J1 S1 γ τ) (GsetG_count F E a hE hγ hγτ.le hτ y)
      (Finset.card_le_card (Finset.filter_subset _ _))).1
  calc _ ≤ (AT ∪ AG).card := Finset.card_le_card cover
    _ ≤ AT.card + AG.card := Finset.card_union_le _ _
    _ ≤ (t - 1) * S0 τ + max (3 * Jx J1 S1 γ τ) (S1 γ + Jx J1 S1 γ τ) := by rw [hsum] at hG; omega

/-- Joint `0 → 1` bound for the clause pairs `(τ, γ)` (smaller parent index) and `(τ', γ')`; the repairs are
classified by the clauses at `(τ', γ')`. -/
lemma j0_boundG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (t : ℕ) (hE : Tourn E)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1)
    {τ γ τ' γ' : ℕ} (hγ : 1 ≤ γ) (hγτ : γ < τ) (hτ : τ ≤ F.H)
    (hγ' : 1 ≤ γ') (hγτ' : γ' < τ') (hτ' : τ' ≤ F.H) (hττ : τ ≤ τ') (hγγ : γ' ≤ γ)
    (y : Fin k × Fin r × I → Bool) (hy : ∀ i, ¬ clauseG F E a τ γ y i) (hy' : ∀ i, ¬ clauseG F E a τ' γ' y i) :
    (Finset.univ.filter fun b => (∃ i, clauseG F E a τ γ (flip y {b}) i) ∧
      (∃ i, clauseG F E a τ' γ' (flip y {b}) i)).card ≤ (t - 1) * Jx J0 S0 τ τ' + 3 * Jx J1 S1 γ' γ := by
  set T := TsetG F E a τ' γ' y
  set G := GsetG F E a τ' γ' y
  set AT := T.biUnion (fun p => (jset F (child y p.1 p.2) τ τ' true).map (emb p.1 p.2))
  set AG := G.biUnion (fun p => (jset F (child y p.2 (a p.1 p.2)) γ' γ false).map (emb p.2 (a p.1 p.2)))
  have cover : (Finset.univ.filter fun b => (∃ i, clauseG F E a τ γ (flip y {b}) i) ∧
      (∃ i, clauseG F E a τ' γ' (flip y {b}) i)) ⊆ AT ∪ AG := by
    rintro ⟨j, c, ι⟩ hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨-, i, hi'⟩ := hb
    have hi := clauseG_mono F E a _ i (by omega) hττ hτ' hγ' hγγ (by omega) hi'
    rcases to_true_casesG F E a hE y (hy' i) hi' with ⟨rfl, h1, h2, h3, h4⟩ | ⟨h1, rfl, h2, h3, h4, h5⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(j, c), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [T, TsetG, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3⟩
      · simp only [jset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨F.nested _ _ _ (by omega) hττ hτ' h4, h4⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), ?_, Finset.mem_map.mpr ⟨ι, ?_, rfl⟩⟩)
      · simp only [G, GsetG, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2, h3, h4⟩
      · have h6 := hi.2 j h1
        rw [child_flip_same] at h6
        simp only [jset, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h5, h6⟩
  have hT : AT.card ≤ (t - 1) * Jx J0 S0 τ τ' := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin r => emb p.1 p.2) (fun _ => Jx J0 S0 τ τ')
      fun p hp => ?_).trans ?_
    · simp only [T, TsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hb : F.P τ (child y p.1 p.2) = false := by
        cases hb : F.P τ (child y p.1 p.2)
        · rfl
        · exfalso; apply hy p.1
          exact ⟨fun c' => if h : c' = p.2 then h ▸ hb else F.nested _ _ _ (by omega) hττ hτ' (hp.2.1 c' h),
            fun j' hj' => F.false_of_false _ hγ' hγγ (by omega) (hp.2.2 j' hj')⟩
      exact hP.j0_le_Jx _ (by omega) (by omega) hτ hτ' hb hp.1
    · rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _
        (by have : T.card < t := TsetG_card_lt F E a hγ' hγτ'.le hτ' ht ha y; omega)
  have hG : AG.card ≤ G.card * Jx J1 S1 γ' γ := by
    refine (card_biUnion_map_le (fun p : Fin k × Fin k => emb p.2 (a p.1 p.2)) (fun _ => Jx J1 S1 γ' γ)
      fun p hp => ?_).trans (by rw [Finset.sum_const, smul_eq_mul])
    simp only [G, GsetG, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hb : F.P γ (child y p.2 (a p.1 p.2)) = true := by
      cases hb : F.P γ (child y p.2 (a p.1 p.2))
      · exfalso; apply hy p.1
        exact ⟨fun c' => F.nested _ _ _ (by omega) hττ hτ' (hp.2.1 c'),
          fun j' hj' => if h : j' = p.2 then h ▸ hb
            else F.false_of_false _ hγ' hγγ (by omega) (hp.2.2.2 j' hj' h)⟩
      · rfl
    exact hP.j1_le_Jx _ hγ' hγ (by omega) (by omega) hp.2.2.1 hb
  have hm : G.card ≤ 3 := (g_arith G.card _ 0 0 (GsetG_count F E a hE hγ' hγτ'.le hτ' y)
    (Finset.card_le_card (Finset.filter_subset _ _))).2
  calc _ ≤ (AT ∪ AG).card := Finset.card_le_card cover
    _ ≤ AT.card + AG.card := Finset.card_union_le _ _
    _ ≤ (t - 1) * Jx J0 S0 τ τ' + 3 * Jx J1 S1 γ' γ := by
      have : G.card * Jx J1 S1 γ' γ ≤ 3 * Jx J1 S1 γ' γ := Nat.mul_le_mul_right _ hm
      omega

/-- Admissible index maps for a parent of height `H` over a child family of height `Hc`. -/
structure IdxMaps (H Hc : ℕ) (T g : ℕ → ℕ) : Prop where
  g_pos : ∀ q, 1 ≤ q → q ≤ H → 1 ≤ g q
  g_lt : ∀ q, 1 ≤ q → q ≤ H → g q < T q
  T_le : ∀ q, 1 ≤ q → q ≤ H → T q ≤ Hc
  T_mono : ∀ q q', 1 ≤ q → q ≤ q' → q' ≤ H → T q ≤ T q'
  g_anti : ∀ q q', 1 ≤ q → q ≤ q' → q' ≤ H → g q' ≤ g q

/-- The parent family with index maps `T, g`: height `H`, `P q = ⋁ᵢ clauseG i (T q) (g q)`. -/
def parentG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (H : ℕ) (T g : ℕ → ℕ)
    (hm : IdxMaps H F.H T g) : Nested (Fin k × Fin r × I) where
  H := H
  P q y := decide (∃ i, clauseG F E a (T q) (g q) y i)
  nested := by
    intro q q' y hq hqq hq' h
    simp only [decide_eq_true_eq] at h ⊢
    obtain ⟨i, hi⟩ := h
    have := hm.g_pos q hq (by omega); have := hm.g_lt q hq (by omega); have := hm.T_le q hq (by omega)
    have := hm.g_pos q' (by omega) hq'
    exact ⟨i, clauseG_mono F E a y i (by omega) (hm.T_mono q q' hq hqq hq') (hm.T_le q' (by omega) hq')
      (hm.g_pos q' (by omega) hq') (hm.g_anti q q' hq hqq hq') (by omega) hi⟩

theorem step_iprofileG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (D t H : ℕ)
    (T g : ℕ → ℕ) (hm : IdxMaps H F.H T g) (hE : Tourn E) (hD : ∀ i, (Finset.univ.filter fun j => E i j).card ≤ D)
    (ht : 1 ≤ t) (ha : NoConsistent E a t) {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ} (hP : IProfile F S0 S1 J0 J1) :
    IProfile (parentG F E a H T g hm)
      (fun q => (t - 1) * S0 (T q) + max (3 * Jx J1 S1 (g q) (T q)) (S1 (g q) + Jx J1 S1 (g q) (T q)))
      (fun q => D * S0 (g q) + r * S1 (T q))
      (fun p q => (t - 1) * Jx J0 S0 (T p) (T q) + 3 * Jx J1 S1 (g q) (g p))
      (fun p q => D * Jx J0 S0 (g q) (g p) + r * Jx J1 S1 (T p) (T q)) where
  s0 := by
    intro q y hq hqH hy
    simp only [parentG, decide_eq_false_iff_not, not_exists, decide_eq_true_eq] at hy hqH ⊢
    exact s0_boundG F E a t hE ht ha hP (hm.g_pos q hq hqH) (hm.g_lt q hq hqH) (hm.T_le q hq hqH) y hy
  s1 := by
    intro q y hq hqH hy
    simp only [parentG, decide_eq_true_eq, decide_eq_false_iff_not] at hy hqH ⊢
    obtain ⟨i0, h0⟩ := hy
    exact s1_boundG F E a D hD hP (hm.g_pos q hq hqH) (hm.g_lt q hq hqH) (hm.T_le q hq hqH) y i0 h0
  j0 := by
    intro p q y hp hpq hqH hy hy'
    simp only [parentG, decide_eq_false_iff_not, not_exists, decide_eq_true_eq] at hy hy' hqH ⊢
    exact j0_boundG F E a t hE ht ha hP (hm.g_pos p hp (by omega)) (hm.g_lt p hp (by omega))
      (hm.T_le p hp (by omega)) (hm.g_pos q (by omega) hqH) (hm.g_lt q (by omega) hqH) (hm.T_le q (by omega) hqH)
      (hm.T_mono p q hp hpq.le hqH) (hm.g_anti p q hp hpq.le hqH) y hy hy'
  j1 := by
    intro p q y hp hpq hqH hy hy'
    simp only [parentG, decide_eq_true_eq, decide_eq_false_iff_not] at hy hy' hqH ⊢
    obtain ⟨i0, h0⟩ := hy'
    exact j1_boundG F E a D hD hP (hm.g_pos p hp (by omega)) (hm.g_lt p hp (by omega))
      (hm.T_le p hp (by omega)) (hm.g_pos q (by omega) hqH) (hm.g_lt q (by omega) hqH) (hm.T_le q (by omega) hqH)
      (hm.T_mono p q hp hpq.le hqH) (hm.g_anti p q hp hpq.le hqH) y i0 h0

theorem step_zeroG (F : Nested I) (E : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin r) (H : ℕ) (T g : ℕ → ℕ)
    (hm : IdxMaps H F.H T g) (hE : Tourn E) (hr : 1 ≤ r) {N : ℕ} (hZ : ZeroBlocks F N) :
    ZeroBlocks (parentG F E a H T g hm) (k * N) where
  zero := by
    intro q hq hqH
    simp only [parentG, decide_eq_false_iff_not, not_exists] at hqH ⊢
    intro i hi
    have := hi.1 ⟨0, hr⟩
    have h1 := hm.g_pos q hq hqH; have h2 := hm.g_lt q hq hqH
    rw [show child (fun _ => false) i ⟨0, hr⟩ = (fun _ => false) from rfl,
      hZ.zero (T q) (by omega) (hm.T_le q hq hqH)] at this
    exact absurd this (by decide)
  blocks := by
    obtain ⟨B, hne, hdisj, hacc⟩ := hZ.blocks
    -- block (i, u): the copies of child block `B u` in every child of row `i`
    let blk : Fin k × Fin N → Finset (Fin k × Fin r × I) := fun p =>
      (Finset.univ : Finset (Fin r)).biUnion fun c => (B p.2).map (emb p.1 c)
    let e : Fin (k * N) ≃ Fin k × Fin N := finProdFinEquiv.symm
    refine ⟨fun u => blk (e u), fun u => ?_, fun u v huv => ?_, fun u q hq hqH => ?_⟩
    · obtain ⟨ι, hι⟩ := hne (e u).2
      exact ⟨((e u).1, ⟨0, hr⟩, ι), Finset.mem_biUnion.mpr ⟨⟨0, hr⟩, Finset.mem_univ _,
        Finset.mem_map.mpr ⟨ι, hι, rfl⟩⟩⟩
    · have hne' : e u ≠ e v := fun h => huv (e.injective h)
      rw [Finset.disjoint_left]
      rintro x h1 h2
      rw [mem_rowBlock] at h1 h2
      by_cases hp : (e u).2 = (e v).2
      · exact hne' (Prod.ext (h1.1.symm.trans h2.1) hp)
      · exact Finset.disjoint_left.mp (hdisj _ _ hp) h1.2 h2.2
    · simp only [parentG, decide_eq_true_eq] at hqH ⊢
      have h1 := hm.g_pos q hq hqH; have h2 := hm.g_lt q hq hqH; have h3 := hm.T_le q hq hqH
      refine ⟨(e u).1, fun c => ?_, fun j hj => ?_⟩
      · have hc : child (flip (fun _ => false) (blk (e u))) (e u).1 c = flip (fun _ => false) (B (e u).2) := by
          funext ι
          simp only [child, flip, blk, mem_rowBlock]
          simp
        rw [hc]; exact hacc _ _ (by omega) h3
      · have hc : child (flip (fun _ => false) (blk (e u))) j (a (e u).1 j) = fun _ => false := by
          funext ι
          simp only [child, flip, blk, mem_rowBlock]
          have : j ≠ (e u).1 := fun h => hE.irrefl j (by rw [h] at hj ⊢; exact hj)
          simp [this]
        rw [hc]; exact hZ.zero _ h1 (by omega)

end BSSep

-- ===== module ChainG =====

/-!
# Iterating the step with general index maps

A level is `(D, r, t, E)`: the cyclic tournament on `2D+1` rows of `r` children with label threshold `t`, and `E ≥ 1`
extra target indices. Heights are computed from the top: the outermost family has height `1`, and a parent of height
`H` sits over a child of height `H + E`. The maps are `g q = H + 1 - q` and `T q = H + ⌈q E / H⌉`. Profile tables are
lists indexed by the predicate index (entry `0` unused); joint entries at coinciding child indices are read from the
single-predicate list.
-/

noncomputable section
open scoped Classical

namespace BSSep

/-- The input type of the family of height `h` built from the levels `ps` (outermost first). -/
def InpG (M : ℕ) : ℕ → List (ℕ × ℕ × ℕ × ℕ) → Type
  | h, [] => Fin M × Fin (h - 1 + 2)
  | h, (D, r, _, e) :: ps => Fin (2 * D + 1) × Fin r × InpG M (h + e) ps

instance instFintypeInpG (M : ℕ) : (h : ℕ) → (ps : List (ℕ × ℕ × ℕ × ℕ)) → Fintype (InpG M h ps)
  | h, [] => inferInstanceAs (Fintype (Fin M × Fin (h - 1 + 2)))
  | h, (D, r, _, e) :: ps =>
    letI := instFintypeInpG M (h + e) ps
    inferInstanceAs (Fintype (Fin (2 * D + 1) × Fin r × InpG M (h + e) ps))

/-- Target index `H + ⌈q E / H⌉`. -/
def tgtIdx (H E q : ℕ) : ℕ := H + (q * E + H - 1) / H

/-- Gate index `H + 1 - q`. -/
def gateIdx (H q : ℕ) : ℕ := H + 1 - q

lemma idxMaps_std (H E : ℕ) (hH : 1 ≤ H) (hE : 1 ≤ E) : IdxMaps H (H + E) (tgtIdx H E) (gateIdx H) where
  g_pos q _ hq := by unfold gateIdx; omega
  g_lt q hq hqH := by
    have h1 : 1 * 1 ≤ q * E := Nat.mul_le_mul hq hE
    have h2 : 1 ≤ (q * E + H - 1) / H := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    unfold gateIdx tgtIdx; omega
  T_le q _ hqH := by
    have h1 : q * E ≤ H * E := Nat.mul_le_mul_right E hqH
    have h2 : (q * E + H - 1) / H < E + 1 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.add_mul, Nat.mul_comm E H]; omega)
    unfold tgtIdx; omega
  T_mono q q' _ hqq _ := by
    have h1 : q * E ≤ q' * E := Nat.mul_le_mul_right E hqq
    unfold tgtIdx
    exact Nat.add_le_add_left (Nat.div_le_div_right (by omega)) _
  g_anti q q' _ hqq _ := by unfold gateIdx; omega

/-- One level of the recurrence; `H` is the parent height, `E` the number of extra target indices. -/
def stepTabG (D r t H E : ℕ) (C : Tab) : Tab :=
  ((List.range (H + 1)).map fun q =>
      (t - 1) * gS C.1 (tgtIdx H E q) +
        max (3 * Jx (gJ C.2.2.2) (gS C.2.1) (gateIdx H q) (tgtIdx H E q))
          (gS C.2.1 (gateIdx H q) + Jx (gJ C.2.2.2) (gS C.2.1) (gateIdx H q) (tgtIdx H E q)),
   (List.range (H + 1)).map fun q => D * gS C.1 (gateIdx H q) + r * gS C.2.1 (tgtIdx H E q),
   (List.range (H + 1)).map fun p => (List.range (H + 1)).map fun q =>
      (t - 1) * Jx (gJ C.2.2.1) (gS C.1) (tgtIdx H E p) (tgtIdx H E q) +
        3 * Jx (gJ C.2.2.2) (gS C.2.1) (gateIdx H q) (gateIdx H p),
   (List.range (H + 1)).map fun p => (List.range (H + 1)).map fun q =>
      D * Jx (gJ C.2.2.1) (gS C.1) (gateIdx H q) (gateIdx H p) +
        r * Jx (gJ C.2.2.2) (gS C.2.1) (tgtIdx H E p) (tgtIdx H E q))

/-- Tables of the family of height `h` built from `ps`; the base is the Hamming-ball family of height `h`. -/
def tabG (M : ℕ) : ℕ → List (ℕ × ℕ × ℕ × ℕ) → Tab
  | h, [] => baseTab M (h - 1)
  | h, (D, r, t, e) :: ps => stepTabG D r t h e (tabG M (h + e) ps)

/-- Number of disjoint zero blocks. -/
def nblocksG (M : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → ℕ
  | [] => M
  | (D, _, _, _) :: ps => (2 * D + 1) * nblocksG M ps

/-- A level is admissible when its label condition holds and it adds at least one index. -/
def LevelOKG (x : ℕ × ℕ × ℕ × ℕ) : Prop := LevelOK (x.1, x.2.1, x.2.2.1) ∧ 1 ≤ x.2.2.2

instance : DecidablePred LevelOKG := fun _ => by unfold LevelOKG; infer_instance

theorem chainG (M : ℕ) : ∀ (h : ℕ) (ps : List (ℕ × ℕ × ℕ × ℕ)), 1 ≤ h → (∀ x ∈ ps, LevelOKG x) →
    ∃ F : Nested (InpG M h ps), F.H = h ∧
      IProfile F (gS (tabG M h ps).1) (gS (tabG M h ps).2.1) (gJ (tabG M h ps).2.2.1) (gJ (tabG M h ps).2.2.2) ∧
      ZeroBlocks F (nblocksG M ps)
  | h, [], hh, _ => by
    refine ⟨baseFam M (h - 1), by simp only [baseFam]; omega, (base_iprofile M (h - 1)).mono ?_ ?_ ?_ ?_,
      base_zero M (h - 1)⟩
    · intro q _ hq; simp only [tabG, baseTab]; rw [gS_map_range _ (by simp [baseFam] at hq; omega)]
    · intro q _ hq; simp only [tabG, baseTab]; rw [gS_map_range _ (by simp [baseFam] at hq; omega)]
    · intro q q' _ _ _; exact Nat.zero_le _
    · intro q q' _ _ _; exact Nat.zero_le _
  | h, (D, r, t, e) :: ps, hh, hok => by
    obtain ⟨F, hH, hP, hZ⟩ := chainG M (h + e) ps (by omega) (fun x hx => hok x (by simp [hx]))
    have hk := hok (D, r, t, e) (by simp)
    simp only [LevelOKG, LevelOK] at hk
    obtain ⟨⟨hr, ht, hlab⟩, he⟩ := hk
    obtain ⟨a, ha⟩ := labels_exist D r t hr ht hlab
    have hE : Tourn (cyc D) := ⟨cyc_irrefl D, fun _ _ h => cyc_total D h, fun _ _ h => cyc_asymm D h⟩
    have ha' : NoConsistent (cyc D) a t := fun T hT h => ha T hT h
    have hm : IdxMaps h F.H (tgtIdx h e) (gateIdx h) := by rw [hH]; exact idxMaps_std h e hh he
    refine ⟨parentG F (cyc D) a h _ _ hm, rfl, ?_, step_zeroG F (cyc D) a h _ _ hm hE hr hZ⟩
    refine (step_iprofileG F (cyc D) a D t h _ _ hm hE (fun i => by convert cyc_outdeg D i) (by omega) ha'
      hP).mono ?_ ?_ ?_ ?_ <;> simp only [parentG, tabG, stepTabG] <;> intros <;>
      first
      | (rw [gS_map_range _ (by omega)])
      | (rw [gJ_map_range _ (by omega) (by omega)])

theorem separation_of_levelsG (M c p q : ℕ) (ps : List (ℕ × ℕ × ℕ × ℕ))
    (hok : ∀ x ∈ ps, LevelOKG x) (hq : 0 < q) (h2 : 2 ≤ c * nblocksG M ps)
    (hpow : (max (c * gS (tabG M 1 ps).1 1) (gS (tabG M 1 ps).2.1 1)) ^ p ≤ (c * nblocksG M ps) ^ q) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
      (sensitivity f : ℝ) ^ ((p : ℝ) / q) ≤ (blockSensitivity f : ℝ) := by
  obtain ⟨F, hH, hP, hZ⟩ := chainG M 1 ps le_rfl hok
  exact separation_of_family F (by omega) (hP.toProfile hH) hZ c _ p q hq h2 le_rfl hpow

end BSSep

-- ===== module ChainM =====

/-!
# Iterating the step with explicitly listed index maps

A level is `(D, r, t, Hc, Tl, gl)`: the cyclic tournament on `2D+1` rows of `r` children with label threshold `t`, over
a child family of height `Hc`, with target and gate index maps read from the lists `Tl`, `gl` (entry `q` for parent
index `q`; entry `0` unused). Admissibility of the maps is a finite check decided by the kernel.
-/

noncomputable section
open scoped Classical

namespace BSSep

abbrev LvM := ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ

/-- The input type of the family of height `h` built from the levels `ps` (outermost first). -/
def InpM (M : ℕ) : ℕ → List LvM → Type
  | h, [] => Fin M × Fin (h - 1 + 2)
  | _, (D, r, _, hc, _, _) :: ps => Fin (2 * D + 1) × Fin r × InpM M hc ps

instance instFintypeInpM (M : ℕ) : (h : ℕ) → (ps : List LvM) → Fintype (InpM M h ps)
  | h, [] => inferInstanceAs (Fintype (Fin M × Fin (h - 1 + 2)))
  | _, (D, r, _, hc, _, _) :: ps =>
    letI := instFintypeInpM M hc ps
    inferInstanceAs (Fintype (Fin (2 * D + 1) × Fin r × InpM M hc ps))

/-- The listed maps satisfy the index-map conditions for parent height `h` over child height `hc`. -/
def MapsOK (h hc : ℕ) (Tl gl : List ℕ) : Prop :=
  ∀ q ∈ List.range (h + 1), ∀ q' ∈ List.range (h + 1), 1 ≤ q → q ≤ q' →
    1 ≤ gS gl q ∧ gS gl q < gS Tl q ∧ gS Tl q ≤ hc ∧ gS Tl q ≤ gS Tl q' ∧ gS gl q' ≤ gS gl q

instance (h hc : ℕ) (Tl gl : List ℕ) : Decidable (MapsOK h hc Tl gl) := by unfold MapsOK; infer_instance

lemma MapsOK.idxMaps {h hc : ℕ} {Tl gl : List ℕ} (hm : MapsOK h hc Tl gl) : IdxMaps h hc (gS Tl) (gS gl) where
  g_pos q hq hqh := (hm q (List.mem_range.mpr (by omega)) q (List.mem_range.mpr (by omega)) hq le_rfl).1
  g_lt q hq hqh := (hm q (List.mem_range.mpr (by omega)) q (List.mem_range.mpr (by omega)) hq le_rfl).2.1
  T_le q hq hqh := (hm q (List.mem_range.mpr (by omega)) q (List.mem_range.mpr (by omega)) hq le_rfl).2.2.1
  T_mono q q' hq hqq hq' :=
    (hm q (List.mem_range.mpr (by omega)) q' (List.mem_range.mpr (by omega)) hq hqq).2.2.2.1
  g_anti q q' hq hqq hq' :=
    (hm q (List.mem_range.mpr (by omega)) q' (List.mem_range.mpr (by omega)) hq hqq).2.2.2.2

/-- One level of the recurrence with listed maps; `H` is the parent height. -/
def stepTabM (D r t H : ℕ) (Tl gl : List ℕ) (C : Tab) : Tab :=
  ((List.range (H + 1)).map fun q =>
      (t - 1) * gS C.1 (gS Tl q) +
        max (3 * Jx (gJ C.2.2.2) (gS C.2.1) (gS gl q) (gS Tl q))
          (gS C.2.1 (gS gl q) + Jx (gJ C.2.2.2) (gS C.2.1) (gS gl q) (gS Tl q)),
   (List.range (H + 1)).map fun q => D * gS C.1 (gS gl q) + r * gS C.2.1 (gS Tl q),
   (List.range (H + 1)).map fun p => (List.range (H + 1)).map fun q =>
      (t - 1) * Jx (gJ C.2.2.1) (gS C.1) (gS Tl p) (gS Tl q) +
        3 * Jx (gJ C.2.2.2) (gS C.2.1) (gS gl q) (gS gl p),
   (List.range (H + 1)).map fun p => (List.range (H + 1)).map fun q =>
      D * Jx (gJ C.2.2.1) (gS C.1) (gS gl q) (gS gl p) +
        r * Jx (gJ C.2.2.2) (gS C.2.1) (gS Tl p) (gS Tl q))

/-- Tables of the family of height `h` built from `ps`; the base is the Hamming-ball family of height `h`. -/
def tabM (M : ℕ) : ℕ → List LvM → Tab
  | h, [] => baseTab M (h - 1)
  | h, (D, r, t, hc, Tl, gl) :: ps => stepTabM D r t h Tl gl (tabM M hc ps)

/-- Number of disjoint zero blocks. -/
def nblocksM (M : ℕ) : List LvM → ℕ
  | [] => M
  | (D, _, _, _, _, _) :: ps => (2 * D + 1) * nblocksM M ps

/-- Admissibility of every level, threading the heights from the top. -/
def LevelsOKM : ℕ → List LvM → Prop
  | _, [] => True
  | h, (D, r, t, hc, Tl, gl) :: ps => LevelOK (D, r, t) ∧ 1 ≤ hc ∧ MapsOK h hc Tl gl ∧ LevelsOKM hc ps

instance instDecLevelsOKM : (h : ℕ) → (ps : List LvM) → Decidable (LevelsOKM h ps)
  | _, [] => isTrue trivial
  | h, (D, r, t, hc, Tl, gl) :: ps => by
    unfold LevelsOKM
    haveI := instDecLevelsOKM hc ps
    infer_instance

theorem chainM (M : ℕ) : ∀ (h : ℕ) (ps : List LvM), 1 ≤ h → LevelsOKM h ps →
    ∃ F : Nested (InpM M h ps), F.H = h ∧
      IProfile F (gS (tabM M h ps).1) (gS (tabM M h ps).2.1) (gJ (tabM M h ps).2.2.1) (gJ (tabM M h ps).2.2.2) ∧
      ZeroBlocks F (nblocksM M ps)
  | h, [], hh, _ => by
    refine ⟨baseFam M (h - 1), by simp only [baseFam]; omega, (base_iprofile M (h - 1)).mono ?_ ?_ ?_ ?_,
      base_zero M (h - 1)⟩
    · intro q _ hq; simp only [tabM, baseTab]; rw [gS_map_range _ (by simp [baseFam] at hq; omega)]
    · intro q _ hq; simp only [tabM, baseTab]; rw [gS_map_range _ (by simp [baseFam] at hq; omega)]
    · intro q q' _ _ _; exact Nat.zero_le _
    · intro q q' _ _ _; exact Nat.zero_le _
  | h, (D, r, t, hc, Tl, gl) :: ps, hh, hok => by
    obtain ⟨hlv, hhc, hmap, hrest⟩ := hok
    obtain ⟨F, hH, hP, hZ⟩ := chainM M hc ps hhc hrest
    simp only [LevelOK] at hlv
    obtain ⟨hr, ht, hlab⟩ := hlv
    obtain ⟨a, ha⟩ := labels_exist D r t hr ht hlab
    have hE : Tourn (cyc D) := ⟨cyc_irrefl D, fun _ _ h => cyc_total D h, fun _ _ h => cyc_asymm D h⟩
    have ha' : NoConsistent (cyc D) a t := fun T hT h => ha T hT h
    have hm : IdxMaps h F.H (gS Tl) (gS gl) := by rw [hH]; exact hmap.idxMaps
    refine ⟨parentG F (cyc D) a h _ _ hm, rfl, ?_, step_zeroG F (cyc D) a h _ _ hm hE hr hZ⟩
    refine (step_iprofileG F (cyc D) a D t h _ _ hm hE (fun i => by convert cyc_outdeg D i) (by omega) ha'
      hP).mono ?_ ?_ ?_ ?_ <;> simp only [parentG, tabM, stepTabM] <;> intros <;>
      first
      | (rw [gS_map_range _ (by omega)])
      | (rw [gJ_map_range _ (by omega) (by omega)])

theorem separation_of_levelsM (M c p q : ℕ) (ps : List LvM) (hok : LevelsOKM 1 ps) (hq : 0 < q)
    (h2 : 2 ≤ c * nblocksM M ps)
    (hpow : (max (c * gS (tabM M 1 ps).1 1) (gS (tabM M 1 ps).2.1 1)) ^ p ≤ (c * nblocksM M ps) ^ q) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
      (sensitivity f : ℝ) ^ ((p : ℝ) / q) ≤ (blockSensitivity f : ℝ) := by
  obtain ⟨F, hH, hP, hZ⟩ := chainM M 1 ps le_rfl hok
  exact separation_of_family F (by omega) (hP.toProfile hH) hZ c _ p q hq h2 le_rfl hpow

end BSSep

-- ===== module ChainB =====

/-!
# Grouped bases

A nested family reindexed by a monotone class map `c` (`P'_u = P_{c u}`) is nested; its profile is the original
profile read at the classes, with joint bounds within one class replaced by the single-predicate bound. Applied to the
Hamming-ball base, consecutive base indices may share one radius: their joint sensitivity is then the ordinary one,
while fewer distinct radii make the blocks shorter.
-/

noncomputable section
open scoped Classical

namespace BSSep

/-- Reindexing by a monotone class map into `[1, F.H]`. -/
def Nested.reindex {I : Type} (F : Nested I) (h : ℕ) (c : ℕ → ℕ)
    (hc : ∀ u v, 1 ≤ u → u ≤ v → v ≤ h → 1 ≤ c u ∧ c u ≤ c v ∧ c v ≤ F.H) : Nested I where
  H := h
  P u x := F.P (c u) x
  nested u v x hu huv hv hP := F.nested (c u) (c v) x (hc u v hu huv hv).1 (hc u v hu huv hv).2.1
    (hc u v hu huv hv).2.2 hP

lemma IProfile.reindex {I : Type} [Fintype I] {F : Nested I} {S0 S1 : ℕ → ℕ} {J0 J1 : ℕ → ℕ → ℕ}
    (hP : IProfile F S0 S1 J0 J1) (h : ℕ) (c : ℕ → ℕ)
    (hc : ∀ u v, 1 ≤ u → u ≤ v → v ≤ h → 1 ≤ c u ∧ c u ≤ c v ∧ c v ≤ F.H) :
    IProfile (F.reindex h c hc) (fun u => S0 (c u)) (fun u => S1 (c u))
      (fun u v => Jx J0 S0 (c u) (c v)) (fun u v => Jx J1 S1 (c u) (c v)) where
  s0 u x hu huH hx := hP.s0 (c u) x (hc u u hu le_rfl huH).1 (hc u u hu le_rfl huH).2.2 hx
  s1 u x hu huH hx := hP.s1 (c u) x (hc u u hu le_rfl huH).1 (hc u u hu le_rfl huH).2.2 hx
  j0 u v x hu huv hvH hx hx' := by
    have h1 := hc u v hu huv.le hvH
    have h2 := hc v v (by omega) le_rfl hvH
    exact hP.j0_le_Jx x h1.1 (by omega) (h1.2.1.trans h2.2.2) h2.2.2 hx hx'
  j1 u v x hu huv hvH hx hx' := by
    have h1 := hc u v hu huv.le hvH
    have h2 := hc v v (by omega) le_rfl hvH
    exact hP.j1_le_Jx x h1.1 (by omega) (h1.2.1.trans h2.2.2) h2.2.2 hx hx'

lemma ZeroBlocks.reindex {I : Type} {F : Nested I} {N : ℕ} (hZ : ZeroBlocks F N) (h : ℕ) (c : ℕ → ℕ)
    (hc : ∀ u v, 1 ≤ u → u ≤ v → v ≤ h → 1 ≤ c u ∧ c u ≤ c v ∧ c v ≤ F.H) :
    ZeroBlocks (F.reindex h c hc) N where
  zero u hu huH := hZ.zero (c u) (hc u u hu le_rfl huH).1 (hc u u hu le_rfl huH).2.2
  blocks := by
    obtain ⟨B, hne, hdisj, hacc⟩ := hZ.blocks
    exact ⟨B, hne, hdisj, fun w u hu huH => hacc w (c u) (hc u u hu le_rfl huH).1 (hc u u hu le_rfl huH).2.2⟩

/-- The class map of a grouped base is admissible for `h0` indices over `hp` radii. -/
def ClassOK (h0 hp : ℕ) (bl : List ℕ) : Prop :=
  ∀ u ∈ List.range (h0 + 1), ∀ v ∈ List.range (h0 + 1), 1 ≤ u → u ≤ v →
    1 ≤ gS bl u ∧ gS bl u ≤ gS bl v ∧ gS bl v ≤ hp

instance (h0 hp : ℕ) (bl : List ℕ) : Decidable (ClassOK h0 hp bl) := by unfold ClassOK; infer_instance

/-- Base tables of the grouped Hamming-ball base: `hp` radii, class list `bl` over `h0` indices. -/
def gbaseTab (M hp h0 : ℕ) (bl : List ℕ) : Tab :=
  ((List.range (h0 + 1)).map fun u => hp + 1 - gS bl u, (List.range (h0 + 1)).map fun _ => M * (hp + 1),
   (List.range (h0 + 1)).map fun u => (List.range (h0 + 1)).map fun v =>
      if gS bl u = gS bl v then hp + 1 - gS bl u else 0,
   (List.range (h0 + 1)).map fun u => (List.range (h0 + 1)).map fun v =>
      if gS bl u = gS bl v then M * (hp + 1) else 0)

def tabB (M hp : ℕ) (bl : List ℕ) : ℕ → List LvM → Tab
  | h, [] => gbaseTab M hp h bl
  | h, (D, r, t, hc, Tl, gl) :: ps => stepTabM D r t h Tl gl (tabB M hp bl hc ps)

def InpB (M hp : ℕ) : ℕ → List LvM → Type
  | _, [] => Fin M × Fin (hp - 1 + 2)
  | _, (D, r, _, hc, _, _) :: ps => Fin (2 * D + 1) × Fin r × InpB M hp hc ps

instance instFintypeInpB (M hp : ℕ) : (h : ℕ) → (ps : List LvM) → Fintype (InpB M hp h ps)
  | _, [] => inferInstanceAs (Fintype (Fin M × Fin (hp - 1 + 2)))
  | _, (D, r, _, hc, _, _) :: ps =>
    letI := instFintypeInpB M hp hc ps
    inferInstanceAs (Fintype (Fin (2 * D + 1) × Fin r × InpB M hp hc ps))

/-- Height of the base family under the levels `ps` below a family of height `h`. -/
def baseHeight : ℕ → List LvM → ℕ
  | h, [] => h
  | _, (_, _, _, hc, _, _) :: ps => baseHeight hc ps

theorem chainB (M hp : ℕ) (bl : List ℕ) (hhp : 1 ≤ hp) :
    ∀ (h : ℕ) (ps : List LvM), 1 ≤ h → LevelsOKM h ps → ClassOK (baseHeight h ps) hp bl →
    ∃ F : Nested (InpB M hp h ps), F.H = h ∧
      IProfile F (gS (tabB M hp bl h ps).1) (gS (tabB M hp bl h ps).2.1) (gJ (tabB M hp bl h ps).2.2.1)
        (gJ (tabB M hp bl h ps).2.2.2) ∧
      ZeroBlocks F (nblocksM M ps)
  | h, [], hh, _, hcl => by
    have hc : ∀ u v, 1 ≤ u → u ≤ v → v ≤ h → 1 ≤ gS bl u ∧ gS bl u ≤ gS bl v ∧ gS bl v ≤ (baseFam M (hp - 1)).H := by
      intro u v hu huv hv
      have := hcl u (List.mem_range.mpr (by simp [baseHeight]; omega)) v
        (List.mem_range.mpr (by simp [baseHeight]; omega)) hu huv
      simp only [baseFam]; omega
    refine ⟨(baseFam M (hp - 1)).reindex h (gS bl) hc, rfl, ?_, (base_zero M (hp - 1)).reindex h _ hc⟩
    have e : hp - 1 + 2 = hp + 1 := by omega
    refine ((base_iprofile M (hp - 1)).reindex h (gS bl) hc).mono ?_ ?_ ?_ ?_
    · intro u _ hu; simp only [tabB, gbaseTab, Nested.reindex, e] at hu ⊢; rw [gS_map_range _ (by omega)]
    · intro u _ hu; simp only [tabB, gbaseTab, Nested.reindex, e] at hu ⊢; rw [gS_map_range _ (by omega)]
    · intro u v _ huv hv; simp only [tabB, gbaseTab, Nested.reindex, e] at hv ⊢
      rw [gJ_map_range _ (by omega) (by omega)]; unfold Jx; split_ifs <;> simp_all
    · intro u v _ huv hv; simp only [tabB, gbaseTab, Nested.reindex, e] at hv ⊢
      rw [gJ_map_range _ (by omega) (by omega)]; unfold Jx; split_ifs <;> simp_all
  | h, (D, r, t, hc, Tl, gl) :: ps, hh, hok, hcl => by
    obtain ⟨hlv, hhc, hmap, hrest⟩ := hok
    obtain ⟨F, hH, hP, hZ⟩ := chainB M hp bl hhp hc ps hhc hrest (by simpa [baseHeight] using hcl)
    simp only [LevelOK] at hlv
    obtain ⟨hr, ht, hlab⟩ := hlv
    obtain ⟨a, ha⟩ := labels_exist D r t hr ht hlab
    have hE : Tourn (cyc D) := ⟨cyc_irrefl D, fun _ _ h => cyc_total D h, fun _ _ h => cyc_asymm D h⟩
    have ha' : NoConsistent (cyc D) a t := fun T hT h => ha T hT h
    have hm : IdxMaps h F.H (gS Tl) (gS gl) := by rw [hH]; exact hmap.idxMaps
    refine ⟨parentG F (cyc D) a h _ _ hm, rfl, ?_, step_zeroG F (cyc D) a h _ _ hm hE hr hZ⟩
    refine (step_iprofileG F (cyc D) a D t h _ _ hm hE (fun i => by convert cyc_outdeg D i) (by omega) ha'
      hP).mono ?_ ?_ ?_ ?_ <;> simp only [parentG, tabB, stepTabM] <;> intros <;>
      first
      | (rw [gS_map_range _ (by omega)])
      | (rw [gJ_map_range _ (by omega) (by omega)])

theorem separation_of_levelsB (M hp c p q : ℕ) (bl : List ℕ) (ps : List LvM) (hhp : 1 ≤ hp)
    (hok : LevelsOKM 1 ps) (hcl : ClassOK (baseHeight 1 ps) hp bl) (hq : 0 < q)
    (h2 : 2 ≤ c * nblocksM M ps)
    (hpow : (max (c * gS (tabB M hp bl 1 ps).1 1) (gS (tabB M hp bl 1 ps).2.1 1)) ^ p ≤ (c * nblocksM M ps) ^ q) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
      (sensitivity f : ℝ) ^ ((p : ℝ) / q) ≤ (blockSensitivity f : ℝ) := by
  obtain ⟨F, hH, hP, hZ⟩ := chainB M hp bl hhp 1 ps le_rfl hok hcl
  exact separation_of_family F (by omega) (hP.toProfile hH) hZ c _ p q hq h2 le_rfl hpow

end BSSep

-- ===== module B24 =====

/-!
# A concrete separation with exponent 2.0391 (listed index maps)

24 levels `(D, r, t, Hc, T, g)` outermost first (rows `2D+1`, row width
`r`, label threshold `t`, child height `Hc`, target and gate index maps), base of `M = 4192155` centres, top OR of `c = 7424`
copies. Level and map admissibility and the power inequality `A^20391 ≤ B^10000` are decided by the kernel.
-/

namespace BSSep

def levelsB24 : List LvM := [
    (17071446, 2, 45, 2, [0, 2], [0, 1]),
    (12740655, 2, 44, 3, [0, 3, 3], [0, 2, 1]),
    (12740001, 2, 44, 5, [0, 5, 5, 5], [0, 4, 2, 1]),
    (12753727, 2, 44, 6, [0, 6, 6, 6, 6, 6], [0, 5, 4, 1, 1, 1]),
    (26583429, 2, 46, 7, [0, 7, 7, 7, 7, 7, 7], [0, 6, 5, 3, 3, 2, 2]),
    (42010527, 3, 32, 9, [0, 8, 8, 8, 8, 8, 8, 9], [0, 7, 7, 5, 4, 2, 1, 1]),
    (5171963, 3, 28, 11, [0, 10, 10, 11, 11, 11, 11, 11, 11, 11], [0, 9, 7, 5, 3, 3, 3, 1, 1, 1]),
    (11145699, 5, 22, 13, [0, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13], [0, 11, 11, 9, 9, 8, 7, 7, 6, 3, 3, 1]),
    (13094117, 3, 30, 15, [0, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15], [0, 13, 11, 11, 11, 7, 7, 6, 5, 5, 3, 3, 3, 1]),
    (35472939, 5, 23, 17, [0, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17], [0, 15, 14, 13, 12, 12, 11, 9, 8, 7, 7, 7, 6, 2, 2, 1]),
    (41179728, 3, 32, 19, [0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19], [0, 17, 16, 16, 15, 14, 14, 13, 12, 11, 10, 7, 6, 4, 3, 2, 2, 1]),
    (63298507, 7, 20, 21, [0, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21], [0, 19, 17, 16, 16, 16, 14, 14, 14, 14, 12, 12, 11, 7, 7, 6, 4, 3, 3, 2]),
    (80112788, 2, 49, 23, [0, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23], [0, 21, 21, 19, 18, 16, 16, 15, 13, 12, 12, 12, 12, 12, 8, 5, 5, 4, 4, 3, 3, 1]),
    (304707459, 4, 29, 25, [0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25], [0, 23, 22, 21, 20, 19, 17, 17, 15, 15, 15, 14, 13, 13, 10, 9, 8, 6, 6, 4, 3, 2, 2, 1]),
    (497089920, 2, 54, 27, [0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27], [0, 25, 24, 23, 22, 20, 19, 19, 18, 18, 16, 16, 16, 16, 14, 10, 10, 8, 8, 7, 6, 5, 5, 2, 2, 1]),
    (1530711088, 4, 31, 29, [0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29], [0, 27, 25, 24, 23, 23, 22, 21, 21, 21, 19, 16, 16, 16, 15, 15, 13, 13, 12, 9, 9, 7, 6, 5, 3, 2, 2, 1]),
    (3055026909, 2, 59, 31, [0, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31], [0, 29, 28, 27, 26, 24, 23, 22, 22, 22, 18, 18, 18, 18, 17, 15, 13, 12, 12, 11, 8, 8, 7, 6, 5, 4, 3, 2, 2, 1]),
    (9374835018, 3, 41, 33, [0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33], [0, 31, 30, 30, 28, 27, 26, 25, 24, 23, 23, 22, 22, 22, 21, 20, 16, 14, 13, 13, 11, 11, 10, 9, 7, 7, 7, 5, 4, 2, 2, 1]),
    (25995548084, 2, 65, 35, [0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35], [0, 33, 32, 31, 30, 29, 28, 28, 27, 26, 25, 24, 22, 22, 21, 17, 16, 16, 15, 15, 14, 14, 14, 10, 8, 7, 6, 5, 5, 5, 4, 2, 2, 1]),
    (79339313764, 3, 45, 37, [0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37], [0, 35, 34, 33, 33, 32, 31, 30, 29, 29, 26, 24, 22, 22, 22, 22, 21, 19, 16, 16, 16, 15, 14, 14, 12, 11, 9, 9, 9, 8, 7, 5, 4, 3, 3, 1]),
    (229953268261, 2, 71, 39, [0, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39], [0, 37, 36, 35, 34, 33, 32, 32, 30, 29, 27, 27, 26, 26, 24, 23, 22, 21, 20, 19, 19, 13, 13, 13, 13, 13, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3, 3, 1]),
    (341023017836, 3, 48, 41, [0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41], [0, 39, 38, 38, 37, 36, 35, 34, 33, 32, 32, 30, 29, 28, 26, 25, 23, 22, 22, 22, 19, 18, 18, 17, 17, 16, 15, 14, 14, 12, 11, 10, 9, 9, 7, 6, 4, 3, 3, 1]),
    (134189057921613, 2, 89, 43, [0, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43], [0, 40, 39, 38, 38, 34, 34, 32, 32, 31, 30, 29, 28, 27, 26, 25, 25, 23, 22, 21, 20, 19, 19, 18, 18, 14, 14, 11, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3, 2, 2, 1]),
    (115863029753359, 3, 58, 44, [0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44], [0, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 32, 31, 31, 31, 31, 31, 31, 30, 30, 30, 29, 29, 29, 28, 28, 27, 26, 25, 24, 23, 22, 21, 20, 20, 19, 19, 19, 18, 17, 16, 15, 14, 12])]

def classesB24 : List ℕ := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 10, 10, 10, 10, 11, 11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 20]


theorem levelsB24_ok : LevelsOKM 1 levelsB24 := by decide +kernel

theorem powB24_ok :
    (max (7424 * gS (tabB 4192155 20 classesB24 1 levelsB24).1 1) (gS (tabB 4192155 20 classesB24 1 levelsB24).2.1 1)) ^ 20391 ≤
      (7424 * nblocksM 4192155 levelsB24) ^ 10000 := by decide +kernel

theorem separationB24 : ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), 1 < sensitivity f ∧
    (sensitivity f : ℝ) ^ (2.0391 : ℝ) ≤ (blockSensitivity f : ℝ) := by
  obtain ⟨n, f, h1, h2⟩ := separation_of_levelsB 4192155 20 7424 20391 10000 classesB24 levelsB24 (by norm_num) levelsB24_ok (by decide +kernel) (by norm_num)
    (by decide +kernel) powB24_ok
  refine ⟨n, f, h1, ?_⟩
  have : (((20391 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) = (2.0391 : ℝ) := by norm_num
  rwa [this] at h2

end BSSep

-- ===== module Cert =====

/-!
# The finite certificate in the campaign's form

A function on `Fin n → Bool`, the all-false input, integers `A, B > 1` with `s(f) ≤ A`, `B ≤ bs(f, 0)` and
`A ^ 2.0391 ≤ B` (as reals), for the construction of `B24`.
-/

noncomputable section
open scoped Classical

namespace BSSep

variable {I J : Type}

lemma blockSensitivityAt_le_reindex [Fintype I] [Fintype J] (e : I ≃ J) (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt f x ≤ blockSensitivityAt (fun y : J → Bool => f (y ∘ e)) (x ∘ e.symm) := by
  have hx : x ∘ e.symm ∘ e = x := by funext k; simp
  unfold blockSensitivityAt
  refine Finset.sup_le fun blocks _ => ?_
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (blocks.image fun B => B.map e.toEmbedding)))
  dsimp only
  split_ifs with hc'
  · rw [Finset.card_image_of_injective _ (Finset.map_injective e.toEmbedding)]
  · exfalso; apply hc'
    refine ⟨?_, ?_⟩
    · intro A' hA' B' hB' hne
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hA'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      have hAB : A ≠ B := fun h => hne (h ▸ rfl)
      exact (Finset.disjoint_map _).2 (hc.1 A hA B hB hAB)
    · intro B' hB'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      refine ⟨Finset.map_nonempty.2 (hc.2 B hB).1, ?_⟩
      rw [Function.comp_assoc, hx, flip_map_comp]
      exact (hc.2 B hB).2

/-- A nested family with its top profile and zero blocks gives a function on `Fin n` with `s ≤ max (c S₀) S₁` and
`c N ≤ bs` at the all-false input. -/
theorem certificate_of_family [Fintype I] (F : Nested I) (hH : 1 ≤ F.H) {S0 S1 J0 J1 N : ℕ}
    (hP : Profile F S0 S1 J0 J1) (hZ : ZeroBlocks F N) (c : ℕ) :
    ∃ (n : ℕ) (g : (Fin n → Bool) → Bool), sensitivity g ≤ max (c * S0) S1 ∧
      c * N ≤ blockSensitivityAt g (fun _ => false) := by
  let e := Fintype.equivFin (Fin c × I)
  refine ⟨Fintype.card (Fin c × I), fun y => orTop F c (y ∘ e), ?_, ?_⟩
  · rw [sensitivity_reindex e (orTop F c)]; exact orTop_sensitivity_le F hH hP c
  · exact (orTop_zeroBlocks F hH hZ c).trans (blockSensitivityAt_le_reindex e (orTop F c) (fun _ => false))

theorem certificate_of_levelsB (M hp c : ℕ) (bl : List ℕ) (ps : List LvM) (hhp : 1 ≤ hp)
    (hok : LevelsOKM 1 ps) (hcl : ClassOK (baseHeight 1 ps) hp bl) :
    ∃ (n : ℕ) (g : (Fin n → Bool) → Bool),
      sensitivity g ≤ max (c * gS (tabB M hp bl 1 ps).1 1) (gS (tabB M hp bl 1 ps).2.1 1) ∧
      c * nblocksM M ps ≤ blockSensitivityAt g (fun _ => false) := by
  obtain ⟨F, hH, hP, hZ⟩ := chainB M hp bl hhp 1 ps le_rfl hok hcl
  exact certificate_of_family F (by omega) (hP.toProfile hH) hZ c

lemma real_rpow_le_of_pow_le (A B p q : ℕ) (hq : 0 < q) (hA : 1 ≤ A) (h : A ^ p ≤ B ^ q) :
    (A : ℝ) ^ ((p : ℝ) / q) ≤ B :=
  rpow_le_of_pow_le A A B B p q hq hA le_rfl le_rfl h

end BSSep

-- ===== the campaign goal =====
/-- The construction of `B24`: `s(f) ≤ A`, `B ≤ bs(f, 0)` with `A ^ 20391 ≤ B ^ 10000`, hence `A ^ 2.0391 ≤ B`. -/
theorem solution : SensitivityCampaign.AchievesExponent (2.0391 : ℝ) := by
  obtain ⟨n, g, hs, hb⟩ := BSSep.certificate_of_levelsB 4192155 20 7424 BSSep.classesB24 BSSep.levelsB24
    (by norm_num) BSSep.levelsB24_ok (by decide +kernel)
  have hpow := BSSep.real_rpow_le_of_pow_le
    (max (7424 * BSSep.gS (BSSep.tabB 4192155 20 BSSep.classesB24 1 BSSep.levelsB24).1 1)
      (BSSep.gS (BSSep.tabB 4192155 20 BSSep.classesB24 1 BSSep.levelsB24).2.1 1))
    (7424 * BSSep.nblocksM 4192155 BSSep.levelsB24) 20391 10000 (by norm_num) (by decide +kernel)
    BSSep.powB24_ok
  have h2 : ((20391 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) = (2.0391 : ℝ) := by norm_num
  rw [h2] at hpow
  exact SensitivityCampaign.finite_certificate g (fun _ => false) _ _ (2.0391 : ℝ)
    (by decide +kernel) (by decide +kernel) (by norm_num) hs hb hpow
