-- Prove2me | solution 1 for PlanarQueue.Genus.eulerGenusLE_component
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T14:20:18.879229+00:00
-- url     : https://prove2.me/submissions/d1e730c9-a739-4557-91dc-34af281eaeb3

import Mathlib
import Definitions.Def_PlanarQueue_Genus_EulerGenus

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

/-! eulerGenusLE_component (child of 2de08a18): restrict a scheme to a connected component;
Euler genus is additive over components, each component has Euler genus `≥ 0`. -/

namespace PQComp

open Equiv Equiv.Perm SimpleGraph PlanarQueue.Genus PQL21

section restrict

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem card_cc_one (hconn : G.Connected) : Nat.card G.ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  obtain ⟨v⟩ := hconn.nonempty
  refine ⟨G.connectedComponentMk v, fun c => ?_⟩
  refine c.ind (fun w => ?_)
  exact SimpleGraph.ConnectedComponent.eq.mpr (hconn.preconnected w v)

/-- Euler's inequality for a connected scheme -/
theorem eg_nonneg_conn (S : EmbeddingScheme G) (hconn : G.Connected) : 0 ≤ S.eulerGenus := by
  by_cases h2 : 2 ≤ Fintype.card V
  · obtain ⟨T, hTG, hTt⟩ := hconn.exists_isTree_le
    obtain ⟨r⟩ := hconn.nonempty
    obtain ⟨TD, L, p, I, hsub⟩ := ginv_along S T hTG hTt.connected r
    have htd := td_eq_tree S T hTG hTt I hsub
    have hTD : ∀ d ∈ TD, d.symm ∈ TD := fun d hd => (htd _).2 ((htd d).1 hd).symm
    obtain ⟨E, hE, hEs, _, hstop⟩ := deletion_exists S TD hTD
    have hnorb := one_face S hconn h2 T hTt I htd E hE hEs hstop
    have hgb := genus_bound S hconn h2 I E hE hEs hnorb
    have : (0 : ℤ) ≤ E.card := by positivity
    linarith
  · have h1 : Fintype.card V = 1 := by
      have := Fintype.card_pos_iff.mpr hconn.nonempty
      omega
    have hss : ∀ u v : V, u = v := fun u v =>
      Fintype.card_le_one_iff.mp h1.le u v
    have hnoadj : ∀ u v : V, ¬ G.Adj u v := fun u v h => G.ne_of_adj h (hss u v)
    haveI : IsEmpty G.Dart := ⟨fun d => hnoadj _ _ d.adj⟩
    have hm : G.edgeFinset.card = 0 := by
      have := G.dart_card_eq_twice_card_edges
      rw [Fintype.card_eq_zero] at this
      omega
    have hfo : Nat.card S.FaceOrbit = 0 := by
      rw [card_faceOrbit]
      unfold norb
      haveI : IsEmpty (Quotient (SameCycle.setoid (SigP S * AP S))) :=
        ⟨fun q => Quotient.inductionOn q (fun x => isEmptyElim x.1)⟩
      exact Nat.card_of_isEmpty
    have hiso : (Finset.univ.filter (fun v => G.degree v = 0)).card = 1 := by
      rw [Finset.filter_true_of_mem, Finset.card_univ, h1]
      intro v _
      by_contra h
      obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero h)
      exact hnoadj _ _ hw
    unfold EmbeddingScheme.eulerGenus EmbeddingScheme.faces
    rw [card_cc_one hconn, hm, hfo, hiso, h1]
    norm_num

/-- the number of face orbits is even (mirror pairing) -/
theorem norb_even (S : EmbeddingScheme G) : Even (norb (SigP S * AP S)) := by
  classical
  set Φ := SigP S * AP S with hΦ
  have hAA : ∀ y, apFun S (apFun S y) = y := apFun_invol S
  have hinvol : Function.Involutive (fun x => apFun S (nuF x)) := by
    intro x
    show apFun S (nuF (apFun S (nuF x))) = x
    rw [apFun_nu, hAA, nuF_nuF]
  let μ : Perm (G.Dart × Bool) := hinvol.toPerm
  have hμa : ∀ y, μ y = apFun S (nuF y) := fun _ => rfl
  have hΦa : ∀ y, Φ y = SigP S (apFun S y) := fun _ => rfl
  have hμμ : ∀ x, μ (μ x) = x := fun x => hinvol x
  have hconj : ∀ x, μ (Φ (μ x)) = Φ⁻¹ x := by
    intro x
    rw [eq_comm, Perm.inv_eq_iff_eq]
    simp only [hΦa, hμa, hAA]
    exact (SigP_nu S x).symm
  have hfp : ∀ x, μ x ≠ x := fun x h => x.1.symm_ne (congrArg Prod.fst h)
  have hfp2 : ∀ x, μ (Φ x) ≠ x := by
    intro x h
    have h3 : nuF (SigP S (apFun S x)) = apFun S x := by
      have := congrArg (apFun S) h
      rwa [hμa, hΦa, hAA] at this
    have h4 := congrArg Prod.snd h3
    simp [nuF, SigP_apply] at h4
  have hnsc : ∀ x, ¬ SameCycle Φ x (μ x) := mirror_not_sc Φ μ hμμ hconj hfp hfp2
  have hresp : ∀ x y, SameCycle Φ x y → SameCycle Φ (μ x) (μ y) := by
    intro x y h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hm := mirror_pow Φ μ hμμ hconj x n
    rw [hn] at hm
    rw [hm]
    exact sameCycle_inv.mp (sc_of_nat n (by rw [inv_pow]))
  let s := SameCycle.setoid Φ
  let f : Quotient s → Quotient s := Quotient.map μ (fun a b h => hresp a b h)
  have hf : Function.Involutive f := by
    intro q
    induction q using Quotient.ind with
    | _ x =>
      show Quotient.mk s (μ (μ x)) = Quotient.mk s x
      rw [hμμ]
  let F : Perm (Quotient s) := hf.toPerm
  have hF2 : F ^ 2 = 1 := by
    ext q
    rw [pow_two, Perm.mul_apply]
    exact hf q
  have hsupp : F.support = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro q
    rw [Perm.mem_support]
    induction q using Quotient.ind with
    | _ x =>
      intro h
      have h' : Quotient.mk s (μ x) = Quotient.mk s x := h
      exact hnsc x (Quotient.exact h').symm
  have h2 := Perm.two_dvd_card_support hF2
  rw [hsupp, Finset.card_univ] at h2
  unfold norb
  rw [Nat.card_eq_fintype_card]
  exact even_iff_two_dvd.mpr (by convert h2)

/-! ### restriction to an adjacency-closed vertex set -/

def dIn (A : Set V) (d : (G.induce A).Dart) : G.Dart := ⟨(d.fst.1, d.snd.1), d.adj⟩

def dOut (A : Set V) (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (d : G.Dart) (h : d.fst ∈ A) :
    (G.induce A).Dart := ⟨(⟨d.fst, h⟩, ⟨d.snd, hA _ _ d.adj h⟩), d.adj⟩

theorem dIn_dOut (A : Set V) (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (d : G.Dart)
    (h : d.fst ∈ A) : dIn A (dOut A hA d h) = d := rfl

theorem dIn_inj (A : Set V) : Function.Injective (dIn (G := G) A) := by
  intro d d' h
  have h1 : d.fst.1 = d'.fst.1 := congrArg (fun e : G.Dart => e.fst) h
  have h2 : d.snd.1 = d'.snd.1 := congrArg (fun e : G.Dart => e.snd) h
  exact SimpleGraph.Dart.ext _ _ (Prod.ext (Subtype.ext h1) (Subtype.ext h2))

theorem SigP_fst' (S : EmbeddingScheme G) (q : G.Dart × Bool) :
    (SigP S q).1.fst = q.1.fst := by
  rw [SigP_apply]
  split_ifs
  · exact rot_inv_fst S _
  · exact S.rot_fst _

def rotR (A : Set V) (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G) :
    Perm (G.induce A).Dart where
  toFun d := dOut A hA (S.rot (dIn A d)) (by rw [S.rot_fst]; exact d.fst.2)
  invFun d := dOut A hA (S.rot.symm (dIn A d)) (by rw [rot_symm_fst S]; exact d.fst.2)
  left_inv d := dIn_inj A (by simp only [dIn_dOut, Equiv.symm_apply_apply])
  right_inv d := dIn_inj A (by simp only [dIn_dOut, Equiv.apply_symm_apply])

theorem dIn_rotR (A : Set V) (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G)
    (d : (G.induce A).Dart) : dIn A (rotR A hA S d) = S.rot (dIn A d) := rfl

theorem dIn_rotR_inv (A : Set V) (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G)
    (d : (G.induce A).Dart) : dIn A ((rotR A hA S)⁻¹ d) = S.rot⁻¹ (dIn A d) := rfl

theorem dIn_rotR_pow (A : Set V) (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G)
    (d : (G.induce A).Dart) (n : ℕ) : dIn A ((rotR A hA S ^ n) d) = (S.rot ^ n) (dIn A d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, dIn_rotR, ih, pow_succ', Perm.mul_apply]

variable (A : Set V) [Fintype A] [DecidableRel (G.induce A).Adj]

/-- the restriction of a scheme to an adjacency-closed vertex set -/
def restrict (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G) :
    EmbeddingScheme (G.induce A) where
  rot := rotR A hA S
  rot_fst d := Subtype.ext (S.rot_fst (dIn A d))
  rot_cyclic d d' h := by
    obtain ⟨n, hn⟩ := S.rot_cyclic (dIn A d) (dIn A d') (congrArg Subtype.val h)
    exact ⟨n, dIn_inj A (by rw [dIn_rotR_pow]; exact hn)⟩
  sig d := S.sig (dIn A d)
  sig_symm d := S.sig_symm (dIn A d)

def iota (y : (G.induce A).Dart × Bool) : G.Dart × Bool := (dIn A y.1, y.2)

theorem iota_inj : Function.Injective (iota (G := G) A) := fun y y' h =>
  Prod.ext (dIn_inj A (congrArg (fun z : G.Dart × Bool => z.1) h))
    (congrArg (fun z : G.Dart × Bool => z.2) h)

theorem phi_iota (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G)
    (y : (G.induce A).Dart × Bool) :
    (SigP S * AP S) (iota A y) =
      iota A ((SigP (restrict A hA S) * AP (restrict A hA S)) y) := by
  rcases y with ⟨d, b⟩
  have key : ∀ c : Bool, (if c = true then S.rot⁻¹ (dIn A d.symm) else S.rot (dIn A d.symm)) =
      dIn A (if c = true then (restrict A hA S).rot⁻¹ d.symm else (restrict A hA S).rot d.symm) := by
    intro c; cases c <;> rfl
  rw [Perm.mul_apply, Perm.mul_apply, AP_apply, AP_apply, SigP_apply, SigP_apply]
  exact Prod.ext (key _) rfl

theorem phi_iota_pow (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G)
    (y : (G.induce A).Dart × Bool) (n : ℕ) :
    ((SigP S * AP S) ^ n) (iota A y) =
      iota A (((SigP (restrict A hA S) * AP (restrict A hA S)) ^ n) y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, phi_iota A hA S, pow_succ']; rfl

theorem sc_iota (hA : ∀ u v, G.Adj u v → u ∈ A → v ∈ A) (S : EmbeddingScheme G)
    (y y' : (G.induce A).Dart × Bool) :
    SameCycle (SigP (restrict A hA S) * AP (restrict A hA S)) y y' ↔
      SameCycle (SigP S * AP S) (iota A y) (iota A y') := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact sc_of_nat n (by rw [phi_iota_pow A hA, hn])
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [phi_iota_pow A hA] at hn
    exact sc_of_nat n (iota_inj A hn)

end restrict

/-! ### components -/

section comp

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem closedD (D : G.ConnectedComponent) : ∀ u v, G.Adj u v → u ∈ D.supp → v ∈ D.supp := by
  intro u v h hu
  rw [ConnectedComponent.mem_supp_iff] at hu ⊢
  rw [← hu]
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj h).symm

theorem card_fib {X : Type} [Finite X] (κ : X → G.ConnectedComponent) :
    Nat.card X = ∑ D, Nat.card {x // κ x = D} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv κ), Nat.card_sigma]

def kap (x : G.Dart × Bool) : G.ConnectedComponent := G.connectedComponentMk x.1.fst

theorem kap_phi (S : EmbeddingScheme G) (x : G.Dart × Bool) : kap ((SigP S * AP S) x) = kap x := by
  unfold kap
  rw [Perm.mul_apply, SigP_fst', AP_apply]
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj x.1.adj).symm

theorem kap_pow (S : EmbeddingScheme G) (x : G.Dart × Bool) (n : ℕ) :
    kap (((SigP S * AP S) ^ n) x) = kap x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, kap_phi, ih]

theorem kap_sc (S : EmbeddingScheme G) {x y : G.Dart × Bool}
    (h : SameCycle (SigP S * AP S) x y) : kap x = kap y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, kap_pow]

def kapQ (S : EmbeddingScheme G) : Quotient (SameCycle.setoid (SigP S * AP S)) → G.ConnectedComponent :=
  Quotient.lift kap (fun _ _ h => kap_sc S h)

variable (D : G.ConnectedComponent) [Fintype D.supp] [DecidableRel (G.induce D.supp).Adj]

theorem norb_fiber (S : EmbeddingScheme G) :
    norb (SigP (restrict D.supp (closedD D) S) * AP (restrict D.supp (closedD D) S)) =
      Nat.card {q // kapQ S q = D} := by
  unfold norb
  set A := D.supp
  have hA := closedD D
  have hmem : ∀ y : (G.induce A).Dart × Bool, kap (iota A y) = D := fun y =>
    (ConnectedComponent.mem_supp_iff D _).mp y.1.fst.2
  let g : Quotient (SameCycle.setoid (SigP (restrict A hA S) * AP (restrict A hA S))) →
      {q // kapQ S q = D} := fun q =>
    ⟨Quotient.map (iota A) (fun a b h => (sc_iota A hA S a b).mp h) q, by
      induction q using Quotient.ind with
      | _ y => exact hmem y⟩
  apply Nat.card_eq_of_bijective g
  constructor
  · intro q q' h
    induction q using Quotient.ind with
    | _ y =>
    induction q' using Quotient.ind with
    | _ y' =>
      have h' : Quotient.mk _ (iota A y) = Quotient.mk (SameCycle.setoid (SigP S * AP S)) (iota A y') :=
        congrArg Subtype.val h
      exact Quotient.sound ((sc_iota A hA S y y').mpr (Quotient.exact h'))
  · rintro ⟨q, hq⟩
    induction q using Quotient.ind with
    | _ x =>
      have hx : x.1.fst ∈ A := (ConnectedComponent.mem_supp_iff D _).mpr hq
      exact ⟨Quotient.mk _ (dOut A hA x.1 hx, x.2), rfl⟩

theorem dart_fiber :
    Nat.card (G.induce D.supp).Dart = Nat.card {d : G.Dart // G.connectedComponentMk d.fst = D} := by
  apply Nat.card_eq_of_bijective
    (fun d => ⟨dIn D.supp d, (ConnectedComponent.mem_supp_iff D _).mp d.fst.2⟩)
  constructor
  · intro d d' h
    exact dIn_inj D.supp (congrArg Subtype.val h)
  · rintro ⟨d, hd⟩
    exact ⟨dOut D.supp (closedD D) d ((ConnectedComponent.mem_supp_iff D _).mpr hd), rfl⟩

theorem vert_fiber : Nat.card D.supp = Nat.card {v : V // G.connectedComponentMk v = D} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun v => ConnectedComponent.mem_supp_iff D v)

theorem deg_zero_iff (w : D.supp) : (G.induce D.supp).degree w = 0 ↔ G.degree w.1 = 0 := by
  rw [← not_iff_not, ← Ne, ← Ne, ← Nat.pos_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    SimpleGraph.degree_pos_iff_exists_adj, SimpleGraph.degree_pos_iff_exists_adj]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.1, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨⟨u, closedD D _ _ hu w.2⟩, hu⟩

theorem iso_fiber :
    Nat.card {w : D.supp // (G.induce D.supp).degree w = 0} =
      Nat.card {x : {v : V // G.degree v = 0} // G.connectedComponentMk x.1 = D} := by
  apply Nat.card_eq_of_bijective
    (fun w => ⟨⟨w.1.1, (deg_zero_iff D w.1).mp w.2⟩, (ConnectedComponent.mem_supp_iff D _).mp w.1.2⟩)
  constructor
  · intro w w' h
    have := congrArg (fun z => z.1.1) h
    exact Subtype.ext (Subtype.ext this)
  · rintro ⟨⟨v, hv⟩, hD⟩
    have hvD : v ∈ D.supp := (ConnectedComponent.mem_supp_iff D v).mpr hD
    exact ⟨⟨⟨v, hvD⟩, (deg_zero_iff D ⟨v, hvD⟩).mpr hv⟩, rfl⟩

end comp

section sum

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem filter_card {X : Type} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x // p x} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
theorem eg_sum (S : EmbeddingScheme G) :
    S.eulerGenus = ∑ D : G.ConnectedComponent, (restrict D.supp (closedD D) S).eulerGenus := by
  have hc : Nat.card G.ConnectedComponent =
      ∑ D : G.ConnectedComponent, Nat.card (G.induce D.supp).ConnectedComponent := by
    rw [Finset.sum_congr rfl (fun D _ => card_cc_one (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp D).1)]
    simp [Nat.card_eq_fintype_card]
  have hn : Fintype.card V = ∑ D : G.ConnectedComponent, Fintype.card D.supp := by
    rw [← Nat.card_eq_fintype_card, card_fib (fun v : V => G.connectedComponentMk v)]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    rw [← vert_fiber D, Nat.card_eq_fintype_card]
  have hm : G.edgeFinset.card = ∑ D : G.ConnectedComponent, (G.induce D.supp).edgeFinset.card := by
    have h2 := G.dart_card_eq_twice_card_edges
    rw [← Nat.card_eq_fintype_card, card_fib (fun d : G.Dart => G.connectedComponentMk d.fst)] at h2
    have h3 : ∀ D : G.ConnectedComponent,
        Nat.card {d : G.Dart // G.connectedComponentMk d.fst = D} =
          2 * (G.induce D.supp).edgeFinset.card := by
      intro D
      rw [← dart_fiber D, Nat.card_eq_fintype_card, SimpleGraph.dart_card_eq_twice_card_edges]
    rw [Finset.sum_congr rfl (fun D _ => h3 D), ← Finset.mul_sum] at h2
    omega
  have hf : S.faces = ∑ D : G.ConnectedComponent, (restrict D.supp (closedD D) S).faces := by
    unfold EmbeddingScheme.faces
    rw [Finset.sum_add_distrib]
    congr 1
    · have ho : norb (SigP S * AP S) = ∑ D : G.ConnectedComponent,
          norb (SigP (restrict D.supp (closedD D) S) * AP (restrict D.supp (closedD D) S)) := by
        unfold norb
        rw [card_fib (kapQ S)]
        refine Finset.sum_congr rfl (fun D _ => ?_)
        rw [← norb_fiber D S]
        rfl
      have hev : norb (SigP S * AP S) = 2 * ∑ D : G.ConnectedComponent,
          norb (SigP (restrict D.supp (closedD D) S) * AP (restrict D.supp (closedD D) S)) / 2 := by
        rw [ho, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun D _ => ?_)
        exact (Nat.two_mul_div_two_of_even (norb_even _)).symm
      simp only [card_faceOrbit]
      rw [hev, Nat.mul_div_cancel_left _ two_pos]
    · rw [filter_card, card_fib (fun x : {v : V // G.degree v = 0} => G.connectedComponentMk x.1)]
      refine Finset.sum_congr rfl (fun D _ => ?_)
      rw [filter_card, iso_fiber D]
  unfold EmbeddingScheme.eulerGenus
  rw [hc, hn, hm, hf]
  push_cast
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem eg_comp_le (S : EmbeddingScheme G) (c : G.ConnectedComponent) [Fintype c.supp]
    [DecidableRel (G.induce c.supp).Adj] :
    (restrict c.supp (closedD c) S).eulerGenus ≤ S.eulerGenus := by
  classical
  have hs := eg_sum S
  have h := Finset.single_le_sum
    (f := fun D : G.ConnectedComponent => (restrict D.supp (closedD D) S).eulerGenus)
    (fun D _ => eg_nonneg_conn _ (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp D).1) (Finset.mem_univ c)
  rw [← hs] at h
  convert h using 3
  rfl

end sum

end PQComp

open PlanarQueue.Genus in
theorem solution (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (g : ℕ) (hG : EulerGenusLE G g) (c : G.ConnectedComponent)
    [Fintype c.supp] [DecidableRel (G.induce c.supp).Adj] :
    EulerGenusLE (G.induce c.supp) g := by
  obtain ⟨S, hS⟩ := hG
  exact ⟨PQComp.restrict c.supp (PQComp.closedD c) S, le_trans (PQComp.eg_comp_le S c) hS⟩
