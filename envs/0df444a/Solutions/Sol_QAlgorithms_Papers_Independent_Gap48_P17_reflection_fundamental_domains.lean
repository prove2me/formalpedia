-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.reflection_fundamental_domains
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:39:42.851612+00:00
-- url     : https://prove2.me/submissions/be63b75b-faa2-4f91-bc24-0dae1d6fc175

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
open QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

def g74c_f1 (x : ℤ) : ℤ := if x % 8 ≤ 2 then x % 8 else if x % 8 ≤ 6 then 4 - x % 8 else x % 8 - 8
def g74c_f2 (y : ℤ) : ℤ := if y % 8 ≤ 3 then y % 8 else if y % 8 ≤ 6 then 6 - y % 8 else y % 8 - 8
def g74c_g1 (x : ℤ) : ℤ := if x % 4 ≤ 2 then x % 4 else 4 - x % 4
def g74c_F (a : ℤ × ℤ) : ℤ × ℤ := (g74c_f1 a.1, g74c_f2 a.2)
def g74c_FT (a : ℤ × ℤ) : ℤ × ℤ := (g74c_g1 a.1, g74c_f2 a.2)

theorem g74c_transl1 (R : ℤ × ℤ → ℤ × ℤ → Prop) (hR : ∀ a b, gammaStep a b → R a b)
    (x y : ℤ) (k : ℤ) : Relation.EqvGen R (x, y) (x + 8 * k, y) := by
  have ht : ∀ x : ℤ, Relation.EqvGen R (x, y) (x + 8, y) := fun x =>
    Relation.EqvGen.trans _ (-4 - x, y) _ (Relation.EqvGen.rel _ _ (hR _ _ (Or.inl rfl)))
      (Relation.EqvGen.rel _ _ (hR _ _ (Or.inr (Or.inl (by ext <;> simp; ring)))))
  induction k using Int.induction_on with
  | zero => simpa using Relation.EqvGen.refl _
  | succ k ih => exact ih.trans _ _ _ (by rw [mul_add, mul_one, ← add_assoc]; exact ht _)
  | pred k ih =>
    refine ih.trans _ _ _ (Relation.EqvGen.symm _ _ ?_)
    have := ht (x + 8 * (-(k : ℤ) - 1))
    rwa [show x + 8 * (-(k : ℤ) - 1) + 8 = x + 8 * -(k : ℤ) by ring] at this

theorem g74c_transl2 (R : ℤ × ℤ → ℤ × ℤ → Prop) (hR : ∀ a b, gammaStep a b → R a b)
    (x y : ℤ) (k : ℤ) : Relation.EqvGen R (x, y) (x, y + 8 * k) := by
  have ht : ∀ y : ℤ, Relation.EqvGen R (x, y) (x, y + 8) := fun y =>
    Relation.EqvGen.trans _ (x, -2 - y) _
      (Relation.EqvGen.rel _ _ (hR _ _ (Or.inr (Or.inr (Or.inl rfl)))))
      (Relation.EqvGen.rel _ _ (hR _ _ (Or.inr (Or.inr (Or.inr (by ext <;> simp; ring))))))
  induction k using Int.induction_on with
  | zero => simpa using Relation.EqvGen.refl _
  | succ k ih => exact ih.trans _ _ _ (by rw [mul_add, mul_one, ← add_assoc]; exact ht _)
  | pred k ih =>
    refine ih.trans _ _ _ (Relation.EqvGen.symm _ _ ?_)
    have := ht (y + 8 * (-(k : ℤ) - 1))
    rwa [show y + 8 * (-(k : ℤ) - 1) + 8 = y + 8 * -(k : ℤ) by ring] at this

theorem g74c_transl1t (x y : ℤ) (k : ℤ) :
    Relation.EqvGen gammaTildeStep (x, y) (x + 4 * k, y) := by
  have ht : ∀ x : ℤ, Relation.EqvGen gammaTildeStep (x, y) (x + 4, y) := fun x =>
    Relation.EqvGen.trans _ (-x, y) _ (Relation.EqvGen.rel _ _ (Or.inr rfl))
      (Relation.EqvGen.rel _ _ (Or.inl (Or.inr (Or.inl (by ext <;> simp; ring)))))
  induction k using Int.induction_on with
  | zero => simpa using Relation.EqvGen.refl _
  | succ k ih => exact ih.trans _ _ _ (by rw [mul_add, mul_one, ← add_assoc]; exact ht _)
  | pred k ih =>
    refine ih.trans _ _ _ (Relation.EqvGen.symm _ _ ?_)
    have := ht (x + 4 * (-(k : ℤ) - 1))
    rwa [show x + 4 * (-(k : ℤ) - 1) + 4 = x + 4 * -(k : ℤ) by ring] at this

theorem g74c_c1 (R : ℤ × ℤ → ℤ × ℤ → Prop) (hR : ∀ a b, gammaStep a b → R a b) (x y : ℤ) :
    Relation.EqvGen R (x, y) (g74c_f1 x, y) := by
  have h0 : Relation.EqvGen R (x, y) (x % 8, y) := by
    have := g74c_transl1 R hR x y (-(x / 8))
    rwa [show x + 8 * -(x / 8) = x % 8 by rw [Int.emod_def]; ring] at this
  refine h0.trans _ _ _ ?_
  unfold g74c_f1
  split_ifs with h1 h2
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (hR _ _ (Or.inr (Or.inl rfl)))
  · have := g74c_transl1 R hR (x % 8) y (-1)
    rwa [show x % 8 + 8 * -1 = x % 8 - 8 by ring] at this

theorem g74c_c2 (R : ℤ × ℤ → ℤ × ℤ → Prop) (hR : ∀ a b, gammaStep a b → R a b) (x y : ℤ) :
    Relation.EqvGen R (x, y) (x, g74c_f2 y) := by
  have h0 : Relation.EqvGen R (x, y) (x, y % 8) := by
    have := g74c_transl2 R hR x y (-(y / 8))
    rwa [show y + 8 * -(y / 8) = y % 8 by rw [Int.emod_def]; ring] at this
  refine h0.trans _ _ _ ?_
  unfold g74c_f2
  split_ifs with h1 h2
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (hR _ _ (Or.inr (Or.inr (Or.inr rfl))))
  · have := g74c_transl2 R hR x (y % 8) (-1)
    rwa [show y % 8 + 8 * -1 = y % 8 - 8 by ring] at this

theorem g74c_c1t (x y : ℤ) : Relation.EqvGen gammaTildeStep (x, y) (g74c_g1 x, y) := by
  have h0 : Relation.EqvGen gammaTildeStep (x, y) (x % 4, y) := by
    have := g74c_transl1t x y (-(x / 4))
    rwa [show x + 4 * -(x / 4) = x % 4 by rw [Int.emod_def]; ring] at this
  refine h0.trans _ _ _ ?_
  unfold g74c_g1
  split_ifs with h1
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inl (Or.inr (Or.inl rfl)))

theorem g74c_toF (z : ℤ × ℤ) : gammaOrbit z (g74c_F z) :=
  (g74c_c1 _ (fun _ _ h => h) z.1 z.2).trans _ _ _ (g74c_c2 _ (fun _ _ h => h) _ z.2)

theorem g74c_toFT (z : ℤ × ℤ) : gammaTildeOrbit z (g74c_FT z) :=
  (g74c_c1t z.1 z.2).trans _ _ _ (g74c_c2 _ (fun _ _ h => Or.inl h) _ z.2)

theorem g74c_F_inv (a b : ℤ × ℤ) (h : gammaOrbit a b) : g74c_F a = g74c_F b := by
  induction h with
  | rel a b h =>
    rcases h with rfl | rfl | rfl | rfl <;>
      simp only [g74c_F, g74c_f1, g74c_f2, Prod.mk.injEq] <;>
      refine ⟨?_, ?_⟩ <;> first | trivial | (split_ifs <;> omega)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem g74c_FT_inv (a b : ℤ × ℤ) (h : gammaTildeOrbit a b) : g74c_FT a = g74c_FT b := by
  induction h with
  | rel a b h =>
    rcases h with (rfl | rfl | rfl | rfl) | rfl <;>
      simp only [g74c_FT, g74c_g1, g74c_f2, Prod.mk.injEq] <;>
      refine ⟨?_, ?_⟩ <;> first | trivial | (split_ifs <;> omega)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem g74c_orbit_iff (a b : ℤ × ℤ) : gammaOrbit a b ↔ g74c_F a = g74c_F b :=
  ⟨g74c_F_inv a b, fun h => (g74c_toF a).trans _ _ _ (h ▸ (g74c_toF b).symm _ _)⟩

theorem g74c_orbitT_iff (a b : ℤ × ℤ) : gammaTildeOrbit a b ↔ g74c_FT a = g74c_FT b :=
  ⟨g74c_FT_inv a b, fun h => (g74c_toFT a).trans _ _ _ (h ▸ (g74c_toFT b).symm _ _)⟩

theorem g74c_memR (z : ℤ × ℤ) : z ∈ reflectionDomain ↔
    -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 - 1 ∧ z.2 - 1 ≤ 2 ∧ Even (z.1 + z.2) := by
  obtain ⟨a, b⟩ := z
  constructor
  · intro h
    simp only [reflectionDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rintro ⟨h1, h2, h3, h4, h5⟩
    simp only at h1 h2 h3 h4 h5
    have h3' : -1 ≤ b := by omega
    have h4' : b ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> revert h5 <;> decide

theorem g74c_memE (z : ℤ × ℤ) : z ∈ enlargedDomain ↔
    0 ≤ z.1 ∧ z.1 ≤ 2 ∧ -1 ≤ z.2 ∧ z.2 ≤ 3 ∧ Even (z.1 + z.2) := by
  obtain ⟨a, b⟩ := z
  constructor
  · intro h
    simp only [enlargedDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> decide
  · rintro ⟨h1, h2, h3, h4, h5⟩
    simp only at h1 h2 h3 h4 h5
    interval_cases a <;> interval_cases b <;> revert h5 <;> decide

/-- Introduction, PDF pp. 4--5: both reflection domains and the seven nonnegative
signature representatives. Closed boundary conventions match the source. -/
theorem solution :
    (∀ z : ℤ × ℤ,
      (∃ p q : ℤ, z = (p + q, p - q)) ↔ Even (z.1 + z.2)) ∧
    (∀ z : ℤ × ℤ, z ∈ reflectionDomain ↔
      -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 - 1 ∧ z.2 - 1 ≤ 2 ∧ Even (z.1 + z.2)) ∧
    reflectionDomain.card = 12 ∧ enlargedDomain.card = 7 ∧ signatureDomain.card = 7 ∧
    (∀ z : ℤ × ℤ, Even (z.1 + z.2) →
      ∃! w : ℤ × ℤ, w ∈ reflectionDomain ∧ gammaOrbit z w) ∧
    (∀ z : ℤ × ℤ, Even (z.1 + z.2) →
      ∃! w : ℤ × ℤ, w ∈ enlargedDomain ∧ gammaTildeOrbit z w) ∧
    (∀ z : ℤ × ℤ, Even (z.1 + z.2) →
      ∃! w : ℤ × ℤ, w ∈ signatureDomain ∧ 0 ≤ w.1 ∧ 0 ≤ w.2 ∧
        gammaTildeOrbit z (w.1 + w.2, w.1 - w.2)) := by
  have hFmem : ∀ z : ℤ × ℤ, Even (z.1 + z.2) → g74c_F z ∈ reflectionDomain := by
    intro z hz
    rw [g74c_memR]
    rw [Int.even_iff] at hz ⊢
    simp only [g74c_F, g74c_f1, g74c_f2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega
  have hFid : ∀ w : ℤ × ℤ, w ∈ reflectionDomain → g74c_F w = w := by
    intro w hw
    rw [g74c_memR] at hw
    obtain ⟨a, b⟩ := w
    simp only at hw
    simp only [g74c_F, g74c_f1, g74c_f2, Prod.mk.injEq]
    constructor <;> split_ifs <;> omega
  have hFTmem : ∀ z : ℤ × ℤ, Even (z.1 + z.2) → g74c_FT z ∈ enlargedDomain := by
    intro z hz
    rw [g74c_memE]
    rw [Int.even_iff] at hz ⊢
    simp only [g74c_FT, g74c_g1, g74c_f2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega
  have hFTid : ∀ w : ℤ × ℤ, w ∈ enlargedDomain → g74c_FT w = w := by
    intro w hw
    rw [g74c_memE] at hw
    obtain ⟨a, b⟩ := w
    simp only at hw
    simp only [g74c_FT, g74c_g1, g74c_f2, Prod.mk.injEq]
    constructor <;> split_ifs <;> omega
  refine ⟨?_, g74c_memR, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro z
    constructor
    · rintro ⟨p, q, rfl⟩; exact ⟨p, by ring⟩
    · rintro ⟨r, hr⟩; exact ⟨r, z.1 - r, by ext <;> simp <;> omega⟩
  · intro z hz
    refine ⟨g74c_F z, ⟨hFmem z hz, g74c_toF z⟩, ?_⟩
    rintro w ⟨hw, ho⟩
    rw [← hFid w hw, ← (g74c_orbit_iff z w).mp ho]
  · intro z hz
    refine ⟨g74c_FT z, ⟨hFTmem z hz, g74c_toFT z⟩, ?_⟩
    rintro w ⟨hw, ho⟩
    rw [← hFTid w hw, ← (g74c_orbitT_iff z w).mp ho]
  · intro z hz
    have hc := hFTmem z hz
    simp only [enlargedDomain, Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [g74c_orbitT_iff]
    rcases hc with h | h | h | h | h | h | h <;> rw [h]
    · refine ⟨(2, 2), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
    · refine ⟨(3, 1), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
    · refine ⟨(1, 2), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
    · refine ⟨(2, 1), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
    · refine ⟨(3, 0), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
    · refine ⟨(1, 1), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
    · refine ⟨(2, 0), by decide, ?_⟩
      rintro ⟨a, b⟩ ⟨hw, -, -, ho⟩
      simp only [signatureDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> revert ho <;> decide
