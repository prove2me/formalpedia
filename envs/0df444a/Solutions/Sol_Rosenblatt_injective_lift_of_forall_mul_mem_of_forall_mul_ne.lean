-- Prove2me | solution 1 for Rosenblatt.injective_lift_of_forall_mul_mem_of_forall_mul_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-21T16:27:48.017778+00:00
-- url     : https://prove2.me/submissions/87db1f0b-db3c-4650-b6ab-e370343a4230

import Mathlib

/-!
# Rosenblatt, Corollary 2.5: a ping-pong criterion for free subsemigroups

*Invariant measures and growth conditions*, Trans. Amer. Math. Soc. 193 (1974), Proposition 2.4
(p. 36) and Corollary 2.5 (p. 37).

If some nonempty `A ⊆ G` satisfies `aA ∪ bA ⊆ A` with `aA` and `bA` disjoint, then `a` and `b`
generate a free subsemigroup.  This is the tool Theorem 4.17 uses to build a free subsemigroup
out of a matrix eigenvalue off the unit circle, and it is the only place in that argument where
freeness is actually established.

Rosenblatt's Proposition 2.4 is the sharper statement: from `aA ∪ bA ⊆ A` alone, *either* `a` and
`b` generate a free subsemigroup *or* some `z` in the subsemigroup they generate has
`zA ⊆ aA ∩ bA`.  Disjointness kills the second alternative because `A` is nonempty, which is
exactly how Corollary 2.5 follows.  The proof below inlines that dichotomy rather than splitting
it out, and the place it appears is `lift_ne_one`: a nonempty word equal to `1` forces
`A ⊆ (a or b)A`, and then the *other* letter's translate lands in both translates at once.

The conclusion is stated for the given pair `a`, `b` — Rosenblatt's "in this case `a`, `b`
generate a free subsemigroup" — which is stronger than the bare existence statement
`Chou.HasFreeSubsemigroupOfRankTwo`, and is what Theorem 4.17 needs, since it produces a
specific pair.
-/

namespace Rosenblatt

/-- Applying any word in `a` and `b` to a point of `A` stays inside `A`. -/
theorem lift_mul_mem {G : Type*} [Group G] {a b : G} {A : Set G}
    (hmem : ∀ x ∈ A, a * x ∈ A ∧ b * x ∈ A) {α : G} (hα : α ∈ A) :
    ∀ w : FreeMonoid (Fin 2), FreeMonoid.lift ![a, b] w * α ∈ A := by
  intro w
  induction w using FreeMonoid.recOn with
  | one => simpa using hα
  | of_mul x w ih =>
      rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc]
      fin_cases x
      · simpa using (hmem _ ih).1
      · simpa using (hmem _ ih).2

/-- No nonempty word in `a` and `b` is trivial.  This is where Proposition 2.4's second
alternative is excluded: if a word beginning with one letter is trivial then `A` is contained in
that letter's translate, and then the other letter's translate meets both. -/
theorem lift_ne_one {G : Type*} [Group G] {a b : G} {A : Set G} (hA : A.Nonempty)
    (hmem : ∀ x ∈ A, a * x ∈ A ∧ b * x ∈ A)
    (hne : ∀ x ∈ A, ∀ y ∈ A, a * x ≠ b * y) (x : Fin 2) (w : FreeMonoid (Fin 2)) :
    FreeMonoid.lift ![a, b] (FreeMonoid.of x * w) ≠ 1 := by
  intro hw
  obtain ⟨α, hα⟩ := hA
  -- every point of `A` lies in the translate of `A` by the first letter
  have hstep : ∀ β ∈ A, ∃ γ ∈ A, β = ![a, b] x * γ := by
    intro β hβ
    refine ⟨FreeMonoid.lift ![a, b] w * β, lift_mul_mem hmem hβ w, ?_⟩
    have h1 : ![a, b] x * (FreeMonoid.lift ![a, b] w * β) = β := by
      rw [← mul_assoc, ← FreeMonoid.lift_eval_of ![a, b] x, ← map_mul, hw, one_mul]
    exact h1.symm
  fin_cases x
  · obtain ⟨γ, hγ, hβγ⟩ := hstep (b * α) (hmem _ hα).2
    exact hne γ hγ α hα (by simpa using hβγ.symm)
  · obtain ⟨γ, hγ, hβγ⟩ := hstep (a * α) (hmem _ hα).1
    exact hne α hα γ hγ (by simpa using hβγ)

/-- **Rosenblatt, Corollary 2.5** (p. 37): if `A` is nonempty, `aA ∪ bA ⊆ A`, and `aA` and `bA`
are disjoint, then `a` and `b` generate a free subsemigroup — distinct words in the two letters
take distinct values. -/
theorem injective_lift_of_pingPong {G : Type*} [Group G] (a b : G)
    (A : Set G) (hA : A.Nonempty)
    (hmem : ∀ x ∈ A, a * x ∈ A ∧ b * x ∈ A)
    (hne : ∀ x ∈ A, ∀ y ∈ A, a * x ≠ b * y) :
    Function.Injective (FreeMonoid.lift ![a, b]) := by
  obtain ⟨α, hα⟩ := hA
  have hA' : A.Nonempty := ⟨α, hα⟩
  intro w
  induction w using FreeMonoid.recOn with
  | one =>
      intro w' hw'
      cases w' using FreeMonoid.casesOn with
      | one => rfl
      | of_mul y t =>
          exact absurd hw'.symm (lift_ne_one hA' hmem hne y t)
  | of_mul x w ih =>
      intro w' hw'
      cases w' using FreeMonoid.casesOn with
      | one => exact absurd hw' (lift_ne_one hA' hmem hne x w)
      | of_mul y t =>
          rw [map_mul, map_mul, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of] at hw'
          -- the first letters must agree, or the two translates of `A` would meet
          have hxy : x = y := by
            by_contra hxy
            have hcoe := congrArg (fun g => g * α) hw'
            simp only [mul_assoc] at hcoe
            have hu := lift_mul_mem hmem hα w
            have hv := lift_mul_mem hmem hα t
            fin_cases x <;> fin_cases y
            · exact hxy rfl
            · exact hne _ hu _ hv (by simpa using hcoe)
            · exact hne _ hv _ hu (by simpa using hcoe.symm)
            · exact hxy rfl
          subst hxy
          have hcancel : FreeMonoid.lift ![a, b] w = FreeMonoid.lift ![a, b] t :=
            mul_left_cancel hw'
          rw [ih hcancel]

end Rosenblatt

theorem solution {G : Type*} [Group G] (a b : G)
    (A : Set G) (hA : A.Nonempty)
    (hmem : ∀ x ∈ A, a * x ∈ A ∧ b * x ∈ A)
    (hne : ∀ x ∈ A, ∀ y ∈ A, a * x ≠ b * y) :
    Function.Injective (FreeMonoid.lift ![a, b]) :=
  Rosenblatt.injective_lift_of_pingPong a b A hA hmem hne
