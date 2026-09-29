-- Prove2me | solution 1 for block_restrict_polyDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-08T21:46:35.418747+00:00
-- url     : https://prove2.me/submissions/2237f9d2-74f3-43bd-956d-9aed71a98735

import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic

/-!
# Polynomial degree under block-restriction

For a Boolean function `f : {0,1}ⁿ → {0,1}` of polynomial degree `d`,
restricting attention to a *block-substitution sub-cube* — fixing some
coordinates to `x`, and grouping the remaining coordinates into pairwise-
disjoint blocks each parameterised by a single bit — yields a Boolean
function on the smaller cube `{0,1}ᵇ` whose polynomial degree is also at
most `d`.

This is the missing block-substitution lemma in the Nisan-Szegedy
proof. Its proof requires:
1. A construction of the substituted multivariate polynomial via
   `MvPolynomial.bind₁` with linear or constant inputs at each variable.
2. A proof that `bind₁` of a polynomial of total degree `≤ d` into linear
   polynomials yields a polynomial of total degree `≤ d` (this is
   `bind₁_totalDegree_le` for the special case `k = 1`, missing from
   Mathlib at present).
3. A proof that the substituted polynomial agrees with the block-restricted
   function on the cube.

Left as a platform leaf — DEFERRED. Estimated 150-250 lines.
-/

/-- The "multi-flip" of `x` selected by `y` over an indexed family of
disjoint blocks: at coordinate `j`, flips `x j` iff some block `e i`
contains `j` and `y i = true`. With `Classical.dec`, this is
`noncomputable`. -/
noncomputable def blockFlipMulti_sol {n b : ℕ}
    (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (y : Fin b → Bool) (j : Fin n) : Bool :=
  open Classical in
  if ∃ i, j ∈ e i ∧ y i = true then !x j else x j


/-!
# Proof — `block_restrict_polyDegree_le`

Construct the block-substitution polynomial `bind₁ s p` where `s` is linear
(or constant) at every variable, and show its `totalDegree` is bounded by
that of the original polynomial. This gives a polynomial witness for
the block-restricted Boolean function of degree `≤ polyDegree f`.
-/

open MvPolynomial

namespace BlockRestrict

variable {n b : ℕ}

/-! ### bind₁ degree-preservation for ≤ 1-degree substitutes -/

/-- Substituting linear-or-constant polynomials into `p` yields a polynomial
of total degree at most `p.totalDegree`. (The general case
`bind₁_totalDegree_le : (bind₁ s p).totalDegree ≤ k * p.totalDegree` for
`k = max (s i).totalDegree` specialises to this when `k = 1`.) -/
lemma bind₁_totalDegree_le_one
    {σ τ R : Type*} [CommSemiring R]
    (s : σ → MvPolynomial τ R)
    (h_each : ∀ i, (s i).totalDegree ≤ 1)
    (p : MvPolynomial σ R) :
    (bind₁ s p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intros m hm
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => totalDegree_pow _ _)).trans ?_
  refine (Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h_each i))).trans ?_
  simp only [mul_one]
  exact le_totalDegree hm

/-! ### The substitution map for block-restriction -/

/-- The substitution polynomial for coordinate `j`. Linear in `Y_i` if `j`
lies in block `e i` (unique by disjointness), constant otherwise. -/
noncomputable def substMap (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (j : Fin n) : MvPolynomial (Fin b) ℝ :=
  open Classical in
  if h : ∃ i, j ∈ e i then
    if x j then 1 - X h.choose else X h.choose
  else
    if x j then 1 else 0

lemma substMap_totalDegree_le_one (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (j : Fin n) : (substMap x e j).totalDegree ≤ 1 := by
  classical
  unfold substMap
  by_cases h : ∃ i, j ∈ e i
  · rw [dif_pos h]
    by_cases hx : x j
    · rw [if_pos hx]
      refine (totalDegree_sub _ _).trans ?_
      rw [totalDegree_one, totalDegree_X]
      omega
    · rw [if_neg hx, totalDegree_X]
  · rw [dif_neg h]
    by_cases hx : x j
    · rw [if_pos hx, totalDegree_one]; omega
    · rw [if_neg hx]; simp

/-! ### Eval correspondence -/

/-- Disjointness: if `j ∈ e i` and `j ∈ e k`, then `i = k`. -/
lemma block_unique (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i k : Fin b, i ≠ k → Disjoint (e i) (e k))
    {j : Fin n} {i k : Fin b} (hi : j ∈ e i) (hk : j ∈ e k) : i = k := by
  by_contra h_ne
  exact (Finset.disjoint_left.mp (h_disj i k h_ne)) hi hk

lemma blockFlipMulti_unique (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i k : Fin b, i ≠ k → Disjoint (e i) (e k))
    (y : Fin b → Bool) (j : Fin n) {i : Fin b} (hi : j ∈ e i) :
    blockFlipMulti_sol x e y j = (if y i then !x j else x j) := by
  classical
  unfold blockFlipMulti_sol
  by_cases hy : y i = true
  · rw [if_pos ⟨i, hi, hy⟩, if_pos hy]
  · rw [if_neg hy]
    rw [if_neg]
    rintro ⟨k, hk, hyk⟩
    have heq : i = k := block_unique e h_disj hi hk
    rw [← heq] at hyk
    exact hy hyk

lemma blockFlipMulti_no_block (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (y : Fin b → Bool) {j : Fin n} (h : ¬ ∃ i, j ∈ e i) :
    blockFlipMulti_sol x e y j = x j := by
  classical
  unfold blockFlipMulti_sol
  rw [if_neg]
  rintro ⟨i, hi, _⟩
  exact h ⟨i, hi⟩

/-- The evaluation of `substMap x e j` matches `boolToReal (blockFlipMulti_sol x e y j)`. -/
lemma eval_substMap (x : Fin n → Bool) (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i k : Fin b, i ≠ k → Disjoint (e i) (e k))
    (y : Fin b → Bool) (j : Fin n) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) (substMap x e j)
      = (if blockFlipMulti_sol x e y j then (1 : ℝ) else 0) := by
  classical
  unfold substMap
  by_cases h : ∃ i, j ∈ e i
  · rw [dif_pos h]
    have h_chose : j ∈ e (Classical.choose h) := Classical.choose_spec h
    rw [blockFlipMulti_unique x e h_disj y j h_chose]
    by_cases hx : x j
    · rw [if_pos hx, hx]
      simp only [map_sub, map_one, eval_X]
      cases y (Classical.choose h) <;> simp
    · have hxf : x j = false := Bool.eq_false_of_not_eq_true hx
      rw [if_neg hx, hxf]
      simp only [eval_X]
      cases y (Classical.choose h) <;> simp
  · rw [dif_neg h, blockFlipMulti_no_block x e y h]
    by_cases hx : x j
    · rw [if_pos hx, hx]; simp
    · have hxf : x j = false := Bool.eq_false_of_not_eq_true hx
      rw [if_neg hx, hxf]; simp

end BlockRestrict

open BlockRestrict

/-! ### Main proof. -/

theorem solution
    {n b : ℕ} (f : BoolFunc n) (x : Fin n → Bool)
    (e : Fin b → Finset (Fin n))
    (h_disj : ∀ i j : Fin b, i ≠ j → Disjoint (e i) (e j)) :
    polyDegree (fun y : Fin b → Bool => f (blockFlipMulti_sol x e y))
      ≤ polyDegree f := by
  classical
  -- Get the polynomial witness for f at degree polyDegree f
  have hp : HasPolyRep f (polyDegree f) :=
    Nat.find_spec (⟨n, hasPolyRep_card f⟩ : ∃ d, HasPolyRep f d)
  obtain ⟨p, hp_deg, hp_eval⟩ := hp
  -- Build the substitution polynomial
  set q : MvPolynomial (Fin b) ℝ := bind₁ (substMap x e) p with hq_def
  -- Step 1: q.totalDegree ≤ p.totalDegree ≤ polyDegree f
  have hq_deg : q.totalDegree ≤ polyDegree f :=
    (bind₁_totalDegree_le_one (substMap x e) (substMap_totalDegree_le_one x e) p).trans hp_deg
  -- Step 2: q evaluates correctly: eval ∘ y on q matches g
  have hq_eval : ∀ y : Fin b → Bool,
      MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) q
        = if f (blockFlipMulti_sol x e y) then (1 : ℝ) else 0 := by
    intro y
    rw [hq_def]
    -- aeval_bind₁: aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ
    -- For eval (a non-AlgHom version), we use the fact that eval = aeval applied to the right algebra map.
    -- More directly: use eval_bind₁-style by unfolding.
    have h_aeval :
        (MvPolynomial.aeval (fun i => if y i then (1 : ℝ) else 0)) (bind₁ (substMap x e) p)
        = (MvPolynomial.aeval
            (fun j => MvPolynomial.aeval (fun i => if y i then (1 : ℝ) else 0) (substMap x e j))) p :=
      MvPolynomial.aeval_bind₁ _ _ _
    -- aeval = eval (since the target algebra is the identity over ℝ).
    rw [MvPolynomial.aeval_eq_eval] at h_aeval
    rw [h_aeval]
    -- Goal: (aeval (fun j => eval ... (substMap x e j))) p = if f (...) then 1 else 0
    -- Rewrite the inner eval ... (substMap x e j) using eval_substMap.
    have h_eq_lambdas :
        (fun j : Fin n => MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0)
                            (substMap x e j))
          = (fun j : Fin n => if blockFlipMulti_sol x e y j then (1 : ℝ) else 0) := by
      funext j
      exact eval_substMap x e h_disj y j
    rw [h_eq_lambdas, MvPolynomial.aeval_eq_eval]
    exact hp_eval (blockFlipMulti_sol x e y)
  -- Step 3: assemble HasPolyRep witness for g at degree polyDegree f
  have h_witness : HasPolyRep (fun y : Fin b → Bool => f (blockFlipMulti_sol x e y))
                              (polyDegree f) := by
    refine ⟨q, hq_deg, ?_⟩
    intro y
    exact hq_eval y
  -- Step 4: apply Nat.find_le
  show Nat.find _ ≤ _
  exact Nat.find_le h_witness
