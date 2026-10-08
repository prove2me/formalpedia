-- Prove2me | solution 1 for ThreeSumApsp.Mult_arrays_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:24:08.619914+00:00
-- url     : https://prove2.me/submissions/485ffbcc-747d-4191-ab25-03d0d66d99c1

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Levels
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Lemmas 7 and 8: what `Full` computes

Section 2.3.2. Lemma 7: at the leaf `τ`, `Full(a, b)` multiplies `Φ_τ(a)` by
`Ψ_τ(b)`, and it returns `Mult(a, b)`, whose entry at `w` is the sum of these products over the
leaves contributing to `w` (equation (2)). Lemma 8:
`Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) ⋯ γ(u_L, v_L, w_L) a[u] b[v]`, with the `γ` of equation (3).

* `Φ_τ` and `Ψ_τ` are the same expression for two families of linear forms (`encodeWith`), so what
  holds for both is proved once.
* Lemma 7 is proved by induction on `L`, as in the paper. Step (2) is the encoding:
  `Φ_{λτ'}(a) = Φ_{τ'}(A_λ)` and `Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)` (`Phi_cons`, `Psi_cons`). Step (4) is
  the decoding: the leaves contributing to `z w'` are the `λτ'` with `λ` contributing to `z` and
  `τ'` to `w'` (`Leaf.contributes_succ`), so `Full` and `Mult` both satisfy
  `c[z w'] = ∑_{λ contributing to z} C_λ[w']` (`Full_succ`, `Mult_succ`).
* Lemma 8: the leaves contributing to `w` choose a term contributing to `w_ℓ` independently at each
  level `ℓ` (`Leaf.filter_contributes_eq_piFinset`), so the sum over these leaves of a product over
  the levels is a product of sums (`prod_gamma_eq_sum_contributes`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Which leaves contribute to an output string -/


























/-- In the proof of Lemma 8: the leaves contributing to `w` "are the leaves whose term at
level ℓ contributes to w_ℓ, independently for each ℓ". -/
theorem Leaf.filter_contributes_eq_piFinset {L : ℕ} (w : OutStr L) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w)
      = Fintype.piFinset fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ) := by
  ext τ
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rfl







/-! ### The two encodings at once -/

section encodeWith

variable {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}



















end encodeWith

/-! ### Lemma 7 -/





































































/-! ### Lemma 8 -/

/-- The display in the proof of Lemma 8: the sum, over the leaves `τ` contributing
to `w`, of `∏_ℓ φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ)` "is the product of sums ∏_ℓ ∑_{τ_ℓ contributing to w_ℓ}
φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ) = ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) by (3)". -/
theorem prod_gamma_eq_sum_contributes {L : ℕ} (u : LeftStr L) (v : RightStr L) (w : OutStr L) :
    ∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)
      = ∑ τ : Leaf L with Leaf.Contributes τ w, (∏ ℓ, phi (τ ℓ) (u ℓ)) * ∏ ℓ, psi (τ ℓ) (v ℓ) := by
  simp only [gamma]
  rw [prod_univ_sum, Leaf.filter_contributes_eq_piFinset]
  exact sum_congr rfl fun τ _ => prod_mul_distrib

/-- **Lemma 8**.  "For all arrays a, b and every output string w,
Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) γ(u₂, v₂, w₂) ⋯ γ(u_L, v_L, w_L) a[u] b[v],
the sum over all left strings u and right strings v." -/
theorem lemma_8 {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L) :
    Mult a b w = ∑ u, ∑ v, (∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)) * a u * b v := by
  -- "the coefficient of a[u] b[v] in (2) is ∑_τ ∏_ℓ φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ), summed over the
  -- leaves τ contributing to w": expand `Φ_τ(a) Ψ_τ(b)` and sum over `τ` last.
  simp only [Mult, Phi, Psi, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_gamma_eq_sum_contributes, sum_mul, sum_mul]
  exact sum_congr rfl fun τ _ => by ring

end ThreeSumApsp

end



/-!
# Strings cut along a set of levels

Section 2.3.3 cuts a string of `L` variables along a set `Q` of `m` levels: its variables
at the levels of `Q`, in the order of the levels, form a string of length `m`, and its variables at
the other levels form a string of length `L - m`. The first three parts of this file hold for every
alphabet; the last part specializes them to left, right and output strings.

* Every level is the `k`-th lowest level of `Q` or the `k`-th lowest level outside `Q` for some `k`.
  So a statement about all levels is checked on these two kinds of levels (`forall_level_iff`), and
  so is the statement that a set of levels is `Q` (`filter_eq_iff_forall_level`).
* `glue Q hQ f g` is the string with the letters of `f` at the levels of `Q` and the letters of `g`
  at the other levels. It is the only such string (`eq_glue_iff`), and `f` and `g` can be read off
  it (`glue_inj`).
* If the letters are of two kinds, inner and outer, and each is given by its kind and an index, then
  a string can be rebuilt from its inner set and the indices of its letters (`glue_index`).
* "A string is determined by its inner set, its outer part, and its inner part": the strings
  `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and `outStrOf Q hQ r c` have the parts that their
  names say, and no other string has them (`existsUnique_leftStr`, `existsUnique_rightStr`,
  `existsUnique_outStr`). No later proof uses these three statements; the later proofs use the
  lemmas from which they follow.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### The levels of a set and of its complement, in order -/

/-- The `k`-th lowest level of `Q` is a level of `Q`. -/
theorem innerLevel_mem (k : Fin m) : innerLevel Q hQ k ∈ Q :=
  Q.orderEmbOfFin_mem hQ k

/-- The `k`-th lowest level outside `Q` is not a level of `Q`. -/
theorem outerLevel_notMem (k : Fin (L - m)) : outerLevel Q hQ k ∉ Q :=
  mem_compl.mp (Qᶜ.orderEmbOfFin_mem (card_compl_of_card_eq Q hQ) k)

/-- Every level of `Q` is the `k`-th lowest level of `Q` for some `k`. -/
theorem exists_innerLevel {ℓ : Fin L} (hℓ : ℓ ∈ Q) : ∃ k, innerLevel Q hQ k = ℓ :=
  (Q.range_orderEmbOfFin hQ).ge hℓ

/-- Every level outside `Q` is the `k`-th lowest level outside `Q` for some `k`. -/
theorem exists_outerLevel {ℓ : Fin L} (hℓ : ℓ ∉ Q) : ∃ k, outerLevel Q hQ k = ℓ :=
  (Qᶜ.range_orderEmbOfFin (card_compl_of_card_eq Q hQ)).ge (mem_coe.mpr (mem_compl.mpr hℓ))

/-- The levels of `Q` in order depend only on the set `Q`. -/
theorem innerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    innerLevel Q' hQ' = innerLevel Q hQ := by
  subst h
  rfl

/-- The levels outside `Q` in order depend only on the set `Q`. -/
theorem outerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    outerLevel Q' hQ' = outerLevel Q hQ := by
  subst h
  rfl

/-- A property holds at every level if and only if it holds at the levels of `Q` and at the levels
outside `Q`. -/
theorem forall_level_iff {P : Fin L → Prop} :
    (∀ ℓ, P ℓ) ↔ (∀ k, P (innerLevel Q hQ k)) ∧ ∀ k, P (outerLevel Q hQ k) := by
  refine ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hin, hout⟩ ℓ => ?_⟩
  by_cases hℓ : ℓ ∈ Q
  · obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
    exact hin k
  · obtain ⟨k, rfl⟩ := exists_outerLevel Q hQ hℓ
    exact hout k

/-- A property cuts out the set `Q` if and only if it holds at the levels of `Q` and fails at the
other levels. -/
theorem filter_eq_iff_forall_level {P : Fin L → Prop} [DecidablePred P] :
    univ.filter P = Q ↔ (∀ k, P (innerLevel Q hQ k)) ∧ ∀ k, ¬ P (outerLevel Q hQ k) := by
  simp only [Finset.ext_iff, forall_level_iff Q hQ, mem_filter, mem_univ, true_and,
    innerLevel_mem, outerLevel_notMem, iff_true, iff_false]

/-- A property that holds at the `m` levels of `Q`, and at `m` levels in all, cuts out `Q`. -/
theorem filter_eq_of_forall_innerLevel {P : Fin L → Prop} [DecidablePred P]
    (hin : ∀ k, P (innerLevel Q hQ k)) (hcard : (univ.filter P).card = m) : univ.filter P = Q := by
  refine (eq_of_subset_of_card_le (fun ℓ hℓ => ?_) (hcard.trans hQ.symm).le).symm
  obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
  exact mem_filter.mpr ⟨mem_univ _, hin k⟩

/-! ### Gluing two strings along a set of levels -/

variable {α : Type*}








/-- At the `k`-th lowest level of `Q`, the glued string has the `k`-th letter of `f`. -/
@[simp]
theorem glue_innerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin m) :
    glue Q hQ f g (innerLevel Q hQ k) = f k := by
  rw [glue, dif_pos (innerLevel_mem Q hQ k)]
  exact congrArg f ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level outside `Q`, the glued string has the `k`-th letter of `g`. -/
@[simp]
theorem glue_outerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin (L - m)) :
    glue Q hQ f g (outerLevel Q hQ k) = g k := by
  rw [glue, dif_neg (outerLevel_notMem Q hQ k)]
  exact congrArg g ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level of a set `Q'` that is equal to `Q`, the string glued along `Q` has
the `k`-th letter of `f`. -/
private theorem glue_innerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin m) : glue Q hQ f g (innerLevel Q' hQ' k) = f k := by
  rw [innerLevel_congr Q hQ h, glue_innerLevel]

/-- At the `k`-th lowest level outside a set `Q'` that is equal to `Q`, the string glued along `Q`
has the `k`-th letter of `g`. -/
private theorem glue_outerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin (L - m)) :
    glue Q hQ f g (outerLevel Q' hQ' k) = g k := by
  rw [outerLevel_congr Q hQ h, glue_outerLevel]

variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}

/-- The glued string is the only string with the letters of `f` at the levels of `Q` and the letters
of `g` at the other levels. -/
theorem eq_glue_iff {u : Fin L → α} :
    u = glue Q hQ f g
      ↔ (∀ k, u (innerLevel Q hQ k) = f k) ∧ ∀ k, u (outerLevel Q hQ k) = g k := by
  simp only [funext_iff, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel]

/-- The two strings can be read off the glued string. -/
theorem glue_inj : glue Q hQ f g = glue Q hQ f' g' ↔ f = f' ∧ g = g' := by
  rw [eq_glue_iff]
  simp only [glue_innerLevel, glue_outerLevel, funext_iff]






/-! ### Alphabets with inner and outer letters -/

variable (IsInner : α → Prop) [DecidablePred IsInner]

/-- If the letters of `f` are inner and those of `g` are outer, then the glued string has its inner
letters exactly at the levels of `Q`. -/
theorem filter_glue (hf : ∀ k, IsInner (f k)) (hg : ∀ k, ¬ IsInner (g k)) :
    (univ.filter fun ℓ => IsInner (glue Q hQ f g ℓ)) = Q := by
  simpa only [filter_eq_iff_forall_level Q hQ, glue_innerLevel, glue_outerLevel] using
    And.intro hf hg













/-! ### Left, right and output strings with a given inner set, outer part and inner part -/















/-- The inner set of `leftStrOf Q hQ r π` is `Q`. -/
@[simp]
theorem innerSetL_leftStrOf (r : OuterStr L m) (π : InnerStr m) :
    innerSetL (leftStrOf Q hQ r π) = Q :=
  filter_glue Q hQ LeftVar.IsInner (fun _ => trivial) fun _ => id

/-- The inner set of `rightStrOf Q hQ π c` is `Q`. -/
@[simp]
theorem innerSetR_rightStrOf (π : InnerStr m) (c : OuterStr L m) :
    innerSetR (rightStrOf Q hQ π c) = Q :=
  filter_glue Q hQ RightVar.IsInner (fun _ => trivial) fun _ => id






/-- The outer part of `leftStrOf Q hQ r π` is `r`. -/
@[simp]
theorem outerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : outerPartL (leftStrOf Q hQ r π) h = r :=
  funext fun k => congrArg LeftVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `leftStrOf Q hQ r π` is `π`. -/
@[simp]
theorem innerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : innerPartL (leftStrOf Q hQ r π) h = π :=
  funext fun k => congrArg LeftVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `rightStrOf Q hQ π c` is `π`. -/
@[simp]
theorem innerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : innerPartR (rightStrOf Q hQ π c) h = π :=
  funext fun k => congrArg RightVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The outer part of `rightStrOf Q hQ π c` is `c`. -/
@[simp]
theorem outerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : outerPartR (rightStrOf Q hQ π c) h = c :=
  funext fun k => congrArg RightVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)



















variable {Q}



































variable {hQ}

/-- Left strings with the same inner set and different outer or inner parts are different. -/
theorem leftStrOf_inj {r r' : OuterStr L m} {π π' : InnerStr m} :
    leftStrOf Q hQ r π = leftStrOf Q hQ r' π' ↔ r = r' ∧ π = π' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  obtain ⟨hp, hx⟩ := (glue_inj Q hQ).mp h
  exact ⟨funext fun k => LeftVar.x.inj (congrFun hx k),
    funext fun k => Prod.ext (LeftVar.p.inj (congrFun hp k)).1 (LeftVar.p.inj (congrFun hp k)).2⟩









variable (Q) (hQ)
include hQ




































end ThreeSumApsp

end



/-!
# Lemma 9: one run of `Full` computes all the products `X_Q Y_Q`

Section 2.3.3. The inner set of a string is the set of the levels at which it has
an inner variable (`p`, `q` or `z₀`). For a set `Q` of `m` levels, the left strings with inner set
`Q` index the entries of an `N₀ × D` matrix `X_Q`, the right strings those of a `D × N₀` matrix
`Y_Q`, and the output strings those of the product `X_Q Y_Q`. The arrays `a` and `b` hold all the
`X_Q` and all the `Y_Q` side by side. Lemma 9 says that `Mult(a, b)[w] = (X_Q Y_Q)[w]` for every
output string `w` with such an inner set.

* The strings with inner set `Q` are `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and
  `outStrOf Q hQ r c` (`existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`). At
  the first two the arrays hold `X_Q[r, π]` and `Y_Q[π, c]` (`arrayL_leftStrOf`,
  `arrayR_rightStrOf`).
* The two facts about `γ` that the proof needs are finite checks on the definition of `gamma`
  (`gamma_z0`, `gamma_x_y_z`); no other lemma is used for them.
* The proof of Lemma 9. By Lemma 8 the entry at `w` is a sum over all pairs `(u, v)`. In a summand
  that is not zero, `u` has inner set `Q`, the row of `w` as its outer part and some inner part `π`,
  and `v` has inner set `Q`, the column of `w` as its outer part and the same inner part
  (`exists_of_summand_ne_zero`). Each of these summands has coefficient 1 (`prod_gamma_eq_one`).
  Their sum is the entry of the matrix product (`Mult_arrays_eq_mul`, `lemma_9`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The sizes of the matrices, and Figure 4 -/
















































/-! ### The input arrays -/

/-- The entry of the left input array at the string with inner set `Q`, outer part `r` and inner
part `π` is `X_Q[r, π]`. -/
@[simp]
theorem arrayL_leftStrOf {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (r : OuterStr L m) (π : InnerStr m) :
    arrayL m X (leftStrOf Q hQ r π) = X Q r π := by
  have h : (innerSetL (leftStrOf Q hQ r π)).card = m := by rw [innerSetL_leftStrOf, hQ]
  rw [arrayL, dif_pos h, outerPartL_leftStrOf, innerPartL_leftStrOf, innerSetL_leftStrOf]

/-- The entry of the right input array at the string with inner set `Q`, inner part `π` and outer
part `c` is `Y_Q[π, c]`. -/
@[simp]
theorem arrayR_rightStrOf {L m : ℕ} (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (π : InnerStr m) (c : OuterStr L m) :
    arrayR m Y (rightStrOf Q hQ π c) = Y Q π c := by
  have h : (innerSetR (rightStrOf Q hQ π c)).card = m := by rw [innerSetR_rightStrOf, hQ]
  rw [arrayR, dif_pos h, innerPartR_rightStrOf, outerPartR_rightStrOf, innerSetR_rightStrOf]

/-! ### The proof of Lemma 9 -/

/-- In the proof of Lemma 9: "the only monomials of G + E that contain z₀ are the p_ij q_ij
z₀, with coefficient 1." Stated for `γ(s, t, z₀)`, which is the coefficient of `s t z₀` in `G + E`
by `gamma_eq_coeff`. -/
theorem gamma_z0 (s : LeftVar) (t : RightVar) :
    gamma s t .z0 = if ∃ i j, s = .p i j ∧ t = .q i j then 1 else 0 := by
  decide +revert

/-- In the proof of Lemma 9: "The only monomial of G + E that contains z_ij and no inner
variable is x_i y_j z_ij, with coefficient 1". Stated for `γ(x_i', y_j', z_ij)`, which is the
coefficient of `x_i' y_j' z_ij` in `G + E` by `gamma_eq_coeff`. -/
theorem gamma_x_y_z (i' j' i j : Fin 3) :
    gamma (.x i') (.y j') (.z i j) = if i' = i ∧ j' = j then 1 else 0 := by
  decide +revert

/-- The statement on `γ(x_i', y_j', z_ij)` as it is used: if `s` and `t` are outer and
`γ(s, t, z_ij) ≠ 0`, then `(s, t) = (x_i, y_j)`. -/
private theorem eq_x_y_of_gamma_ne_zero {s : LeftVar} {t : RightVar} {i j : Fin 3}
    (hs : ¬ s.IsInner) (ht : ¬ t.IsInner) (h : gamma s t (.z i j) ≠ 0) : s = .x i ∧ t = .y j := by
  rcases s with i' | _
  · rcases t with j' | _
    · by_contra hne
      exact h ((gamma_x_y_z i' j' i j).trans
        (if_neg fun ⟨hi, hj⟩ => hne ⟨hi ▸ rfl, hj ▸ rfl⟩))
    · exact (ht trivial).elim
  · exact (hs trivial).elim

/-- The summands of Lemma 8 that can be nonzero. Let `w` be the output string with inner
set `Q`, row `r` and column `c`. If `γ(u_ℓ, v_ℓ, w_ℓ) ≠ 0` at every level and the inner sets of `u`
and `v` have `m` elements, then `u` has inner set `Q`, outer part `r` and some inner part `π`, and
`v` has inner set `Q`, outer part `c` and the inner part with the same indices. -/
private theorem exists_of_summand_ne_zero {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) {u : LeftStr L} {v : RightStr L}
    (hγ : ∀ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ) ≠ 0) (hu : (innerSetL u).card = m)
    (hv : (innerSetR v).card = m) : ∃ π, u = leftStrOf Q hQ r π ∧ v = rightStrOf Q hQ π c := by
  simp only [outStrOf, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel] at hγ
  obtain ⟨hγin, hγout⟩ := hγ
  -- "at a level ℓ ∈ Q we have w_ℓ = z₀ […] So (u_ℓ, v_ℓ) = (p_ij, q_ij) for some i, j."
  have hin : ∀ k, ∃ ij : Fin 2 × Fin 2,
      u (innerLevel Q hQ k) = .p ij.1 ij.2 ∧ v (innerLevel Q hQ k) = .q ij.1 ij.2 := fun k => by
    by_contra hne
    exact hγin k ((gamma_z0 _ _).trans (if_neg fun ⟨i, j, h⟩ => hne ⟨(i, j), h⟩))
  choose π hπ using hin
  -- "Thus u and v have an inner variable at every level of Q, and their inner sets are therefore
  -- exactly Q."  So "u_ℓ and v_ℓ are outer" at the levels outside Q.
  have huQ : innerSetL u = Q :=
    filter_eq_of_forall_innerLevel Q hQ (fun k => by rw [(hπ k).1]; trivial) hu
  have hvQ : innerSetR v = Q :=
    filter_eq_of_forall_innerLevel Q hQ (fun k => by rw [(hπ k).2]; trivial) hv
  have huout := ((filter_eq_iff_forall_level Q hQ).mp huQ).2
  have hvout := ((filter_eq_iff_forall_level Q hQ).mp hvQ).2
  -- "at a level ℓ ∉ Q we have w_ℓ = z_ij for some i, j […] so (u_ℓ, v_ℓ) = (x_i, y_j)."
  have hout : ∀ k, u (outerLevel Q hQ k) = .x (r k) ∧ v (outerLevel Q hQ k) = .y (c k) :=
    fun k => eq_x_y_of_gamma_ne_zero (huout k) (hvout k) (hγout k)
  exact ⟨π, (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).1, fun k => (hout k).1⟩,
    (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).2, fun k => (hout k).2⟩⟩

/-- In the proof of Lemma 9: the coefficient of the summand of `π` "is 1". -/
private theorem prod_gamma_eq_one {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) (π : InnerStr m) :
    ∏ ℓ, gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
  have hone : ∀ ℓ,
      gamma (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
    simp only [forall_level_iff Q hQ, leftStrOf, rightStrOf, outStrOf, glue_innerLevel,
      glue_outerLevel]
    exact ⟨fun _ => (gamma_z0 _ _).trans (if_pos ⟨_, _, rfl, rfl⟩),
      fun _ => (gamma_x_y_z _ _ _ _).trans (if_pos ⟨rfl, rfl⟩)⟩
  exact prod_eq_one fun ℓ _ => hone ℓ

/-- Lemma 9 for the output string with inner set `Q`, row `r` and column `c`: by Lemma 8 the entry
is a sum over all pairs `(u, v)`, and the summands that remain are those of the matrix product. -/
theorem Mult_arrays_eq_mul_sourceProof {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Mult (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  -- To show: `∑_{(u,v)} ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) a[u] b[v] = ∑_π X_Q[r, π] Y_Q[π, c]`. The right-hand
  -- side is the part of the left-hand side over the pairs `(u, v)` that belong to some `π`.
  rw [lemma_8, Matrix.mul_apply, ← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_of_injective (fun π => (leftStrOf Q hQ r π, rightStrOf Q hQ π c)) ?_ _ _ ?_ ?_
  · -- "There is one such summand for each of the D strings π".
    exact fun π π' h => (leftStrOf_inj.mp (congrArg Prod.fst h)).2
  · -- Every other summand is zero.  "a[u] b[v] ≠ 0 requires the inner sets of u and v to have
    -- exactly m elements."
    rintro ⟨u, v⟩ hnot
    by_contra hne
    obtain ⟨⟨hγ, ha⟩, hb⟩ : ((∏ ℓ, gamma (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ)) ≠ 0
        ∧ arrayL m X u ≠ 0) ∧ arrayR m Y v ≠ 0 := by
      simpa only [mul_ne_zero_iff] using hne
    obtain ⟨π, rfl, rfl⟩ := exists_of_summand_ne_zero Q hQ r c
      (fun ℓ => prod_ne_zero_iff.mp hγ ℓ (mem_univ ℓ))
      (by_contra fun h => ha (dif_neg h)) (by_contra fun h => hb (dif_neg h))
    exact hnot ⟨π, rfl⟩
  · -- The summand of `π` is `1 · X_Q[r, π] · Y_Q[π, c]`.
    intro π
    rw [prod_gamma_eq_one, one_mul, arrayL_leftStrOf, arrayR_rightStrOf]



















end ThreeSumApsp

end


theorem solution : ∀ {L m : Nat} (X : Finset.{0} (Fin L) → ThreeSumApsp.LeftMat L m) (Y : Finset.{0} (Fin L) → ThreeSumApsp.RightMat L m)
  (Q : Finset.{0} (Fin L)) (hQ : @Eq.{1} Nat (@Finset.card.{0} (Fin L) Q) m) (r c : ThreeSumApsp.OuterStr L m),
  @Eq.{1} Int
    (@ThreeSumApsp.Mult L (@ThreeSumApsp.arrayL L m X) (@ThreeSumApsp.arrayR L m Y)
      (@ThreeSumApsp.outStrOf L m Q hQ r c))
    (@HMul.hMul.{0, 0, 0} (ThreeSumApsp.LeftMat L m) (ThreeSumApsp.RightMat L m)
      (Matrix.{0, 0, 0} (ThreeSumApsp.OuterStr L m) (ThreeSumApsp.OuterStr L m) Int)
      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (ThreeSumApsp.OuterStr L m) (ThreeSumApsp.InnerStr m)
        (ThreeSumApsp.OuterStr L m) Int
        (@Pi.instFintype.{0, 0} (Fin m)
          (fun (a : Fin m) =>
            Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (instDecidableEqFin m) (Fin.fintype m) fun (a : Fin m) =>
          @instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        Int.instMul Int.instAddCommMonoid)
      (X Q) (Y Q) r c) := by
  exact @ThreeSumApsp.Mult_arrays_eq_mul_sourceProof

#print axioms solution
