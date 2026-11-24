-- Prove2me | solution 1 for ValiantBorder.gridProjections
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:16:37.650093+00:00
-- url     : https://prove2.me/submissions/7b1b8b2c-ab8f-40bd-99fb-8fc4e06b389b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_VP_VNP_all_fields
import Definitions.Def_ValiantBorder_gridComplete

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, Appendix M and the sections
on grids. Source: `anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5,
`vp-vnp/Nc/PermValiant.lean`, `Nc/Rate/Defs.lean`, `Nc/Perm{Coeff,Grid,Sum,Pad}.lean`,
`Nc/Hc/{Grid,Segments}.lean` and `Paper/{Grids,HcGrid}.lean`, Apache-2.0. -/
section
namespace Nc
open ValiantBorder Finset MvPolynomial
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_affIn (o : Option ι) : (1 : MvPolynomial ι F) ∈ affIn (F := F) o := by
  cases o
  · exact Submodule.subset_span rfl
  · exact Submodule.subset_span (by simp)

omit [Fintype ι] [DecidableEq ι] in
theorem C_mem_affIn (o : Option ι) (b : F) : (C b : MvPolynomial ι F) ∈ affIn (F := F) o := by
  have := (affIn (F := F) o).smul_mem b (one_mem_affIn o)
  rwa [MvPolynomial.smul_eq_C_mul, mul_one] at this

omit [Fintype ι] [DecidableEq ι] in
theorem isAffine_of_mem {o : Option ι} {p : MvPolynomial ι F} (h : p ∈ affIn (F := F) o) : IsAffine p := by
  cases o with
  | none =>
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 h
    exact Or.inl ⟨b, by rw [MvPolynomial.smul_eq_C_mul, mul_one]⟩
  | some i =>
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
    exact Or.inr ⟨i, a, b, by rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, mul_one]⟩

section Circuits

/-- The permanent of the generic matrix. -/
noncomputable def genPerm (F : Type*) [Field F] (S : ℕ) : MvPolynomial (Fin S × Fin S) F :=
  (Matrix.of fun i j => X (i, j) : Matrix (Fin S) (Fin S) (MvPolynomial (Fin S × Fin S) F)).permanent

omit [Fintype ι] [DecidableEq ι] in
theorem aeval_genPerm {S : ℕ} (M : Matrix (Fin S) (Fin S) (MvPolynomial ι F)) :
    aeval (fun p : Fin S × Fin S => M p.1 p.2) (genPerm F S) = M.permanent := by
  simp [genPerm, Matrix.permanent, map_sum, map_prod]

end Circuits
end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The permanent as a coefficient

The permanent of a matrix is the coefficient of the product of all variables in the product of the linear
forms given by the rows. This coefficient does not change modulo the squares of the variables.
-/

namespace Nc

open Finset MvPolynomial

variable {R : Type*} [CommRing R]

/-- The exponent of the product of all variables. -/
noncomputable def ones (C : Type*) [Fintype C] : C →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

@[simp] theorem ones_apply {C : Type*} [Fintype C] (c : C) : ones C c = 1 := rfl

section Bij

variable {C I : Type*} [Fintype C] [Fintype I]

theorem sum_single_eq_ones [DecidableEq C] (f : I → C) :
    (∑ i, Finsupp.single (f i) 1 = ones C) ↔ Function.Bijective f := by
  classical
  have hap : ∀ c, (∑ i, Finsupp.single (f i) 1 : C →₀ ℕ) c = #{i | f i = c} := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.single_apply]
  rw [Function.bijective_iff_existsUnique]
  constructor
  · intro h c
    have := hap c
    rw [h, ones_apply] at this
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 this.symm
    refine ⟨i, ?_, fun j hj => ?_⟩
    · have : i ∈ ({i | f i = c} : Finset I) := by rw [hi]; simp
      simpa using this
    · have : j ∈ ({i | f i = c} : Finset I) := by simpa using hj
      rw [hi] at this
      simpa using this
  · intro h
    ext c
    rw [hap, ones_apply, Finset.card_eq_one]
    obtain ⟨i, hi, hu⟩ := h c
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨hu j, fun e => e ▸ hi⟩

variable {N J κ : Type*} [Fintype N] [Fintype J] [Fintype κ] [DecidableEq N]

open scoped Classical in
/-- Expanding a product of sums of terms and taking the coefficient of the product of all variables. -/
theorem coeff_ones_prod (w : N → κ → R) (g : N → κ → J → C) :
    coeff (ones C) (∏ i, ∑ a, MvPolynomial.C (w i a) * ∏ j, (X (g i a j) : MvPolynomial C R)) =
      ∑ f : N → κ, if Function.Bijective (fun p : N × J => g p.1 (f p.1) p.2) then ∏ i, w i (f i)
        else 0 := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, ← Fintype.prod_prod_type'
    (f := fun i j => (X (g i (f i) j) : MvPolynomial C R))]
  have : (∏ p : N × J, (X (g p.1 (f p.1) p.2) : MvPolynomial C R)) =
      monomial (∑ p : N × J, Finsupp.single (g p.1 (f p.1) p.2) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [this, coeff_monomial]
  simp only [sum_single_eq_ones (fun p : N × J => g p.1 (f p.1) p.2)]
  split_ifs <;> simp

open scoped Classical in
theorem sum_perm_eq [DecidableEq C] (w : C → C → R) :
    ∑ σ : Equiv.Perm C, ∏ i, w i (σ i) =
      ∑ f : C → C, if Function.Bijective f then ∏ i, w i (f i) else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (i := fun f hf => Equiv.ofBijective f (Finset.mem_filter.1 hf).2)
    (j := fun σ _ => (σ : C → C)) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    exact σ.bijective
  · intros; rfl
  · intros; ext; rfl
  · intros; rfl

/-- The permanent is a coefficient. -/
theorem permanent_eq_coeff [DecidableEq C] (M : Matrix C C R) :
    M.permanent = coeff (ones C) (∏ i, ∑ j, MvPolynomial.C (M i j) * (X j : MvPolynomial C R)) := by
  classical
  have h := coeff_ones_prod (N := C) (J := Unit) (κ := C) (C := C) (fun i j => M i j) (fun _ a _ => a)
  have h2 : M.permanent = ∑ σ : Equiv.Perm C, ∏ i, M i (σ i) := by
    rw [← Matrix.permanent_transpose]
    rfl
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  rw [h, h2]
  refine (sum_perm_eq (fun i j => M i j)).trans (Finset.sum_congr rfl fun f _ => ?_)
  have hiff : Function.Bijective f ↔ Function.Bijective fun p : C × Unit => f p.1 :=
    ⟨fun hb => hb.comp (Equiv.prodPUnit C).bijective, fun hb => hb.comp (Equiv.prodPUnit C).symm.bijective⟩
  by_cases hb : Function.Bijective f
  · rw [if_pos hb, if_pos (hiff.1 hb)]
  · rw [if_neg hb, if_neg (fun h' => hb (hiff.2 h'))]

end Bij

section Squares

variable {C : Type*} [Fintype C]

variable (C R) in
/-- The ideal of the squares of the variables. -/
noncomputable def sqIdeal : Ideal (MvPolynomial C R) := Ideal.span (Set.range fun c => X c * X c)

theorem coeff_ones_of_mem {p : MvPolynomial C R} (h : p ∈ sqIdeal R C) : coeff (ones C) p = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_assoc, coeff_mul_X', coeff_mul_X']
  simp [Finsupp.mem_support_iff]

theorem coeff_ones_congr {p q : MvPolynomial C R}
    (h : Ideal.Quotient.mk (sqIdeal R C) p = Ideal.Quotient.mk (sqIdeal R C) q) :
    coeff (ones C) p = coeff (ones C) q := by
  have := coeff_ones_of_mem (Ideal.Quotient.eq.1 h)
  rwa [coeff_sub, sub_eq_zero] at this

omit [Fintype C] in
theorem mk_X_sq (c : C) : Ideal.Quotient.mk (sqIdeal R C) (X c) ^ 2 = 0 := by
  rw [sq, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨c, rfl⟩)

omit [Fintype C] in
/-- Modulo squares, a product of two linear forms in four variables has only two terms. -/
theorem mk_gadget (h : R) (hh : h * 2 = 1) (p q r s : C) :
    Ideal.Quotient.mk (sqIdeal R C)
      ((MvPolynomial.C h * X p + MvPolynomial.C h * X q + MvPolynomial.C h * X r - MvPolynomial.C h * X s) *
        (X p + X q - X r + X s)) = Ideal.Quotient.mk (sqIdeal R C) (X p * X q + X r * X s) := by
  simp only [map_mul, map_add, map_sub]
  have h1 := mk_X_sq (R := R) p
  have h2 := mk_X_sq (R := R) q
  have h3 := mk_X_sq (R := R) r
  have h4 := mk_X_sq (R := R) s
  have h5 : Ideal.Quotient.mk (sqIdeal R C) (MvPolynomial.C h) * 2 = 1 := by
    rw [← map_ofNat (Ideal.Quotient.mk (sqIdeal R C)) 2, ← map_mul, ← map_ofNat MvPolynomial.C 2,
      ← map_mul, hh, map_one, map_one]
  generalize Ideal.Quotient.mk (sqIdeal R C) (X p) = p at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X q) = q at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X r) = r at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X s) = s at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (MvPolynomial.C h) = e at *
  linear_combination e * h1 + e * h2 - e * h3 - e * h4 + (p * q + r * s) * h5

end Squares

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over two families of bits as permanents

`N` is a finite set of incidences with two permutations `σ`, `ρ`. A bit for every orbit of `σ` and a bit for
every orbit of `ρ` are summed over, and every incidence contributes a weight that depends on its two bits.
The sum is a permanent of size `3 * |N|`.
-/

namespace Nc

open Finset MvPolynomial

variable {R : Type*} [CommRing R]
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The row that is chosen at `n`: `n` itself or its successor. -/
def pick (σ : Equiv.Perm N) (s : N → Bool) (n : N) : N := if s n then n else σ n

omit [Fintype N] [DecidableEq N] in
theorem pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : ∀ n, s (σ n) = s n) :
    Function.Injective (pick σ s) := by
  intro n m e
  unfold pick at e
  rcases hn : s n <;> rcases hm : s m <;> simp only [hn, hm, if_true, if_false, Bool.false_eq_true] at e
  · exact σ.injective e
  · have := h n
    rw [e, hn, hm] at this
    cases this
  · have := h m
    rw [← e, hn, hm] at this
    cases this
  · exact e

omit [DecidableEq N] in
theorem inv_of_pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : Function.Injective (pick σ s)) (n : N) :
    s (σ n) = s n := by
  rcases hn : s n <;> rcases hm : s (σ n)
  · rfl
  · have : pick σ s n = pick σ s (σ n) := by simp [pick, hn, hm]
    have := h this
    rw [← this, hn] at hm
    cases hm
  · obtain ⟨m, hm'⟩ := (Finite.injective_iff_surjective.1 h) (σ n)
    unfold pick at hm'
    rcases hs : s m <;> simp only [hs, if_true, if_false, Bool.false_eq_true] at hm'
    · have := σ.injective hm'
      rw [this, hn] at hs
      cases hs
    · rw [hm', hm] at hs
      cases hs
  · rfl

/-- The columns used by the three rows of an incidence. -/
def slot (σ ρ : Equiv.Perm N) (n : N) (a : Bool × Bool × Bool) : Option Bool → N × Option Bool
  | none => (if a.1 then n else σ n, none)
  | some true => (n, some a.1)
  | some false => (if a.2.1 then n else ρ n, some !a.2.2)

omit [DecidableEq N] in
theorem slot_bijective (σ ρ : Equiv.Perm N) (s r q : N → Bool) :
    Function.Bijective (fun p : N × Option Bool => slot σ ρ p.1 (s p.1, r p.1, q p.1) p.2) ↔
      (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) ∧ ∀ n, s (pick ρ r n) = q n := by
  constructor
  · rintro ⟨h, -⟩
    have h3 : ∀ n, s (pick ρ r n) = q n := by
      intro n
      by_contra hne
      have : ((n, some false) : N × Option Bool) = (pick ρ r n, some true) := by
        apply h
        simp only [slot, pick] at hne ⊢
        congr 2
        revert hne
        generalize s _ = x
        generalize q n = y
        revert x y
        decide
      simp at this
    refine ⟨fun n => inv_of_pick_injective (fun n m e => ?_) n,
      fun n => inv_of_pick_injective (fun n m e => ?_) n, h3⟩
    · have : ((n, none) : N × Option Bool) = (m, none) := h (by
        simp only [slot]
        exact congrArg (fun x => (x, none)) e)
      exact (Prod.mk.inj this).1
    · have : ((n, some false) : N × Option Bool) = (m, some false) := h (by
        simp only [slot]
        rw [← h3 n, ← h3 m, e]
        exact congrArg (fun x => (x, some !s (pick ρ r m))) e)
      exact (Prod.mk.inj this).1
  · intro ⟨h1, h2, h3⟩
    rw [← Finite.injective_iff_bijective]
    have i1 := pick_injective h1
    have i2 := pick_injective h2
    rintro ⟨n, _ | _ | _⟩ ⟨m, _ | _ | _⟩ e <;> simp only [slot, Prod.mk.injEq, reduceCtorEq, and_false,
      Option.some.injEq] at e
    · rw [i1 e.1]
    · rw [i2 e.1]
    · obtain ⟨e1, e2⟩ := e
      have := h3 n
      unfold pick at this
      rw [e1] at this
      rw [this] at e2
      exact absurd e2 (by cases q n <;> decide)
    · obtain ⟨e1, e2⟩ := e
      have := h3 m
      unfold pick at this
      rw [← e1] at this
      rw [this] at e2
      exact absurd e2 (by cases q m <;> decide)
    · rw [e.1]

/-- The indicator of a column. -/
def ind (c₀ : N × Option Bool) (a : R) (c : N × Option Bool) : R := if c = c₀ then a else 0

/-- The matrix. -/
def gridMatrix (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    Matrix (N × Option Bool) (N × Option Bool) R
  | (n, none), c => ind (n, none) h c + ind (n, some true) h c + ind (σ n, none) h c - ind (n, some false) h c
  | (n, some true), c =>
    ind (n, none) 1 c + ind (n, some true) 1 c - ind (σ n, none) 1 c + ind (n, some false) 1 c
  | (n, some false), c =>
    ind (n, some false) (W n true true) c + ind (n, some true) (W n false true) c +
      ind (ρ n, some false) (W (ρ n) true false) c + ind (ρ n, some true) (W (ρ n) false false) c

theorem sum_ind (c₀ : N × Option Bool) (a : R) :
    ∑ c, MvPolynomial.C (ind c₀ a c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C a * X c₀ := by
  simp [ind, apply_ite MvPolynomial.C, ite_mul]

/-- The weight of a choice. -/
def wt (ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) (a : Bool × Bool × Bool) : R :=
  if a.2.1 then W n a.2.2 true else W (ρ n) a.2.2 false

theorem sum_row_none (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, none) c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C h * X (n, none) + MvPolynomial.C h * X (n, some true) +
        MvPolynomial.C h * X (σ n, none) - MvPolynomial.C h * X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind]

theorem sum_row_true (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, some true) c) * (X c : MvPolynomial (N × Option Bool) R) =
      X (n, none) + X (n, some true) - X (σ n, none) + X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind, map_one, one_mul]

theorem sum_row_false (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, some false) c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C (W n true true) * X (n, some false) + MvPolynomial.C (W n false true) * X (n, some true) +
        MvPolynomial.C (W (ρ n) true false) * X (ρ n, some false) +
        MvPolynomial.C (W (ρ n) false false) * X (ρ n, some true) := by
  simp only [gridMatrix, map_add, add_mul, Finset.sum_add_distrib, sum_ind]

theorem gridMatrix_permanent_aux (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = coeff (ones (N × Option Bool))
      (∏ n, ∑ a, MvPolynomial.C (wt ρ W n a) * ∏ j, (X (slot σ ρ n a j) : MvPolynomial (N × Option Bool) R)) := by
  rw [permanent_eq_coeff]
  apply coeff_ones_congr
  rw [Fintype.prod_prod_type, map_prod, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  simp only [Fintype.prod_option, Fintype.prod_bool]
  rw [sum_row_none, sum_row_true, sum_row_false, ← mul_assoc, map_mul, mk_gadget h hh, ← map_mul]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slot, wt, if_true, if_false, Bool.false_eq_true,
    Bool.not_true, Bool.not_false]
  ring

open scoped Classical in
theorem gridMatrix_permanent (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = ∑ s : N → Bool, ∑ r : N → Bool,
      if (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) then ∏ n, W n (s n) (r n) else 0 := by
  classical
  rw [gridMatrix_permanent_aux h hh, coeff_ones_prod]
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool × Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single (fun n => s (pick ρ r n))]
  · have key := slot_bijective σ ρ s r (fun n => s (pick ρ r n))
    simp only [implies_true, and_true] at key
    by_cases hc : (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n)
    · rw [if_pos hc]
      refine (if_pos (key.2 hc)).trans ?_
      have e1 : ∀ n, wt ρ W n (s n, r n, s (pick ρ r n)) =
          (if r n then W n (s n) (r n) else 1) *
            (if r (ρ n) then 1 else W (ρ n) (s (ρ n)) (r (ρ n))) := by
        intro n
        rw [hc.2 n]
        rcases hr : r n <;> simp [wt, pick, hr]
      refine (Finset.prod_congr rfl fun n _ => e1 n).trans ?_
      rw [Finset.prod_mul_distrib, Equiv.prod_comp ρ (fun n => if r n then 1 else W n (s n) (r n)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun n _ => ?_
      split_ifs <;> simp
    · rw [if_neg hc]
      exact if_neg fun hb => hc (key.1 hb)
  · intro q _ hq
    apply if_neg
    intro hb
    apply hq
    have := (slot_bijective σ ρ s r q).1 hb
    funext n
    exact (this.2.2 n).symm
  · intro hc
    exact absurd (mem_univ _) hc

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over two families of bits, indexed by maps

The permutations of the grid are replaced by maps: all incidences with the same value of a map share a bit.
-/

namespace Nc

open Finset MvPolynomial

section Fibres

variable {N V : Type*} [Fintype N] [DecidableEq N]

/-- A permutation whose cycles are the fibres of a map. -/
theorem exists_perm_fibres (v : N → V) : ∃ σ : Equiv.Perm N, (∀ n, v (σ n) = v n) ∧
    ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m := by
  classical
  have h : ∀ y, ∃ f : Equiv.Perm {n // v n = y}, f.IsCycleOn ((univ : Finset {n // v n = y}) : Set _) :=
    fun y => (Finset.exists_cycleOn univ).imp fun f hf => hf.1
  choose f hf using h
  let e := Equiv.sigmaFiberEquiv v
  let σ : Equiv.Perm N := (e.symm.trans (Equiv.sigmaCongrRight f)).trans e
  have hσ : ∀ n, σ n = (f (v n) ⟨n, rfl⟩).1 := fun n => rfl
  refine ⟨σ, fun n => ?_, fun s hs n m e => ?_⟩
  · rw [hσ]
    exact (f (v n) ⟨n, rfl⟩).2
  · have h1 : ∀ y, ∀ x : {n // v n = y}, s (f y x).1 = s x.1 := by
      rintro y ⟨x, rfl⟩
      rw [← hσ]
      exact hs x
    obtain ⟨i, -, hi⟩ := (hf (v m)).exists_pow_eq (mem_univ ⟨n, e⟩) (mem_univ ⟨m, rfl⟩)
    have h2 : ∀ i : ℕ, s ((f (v m) ^ i) ⟨n, e⟩).1 = s n := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]
    rw [← h2 i, hi]

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- A sum over the functions that are constant on the fibres. -/
theorem sum_invariant [Fintype V] [DecidableEq V] {v : N → V} (hv : Function.Surjective v) {σ : Equiv.Perm N}
    (h1 : ∀ n, v (σ n) = v n)
    (h2 : ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m) (Φ : (N → Bool) → R) :
    ∑ s : N → Bool, (if ∀ n, s (σ n) = s n then Φ s else 0) = ∑ x : V → Bool, Φ fun n => x (v n) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ n => x (v n)) ?_ ?_ ?_ ?_
  · intro x _
    simp [h1]
  · intro x _ y _ e
    exact hv.injective_comp_right e
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    refine ⟨fun y => s (Function.surjInv hv y), mem_univ _, ?_⟩
    funext n
    exact h2 s hs _ _ (Function.surjInv_eq hv _)
  · intros
    rfl

/-- A sum over two families of bits is a permanent. -/
theorem exists_grid {K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] (v : N → V) (w : N → K)
    (hv : Function.Surjective v) (hw : Function.Surjective w) :
    ∃ σ ρ : Equiv.Perm N, (∀ n, w (ρ n) = w n) ∧ ∀ (h : R) (_ : h * 2 = 1) (W : N → Bool → Bool → R),
      (gridMatrix h σ ρ W).permanent =
        ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  obtain ⟨σ, s1, s2⟩ := exists_perm_fibres v
  obtain ⟨ρ, r1, r2⟩ := exists_perm_fibres w
  refine ⟨σ, ρ, r1, fun h hh W => ?_⟩
  rw [gridMatrix_permanent h hh]
  refine Eq.trans ?_ (sum_invariant hv s1 s2 fun s => ∑ r : K → Bool, ∏ n, W n (s n) (r (w n)))
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ n, s (σ n) = s n
  · rw [if_pos hs]
    refine Eq.trans ?_ (sum_invariant hw r1 r2 fun r => ∏ n, W n (s n) (r n))
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hs]
  · rw [if_neg hs]
    exact Finset.sum_eq_zero fun r _ => if_neg fun hc => hs hc.1

end Fibres

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The permanent under renaming and padding
-/

namespace Nc

open Finset

variable {R : Type*} [CommSemiring R]
variable {C D E : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem permanent_submatrix_equiv (e : D ≃ C) (M : Matrix C C R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv e.permCongr _ _ fun σ => ?_
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Matrix.submatrix_apply, Equiv.permCongr_apply]

/-- A diagonal of ones does not change the permanent. -/
theorem permanent_pad (M : Matrix C C R) :
    (Matrix.fromBlocks M 0 0 (1 : Matrix E E R)).permanent = M.permanent := by
  unfold Matrix.permanent
  symm
  refine Finset.sum_of_injOn (fun τ => Equiv.Perm.sumCongr τ 1) ?_ ?_ ?_ ?_
  · intro τ _ τ' _ e
    have := Equiv.Perm.sumCongrHom_injective (α := C) (β := E) (a₁ := (τ, 1)) (a₂ := (τ', 1)) e
    exact (Prod.mk.inj this).1
  · intro τ _
    simp
  · intro σ _ hσ
    by_contra hne
    apply hσ
    have hfix : ∀ k : E, σ (Sum.inr k) = Sum.inr k := by
      intro k
      by_contra hk
      apply hne
      refine Finset.prod_eq_zero (mem_univ (Sum.inr k)) ?_
      rcases hs : σ (Sum.inr k) with c | e
      · rw [Matrix.fromBlocks_apply₁₂]
        rfl
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_ne]
        rintro rfl
        exact hk hs
    have hmaps : Set.MapsTo σ (Set.range (Sum.inl : C → C ⊕ E)) (Set.range Sum.inl) := by
      rintro _ ⟨c, rfl⟩
      rcases hs : σ (Sum.inl c) with c' | e
      · exact ⟨c', rfl⟩
      · have := σ.injective (hs.trans (hfix e).symm)
        cases this
    obtain ⟨⟨τ, κ⟩, rfl⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    have : κ = 1 := by
      ext k
      have := hfix k
      simpa using this
    subst this
    exact ⟨τ, by simp, rfl⟩
  · intro τ _
    rw [Fintype.prod_sum_type]
    simp

/-- A square matrix sits in every larger one with the same permanent. -/
theorem exists_permanent_fin (M : Matrix C C R) {S : ℕ} (hS : Fintype.card C ≤ S) :
    ∃ M' : Matrix (Fin S) (Fin S) R, M'.permanent = M.permanent ∧
      ∀ i j, (M' i j = 0 ∨ M' i j = 1) ∨ ∃ c d, M' i j = M c d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hS
  let e : Fin (Fintype.card C + k) ≃ C ⊕ Fin k :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _))
  refine ⟨(Matrix.fromBlocks M 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e, ?_, fun i j => ?_⟩
  · rw [permanent_submatrix_equiv, permanent_pad]
  · rw [Matrix.submatrix_apply]
    rcases e i with c | a <;> rcases e j with d | b
    · exact Or.inr ⟨c, d, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Rows of segments joined by exclusive-or gadgets

A row of segments is closed to a cycle. Every segment offers some options, and each option is a path from the head of
the segment to the head of the next one. An exclusive-or gadget has three vertices, two tips and a middle one, with
edges both ways between each tip and the middle. It joins two options: one runs through it in one direction, the
other in the opposite one. The cycles through all vertices correspond to the selections of one option in every
segment that use every gadget exactly once.
-/

namespace Nc.Hc

open Finset

/-- The sum over the cycles through all points of a finite set of the products of the weights of their edges. -/
noncomputable def hcSum {R : Type*} [CommSemiring R] {A : Type*} [Fintype A] [DecidableEq A] (M : A → A → R) : R :=
  open Classical in ∑ σ : Equiv.Perm A with σ.IsCycleOn Set.univ, ∏ a, M a (σ a)

/-- A vertex of the graph: the head of a segment, or one of the three vertices of a gadget. -/
inductive Vtx (I G : Type*) where
  | head (i : I)
  | tip (g : G) (s : Bool)
  | mid (g : G)
  deriving DecidableEq

namespace Vtx

variable {I G : Type*}

/-- The vertices as a disjoint union. -/
def equivSum : Vtx I G ≃ I ⊕ (G × Bool) ⊕ G where
  toFun
    | head i => .inl i
    | tip g s => .inr (.inl (g, s))
    | mid g => .inr (.inr g)
  invFun
    | .inl i => head i
    | .inr (.inl (g, s)) => tip g s
    | .inr (.inr g) => mid g
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩ | _) <;> rfl

instance [Fintype I] [Fintype G] : Fintype (Vtx I G) := Fintype.ofEquiv _ equivSum.symm

/-- There is one vertex for every segment and three for every gadget. -/
theorem card_eq [Fintype I] [Fintype G] : Fintype.card (Vtx I G) = Fintype.card I + 3 * Fintype.card G := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  ring

end Vtx

/-- A row of segments with gadgets: the successor of each segment, and for each gadget and each of its two sides the
option that runs through the gadget on this side. -/
structure Row {I : Type*} (O : I → Type*) (G : Type*) where
  /-- the next segment -/
  next : Equiv.Perm I
  /-- the option through a side of a gadget -/
  port : G × Bool → Σ i, O i

namespace Row

variable {I G : Type*} {O : I → Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
  [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)] (T : Row O G)

/-- The number of gadgets on an option. -/
def len (o : Σ i, O i) : ℕ := Fintype.card {p // T.port p = o}

/-- The place of a side of a gadget on its option: the gadgets of an option are put in some order. -/
noncomputable def slot : G × Bool ≃ Σ o, Fin (T.len o) :=
  (Equiv.sigmaFiberEquiv T.port).symm.trans (Equiv.sigmaCongrRight fun _ => Fintype.equivFin _)

omit [Fintype I] [∀ i, Fintype (O i)] [DecidableEq G] in
theorem slot_fst (p : G × Bool) : (T.slot p).1 = T.port p := rfl

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem port_slot_symm (o : Σ i, O i) (j : Fin (T.len o)) : T.port (T.slot.symm ⟨o, j⟩) = o := by
  rw [← T.slot_fst, Equiv.apply_symm_apply]

/-- The entry of the gadget in place j on an option; behind the last gadget, the head of the next segment. -/
noncomputable def place (o : Σ i, O i) (j : ℕ) : Vtx I G :=
  if h : j < T.len o then Vtx.tip (T.slot.symm ⟨o, j, h⟩).1 (T.slot.symm ⟨o, j, h⟩).2 else Vtx.head (T.next o.1)

/-- The vertex that follows a side of a gadget on its option. -/
noncomputable def after (p : G × Bool) : Vtx I G := T.place (T.slot p).1 (((T.slot p).2 : ℕ) + 1)

/-- The edges. -/
def Edge : Vtx I G → Vtx I G → Prop
  | .head i, q => ∃ o : O i, q = T.place ⟨i, o⟩ 0
  | .tip g s, q => q = .mid g ∨ q = T.after (g, !s)
  | .mid g, q => ∃ s, q = .tip g s

open Classical in
/-- The weights of the edges: the first edge of an option carries the weight of the option, every other edge 1. -/
noncomputable def weight {R : Type*} [CommSemiring R] (w : ∀ i, O i → R) : Vtx I G → Vtx I G → R
  | .head i, q => ∑ o : O i with T.place ⟨i, o⟩ 0 = q, w i o
  | p, q => if T.Edge p q then 1 else 0

/-- No two options of one segment avoid all gadgets. -/
def NoParallel : Prop :=
  ∀ i (o o' : O i), (∀ p, T.port p ≠ ⟨i, o⟩) → (∀ p, T.port p ≠ ⟨i, o'⟩) → o = o'

/-- The option at a side of a gadget is selected. -/
def Sel (J : ∀ i, O i) (p : G × Bool) : Prop := J (T.port p).1 = (T.port p).2

/-- A selection uses every gadget exactly once. -/
def Valid (J : ∀ i, O i) : Prop := ∀ g, T.Sel J (g, true) ↔ ¬ T.Sel J (g, false)

open Classical in
/-- The side of a gadget that is used by a selection. -/
noncomputable def side (J : ∀ i, O i) (g : G) : Bool := decide (T.Sel J (g, true))

/-- The successor of a vertex, for a selection and one side for every gadget. -/
noncomputable def route (J : ∀ i, O i) (d : G → Bool) : Vtx I G → Vtx I G
  | .head i => T.place ⟨i, J i⟩ 0
  | .tip g s => if d g = s then .mid g else T.after (g, !s)
  | .mid g => .tip g (!d g)

variable {T}

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)] in
theorem sel_iff {J : ∀ i, O i} (h : T.Valid J) (g : G) (s : Bool) : T.Sel J (g, s) ↔ T.side J g = s := by
  have := h g
  unfold side
  cases s <;> simp
  tauto

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)] in
theorem sel_eq {J : ∀ i, O i} {p : G × Bool} (h : T.Sel J p) :
    T.port p = ⟨(T.port p).1, J (T.port p).1⟩ :=
  Sigma.ext rfl (heq_of_eq h.symm)

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem sel_slot_symm (J : ∀ i, O i) (i : I) (j : Fin (T.len ⟨i, J i⟩)) :
    T.Sel J (T.slot.symm ⟨⟨i, J i⟩, j⟩) := by
  unfold Sel
  rw [T.port_slot_symm]

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem after_slot_symm (o : Σ i, O i) (j : Fin (T.len o)) :
    T.after (T.slot.symm ⟨o, j⟩) = T.place o ((j : ℕ) + 1) := by
  unfold after
  rw [Equiv.apply_symm_apply]

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem place_len (o : Σ i, O i) : T.place o (T.len o) = .head (T.next o.1) := dif_neg (lt_irrefl _)

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- The successor along a selection is always an edge. -/
theorem edge_route (J : ∀ i, O i) (d : G → Bool) (p : Vtx I G) : T.Edge p (T.route J d p) := by
  rcases p with i | ⟨g, s⟩ | g
  · exact ⟨J i, rfl⟩
  · simp only [route]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact ⟨_, rfl⟩

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- The first edges of different options of one segment differ. -/
theorem place_zero_injective (h : T.NoParallel) {i : I} {o o' : O i}
    (e : T.place ⟨i, o⟩ 0 = T.place ⟨i, o'⟩ 0) : o = o' := by
  unfold place at e
  split_ifs at e with h1 h2 h3
  · simp only [Vtx.tip.injEq] at e
    have := congrArg T.port (Prod.ext e.1 e.2)
    rw [T.port_slot_symm, T.port_slot_symm] at this
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2
  · have hno : ∀ o : Σ i, O i, ¬ 0 < T.len o → ∀ p, T.port p ≠ o := fun o ho p hp =>
      ho (Fintype.card_pos_iff.2 ⟨⟨p, hp⟩⟩)
    exact h i o o' (hno _ h1) (hno _ h3)

/-! ## From a selection to a cycle -/

omit [DecidableEq G] [∀ i, Fintype (O i)] in
/-- Following a selection that uses every gadget exactly once, one
comes from the head of any segment to every vertex. -/
theorem route_reaches (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i} (hJ : T.Valid J) (i₀ : I) (v : Vtx I G) :
    ∃ m, (T.route J (T.side J))^[m] (.head i₀) = v := by
  set f := T.route J (T.side J)
  let Rch : Vtx I G → Prop := fun v => ∃ m, f^[m] (.head i₀) = v
  have hstep : ∀ v, Rch v → Rch (f v) := by
    rintro v ⟨m, rfl⟩
    exact ⟨m + 1, Function.iterate_succ_apply' f m _⟩
  have hchain : ∀ i, Rch (.head i) → ∀ j ≤ T.len ⟨i, J i⟩, Rch (T.place ⟨i, J i⟩ j) := by
    intro i hi j
    induction j with
    | zero => exact fun _ => hstep _ hi
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      rw [place, dif_pos (show j < _ by omega)] at h
      generalize hp : T.slot.symm ⟨⟨i, J i⟩, ⟨j, by omega⟩⟩ = p at h
      have hs : T.side J p.1 = p.2 := (sel_iff hJ p.1 p.2).1 (hp ▸ sel_slot_symm J i _)
      have h3 := hstep _ (hstep _ (hstep _ h))
      have e : f (f (f (.tip p.1 p.2))) = T.after p := by
        simp only [f, route, hs, if_true, Bool.not_not]
        rw [if_neg (by cases p.2 <;> simp)]
      rw [e, ← hp, after_slot_symm] at h3
      exact h3
  have hheads : ∀ i, Rch (.head i) := by
    intro i
    obtain ⟨m, hm⟩ := (hnext.2 (Set.mem_univ i₀) (Set.mem_univ i)).exists_nat_pow_eq
    rw [← hm]
    clear hm
    induction m with
    | zero => exact ⟨0, rfl⟩
    | succ m ih =>
      have h := hchain _ ih _ le_rfl
      rw [place_len] at h
      rwa [pow_succ', Equiv.Perm.mul_apply]
  have hgad : ∀ g, Rch (.tip g (T.side J g)) ∧ Rch (.mid g) ∧ Rch (.tip g (!T.side J g)) := by
    intro g
    have hsel : T.Sel J (g, T.side J g) := (sel_iff hJ g _).2 rfl
    obtain ⟨⟨o, j⟩, e⟩ : ∃ q, T.slot.symm q = (g, T.side J g) := T.slot.symm.surjective _
    have ho : o = ⟨o.1, J o.1⟩ := by
      have h1 : T.port (g, T.side J g) = o := by rw [← e, T.port_slot_symm]
      exact h1 ▸ sel_eq hsel
    have h := hchain o.1 (hheads o.1) (j : ℕ) (by rw [← ho]; exact j.2.le)
    rw [← ho, place, dif_pos j.2, Fin.eta, e] at h
    have h2 := hstep _ h
    have e1 : f (.tip g (T.side J g)) = .mid g := by simp [f, route]
    rw [e1] at h2
    exact ⟨h, h2, hstep _ h2⟩
  rcases v with i | ⟨g, s⟩ | g
  · exact hheads i
  · by_cases hs : s = T.side J g
    · exact hs ▸ (hgad g).1
    · have : s = !T.side J g := by revert hs; cases s <;> cases T.side J g <;> simp
      exact this ▸ (hgad g).2.2
  · exact (hgad g).2.1

omit [DecidableEq G] [∀ i, Fintype (O i)] in
/-- Following such a selection is a permutation of the vertices. -/
theorem route_bijective (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i} (hJ : T.Valid J) :
    Function.Bijective (T.route J (T.side J)) := by
  refine Finite.surjective_iff_bijective.1 fun v => ?_
  rcases v with i | ⟨g, s⟩ | g
  · -- the head is the end of the option selected in the segment before it
    set i' := T.next.symm i with hi'
    by_cases h : T.len ⟨i', J i'⟩ = 0
    · refine ⟨.head i', ?_⟩
      change T.place ⟨i', J i'⟩ 0 = _
      rw [show (0 : ℕ) = T.len ⟨i', J i'⟩ from h.symm, place_len]
      simp [hi']
    · let j : Fin (T.len ⟨i', J i'⟩) := ⟨T.len ⟨i', J i'⟩ - 1, by omega⟩
      generalize hp : T.slot.symm ⟨⟨i', J i'⟩, j⟩ = p
      have hs : T.side J p.1 = p.2 := (sel_iff hJ p.1 p.2).1 (hp ▸ sel_slot_symm J i' j)
      refine ⟨.tip p.1 (!p.2), ?_⟩
      simp only [route, hs, Bool.not_not]
      rw [if_neg (by cases p.2 <;> simp), ← hp, after_slot_symm, show (j : ℕ) + 1 = T.len ⟨i', J i'⟩ by
        simp only [j]; omega, place_len]
      simp [hi']
  all_goals
    obtain ⟨i₀, -⟩ := T.port (g, true)
  · obtain ⟨_ | m, hm⟩ := route_reaches hnext hJ i₀ (.tip g s)
    · cases hm
    · exact ⟨_, (Function.iterate_succ_apply' _ m _).symm.trans hm⟩
  · obtain ⟨_ | m, hm⟩ := route_reaches hnext hJ i₀ (.mid g)
    · cases hm
    · exact ⟨_, (Function.iterate_succ_apply' _ m _).symm.trans hm⟩

/-- The cycle of a selection. -/
noncomputable def routePerm (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i} (hJ : T.Valid J) :
    Equiv.Perm (Vtx I G) :=
  Equiv.ofBijective _ (route_bijective hnext hJ)

omit [DecidableEq G] [∀ i, Fintype (O i)] in
/-- It is one cycle through all vertices. -/
theorem routePerm_isCycleOn (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i} (hJ : T.Valid J) :
    (routePerm hnext hJ).IsCycleOn Set.univ := by
  refine ⟨Set.bijOn_univ.2 (Equiv.bijective _), ?_⟩
  intro u _ v _
  obtain ⟨i₀⟩ : Nonempty I := by
    rcases u with i | ⟨g, _⟩ | g
    exacts [⟨i⟩, ⟨(T.port (g, true)).1⟩, ⟨(T.port (g, true)).1⟩]
  have key : ∀ v, (routePerm hnext hJ).SameCycle (.head i₀) v := by
    intro v
    obtain ⟨m, hm⟩ := route_reaches hnext hJ i₀ v
    refine ⟨m, ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    exact hm
  exact (key u).symm.trans (key v)

/-! ## From a cycle to a selection -/

variable {σ : Equiv.Perm (Vtx I G)}

/-- In one cycle through all vertices, no two vertices are a cycle of their own if there is a third one. -/
theorem not_two_cycle {A : Type*} [Finite A] {τ : Equiv.Perm A} (hτ : τ.IsCycleOn Set.univ) {a b c : A}
    (hca : c ≠ a) (hcb : c ≠ b) (h : τ a = b) : τ b ≠ a := by
  intro h'
  obtain ⟨m, hm⟩ := (hτ.2 (Set.mem_univ a) (Set.mem_univ c)).exists_nat_pow_eq
  have : (τ ^ m) a = a ∨ (τ ^ m) a = b := by
    clear hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with e | e <;> rw [e] <;> [exact Or.inr h; exact Or.inl h']
  rw [hm] at this
  exact this.elim hca hcb

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem place_ne_mid (o : Σ i, O i) (j : ℕ) (g : G) : T.place o j ≠ .mid g := by
  unfold place
  split_ifs <;> simp

omit [DecidableEq G] [∀ i, Fintype (O i)] in
/-- A cycle through all vertices runs through every gadget in one of two
ways: from one tip over the middle to the other tip, and then on along the option of that side. -/
theorem exists_traverse (hσ : σ.IsCycleOn Set.univ) (he : ∀ p, T.Edge p (σ p)) (g : G) :
    ∃ s, σ (.tip g s) = .mid g ∧ σ (.mid g) = .tip g (!s) ∧ σ (.tip g (!s)) = T.after (g, s) := by
  obtain ⟨t, ht⟩ := he (.mid g)
  refine ⟨!t, ?_⟩
  rw [Bool.not_not]
  have h2 : σ (.tip g t) ≠ .mid g :=
    not_two_cycle hσ (c := .tip g (!t)) (by simp) (by simp) ht
  have h3 : σ (.tip g (!t)) = .mid g := by
    obtain ⟨v, hv⟩ := σ.surjective (.mid g)
    have hev := he v
    rw [hv] at hev
    rcases v with i | ⟨g', s⟩ | g'
    · obtain ⟨o, ho⟩ := hev
      exact absurd ho.symm (place_ne_mid _ _ _)
    · rcases hev with e | e
      · obtain rfl : g = g' := Vtx.mid.inj e
        have : s = !t := by
          revert h2 hv
          cases s <;> cases t <;> simp +contextual
        exact this ▸ hv
      · exact absurd e.symm (place_ne_mid _ _ _)
    · obtain ⟨s, e⟩ := hev
      cases e
  exact ⟨h3, ht, (he (.tip g t)).resolve_left h2⟩

omit [DecidableEq G] [∀ i, Fintype (O i)] in
/-- In a cycle through all vertices every option that is entered at
the head of its segment is followed to its end, and every gadget lies on exactly one of these options. So the cycle
is the one of a selection that uses every gadget exactly once. -/
theorem exists_selection (hσ : σ.IsCycleOn Set.univ) (he : ∀ p, T.Edge p (σ p)) :
    ∃ J, T.Valid J ∧ ∀ p, σ p = T.route J (T.side J) p := by
  choose J hJ using fun i => (he (.head i) : ∃ o : O i, _)
  choose d hd using exists_traverse hσ he
  have hrouteD : ∀ p, σ p = T.route J d p := by
    rintro (i | ⟨g, s⟩ | g)
    · exact hJ i
    · simp only [route]
      split_ifs with h
      · exact h ▸ (hd g).1
      · have : s = !d g := by revert h; cases s <;> cases d g <;> simp
        rw [this, Bool.not_not]
        exact (hd g).2.2
    · exact (hd g).2.1
  have hactive : ∀ g s v, σ v = .tip g s → v ≠ .mid g → d g = s := by
    intro g s v hv hne
    by_contra hs
    have : s = !d g := by revert hs; cases s <;> cases d g <;> simp
    exact hne (σ.injective (hv.trans (this ▸ (hd g).2.1).symm))
  have hchosen : ∀ i (j : ℕ) (hj : j < T.len ⟨i, J i⟩),
      d (T.slot.symm ⟨⟨i, J i⟩, j, hj⟩).1 = (T.slot.symm ⟨⟨i, J i⟩, j, hj⟩).2 := by
    intro i j
    induction j with
    | zero =>
      intro hj
      refine hactive _ _ (.head i) ?_ (by simp)
      rw [hJ i, place, dif_pos hj]
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      generalize hp : T.slot.symm ⟨⟨i, J i⟩, j, by omega⟩ = p at h
      refine hactive _ _ (.tip p.1 (!p.2)) ?_ (by simp)
      rw [hrouteD, route, if_neg (by rw [h]; cases p.2 <;> simp), Bool.not_not, ← hp, after_slot_symm, place,
        dif_pos hj]
  have hsel : ∀ p, T.Sel J p → d p.1 = p.2 := by
    intro p hp
    obtain ⟨⟨o, j⟩, rfl⟩ := T.slot.symm.surjective p
    have ho := sel_eq hp
    rw [T.port_slot_symm] at ho
    obtain ⟨i, a⟩ := o
    obtain rfl : a = J i := eq_of_heq (Sigma.mk.inj_iff.1 ho).2
    exact hchosen i j j.2
  have hall : ∀ g, T.Sel J (g, d g) := by
    intro g
    let A : Vtx I G → Prop
      | .head _ => True
      | .tip g _ => T.Sel J (g, d g)
      | .mid g => T.Sel J (g, d g)
    have hplace : ∀ i j, A (T.place ⟨i, J i⟩ j) := by
      intro i j
      unfold place
      split_ifs with h
      · simp only [A]
        rw [hchosen i j h]
        exact sel_slot_symm J i _
      · trivial
    have hstep : ∀ v, A v → A (σ v) := by
      rintro (i | ⟨g', s⟩ | g') hv
      · rw [hJ i]
        exact hplace i 0
      · rw [hrouteD, route]
        split_ifs with h
        · exact hv
        · have : (!s) = d g' := by revert h; cases s <;> cases d g' <;> simp
          have hs : (T.slot (g', !s)).1 = ⟨(T.port (g', !s)).1, J (T.port (g', !s)).1⟩ :=
            (T.slot_fst _).trans (sel_eq (this ▸ hv))
          unfold after
          generalize ((T.slot (g', !s)).2 : ℕ) + 1 = j
          rw [hs]
          exact hplace _ _
      · rw [(hd g').2.1]
        exact hv
    obtain ⟨m, hm⟩ :=
      (hσ.2 (Set.mem_univ (Vtx.head (T.port (g, true)).1)) (Set.mem_univ (Vtx.mid g))).exists_nat_pow_eq
    have : ∀ m : ℕ, A ((σ ^ m) (.head (T.port (g, true)).1)) := by
      intro m
      induction m with
      | zero => trivial
      | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hstep _ ih
    have h := this m
    rw [hm] at h
    exact h
  have hiff : ∀ g s, T.Sel J (g, s) ↔ d g = s := fun g s => ⟨hsel (g, s), fun h => h ▸ hall g⟩
  have hv : T.Valid J := fun g => by rw [hiff, hiff]; cases d g <;> simp
  refine ⟨J, hv, fun p => ?_⟩
  rw [hrouteD, show T.side J = d from funext fun g => (sel_iff hv g _).1 (hall g)]

/-! ## The sum -/

/-- The sum over the cycles through all vertices of the products of the edge
weights is the sum over the selections that use every gadget exactly once of the products of the weights of the
selected options, provided that no two options of one segment avoid all gadgets. -/
theorem hcSum_weight {R : Type*} [CommSemiring R] (hnext : T.next.IsCycleOn Set.univ) (hpar : T.NoParallel)
    (w : ∀ i, O i → R) [DecidablePred T.Valid] :
    hcSum (T.weight w) = ∑ J : ∀ i, O i with T.Valid J, ∏ i, w i (J i) := by
  classical
  unfold hcSum
  rw [← Finset.sum_filter_of_ne (p := fun σ : Equiv.Perm (Vtx I G) => ∀ p, T.Edge p (σ p))]
  swap
  · intro σ _ hne p
    by_contra hp
    refine hne (Finset.prod_eq_zero (mem_univ p) ?_)
    rcases p with i | ⟨g, s⟩ | g
    · simp only [weight]
      refine Finset.sum_eq_zero fun o ho => absurd ⟨o, ?_⟩ hp
      exact (mem_filter.1 ho).2.symm
    all_goals exact if_neg hp
  rw [Finset.filter_filter]
  symm
  refine Finset.sum_bij (fun J hJ => routePerm hnext (mem_filter.1 hJ).2) ?_ ?_ ?_ ?_
  · intro J hJ
    exact mem_filter.2 ⟨mem_univ _, routePerm_isCycleOn _ _, fun p => edge_route J _ p⟩
  · intro J hJ J' hJ' e
    funext i
    exact place_zero_injective hpar (DFunLike.congr_fun e (Vtx.head i))
  · intro σ hσ
    obtain ⟨-, hc, he⟩ := mem_filter.1 hσ
    obtain ⟨J, hv, hp⟩ := exists_selection hc he
    exact ⟨J, mem_filter.2 ⟨mem_univ _, hv⟩, Equiv.ext fun p => (hp p).symm⟩
  · intro J hJ
    have hv := (mem_filter.1 hJ).2
    rw [← Vtx.equivSum.symm.prod_comp, Fintype.prod_sum_type]
    have h1 : ∀ i, T.weight w (.head i) (routePerm hnext hv (.head i)) = w i (J i) := by
      intro i
      simp only [weight]
      refine Finset.sum_eq_single_of_mem (J i) (mem_filter.2 ⟨mem_univ _, rfl⟩) fun o ho hne => ?_
      exact absurd (place_zero_injective hpar (mem_filter.1 ho).2) hne
    have h2 : ∀ p : (G × Bool) ⊕ G, T.weight w (Vtx.equivSum.symm (.inr p))
        (routePerm hnext hv (Vtx.equivSum.symm (.inr p))) = 1 := by
      rintro (⟨g, s⟩ | g)
      · exact if_pos (edge_route J _ (.tip g s))
      · exact if_pos (edge_route J _ (.mid g))
    rw [Finset.prod_congr rfl fun p _ => h2 p, Finset.prod_const_one, mul_one]
    exact Finset.prod_congr rfl fun i _ => (h1 i).symm

end Row

end Nc.Hc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Grid completeness of the permanent and of the Hamiltonian cycle polynomial

A sum over two families of bits of products of weights, one for every incidence, is a Hamiltonian cycle polynomial
with affine entries, in every characteristic. For every incidence there are seven segments and ten gadgets.
-/

namespace Nc

open Finset MvPolynomial

namespace Hc

/-- The segments of a grid: one for every bit of the two families; for every incidence the one that chooses the
weight, one for each of the two sides and one for each of the four pairs of bits; and some for padding. -/
inductive Seg (N V K P : Type) where
  | var (a : V)
  | row (b : K)
  | edge (n : N)
  | left (n : N)
  | right (n : N)
  | tab (n : N) (t : Bool × Bool)
  | pad (p : P)
  deriving DecidableEq

variable {N V K P : Type}

/-- The segments as a disjoint union. -/
def Seg.equivSum : Seg N V K P ≃ V ⊕ K ⊕ N ⊕ N ⊕ N ⊕ (N × Bool × Bool) ⊕ P where
  toFun
    | .var a => .inl a
    | .row b => .inr (.inl b)
    | .edge n => .inr (.inr (.inl n))
    | .left n => .inr (.inr (.inr (.inl n)))
    | .right n => .inr (.inr (.inr (.inr (.inl n))))
    | .tab n t => .inr (.inr (.inr (.inr (.inr (.inl (n, t))))))
    | .pad p => .inr (.inr (.inr (.inr (.inr (.inr p)))))
  invFun
    | .inl a => .var a
    | .inr (.inl b) => .row b
    | .inr (.inr (.inl n)) => .edge n
    | .inr (.inr (.inr (.inl n))) => .left n
    | .inr (.inr (.inr (.inr (.inl n)))) => .right n
    | .inr (.inr (.inr (.inr (.inr (.inl (n, t)))))) => .tab n t
    | .inr (.inr (.inr (.inr (.inr (.inr p))))) => .pad p
  left_inv := by rintro (_ | _ | _ | _ | _ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _ | _ | _ | _ | _) <;> rfl

instance [Fintype N] [Fintype V] [Fintype K] [Fintype P] : Fintype (Seg N V K P) :=
  Fintype.ofEquiv _ Seg.equivSum.symm

/-- The options of a segment. -/
abbrev Opt : Seg N V K P → Type
  | .var _ => Bool
  | .row _ => Bool
  | .edge _ => Bool × Bool
  | .left _ => Option Bool
  | .right _ => Option Bool
  | .tab _ _ => Bool
  | .pad _ => Unit

instance (i : Seg N V K P) : Fintype (Opt i) := by cases i <;> infer_instance

instance (i : Seg N V K P) : DecidableEq (Opt i) := by cases i <;> infer_instance

/-- The ten gadgets of an incidence. -/
abbrev Gad (N : Type) : Type := N × ((Bool × Bool) ⊕ Option Bool ⊕ Option Bool)

/-- The two options of every gadget. -/
def gridPort (v : N → V) (w : N → K) : Gad N × Bool → Σ i : Seg N V K P, Opt i
  | ((n, .inl t), true) => ⟨.edge n, t⟩
  | ((n, .inl t), false) => ⟨.tab n t, false⟩
  | ((n, .inr (.inl o)), true) => ⟨.left n, o⟩
  | ((n, .inr (.inl (some b))), false) => ⟨.tab n (true, b), false⟩
  | ((n, .inr (.inl none)), false) => ⟨.var (v n), true⟩
  | ((n, .inr (.inr o)), true) => ⟨.right n, o⟩
  | ((n, .inr (.inr (some b))), false) => ⟨.tab n (b, true), false⟩
  | ((n, .inr (.inr none)), false) => ⟨.row (w n), true⟩

/-- The row of segments of a grid. -/
def gridRow (v : N → V) (w : N → K) (next : Equiv.Perm (Seg N V K P)) :
    Row (Opt (N := N) (V := V) (K := K) (P := P)) (Gad N) where
  next := next
  port := gridPort v w

/-- The selection that belongs to two families of bits. -/
def choice (v : N → V) (w : N → K) (x : V → Bool) (r : K → Bool) : ∀ i : Seg N V K P, Opt i
  | .var a => x a
  | .row b => r b
  | .edge n => (x (v n), r (w n))
  | .left n => if x (v n) then some (r (w n)) else none
  | .right n => if r (w n) then some (x (v n)) else none
  | .tab n t => decide (t = (x (v n), r (w n)))
  | .pad _ => ()

/-- The weights of the options: only the choices at the incidences carry one. -/
def gridWeight {R : Type*} [One R] (W : N → Bool → Bool → R) : ∀ i : Seg N V K P, Opt i → R
  | .edge n, t => W n t.1 t.2
  | _, _ => 1

variable {v : N → V} {w : N → K} {next : Equiv.Perm (Seg N V K P)}

/-- The three kinds of gadgets at one incidence. -/
theorem choice_cases : (∀ (t : Bool × Bool) (a c : Bool), (a, c) = t ↔ ¬decide (t = (a, c)) = false) ∧
    (∀ a c : Bool, (if a then some c else none) = none ↔ ¬a = true) ∧
    (∀ a c b : Bool, (if a then some c else none) = some b ↔ ¬decide ((true, b) = (a, c)) = false) ∧
    ∀ a c b : Bool, (if a then some c else none) = some b ↔ ¬decide ((b, true) = (c, a)) = false := by
  decide

/-- The selection of two families of bits uses every gadget exactly once. -/
theorem valid_choice (x : V → Bool) (r : K → Bool) : (gridRow v w next).Valid (choice v w x r) := by
  obtain ⟨h1, h2, h3, h4⟩ := choice_cases
  rintro ⟨n, t | (_ | b) | (_ | b)⟩
  exacts [h1 t _ _, h2 _ _, h3 _ _ b, h2 _ _, h4 _ _ b]

/-- The pair chosen at an incidence is the pair of the bits of its two ends. -/
theorem incidence_cases : ∀ (e : Bool × Bool) (l h : Option Bool) (a c : Bool),
    (∀ b, l = some b ↔ e = (true, b)) → (l = none ↔ a = false) →
    (∀ b, h = some b ↔ e = (b, true)) → (h = none ↔ c = false) →
      e = (a, c) ∧ l = (if a then some c else none) ∧ h = (if c then some a else none) := by
  decide

/-- The selections that use every gadget exactly once are those of the
pairs of families of bits. -/
theorem eq_choice_of_valid {J : ∀ i : Seg N V K P, Opt i} (h : (gridRow v w next).Valid J) :
    J = choice v w (fun a => J (.var a)) (fun b => J (.row b)) := by
  have key : ∀ n, J (.edge n) = (J (.var (v n)), J (.row (w n))) ∧
      J (.left n) = (if J (.var (v n)) then some (J (.row (w n))) else none) ∧
      J (.right n) = (if J (.row (w n)) then some (J (.var (v n))) else none) ∧
      ∀ t, J (.tab n t) = decide (t = J (.edge n)) := by
    intro n
    have ht : ∀ t, J (.edge n) = t ↔ ¬ J (.tab n t) = false := fun t => h (n, .inl t)
    have hl : ∀ b, J (.left n) = some b ↔ ¬ J (.tab n (true, b)) = false := fun b => h (n, .inr (.inl (some b)))
    have hr : ∀ b, J (.right n) = some b ↔ ¬ J (.tab n (b, true)) = false := fun b => h (n, .inr (.inr (some b)))
    have hl0 : J (.left n) = none ↔ ¬ J (.var (v n)) = true := h (n, .inr (.inl none))
    have hr0 : J (.right n) = none ↔ ¬ J (.row (w n)) = true := h (n, .inr (.inr none))
    obtain ⟨he, h1, h2⟩ := incidence_cases _ _ _ _ _ (fun b => (hl b).trans (ht _).symm)
      (hl0.trans Bool.eq_false_iff.symm) (fun b => (hr b).trans (ht _).symm) (hr0.trans Bool.eq_false_iff.symm)
    refine ⟨he, h1, h2, fun t => ?_⟩
    rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_comm (a := t), ht t, Bool.not_eq_false]
  funext i
  rcases i with a | b | n | n | n | ⟨n, t⟩ | p
  · rfl
  · rfl
  · exact (key n).1
  · exact (key n).2.1
  · exact (key n).2.2.1
  · exact ((key n).2.2.2 t).trans (by rw [(key n).1]; rfl)
  · rfl

/-- Every option of a grid, except at most one in its segment, runs through a gadget. -/
theorem gridRow_noParallel (hv : Function.Surjective v) (hw : Function.Surjective w) :
    (gridRow v w next).NoParallel := by
  intro i o o' h h'
  rcases i with a | b | n | n | n | ⟨n, t⟩ | p
  · obtain ⟨n, rfl⟩ := hv a
    cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inr (.inl none)), false)) |
      exact absurd rfl (h' ((n, .inr (.inl none)), false))
  · obtain ⟨n, rfl⟩ := hw b
    cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inr (.inr none)), false)) |
      exact absurd rfl (h' ((n, .inr (.inr none)), false))
  · exact absurd rfl (h ((n, .inl o), true))
  · exact absurd rfl (h ((n, .inr (.inl o)), true))
  · exact absurd rfl (h ((n, .inr (.inr o)), true))
  · cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inl t), false)) |
      exact absurd rfl (h' ((n, .inl t), false))
  · rfl

variable [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype P] [DecidableEq P]

/-- Over every commutative semiring, a sum over two families of bits of
products of weights, one for every incidence, is the sum over the cycles through all vertices of the grid graph. -/
theorem hcSum_grid {R : Type*} [CommSemiring R] (hv : Function.Surjective v) (hw : Function.Surjective w)
    (hnext : next.IsCycleOn Set.univ) (W : N → Bool → Bool → R) :
    hcSum ((gridRow v w next).weight (gridWeight W)) =
      ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  rw [Row.hcSum_weight (T := gridRow v w next) hnext (gridRow_noParallel hv hw), ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij' (fun p _ => choice v w p.1 p.2) (fun J _ => (fun a => J (.var a), fun b => J (.row b)))
    (fun p _ => mem_filter.2 ⟨mem_univ _, valid_choice _ _⟩) (fun _ _ => mem_univ _) (fun _ _ => rfl)
    (fun J hJ => (eq_choice_of_valid (mem_filter.1 hJ).2).symm) fun p _ => ?_
  refine Fintype.prod_of_injective Seg.edge (fun a b h => Seg.edge.inj h) _ _ (fun i hi => ?_) fun n => rfl
  rcases i with _ | _ | n | _ | _ | _ | _ <;> first | rfl | exact absurd ⟨n, rfl⟩ hi

omit [DecidableEq N] [DecidableEq V] [DecidableEq K] [DecidableEq P] in
/-- The number of vertices of a grid. -/
theorem card_gridVtx :
    Fintype.card (Vtx (Seg N V K P) (Gad N)) =
      Fintype.card V + Fintype.card K + 37 * Fintype.card N + Fintype.card P := by
  rw [Vtx.card_eq, Fintype.card_congr (Seg.equivSum (N := N) (V := V) (K := K) (P := P))]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_option]
  ring

/-- Renaming the points does not change the sum over the cycles. -/
theorem hcSum_equiv {R : Type*} [CommSemiring R] {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (M : B → B → R) : hcSum (fun a a' => M (e a) (e a')) = hcSum M := by
  classical
  unfold hcSum
  refine Finset.sum_equiv e.permCongr (fun σ => ?_) fun σ _ => ?_
  · simp only [mem_filter, mem_univ, true_and]
    have hz : ∀ (m : ℤ) a, (e.permCongr σ ^ m) (e a) = e ((σ ^ m) a) := by
      intro m a
      have h : e.permCongr σ ^ m = e.permCongr (σ ^ m) := (map_zpow e.permCongrHom σ m).symm
      rw [h, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    constructor
    · refine fun h => ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun a _ b _ => ?_⟩
      obtain ⟨m, hm⟩ := h.2 (Set.mem_univ (e.symm a)) (Set.mem_univ (e.symm b))
      refine ⟨m, ?_⟩
      have := hz m (e.symm a)
      rwa [hm, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    · refine fun h => ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun a _ b _ => ?_⟩
      obtain ⟨m, hm⟩ := h.2 (Set.mem_univ (e a)) (Set.mem_univ (e b))
      exact ⟨m, e.injective ((hz m a).symm.trans hm)⟩
  · exact Fintype.prod_equiv e _ _ fun a => by rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Substitution in the Hamiltonian cycle polynomial gives the sum over the cycles. -/
theorem aeval_genHC {F A : Type} [Field F] {m : ℕ} (M : Fin m × Fin m → MvPolynomial A F) :
    aeval M (Statement.hc F m) = hcSum fun i j => M (i, j) := by
  classical
  unfold Statement.hc hcSum
  simp only [map_sum, map_prod, aeval_X]

end Hc

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "The flat case": sums over bits as permanents
-/

namespace Paper

open Finset MvPolynomial Nc ValiantBorder

/-- The fixed entries of the grid matrix and the sums of weights of one row of clauses. -/
def GridEntry {R N K : Type} [CommRing R] (h : R) (w : N → K) (W : N → Bool → Bool → R) (z : R) : Prop :=
  z = 0 ∨ z = 1 ∨ z = -1 ∨ z = h ∨ z = -h ∨ ∃ k, z ∈ AddSubmonoid.closure {y : R | ∃ n x r, w n = k ∧ y = W n x r}

/-- **Paper: Proposition prop:grid.** "Let R be a commutative ring with an element ½, let v : N → V, w : N → K be
surjections of finite sets, and let W_n(x,r) ∈ R. Then ∑_x ∑_r ∏_n W_n(x_{v(n)}, r_{w(n)}) is the permanent of an S×S
matrix, for every S ≥ 3|N|, whose entries are 0, ±1, ±½ and sums of values W_n with the same w(n)." -/
theorem prop_grid {R : Type} [CommRing R] (h : R) (hh : h * 2 = 1) {N V K : Type} [Fintype N] [DecidableEq N]
    [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] (v : N → V) (w : N → K) (hv : Function.Surjective v)
    (hw : Function.Surjective w) (W : N → Bool → Bool → R) {S : ℕ} (hS : 3 * Fintype.card N ≤ S) :
    ∃ M : Matrix (Fin S) (Fin S) R, (∀ i j, GridEntry h w W (M i j)) ∧
      M.permanent = ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  obtain ⟨σ, ρ, hρ, H⟩ := exists_grid (R := R) v w hv hw
  have hcard : Fintype.card (N × Option Bool) ≤ S := by
    refine le_trans (le_of_eq ?_) hS
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
    ring
  obtain ⟨M, hM, hent⟩ := exists_permanent_fin (gridMatrix h σ ρ W) hcard
  refine ⟨M, fun i j => ?_, hM.trans (H h hh W)⟩
  rcases hent i j with (h0 | h1) | ⟨⟨n, q⟩, d, he⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  rw [he]
  have hh2 : h + h = 1 := by rw [← mul_two]; exact hh
  obtain ⟨n', q'⟩ := d
  rcases q with _ | _ | _
  · rcases q' with _ | _ | _ <;> by_cases e1 : n' = n <;> by_cases e2 : n' = σ n <;>
      simp [GridEntry, gridMatrix, ind, e1, e2, Prod.ext_iff] <;> simp_all
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w n, ?_⟩))))
    have mem : ∀ (m : N) (c₀ : N × Option Bool) x r, w m = w n →
        ind c₀ (W m x r) (n', q') ∈ AddSubmonoid.closure {y : R | ∃ m x r, w m = w n ∧ y = W m x r} := by
      intro m c₀ x r hm
      unfold ind
      split_ifs
      · exact AddSubmonoid.subset_closure ⟨m, x, r, hm, rfl⟩
      · exact zero_mem _
    exact add_mem (add_mem (add_mem (mem n _ _ _ rfl) (mem n _ _ _ rfl)) (mem _ _ _ _ (hρ n))) (mem _ _ _ _ (hρ n))
  · rcases q' with _ | _ | _ <;> by_cases e1 : n' = n <;> by_cases e2 : n' = σ n <;>
      simp [GridEntry, gridMatrix, ind, e1, e2, Prod.ext_iff] <;> simp_all


/-- The affine form of Proposition prop:grid: if the weights at an incidence are affine in the variable of its second
class, the matrix has entries that are affine in one variable each. So the permanent is complete for grid sums. -/
theorem gridComplete_perm {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : GridComplete F (genPerm F) 3 := by
  intro ι N V K _ _ _ _ _ _ v w hv hw W o hW S hS
  have hC2 : (C (2⁻¹ : F) : MvPolynomial ι F) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  obtain ⟨M, hM, hp⟩ := prop_grid (C (2⁻¹ : F)) hC2 v w hv hw W hS
  refine ⟨fun q => M q.1 q.2, fun q => ?_, by rw [← hp, ← aeval_genPerm]⟩
  rcases hM q.1 q.2 with h | h | h | h | h | ⟨k, h⟩
  · exact Or.inl ⟨0, h.trans C_0.symm⟩
  · exact Or.inl ⟨1, h.trans C_1.symm⟩
  · exact Or.inl ⟨-1, h.trans (by rw [map_neg, C_1])⟩
  · exact Or.inl ⟨2⁻¹, h⟩
  · exact Or.inl ⟨-2⁻¹, h.trans (by rw [map_neg])⟩
  · refine isAffine_of_mem (o := o k) ?_
    refine (AddSubmonoid.closure_le (S := (affIn (F := F) (o k)).toAddSubmonoid)).2 ?_ h
    rintro _ ⟨n, x, r, rfl, rfl⟩
    exact hW n x r

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, appendix "All fields and the Hamiltonian cycle polynomial": grids as Hamiltonian cycles
-/

namespace Paper

open Finset MvPolynomial Nc ValiantBorder

/-- **Paper: Proposition prop:hc-grid.** "In every commutative ring, the sum in the proposition on grids is HC_S of a
matrix with entries 0, 1 and single values W_n, for every S ≥ 40|N|." -/
theorem prop_hc_grid {R : Type} [CommRing R] {N V K : Type} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K] (v : N → V) (w : N → K) (hv : Function.Surjective v) (hw : Function.Surjective w)
    (W : N → Bool → Bool → R) {S : ℕ} (hS : 40 * Fintype.card N ≤ S) :
    ∃ M : Fin S → Fin S → R, (∀ i j, M i j = 0 ∨ M i j = 1 ∨ ∃ n x r, M i j = W n x r) ∧
      Hc.hcSum M = ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  have hV := Fintype.card_le_of_surjective v hv
  have hK := Fintype.card_le_of_surjective w hw
  let P := Fin (S - (Fintype.card V + Fintype.card K + 37 * Fintype.card N))
  obtain ⟨next, hnext, -⟩ := Finset.exists_cycleOn (Finset.univ : Finset (Hc.Seg N V K P))
  rw [Finset.coe_univ] at hnext
  have hcard : Fintype.card (Hc.Vtx (Hc.Seg N V K P) (Hc.Gad N)) = Fintype.card (Fin S) := by
    rw [Hc.card_gridVtx, Fintype.card_fin, Fintype.card_fin]
    omega
  let e := Fintype.equivOfCardEq hcard
  let T := Hc.gridRow v w next
  refine ⟨fun i j => T.weight (Hc.gridWeight W) (e.symm i) (e.symm j), fun i j => ?_,
    (Hc.hcSum_equiv e.symm (T.weight (Hc.gridWeight W))).trans (Hc.hcSum_grid hv hw hnext W)⟩
  show T.weight (Hc.gridWeight W) (e.symm i) (e.symm j) = 0 ∨ T.weight (Hc.gridWeight W) (e.symm i) (e.symm j) = 1 ∨
    ∃ n x r, T.weight (Hc.gridWeight W) (e.symm i) (e.symm j) = W n x r
  generalize e.symm i = a, e.symm j = b
  rcases a with s | ⟨g, side⟩ | g
  · simp only [Hc.Row.weight]
    by_cases hex : ∃ o : Hc.Opt s, T.place ⟨s, o⟩ 0 = b
    · obtain ⟨o, ho⟩ := hex
      rw [Finset.sum_eq_single o]
      · cases s with
        | edge n => exact Or.inr (Or.inr ⟨n, o.1, o.2, rfl⟩)
        | _ => exact Or.inr (Or.inl rfl)
      · intro o' ho' hne
        exact absurd (Hc.Row.place_zero_injective (Hc.gridRow_noParallel hv hw) ((mem_filter.1 ho').2.trans ho.symm)) hne
      · exact fun h => absurd (mem_filter.2 ⟨mem_univ o, ho⟩) h
    · exact Or.inl (Finset.sum_eq_zero fun o ho => absurd ⟨o, (mem_filter.1 ho).2⟩ hex)
  · simp only [Hc.Row.weight]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · simp only [Hc.Row.weight]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl



/-- The affine form of Proposition prop:hc-grid: the Hamiltonian cycle polynomial is complete for grid sums in every
characteristic. -/
theorem gridComplete_hc (F : Type) [Field F] : GridComplete F (Statement.hc F) 40 := by
  intro ι N V K _ _ _ _ _ _ v w hv hw W o hW S hS
  obtain ⟨M, hM, hp⟩ := prop_hc_grid v w hv hw W hS
  refine ⟨fun q => M q.1 q.2, fun q => ?_, by rw [Hc.aeval_genHC]; exact hp⟩
  rcases hM q.1 q.2 with h | h | ⟨n, x, r, h⟩
  · exact Or.inl ⟨0, h.trans C_0.symm⟩
  · exact Or.inl ⟨1, h.trans C_1.symm⟩
  · show IsAffine (M q.1 q.2)
    rw [h]
    exact isAffine_of_mem (hW n x r)

end Paper
end

theorem solution (K : Type) [Field K] :
    ValiantBorder.GridComplete K (Statement.hc K) 40 ∧
      ((2 : K) ≠ 0 → ValiantBorder.GridComplete K (Statement.perm K) 3) :=
  ⟨Paper.gridComplete_hc K, Paper.gridComplete_perm⟩
